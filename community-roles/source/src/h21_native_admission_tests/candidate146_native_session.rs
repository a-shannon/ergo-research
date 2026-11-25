//! Native c146 paired-cut R/first-Score/Cap producer diagnostic.
//! The ignored selector checks one pinned ERFV frame; it is not a proof,
//! verifier, common witness, or light-client admission.

use super::*;
use crate::{
    h21_row_support::{MapParameters, ParentMapSources},
    h21_scheduled_max_cap::Patch,
    legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map},
    native_v_max_cap_loan::{NativeVGroup, NativeVLoan},
    native_w_loan::{NativeWLoanGroup, WLoanDestination},
    score_prefix_r_anchor::{
        self, Destination, Endpoint, Inputs, Plan as ScorePlan, SourceIdentity,
    },
};
use num_bigint::BigUint;

const CUTS: [u64; 2] = [1_827_840, 1_827_775];
const W_OWNERS: [usize; 3] = [417_789, 845_757, 845_758];
const W_HEIGHTS: [usize; 3] = [417_791, 845_759, 845_760];
const W_LOCAL: usize = 987_450;
const SESSION_SHA: [u8; 32] = [
    0xa6, 0x8d, 0x86, 0x56, 0x2a, 0x56, 0xc5, 0xb7, 0x1c, 0xf2, 0x18, 0x0e, 0x47, 0x62, 0xbf, 0x87,
    0x75, 0xb1, 0x06, 0x1b, 0x69, 0x53, 0xbf, 0xf7, 0x28, 0x1e, 0xc5, 0x0b, 0x7e, 0xe5, 0x2c, 0x5e,
];

fn phase(label: &str, started: Instant) {
    println!(
        "C146_NATIVE_SESSION_PHASE label={label} elapsed_s={:.6}",
        started.elapsed().as_secs_f64()
    );
    std::io::stdout().flush().expect("flush c146 native phase");
}

fn source_identity(frame: [u8; 32], context: usize) -> SourceIdentity {
    SourceIdentity {
        frame,
        cut: CUTS[context],
        parent_root: None,
    }
}

fn map_parameters(cuts: &[candidate138_native_global_u::NativeCutU; 2]) -> [MapParameters; 2] {
    std::array::from_fn(|c| MapParameters {
        cut: cuts[c].cut,
        exponent: cuts[c].envelope.exponent,
        lower: cuts[c].selected_lower,
    })
}

/// The fields are private and this token is returned only after complete ERFV
/// parsing, whole-frame SHA-256, and a post-read filesystem identity check.
struct VerifiedFrame {
    prefix: NativePrefix,
    plan: WorkTreeHistoryPlan,
    digest: [u8; 32],
}

impl VerifiedFrame {
    fn read(path: &Path) -> Result<Self, String> {
        if !path.is_absolute() {
            return Err("frame path must be absolute".into());
        }
        let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
        if !before.is_file() || before.file_type().is_symlink() || before.len() != FRAME_BYTES {
            return Err("pinned frame type/length mismatch".into());
        }
        let file = File::open(path).map_err(|e| e.to_string())?;
        if file.metadata().map_err(|e| e.to_string())?.len() != FRAME_BYTES {
            return Err("opened frame length mismatch".into());
        }
        let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
        preamble(&mut frame, 1_827_839, N as u32)?;
        let (prefix, extensions) = {
            let mut headers = HeaderIter::new(&mut frame, N);
            let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
            if headers.remaining != 0 {
                return Err("ERFV header records remain".into());
            }
            (prefix, headers.extensions)
        };
        if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
            return Err("ERFV prefix/census/extension mismatch".into());
        }
        frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
        if hex(&SESSION_SHA) != FRAME_SHA256 {
            return Err("c146 frame digest encoding mismatch".into());
        }
        let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
        if !after.is_file()
            || after.file_type().is_symlink()
            || after.len() != FRAME_BYTES
            || before.len() != after.len()
            || before.modified().map_err(|e| e.to_string())?
                != after.modified().map_err(|e| e.to_string())?
        {
            return Err("pinned frame changed during complete read".into());
        }
        let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
        validate_native_plan_input(&plan, &prefix)?;
        Ok(Self {
            prefix,
            plan,
            digest: SESSION_SHA,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ParentIdentity {
    headers: u64,
    slot_log: usize,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
}

impl ParentIdentity {
    fn capture(frame: &VerifiedFrame) -> Self {
        Self {
            headers: frame.plan.headers(),
            slot_log: frame.plan.slot_log(),
            root: frame.prefix.root(),
            total: frame.prefix.total_be28(),
            profile: frame.prefix.profile(),
        }
    }
    fn matches(&self, frame: &VerifiedFrame) -> bool {
        self.headers == frame.plan.headers()
            && self.slot_log == frame.plan.slot_log()
            && self.root == frame.prefix.root()
            && self.total == frame.prefix.total_be28()
            && self.profile == frame.prefix.profile()
    }
}

/// This constructor accepts no caller U, W, V, patch, or endpoint values.
/// It derives all session inputs from one verified frame and one parent plan.
struct NativeSession {
    frame: VerifiedFrame,
    parent_identity: ParentIdentity,
    parent_maps: ParentMapSources,
    score: ScorePlan,
    inputs: Inputs,
    d844672: BigUint,
    patches: [Patch; 3],
    v_group: NativeVGroup,
    w_destination: WLoanDestination,
}

impl NativeSession {
    fn validate_parent_binding(
        parent_maps: &ParentMapSources,
        parent: &WorkTreeHistoryPlan,
        claimed: &crate::h21_row_support::ParentMapBinding,
    ) -> Result<(), String> {
        parent_maps.validate(parent, claimed)
    }

    fn from_verified(frame: VerifiedFrame, started: Instant) -> Result<Self, String> {
        let parent_identity = ParentIdentity::capture(&frame);
        if frame.digest != SESSION_SHA || !parent_identity.matches(&frame) {
            return Err("c146 verified frame/parent identity mismatch".into());
        }
        phase("VERIFIED_FRAME_AND_PARENT", started);

        // Fold both source-owned U cuts together; callers cannot supply a pair.
        let cuts = candidate138_native_global_u::fold_native_global_u_cut_pair(
            &frame.plan,
            &frame.prefix,
        )?;
        if cuts
            .iter()
            .any(|cut| cut.consumer_binding.parent_root.is_some())
        {
            return Err("c146 cut consumer Map must remain rootless".into());
        }
        if cuts[0].envelope.u != cuts[1].envelope.u
            || cuts[0].envelope.exponent != 55
            || cuts
                .iter()
                .any(|cut| cut.lower_d != cuts[0].lower_d || cut.lower_owner != 841_727)
        {
            return Err("c146 paired source-derived U/lower binding".into());
        }
        phase("U_PAIR_READY", started);

        let parameters = map_parameters(&cuts);
        let parent_maps = ParentMapSources::new(&frame.plan, parameters)?;
        parent_maps.validate(&frame.plan, parent_maps.binding())?;
        let maps: [Map; 2] = std::array::from_fn(|c| {
            Map::new_modern_global_u_selected_lower(
                CUTS[c],
                H,
                cuts[c].envelope.exponent,
                cuts[c].selected_lower,
            )
            .expect("source-derived selected Map")
        });
        if maps.iter().any(|map| map.binding().parent_root.is_some())
            || maps[0].binding() != parent_maps.binding().maps[0]
            || maps[1].binding() != parent_maps.binding().maps[1]
            || maps[0].binding() != cuts[0].consumer_binding
            || maps[1].binding() != cuts[1].consumer_binding
        {
            return Err("c146 full parent/cut Map binding mismatch".into());
        }
        let sources = [
            source_identity(frame.digest, 0),
            source_identity(frame.digest, 1),
        ];
        let score = ScorePlan::new(&maps, sources.clone())?;

        // Three immutable physical Upper rows support six separate contexts.
        let group = NativeWLoanGroup::issue(&frame.plan, &frame.prefix)?;
        let mut w_destination = WLoanDestination::default();
        let mut w_calls = BTreeSet::new();
        group.consume(
            &frame.plan,
            &frame.prefix,
            |context, owner, source, alias| {
                if context >= 2
                    || !W_OWNERS.contains(&owner)
                    || source != alias
                    || source.bits() > 224
                    || !w_calls.insert((context, owner))
                {
                    return Err("c146 grouped W context/owner/source/alias binding".into());
                }
                Ok(())
            },
            &mut w_destination,
        )?;
        if w_calls.len() != 6
            || !(0..2).all(|c| W_OWNERS.iter().all(|o| w_destination.get(c, *o).is_some()))
        {
            return Err("c146 grouped W consumer census".into());
        }
        for owner in W_OWNERS {
            if w_destination.get(0, owner) != w_destination.get(1, owner) {
                return Err("c146 shared physical W differs across contexts".into());
            }
        }
        phase("W_SIX_CONTEXTS_READY", started);

        let v_loan = NativeVLoan::issue(&frame.plan, &frame.prefix)?;
        let v_group = v_loan.replay_group(&frame.plan, &frame.prefix)?;
        if v_group.patches[0].writers()
            != [
                crate::h21_scheduled_max_cap::Writer::Max {
                    context: 0,
                    end: 844_672,
                },
                crate::h21_scheduled_max_cap::Writer::Max {
                    context: 1,
                    end: 844_672,
                },
            ]
        {
            return Err("c146 V MAX source writer tags".into());
        }

        let exports = NativeExports::new_for_history(&frame.plan, &frame.prefix)?;
        let mut imported = BigUint::from(0u8);
        for bit in 0..224 {
            let wire = 844_670usize
                .checked_mul(1 << 20)
                .and_then(|x| x.checked_add(987_674 + bit))
                .ok_or("c146 D import coordinate overflow")?;
            if exports.bit(wire)? {
                imported |= BigUint::from(1u8) << bit;
            }
        }
        let compact = frame
            .prefix
            .compact_n_bits(844_672)
            .and_then(crate::work_tree_work::native_decode)?;
        if imported != compact || compact != v_group.first_d {
            return Err("c146 D844672 prefix/V/physical export mismatch".into());
        }
        phase("V_GROUP_AND_D_IMPORT_READY", started);

        let endpoints = std::array::from_fn(|context| {
            std::array::from_fn(|j| Endpoint {
                source: sources[context].clone(),
                height: W_HEIGHTS[j],
                owner: W_OWNERS[j],
                local: W_LOCAL,
                value: w_destination.get(context, W_OWNERS[j]).unwrap().clone(),
            })
        });
        let modern_w = w_destination
            .get(0, 845_758)
            .ok_or("missing modern W")?
            .clone();
        let inputs = Inputs {
            endpoints,
            modern_w,
            modern_v: v_group.cap_values.clone(),
        };
        let [max_patch, lookahead_patch, cap_patch] = v_group.patches.clone();
        Ok(Self {
            frame,
            parent_identity,
            parent_maps,
            score,
            inputs,
            d844672: compact,
            patches: [max_patch, lookahead_patch, cap_patch],
            v_group,
            w_destination,
        })
    }

    fn recheck_identity(&self) -> Result<(), String> {
        validate_native_plan_input(&self.frame.plan, &self.frame.prefix)?;
        if self.frame.digest != SESSION_SHA
            || !self.parent_identity.matches(&self.frame)
            || Self::validate_parent_binding(
                &self.parent_maps,
                &self.frame.plan,
                self.parent_maps.binding(),
            )
            .is_err()
            || self
                .parent_maps
                .binding()
                .maps
                .iter()
                .any(|map| map.parent_root.is_some())
        {
            return Err("c146 session frame/parent/Map identity changed".into());
        }
        self.validate_claims(&self.inputs, &self.d844672, self.parent_maps.binding())?;
        if self
            .patches
            .iter()
            .zip(self.v_group.patches.iter())
            .any(|(actual, source)| {
                actual.writers() != source.writers() || !actual.source_replay_matches(source)
            })
        {
            return Err("c146 session retained V patches changed".into());
        }
        Ok(())
    }

    fn validate_claims(
        &self,
        inputs: &Inputs,
        difficulty_d: &BigUint,
        claimed_parent: &crate::h21_row_support::ParentMapBinding,
    ) -> Result<(), String> {
        Self::validate_parent_binding(&self.parent_maps, &self.frame.plan, claimed_parent)?;
        if difficulty_d != &self.v_group.first_d
            || inputs.modern_v != self.v_group.cap_values
            || inputs.modern_w
                != *self
                    .w_destination
                    .get(0, 845_758)
                    .ok_or("missing W consumer")?
        {
            return Err("c146 native session D/V/W source binding".into());
        }
        for context in 0..2 {
            for j in 0..2 {
                let endpoint = &inputs.endpoints[context][j];
                if self.w_destination.get(context, W_OWNERS[j]) != Some(&endpoint.value)
                    || endpoint.source != source_identity(self.frame.digest, context)
                    || endpoint.height != W_HEIGHTS[j]
                    || endpoint.owner != W_OWNERS[j]
                    || endpoint.local != W_LOCAL
                {
                    return Err("c146 session retained W source changed".into());
                }
            }
            if self.w_destination.get(context, W_OWNERS[2]) != Some(&inputs.modern_w) {
                return Err("c146 native session D/V/W source binding".into());
            }
        }
        if inputs.endpoints[0][0].value != inputs.endpoints[1][0].value
            || inputs.endpoints[0][1].value != inputs.endpoints[1][1].value
        {
            return Err("c146 shared physical W differs across contexts".into());
        }
        Ok(())
    }

    fn publish(&self, destination: &mut Destination) -> Result<(), String> {
        self.publish_claims(
            &self.inputs,
            &self.d844672,
            self.parent_maps.binding(),
            destination,
        )
    }

    fn publish_claims(
        &self,
        inputs: &Inputs,
        difficulty_d: &BigUint,
        claimed_parent: &crate::h21_row_support::ParentMapBinding,
        destination: &mut Destination,
    ) -> Result<(), String> {
        let staged = self.stage_claims(inputs, difficulty_d, claimed_parent)?;
        score_prefix_r_anchor::publish_session(&self.score, destination, staged)
    }

    fn stage_claims(
        &self,
        inputs: &Inputs,
        difficulty_d: &BigUint,
        claimed_parent: &crate::h21_row_support::ParentMapBinding,
    ) -> Result<score_prefix_r_anchor::Staged, String> {
        self.recheck_identity()?;
        self.validate_claims(inputs, difficulty_d, claimed_parent)?;
        if inputs.endpoints.iter().flatten().any(|endpoint| {
            endpoint.source.frame != self.frame.digest || endpoint.source.parent_root.is_some()
        }) {
            return Err("c146 session endpoint source identity".into());
        }
        let staged = score_prefix_r_anchor::stage_session(
            &self.score,
            inputs,
            difficulty_d,
            &self.patches[0],
            &self.patches[1],
            &self.patches[2],
        )?;
        score_prefix_r_anchor::validate_session(&self.score, &staged)?;
        self.recheck_identity()?;
        self.validate_claims(inputs, difficulty_d, claimed_parent)?;
        Ok(staged)
    }

    /// Source-bound Score/Cap rows and values for a later common ROW/X commit.
    /// This keeps the native frame and parent checks inside the private session.
    fn project_native_score_values(
        &self,
    ) -> Result<score_prefix_r_anchor::ScoreCapValueProjection, String> {
        let staged = self.stage_claims(&self.inputs, &self.d844672, self.parent_maps.binding())?;
        let projection =
            score_prefix_r_anchor::project_local_score_cap_values(&self.score, &staged)?;
        self.recheck_identity()?;
        Ok(projection)
    }

    fn stage_common_roster(
        &self,
        carry: &super::candidate136_native_bundle::CarryMapExport,
        daa: &super::candidate151_native_daa::NativeDaaStage,
    ) -> Result<super::candidate154_common_roster::CommonRoster, String> {
        self.recheck_identity()?;
        let score = self.project_native_score_values()?;
        let roster = super::candidate154_common_roster::stage_common_roster(
            &self.frame.plan,
            &self.frame.prefix,
            self.frame.digest,
            carry,
            daa,
            &score,
            &self.patches[1],
            self.parent_maps.binding().maps.clone(),
        )?;
        self.recheck_identity()?;
        Ok(roster)
    }

    fn run_negatives(&self) -> Result<usize, String> {
        let mut destination = Destination::default();
        let before = destination.clone();
        let mut bad_d = self.d844672.clone();
        bad_d += 1u8;
        let error = self
            .publish_claims(
                &self.inputs,
                &bad_d,
                self.parent_maps.binding(),
                &mut destination,
            )
            .unwrap_err();
        if error != "c146 native session D/V/W source binding" || destination != before {
            return Err(format!("c146 D mutant rejection: {error}"));
        }

        let mut bad_v = self.inputs.clone();
        bad_v.modern_v[0] += 1u8;
        let error = self
            .publish_claims(
                &bad_v,
                &self.d844672,
                self.parent_maps.binding(),
                &mut destination,
            )
            .unwrap_err();
        if error != "c146 native session D/V/W source binding" || destination != before {
            return Err(format!("c146 V mutant rejection: {error}"));
        }

        let mut bad_w = self.inputs.clone();
        bad_w.endpoints[0][1].value += 1u8;
        let error = self
            .publish_claims(
                &bad_w,
                &self.d844672,
                self.parent_maps.binding(),
                &mut destination,
            )
            .unwrap_err();
        if error != "c146 session retained W source changed" || destination != before {
            return Err(format!("c146 W mutant rejection: {error}"));
        }

        // One modern-W mutation changes both the Score input and the W alias
        // derived from it; the session must reject it against the loaned source.
        let mut bad_coherent_w_score = self.inputs.clone();
        bad_coherent_w_score.modern_w += 1u8;
        let error = self
            .publish_claims(
                &bad_coherent_w_score,
                &self.d844672,
                self.parent_maps.binding(),
                &mut destination,
            )
            .unwrap_err();
        if error != "c146 native session D/V/W source binding" || destination != before {
            return Err(format!("c146 coherent W/Score mutant rejection: {error}"));
        }

        let mut bad_parent = self.parent_maps.binding().clone();
        bad_parent.root[0] ^= 1;
        let error = self
            .publish_claims(&self.inputs, &self.d844672, &bad_parent, &mut destination)
            .unwrap_err();
        if error != "c141 complete parent/Map source binding" || destination != before {
            return Err(format!("c146 parent mutant rejection: {error}"));
        }

        let mut invented_cut_root = self.parent_maps.binding().clone();
        invented_cut_root.maps[1].parent_root = Some(invented_cut_root.root);
        let error = self
            .publish_claims(
                &self.inputs,
                &self.d844672,
                &invented_cut_root,
                &mut destination,
            )
            .unwrap_err();
        if error != "c141 complete parent/Map source binding" || destination != before {
            return Err(format!("c146 invented cut-root rejection: {error}"));
        }

        let mut bad_context = self.inputs.clone();
        bad_context.endpoints[1][0].source.cut = CUTS[0];
        let error = self
            .publish_claims(
                &bad_context,
                &self.d844672,
                self.parent_maps.binding(),
                &mut destination,
            )
            .unwrap_err();
        if error != "c146 session retained W source changed" || destination != before {
            return Err(format!("c146 wrong-context source rejection: {error}"));
        }

        let duplicate = self.patches[0].duplicate_first_span_for_test();
        let error = score_prefix_r_anchor::stage_session(
            &self.score,
            &self.inputs,
            &self.d844672,
            &duplicate,
            &self.patches[1],
            &self.patches[2],
        )
        .unwrap_err();
        if error != "c146 session duplicate X writer including equal" || destination != before {
            return Err(format!("c146 duplicate X mutant rejection: {error}"));
        }
        let mut wrong_tag = self.patches[0].clone();
        wrong_tag.set_writer_for_test(
            0,
            crate::h21_scheduled_max_cap::Writer::Max {
                context: 1,
                end: 844_672,
            },
        )?;
        let error = score_prefix_r_anchor::stage_session(
            &self.score,
            &self.inputs,
            &self.d844672,
            &wrong_tag,
            &self.patches[1],
            &self.patches[2],
        )
        .unwrap_err();
        if error != "c146 session MAX/Cap writer context/source mismatch" || destination != before {
            return Err(format!("c146 V tag mutant rejection: {error}"));
        }
        Ok(9)
    }
}

/// A new source-only scalar selector for the eligible draft-0.8 cut pair.
/// It must run at most once under a separately reviewed bounded Job runner.
/// It does not build a physical Score row, common X, PCS, proof, or client.
#[test]
#[ignore = "new one-use c166 eligible scalar trial; exact source and isolated Job runner review required"]
fn h21_candidate166_native_eligible_cut_score_scalar_once() -> Result<(), String> {
    use super::candidate138_native_global_u::candidate162_cut_score_source::{
        admit_sampled_guard, reduce_native_cut_pair_eligible08,
    };

    let started = Instant::now();
    let path =
        std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame environment variable")?;
    let frame = VerifiedFrame::read(Path::new(&path))?;
    println!(
        "C166_ELIGIBLE_SCALAR_PHASE label=VERIFIED_FRAME elapsed_s={:.6}",
        started.elapsed().as_secs_f64()
    );
    std::io::stdout().flush().map_err(|e| e.to_string())?;

    let parent = ParentIdentity::capture(&frame);
    let descriptor = crate::h21_scheduled_max_cap::CutDescriptor::eligible08();
    if frame.digest != SESSION_SHA
        || !parent.matches(&frame)
        || parent.headers != 1_827_840
        || parent.slot_log != 21
        || frame.plan.slots() != 1 << 21
        || frame.prefix.slot_count() != 1 << 21
        || descriptor.terminals() != [1_827_840, 1_810_842]
        || descriptor.guards() != [1_810_905, 1_810_842]
    {
        return Err("c166 verified frame/parent/eligible geometry".into());
    }

    // One source-bound call folds U separately for each cut and replays D
    // once for both V projections. Neither cut inherits the other's U.
    let pair = reduce_native_cut_pair_eligible08(&frame.plan, &frame.prefix)?;
    println!(
        "C166_ELIGIBLE_SCALAR_PHASE label=SOURCE_REDUCED elapsed_s={:.6}",
        started.elapsed().as_secs_f64()
    );
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    let work = |height| -> Result<BigUint, String> {
        Ok(BigUint::from_bytes_be(&frame.prefix.interval(height)?.1))
    };
    for context in 0..2 {
        let result = &pair[context];
        if result.descriptor != descriptor
            || result.context != context
            || result.terminal != descriptor.terminals()[context]
            || result.last_origin != descriptor.guards()[context]
            || result.modern_spans != [7_542, 7_541][context]
            || result.parent.headers != parent.headers as usize
            || result.parent.slot_log != parent.slot_log
            || result.parent.root != parent.root
            || result.parent.total != parent.total
            || result.parent.profile != parent.profile
            || result.global_u == BigUint::from(0u8)
            || result.global_u > (BigUint::from(1u8) << 64usize)
            || result.work_at_cut != work(result.terminal)?
            || result.t1 != work(417_791)?
            || result.t2 != work(845_759)?
        {
            return Err(format!("c166 cut/context/parent/source mismatch context={context}"));
        }
        let maturities = if context == 0 {
            [43_410u64, 23_155]
        } else {
            [17_867, 9_548]
        };
        let premodern = (&result.t1 + &result.global_u * maturities[0])
            .max(&result.t2 + &result.global_u * maturities[1]);
        if result.premodern != premodern
            || result.maximum < result.premodern
            || result.maximum.bits() > 225
        {
            return Err(format!("c166 premodern/maximum mismatch context={context}"));
        }
        if context == 0 {
            if result.sampled_guard != Some(true) {
                return Err("c166 eligible Eq21 sampled guard rejected".into());
            }
            admit_sampled_guard(descriptor, result)?;
        } else if result.sampled_guard.is_some()
            || admit_sampled_guard(descriptor, result).is_ok()
            || result.maximum <= result.work_at_cut
        {
            return Err("c166 Eq26 AB/WB lower bound or guard separation".into());
        }
        println!(
            "C166_ELIGIBLE_SCALAR_CUT context={context} terminal={} last_origin={} modern_spans={} retained_endpoints={} U={} WB={} T1={} T2={} premodern={} A={} sampled_guard={:?} ab_exceeds_wb={}",
            result.terminal,
            result.last_origin,
            result.modern_spans,
            result.modern_spans + 2,
            result.global_u,
            result.work_at_cut,
            result.t1,
            result.t2,
            result.premodern,
            result.maximum,
            result.sampled_guard,
            result.maximum > result.work_at_cut
        );
        std::io::stdout().flush().map_err(|e| e.to_string())?;
    }
    println!(
        "C166_ELIGIBLE_NATIVE_SCALAR_PASS frame_sha256={} parent_root={} parent_total={} profile={} reducer_calls=1 contexts=2 eq21_admitted=true eq26_guard=not_applicable elapsed_s={:.6} physical_score=false common_x=false pcs=false proof=false client=false",
        super::FRAME_SHA256,
        hex(&parent.root),
        hex(&parent.total),
        hex(&parent.profile),
        started.elapsed().as_secs_f64()
    );
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

#[test]
#[ignore = "single pinned H21 frame scan; separate reviewed one-use Job runner required"]
fn h21_candidate146_native_r_score_cap_session() -> Result<(), String> {
    let started = Instant::now();
    let path =
        std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame environment variable")?;
    let frame = VerifiedFrame::read(Path::new(&path))?;
    phase("FRAME_SHA256_OK", started);
    let session = NativeSession::from_verified(frame, started)?;
    let mut destination = Destination::default();
    let negatives = session.run_negatives()?;
    if negatives != 9 {
        return Err("c146 native negative census".into());
    }
    println!("C146_NATIVE_SESSION_NEGATIVES_PASS count={negatives} D=1 V=1 W=1 coherent_W_score=1 parent=1 cut_root=1 context=1 equal_X=1 V_tag=1");
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    session.publish(&mut destination)?;
    if destination.boundary(0).is_err()
        || destination.boundary(1).is_err()
        || destination.max_running(0).is_err()
    {
        return Err("c146 atomic session publication missing consumer cells".into());
    }
    phase("SESSION_PUBLISHED", started);
    println!("C146_NATIVE_R_SCORE_CAP_PASS cuts=[1827840,1827775] frame_sha256={} contexts=2 W_context_cells=6 U=source-folded V=group-replayed full_proof=false light_client=false",
        super::FRAME_SHA256);
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

#[test]
#[ignore = "one-use pinned H21 frame and three-source partial ROW19/X roster; separate reviewed Job required"]
fn h21_candidate154_native_common_roster() -> Result<(), String> {
    let started = Instant::now();
    let path =
        std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame environment variable")?;
    let frame = VerifiedFrame::read(Path::new(&path))?;
    phase("C154_FRAME_SHA256_OK", started);
    let carry =
        super::candidate135_native_values::run_native_work_max_header_value_join_from_verified(
            &frame.plan,
            &frame.prefix,
            true,
            started,
        )?;
    phase("C154_CARRY_MAP_EXPORTED", started);
    let daa =
        super::candidate151_native_daa::stage_native_mature_eip_844672(&frame.plan, &frame.prefix)?;
    phase("C154_DAA_EXPORTED", started);
    let session = NativeSession::from_verified(frame, started)?;
    let roster = session.stage_common_roster(&carry, &daa)?;
    if roster.frame_digest() != SESSION_SHA || roster.row_count() == 0 || roster.x_count() == 0 {
        return Err("c154 native partial roster identity/census".into());
    }
    if let Some((role, row)) = roster.missing_row19_claims().first() {
        return Err(format!(
            "c154 native ROW19 claim missing: role={role} row={row}"
        ));
    }
    let active_head = roster
        .active_unresolved_read_addresses()
        .iter()
        .take(16)
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let active_owners = roster.active_unresolved_by_owner();
    let owners_top = active_owners
        .iter()
        .take(8)
        .map(|(owner, count)| format!("{owner}:{count}"))
        .collect::<Vec<_>>()
        .join(",");
    let role_hits = roster.active_unresolved_role_hits();
    let terms = roster.term_counts();
    println!(
        "C154_NATIVE_COMMON_ROSTER_PASS rows={} selected_x={} active_x={} role_rows={} work_rows={} cross_rows={} missing_row19=0 unresolved_reads={} active_unresolved={} active_owner_count={} active_owners_top=[{}] active_head=[{}] role_hits=Work:{},MAX:{},CROSS:{},Map0:{},Map1:{},DAA:{},Score:{} terms=Work:{},MAX:{},CROSS:{},Map0:{},Map1:{},DAA:{},Score:{} roster_digest={} frame_sha256={} partial=true proof=false client=false",
        roster.row_count(),
        roster.x_count(),
        roster.active_x_count(),
        roster.evaluated_role_row_count(),
        roster.work_row_count(),
        roster.cross_row_count(),
        roster.unresolved_read_addresses().len(),
        roster.active_unresolved_read_addresses().len(),
        active_owners.len(),
        owners_top,
        active_head,
        role_hits[0].1,
        role_hits[1].1,
        role_hits[2].1,
        role_hits[3].1,
        role_hits[4].1,
        role_hits[5].1,
        role_hits[6].1,
        terms[0].1,
        terms[1].1,
        terms[2].1,
        terms[3].1,
        terms[4].1,
        terms[5].1,
        terms[6].1,
        hex(&roster.digest()),
        super::FRAME_SHA256,
    );
    Ok(())
}

/// Source-bound c149 Map1 producer/ledger join. This intentionally remains an
/// ignored one-use H21 frame selector and must not be run by ordinary tests.
#[test]
#[ignore = "one-use pinned H21 frame producer/ledger join; do not run without reviewed authorization"]
fn h21_candidate149_native_map1_cut_producer_to_ledger_join() -> Result<(), String> {
    const OWNER: usize = 844_670;
    const CONTEXT: usize = 1;
    let path =
        std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame environment variable")?;
    let frame = VerifiedFrame::read(Path::new(&path))?;
    let cuts =
        candidate138_native_global_u::fold_native_global_u_cut_pair(&frame.plan, &frame.prefix)?;
    let cut = &cuts[1];
    if cut.cut != 1_827_775
        || cut.envelope.exponent != 55
        || cut.lower_owner != 841_727
        || cut.selected_lower.source != (LowerSource::HeaderDifficulty { height: 841_729 })
        || cut.selected_lower.branch != LowerBranch::Pivot(54)
    {
        return Err("c149 Map1 cut differs from the approved c146 source cut".into());
    }
    let map = Map::new_modern_global_u_selected_lower(
        cut.cut,
        H,
        cut.envelope.exponent,
        cut.selected_lower,
    )?;
    if map.binding() != cut.consumer_binding || map.binding().parent_root.is_some() {
        return Err("c149 Map1 rootless Binding differs from same-plan c146 fold".into());
    }

    let producer = NativeOwnerProducer::new_for_history(&frame.plan, &frame.prefix)?;
    let row = producer.produce_bank53_map1_cut_h21_for_test(
        OWNER,
        CONTEXT,
        &map,
        &cut.consumer_binding,
    )?;
    let mut foreign = BTreeMap::new();
    let imports = map.imports(OWNER as u64)?;
    let import_count = imports.len();
    let foreign_owners: BTreeSet<usize> = imports
        .into_iter()
        .map(|import| import.owner as usize)
        .filter(|source_owner| *source_owner != OWNER)
        .collect();
    for source_owner in foreign_owners {
        foreign.insert(source_owner, producer.produce(source_owner)?);
    }
    crate::packed_owner_assembly::validate_native_map1_cut_consumer_for_test(
        &frame.plan,
        &frame.prefix,
        &map,
        &cut.consumer_binding,
        &row,
        &foreign,
    )?;

    let ledger = crate::h21_local_merged_ledger::close_native_carry(&frame.plan)?;
    let emitted = crate::bank53_map::map_owner_terms(&map, OWNER as u64, CONTEXT)?;
    let relocated = emitted
        .iter()
        .map(|term| {
            crate::h21_row_support::relocate(
                crate::h21_row_support::Family::Map(CONTEXT),
                OWNER,
                term,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let declared = ledger.relocated_map_terms(CONTEXT)?;
    if !same_term_multiset(&relocated, &declared) {
        return Err("c149 Map1 producer terms differ from owner844670 ledger ROW multiset".into());
    }
    let map_local_start = 671_744 + CONTEXT * 8_192;
    let map_local_end = map_local_start + 5_757;
    let expected_x = OWNER * crate::daa_history_roster::WIDTH + map_local_start
        ..OWNER * crate::daa_history_roster::WIDTH + map_local_end;
    let map1_domains: Vec<_> = ledger
        .x_domains()
        .into_iter()
        .filter(|(writer, _)| *writer == crate::h21_local_merged_ledger::XWriter::Map(CONTEXT))
        .collect();
    if map1_domains.len() != 1
        || map1_domains[0].1 != expected_x
        || emitted.is_empty()
        || relocated.is_empty()
        || declared.is_empty()
        || import_count == 0
    {
        return Err("c149 Map1 exact X span or ROW term multiset is empty/mismatched".into());
    }
    if !(0..5_757).any(|offset| {
        let wire = map_local_start + offset;
        ((row.packed_bytes()[wire / 8] >> (wire % 8)) & 1) != 0
    }) {
        return Err("c149 Map1 packed bank is vacuous".into());
    }

    if producer
        .produce_bank53_map1_cut_h21_for_test(OWNER, 0, &map, &cut.consumer_binding)
        .is_ok()
        || producer
            .produce_bank53_map1_cut_h21_for_test(OWNER + 1, CONTEXT, &map, &cut.consumer_binding)
            .is_ok()
    {
        return Err("c149 Map1 owner/context mutant admitted".into());
    }
    let wrong_cut = Map::new_modern_global_u_selected_lower(1_827_774, H, 55, cut.selected_lower)?;
    if producer
        .produce_bank53_map1_cut_h21_for_test(OWNER, CONTEXT, &wrong_cut, &cut.consumer_binding)
        .is_ok()
    {
        return Err("c149 Map1 wrong-cut mutant admitted".into());
    }
    println!(
        "C149_NATIVE_MAP1_CUT_PASS owner={OWNER} context={CONTEXT} cut={} row_terms={} live_x={} imports={} proof=false client=false",
        cut.cut,
        declared.len(),
        map_local_end - map_local_start,
        import_count,
    );
    std::io::stdout()
        .flush()
        .map_err(|error| error.to_string())?;
    Ok(())
}

fn same_term_multiset(left: &[crate::sparse::Term], right: &[crate::sparse::Term]) -> bool {
    fn multiset(terms: &[crate::sparse::Term]) -> BTreeMap<usize, Vec<(crate::gkr::Gate, usize)>> {
        let mut out = BTreeMap::new();
        for term in terms {
            let gates = out.entry(term.row).or_insert_with(Vec::new);
            if let Some((_, count)) = gates.iter_mut().find(|(gate, _)| gate == &term.gate) {
                *count += 1;
            } else {
                gates.push((term.gate.clone(), 1));
            }
        }
        out
    }
    let left = multiset(left);
    let right = multiset(right);
    left.len() == right.len()
        && left.iter().all(|(row, gates)| {
            right.get(row).is_some_and(|other| {
                gates.len() == other.len()
                    && gates.iter().all(|(gate, count)| {
                        other
                            .iter()
                            .any(|(candidate, n)| gate == candidate && count == n)
                    })
            })
        })
}

#[cfg(test)]
mod no_frame_negatives {
    use super::*;

    #[test]
    fn c146_native_session_map_cut_and_context_binding_rejects_detached_sources() {
        let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x91; 32], [0x92; 28]).unwrap();
        let params = [1_827_840, 1_827_775].map(|cut| MapParameters {
            cut,
            exponent: 55,
            lower: LowerSelector {
                source: LowerSource::HeaderDifficulty { height: 841_729 },
                branch: LowerBranch::Pivot(54),
            },
        });
        let sources = ParentMapSources::new(&parent, params).unwrap();
        assert!(sources
            .binding()
            .maps
            .iter()
            .all(|map| map.parent_root.is_none()));
        let wrong = [params[1], params[0]];
        assert!(
            ParentMapSources::new(&parent, wrong).is_err(),
            "swapped cut/context identity"
        );
        let alternate_pivot = [
            params[0],
            MapParameters {
                lower: LowerSelector {
                    branch: LowerBranch::Pivot(52),
                    ..params[1].lower
                },
                ..params[1]
            },
        ];
        let candidate = ParentMapSources::new(&parent, alternate_pivot).unwrap();
        assert!(
            candidate.binding().maps != sources.binding().maps,
            "detached source parameters must differ"
        );
        let source_ids = [
            source_identity(SESSION_SHA, 0),
            source_identity(SESSION_SHA, 1),
        ];
        let valid_maps = [
            Map::new_modern_global_u_selected_lower(CUTS[0], H, 55, params[0].lower).unwrap(),
            Map::new_modern_global_u_selected_lower(CUTS[1], H, 55, params[1].lower).unwrap(),
        ];
        assert!(
            ScorePlan::new(&valid_maps, [source_ids[1].clone(), source_ids[0].clone()]).is_err(),
            "swapped context source identity"
        );
        let mut rooted = source_ids.clone();
        rooted[0].parent_root = Some([0x91; 32]);
        assert!(
            ScorePlan::new(&valid_maps, rooted).is_err(),
            "invented cut root"
        );
        let other_parent =
            WorkTreeHistoryPlan::compile(1_827_840, 21, [0x93; 32], [0x92; 28]).unwrap();
        assert_eq!(
            NativeSession::validate_parent_binding(&sources, &other_parent, sources.binding())
                .unwrap_err(),
            "c141 complete parent/Map source binding",
            "alternate-parent identity mutant must fail at the same guard used by session"
        );
        println!("C146_NATIVE_SESSION_NOFRAME_NEGATIVES_PASS count=4 root=1 context=1 alternate_parent_identity=1 cut=1");
    }
}

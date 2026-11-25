//! Test-only c146 paired-cut consumer boundary. Synthetic inputs exercise
//! source replay and atomic staging; they do not establish native H21 custody.
use crate::{
    h21_row_support::{MapParameters, ParentMapBinding, ParentMapSources},
    h21_scheduled_max_cap::{Patch, Prepared, Writer as VWriter},
    legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map},
    score_prefix_r_anchor::{
        self, Destination, Endpoint, Inputs, Plan as ScorePlan, SourceIdentity,
    },
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;

const CUTS: [u64; 2] = [1_827_840, 1_827_775];
const FRAME: [u8; 32] = [0x46; 32];
const RAW_W_EXPONENT: [usize; 2] = [80, 81];
const MODERN_W_EXPONENT: usize = 83;
const SCHEDULE_D: u64 = 65_536;

fn parameters() -> [MapParameters; 2] {
    CUTS.map(|cut| MapParameters {
        cut,
        exponent: 55,
        lower: LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        },
    })
}
fn maps() -> [Map; 2] {
    parameters().map(|p| {
        Map::new_modern_global_u_selected_lower(p.cut, 21, p.exponent, p.lower)
            .expect("fixed symbolic Map")
    })
}
fn parent() -> WorkTreeHistoryPlan {
    WorkTreeHistoryPlan::compile(1_827_840, 21, [0x93; 32], [0x94; 28])
        .expect("synthetic H21 geometry")
}
fn identity(context: usize) -> SourceIdentity {
    SourceIdentity {
        frame: FRAME,
        cut: CUTS[context],
        parent_root: None,
    }
}
fn raw_endpoints(sources: &[SourceIdentity; 2]) -> [[Endpoint; 2]; 2] {
    let values = RAW_W_EXPONENT.map(|exponent| BigUint::from(1u8) << exponent);
    std::array::from_fn(|c| {
        std::array::from_fn(|j| Endpoint {
            source: sources[c].clone(),
            height: [417_791, 845_759][j],
            owner: [417_789, 845_757][j],
            local: 987_450,
            value: values[j].clone(),
        })
    })
}
fn modern_w() -> BigUint {
    BigUint::from(1u8) << MODERN_W_EXPONENT
}
fn fixture_prepared() -> Result<Prepared, String> {
    Prepared::from_d_iter(
        (844_672usize..=1_827_840).map(|height| (height, BigUint::from(SCHEDULE_D))),
    )
}
fn cap_values(patch: &Patch) -> Result<[BigUint; 2], String> {
    let mut out = [BigUint::from(0u8), BigUint::from(0u8)];
    let expected = [
        VWriter::Cap {
            context: 0,
            origin: 845_760,
        },
        VWriter::Cap {
            context: 1,
            origin: 845_760,
        },
    ];
    if patch.writers() != expected {
        return Err("c146 session Cap writer/context/source mismatch".into());
    }
    for (owner, start, writer, values) in patch.snapshot() {
        let VWriter::Cap { context, origin } = writer else {
            return Err("c146 session Cap writer/context/source mismatch".into());
        };
        if owner != 845_759
            || origin != 845_760
            || context >= 2
            || start != [1_000_770, 1_002_818][context]
            || values.len() != 2048
        {
            return Err("c146 session Cap writer/context/source mismatch".into());
        }
        for (k, v) in values[740..805].iter().enumerate() {
            if *v != Fr::zero() && *v != Fr::one() {
                return Err("c146 session nonboolean Cap alias".into());
            }
            if v.is_one() {
                out[context] += BigUint::from(1u8) << k;
            }
        }
    }
    Ok(out)
}

#[derive(Clone, Debug)]
pub(super) struct CallerInputs {
    pub claimed_parent: ParentMapBinding,
    pub sources: [SourceIdentity; 2],
    pub inputs: Inputs,
    /// The separately tagged Score W alias must equal the replayed Upper.
    pub score_w_alias: BigUint,
}

pub(super) struct Session {
    parent: WorkTreeHistoryPlan,
    parent_maps: ParentMapSources,
    score: ScorePlan,
    max_patch: Patch,
    lookahead_patch: Patch,
    cap_patch: Patch,
}
impl Session {
    pub(super) fn fixture() -> Result<(Self, CallerInputs), String> {
        let parent = parent();
        let parent_maps = ParentMapSources::new(&parent, parameters())?;
        parent_maps.validate(&parent, parent_maps.binding())?;
        let map = maps();
        if map.iter().any(|m| m.binding().parent_root.is_some()) {
            return Err("c146 symbolic cut root invented".into());
        }
        let sources = [identity(0), identity(1)];
        let score = ScorePlan::new(&map, sources.clone())?;
        let prepared = fixture_prepared()?;
        let max_patch = prepared.owner_patch(844_670)?;
        let lookahead_patch = prepared.owner_patch(844_798)?;
        let cap_patch = prepared.owner_patch(845_759)?;
        if max_patch.writers()
            != vec![
                VWriter::Max {
                    context: 0,
                    end: 844_672,
                },
                VWriter::Max {
                    context: 1,
                    end: 844_672,
                },
            ]
        {
            return Err("c146 session MAX writer/context/source mismatch".into());
        }
        let cap_values = cap_values(&cap_patch)?;
        let source_endpoints = raw_endpoints(&sources);
        let session = Self {
            parent,
            parent_maps,
            score,
            max_patch,
            lookahead_patch,
            cap_patch,
        };
        let caller = CallerInputs {
            claimed_parent: session.parent_maps.binding().clone(),
            sources,
            inputs: Inputs {
                endpoints: source_endpoints,
                modern_w: modern_w(),
                modern_v: cap_values,
            },
            score_w_alias: modern_w(),
        };
        Ok((session, caller))
    }

    fn source_replay(
        &self,
    ) -> Result<
        (
            [[Endpoint; 2]; 2],
            BigUint,
            [BigUint; 2],
            Patch,
            Patch,
            Patch,
        ),
        String,
    > {
        // Recreate the deterministic synthetic stream for the selected MAX and
        // Cap patches. This is test-fixture replay, never NativePrefix replay.
        let replayed = fixture_prepared()?;
        let max = replayed.owner_patch(844_670)?;
        let lookahead = replayed.owner_patch(844_798)?;
        let cap = replayed.owner_patch(845_759)?;
        if max.writers() != self.max_patch.writers()
            || !max.source_replay_matches(&self.max_patch)
            || lookahead.writers() != self.lookahead_patch.writers()
            || !lookahead.source_replay_matches(&self.lookahead_patch)
            || cap.writers() != self.cap_patch.writers()
            || !cap.source_replay_matches(&self.cap_patch)
        {
            return Err("c146 session immutable V source replay mismatch".into());
        }
        Ok((
            raw_endpoints(&[identity(0), identity(1)]),
            modern_w(),
            cap_values(&cap)?,
            max,
            lookahead,
            cap,
        ))
    }

    fn validate_caller_source_bindings(
        &self,
        caller: &CallerInputs,
    ) -> Result<([[Endpoint; 2]; 2], BigUint, [BigUint; 2], Patch, Patch, Patch), String> {
        if self
            .parent_maps
            .validate(&self.parent, &caller.claimed_parent)
            .is_err()
        {
            return Err("c146 complete parent/Map source binding".into());
        }
        let bindings = self.parent_maps.binding();
        if bindings.maps.iter().any(|m| m.parent_root.is_some())
            || caller.sources.iter().any(|s| s.parent_root.is_some())
        {
            return Err("c146 symbolic cut root invented".into());
        }
        let map = maps();
        for c in 0..2 {
            if caller.sources[c] != identity(c)
                || caller.inputs.endpoints[c][0].source != caller.sources[c]
                || caller.inputs.endpoints[c][1].source != caller.sources[c]
            {
                return Err("c146 context/source binding".into());
            }
            if map[c].binding() != bindings.maps[c] {
                return Err("c146 complete parent/Map source binding".into());
            }
        }
        let (upper, modern_w, modern_v, max, lookahead, cap) = self.source_replay()?;
        for c in 0..2 {
            for j in 0..2 {
                let actual = &caller.inputs.endpoints[c][j];
                let expected = &upper[c][j];
                if actual.height != expected.height
                    || actual.owner != expected.owner
                    || actual.local != expected.local
                    || actual.value != expected.value
                    || actual.source != expected.source
                {
                    return Err("c146 session immutable W source replay mismatch".into());
                }
            }
        }
        if caller.inputs.modern_w != modern_w || caller.score_w_alias != modern_w {
            return Err("c146 session immutable W source replay mismatch".into());
        }
        if caller.inputs.modern_v != modern_v {
            return Err("c146 session immutable Cap source replay mismatch".into());
        }
        Ok((upper, modern_w, modern_v, max, lookahead, cap))
    }

    pub(super) fn stage_for_local_ledger_join(
        &self,
        caller: &CallerInputs,
    ) -> Result<(ScorePlan, score_prefix_r_anchor::Staged), String> {
        let (_, _, _, max, lookahead, cap) = self.validate_caller_source_bindings(caller)?;
        let score = ScorePlan::new(&maps(), caller.sources.clone())?;
        let staged = score_prefix_r_anchor::stage_session(
            &score,
            &caller.inputs,
            &BigUint::from(SCHEDULE_D),
            &max,
            &lookahead,
            &cap,
        )?;
        Ok((score, staged))
    }

    pub(super) fn publish(
        &self,
        caller: &CallerInputs,
        destination: &mut Destination,
    ) -> Result<(), String> {
        let (_, _, _, max, lookahead, cap) = self.validate_caller_source_bindings(caller)?;
        if destination.boundary(0).is_ok() {
            return Err("c146 session destination already published".into());
        }
        let staged = score_prefix_r_anchor::stage_session(
            &self.score,
            &caller.inputs,
            &BigUint::from(SCHEDULE_D),
            &max,
            &lookahead,
            &cap,
        )?;
        score_prefix_r_anchor::publish_session(&self.score, destination, staged)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn c146_phase1_paired_cut_session_replays_before_atomic_summary_score_cap_publish() {
        let (session, caller) = Session::fixture().unwrap();
        assert!(session
            .parent_maps
            .binding()
            .maps
            .iter()
            .all(|m| m.parent_root.is_none()));
        let mut destination = Destination::default();
        session.publish(&caller, &mut destination).unwrap();
        let raw = [BigUint::from(1u8) << 80usize, BigUint::from(1u8) << 81usize];
        let maturities = [[43_410u64, 23_155], [17_867, 9_548]];
        for c in 0..2 {
            let u = maps()[c].cap().to_biguint().unwrap();
            let a = &raw[0] + &u * maturities[c][0];
            let b = &raw[1] + &u * maturities[c][1];
            assert_eq!(destination.boundary(c).unwrap(), a.max(b));
            assert_eq!(destination.max_running(c).unwrap().bits(), 17);
            assert_ne!(
                destination.boundary(c).unwrap(),
                destination.max_running(c).unwrap(),
                "Summary R and the MAX running value have separate producers"
            );
        }
        println!("C146_PHASE1_R_SCORE_NOFRAME_PASS cuts=[1827840,1827775] roots=None contexts=2 score_owner=845759 max_owner=844670 cap_owner=845759 synthetic_source_replay=true native_h21_custody=false");
    }

    #[test]
    fn c146_phase1_rejects_root_parent_context_and_coherent_w_score_alias_before_publish() {
        let (session, good) = Session::fixture().unwrap();
        let mut cases: Vec<(CallerInputs, &str)> = Vec::new();
        let mut bad = good.clone();
        bad.sources[1].parent_root = Some([0x94; 32]);
        cases.push((bad, "c146 symbolic cut root invented"));
        let mut bad = good.clone();
        bad.claimed_parent.maps[1].parent_root = Some([0x93; 32]);
        cases.push((bad, "c146 complete parent/Map source binding"));
        let mut bad = good.clone();
        bad.claimed_parent.maps[1].parent_root = Some([0x93; 32]);
        bad.sources[1].parent_root = Some([0x93; 32]);
        for endpoint in &mut bad.inputs.endpoints[1] {
            endpoint.source.parent_root = Some([0x93; 32]);
        }
        cases.push((bad, "c146 complete parent/Map source binding"));
        let mut bad = good.clone();
        bad.claimed_parent.maps[1].e += 1;
        cases.push((bad, "c146 complete parent/Map source binding"));
        let mut bad = good.clone();
        bad.sources.swap(0, 1);
        cases.push((bad, "c146 context/source binding"));
        let mut bad = good.clone();
        bad.inputs.modern_w += BigUint::from(2u8);
        bad.score_w_alias += BigUint::from(2u8);
        cases.push((bad, "c146 session immutable W source replay mismatch"));
        for (input, error) in cases {
            let mut destination = Destination::default();
            assert_eq!(
                session.publish(&input, &mut destination).unwrap_err(),
                error
            );
            assert!(destination.boundary(0).is_err());
        }
    }

    #[test]
    fn c146_local_ledger_staging_rejects_endpoint_and_score_w_alias_mutants() {
        let (session, caller) = Session::fixture().unwrap();
        let mut bad_endpoint = caller.clone();
        bad_endpoint.inputs.endpoints[0][0].value += BigUint::from(1u8);
        assert_eq!(
            session.stage_for_local_ledger_join(&bad_endpoint).err().unwrap(),
            "c146 session immutable W source replay mismatch"
        );

        let mut bad_alias = caller;
        bad_alias.score_w_alias += BigUint::from(1u8);
        assert_eq!(
            session.stage_for_local_ledger_join(&bad_alias).err().unwrap(),
            "c146 session immutable W source replay mismatch"
        );
    }

    #[test]
    fn c146_phase1_private_registry_rejects_equal_x_and_semantic_row_owner_collisions() {
        let (session, caller) = Session::fixture().unwrap();
        let (_, _, _, max, lookahead, cap) = session.source_replay().unwrap();
        let duplicate = max.duplicate_first_span_for_test();
        let mut destination = Destination::default();
        let before = destination.clone();
        assert_eq!(
            score_prefix_r_anchor::stage_session(
                &session.score,
                &caller.inputs,
                &BigUint::from(SCHEDULE_D),
                &duplicate,
                &lookahead,
                &cap
            )
            .unwrap_err(),
            "c146 session duplicate X writer including equal"
        );
        assert_eq!(destination, before);

        let (_, _, _, max, lookahead, cap) = session.source_replay().unwrap();
        let mut staged = score_prefix_r_anchor::stage_session(
            &session.score,
            &caller.inputs,
            &BigUint::from(SCHEDULE_D),
            &max,
            &lookahead,
            &cap,
        )
        .unwrap();
        score_prefix_r_anchor::collide_row_owner_for_test(&mut staged);
        assert_eq!(
            score_prefix_r_anchor::validate_session(&session.score, &staged).unwrap_err(),
            "c146 semantic ROW owner collision"
        );
        assert_eq!(destination, before);
    }

    #[test]
    fn c146_phase1_score_w_and_v_alias_bits_are_independently_bound() {
        let (session, caller) = Session::fixture().unwrap();
        let (_, _, _, max, lookahead, cap) = session.source_replay().unwrap();
        let staged = score_prefix_r_anchor::stage_session(
            &session.score,
            &caller.inputs,
            &BigUint::from(SCHEDULE_D),
            &max,
            &lookahead,
            &cap,
        )
        .unwrap();
        for (context, is_v, bit) in [(0, false, 17), (0, true, 33), (1, false, 91), (1, true, 61)] {
            let mut bad = staged.clone();
            score_prefix_r_anchor::flip_score_alias_for_test(&mut bad, context, is_v, bit);
            let (alias_row, alias_residual) = score_prefix_r_anchor::alias_residual_for_test(
                &bad, context, is_v, bit,
            )
            .unwrap();
            let expected_local = if is_v { [491_629, 506_860][context] }
                else { [491_694, 506_925][context] };
            assert_eq!(alias_row, 845_759 * (1 << 19) + expected_local + bit);
            assert!(!alias_residual.is_zero(), "selected alias ROW must detect the isolated bit mutant");
            assert!(score_prefix_r_anchor::validate_session(&session.score, &bad).is_err());
        }
        let mut destination = Destination::default();
        score_prefix_r_anchor::publish_session(&session.score, &mut destination, staged).unwrap();
        assert!(destination.boundary(0).unwrap().bits() <= 225);
    }
}

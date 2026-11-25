//! One exact H21 parent supplies both Eligible08 Map cuts. No packed row is
//! available until independently authored Score/MAX/Cap leases are joined.
use super::*;
use crate::global_u_roster::{self, CandidateSource, GlobalEnvelope, Schedule, ScheduleIter, SuppliedCandidate};
use crate::legacy_envelope_map::{Kind, LowerBranch, LowerSelector, LowerSource, Map};
use num_bigint::{BigInt, BigUint};

#[path = "h21_eligible_score.rs"]
mod h21_eligible_score;
#[cfg(test)]
pub(crate) use h21_eligible_score::structural_roster;
#[cfg(test)]
pub(crate) use h21_eligible_score::native_owner_values;
#[cfg(test)]
pub(super) use h21_eligible_score::h21_score_class_equations::ClassEquationPlan;
pub(crate) use h21_eligible_score::{
    H21ClosedOwnerSource, H21ClosedScoreOwnerRelation, ScoreRelationReadAuthor, ScoreReplayAuthor, PremodernRPublication,
    Eligible08ScoreAnchorCell,
};
use h21_eligible_score::R450Projection;
#[cfg(test)]
use h21_eligible_score::conditional_r450_projection_for_test;
#[derive(Clone, Debug)]
struct FoldedCut {
    envelope: GlobalEnvelope,
    max_d: (u64, BigUint),
    max_b: (u64, BigUint),
}

struct CandidateStream<F> {
    schedule: ScheduleIter,
    resolve: F,
    first_error: Option<String>,
    max_d: Option<(u64, BigUint)>,
    max_b: Option<(u64, BigUint)>,
}

impl<F> Iterator for CandidateStream<F>
where F: FnMut(CandidateSource) -> Result<BigUint, String> {
    type Item = SuppliedCandidate;
    fn next(&mut self) -> Option<Self::Item> {
        if self.first_error.is_some() { return None; }
        let source = self.schedule.next()?;
        let value = match (self.resolve)(source) {
            Ok(value) => value,
            Err(error) => {
                self.first_error = Some(format!("Eligible08 candidate {source:?}: {error}"));
                return None;
            }
        };
        let maximum = match source {
            CandidateSource::HeaderDifficulty { height, work_owner } => {
                if work_owner != height - 2 {
                    self.first_error = Some("Eligible08 D source owner".into());
                    return None;
                }
                (&mut self.max_d, height)
            }
            CandidateSource::LegacyBound { q, endpoint, map_owner, ell } => {
                if endpoint != 1024 * (q + 1) || map_owner != q * 1024 + 959
                    || ell != q.min(8) as usize {
                    self.first_error = Some("Eligible08 B source tuple".into());
                    return None;
                }
                (&mut self.max_b, q)
            }
        };
        if maximum.0.as_ref().is_none_or(|(_, old)| value > *old) {
            *maximum.0 = Some((maximum.1, value.clone()));
        }
        Some(SuppliedCandidate { source, value })
    }
}

fn fold_cut_with<F>(cut: u64, resolve: F) -> Result<FoldedCut, String>
where F: FnMut(CandidateSource) -> Result<BigUint, String> {
    let mut stream = CandidateStream {
        schedule: Schedule::new(cut)?.iter(), resolve, first_error: None,
        max_d: None, max_b: None,
    };
    let folded = global_u_roster::fold(cut, &mut stream);
    if let Some(error) = stream.first_error.take() { return Err(error); }
    let envelope = folded?;
    if envelope.header_count != cut - 1 || envelope.legacy_count != 822 {
        return Err("Eligible08 D/B candidate census".into());
    }
    let max_d = stream.max_d.ok_or("Eligible08 missing D maximum")?;
    let max_b = stream.max_b.ok_or("Eligible08 missing B maximum")?;
    if envelope.max_difficulty != max_d.1
        || envelope.modern_floor != (&max_d.1 * 3u8) / 2u8 {
        return Err("Eligible08 folded D maximum/floor".into());
    }
    let independent = envelope.modern_floor.clone().max(max_b.1.clone())
        .max(BigUint::from(global_u_roster::INITIAL_I))
        .max(BigUint::from(global_u_roster::RESET_CHILD_417792))
        .max(BigUint::from(global_u_roster::RESET_CHILD_417793));
    if envelope.maximum_candidate != independent
        || envelope.u != BigUint::from(1u8) << envelope.exponent {
        return Err("Eligible08 U maximum/envelope".into());
    }
    Ok(FoldedCut { envelope, max_d, max_b })
}

fn strict_pivot(value: &BigUint, threshold: &BigUint) -> Result<usize, String> {
    if value <= threshold { return Err("Eligible08 lower witness not strictly above threshold".into()); }
    let difference = value ^ threshold;
    let pivot = (difference.bits() - 1) as usize;
    if !value.bit(pivot as u64) || threshold.bit(pivot as u64) {
        return Err("Eligible08 lower witness pivot direction".into());
    }
    Ok(pivot)
}

fn selected_lower(folded: &FoldedCut) -> Result<LowerSelector, String> {
    let e = folded.envelope.exponent;
    let u = BigUint::from(1u8) << e;
    let half = &u / 2u8;
    let maximum = &folded.envelope.maximum_candidate;
    if maximum > &u || maximum <= &half {
        return Err("Eligible08 U is not a minimal dyadic envelope".into());
    }
    let modern = (&folded.max_d.1 * 3u8) / 2u8;
    if &modern == maximum {
        let threshold = (&u + 4u8) / 3u8;
        let branch = if folded.max_d.1 == threshold { LowerBranch::Equality }
            else { LowerBranch::Pivot(strict_pivot(&folded.max_d.1, &threshold)?) };
        return Ok(LowerSelector {
            source: LowerSource::HeaderDifficulty { height: folded.max_d.0 }, branch,
        });
    }
    if &folded.max_b.1 == maximum {
        return Ok(LowerSelector {
            source: LowerSource::LegacyBound { q: folded.max_b.0 },
            branch: LowerBranch::Pivot(strict_pivot(&folded.max_b.1, &half)?),
        });
    }
    for (literal, source) in [
        (global_u_roster::INITIAL_I, LowerSource::InitialI),
        (global_u_roster::RESET_CHILD_417792, LowerSource::Reset417792),
        (global_u_roster::RESET_CHILD_417793, LowerSource::Reset417793),
    ] {
        if BigUint::from(literal) == *maximum {
            return Ok(LowerSelector { source, branch: LowerBranch::Literal });
        }
    }
    Err("Eligible08 maximum has no authenticated lower source".into())
}

fn map_for_fold(cut: u64, folded: &FoldedCut) -> Result<(Map, LowerSelector), String> {
    if folded.envelope.n != cut { return Err("Eligible08 fold/cut mismatch".into()); }
    let lower = selected_lower(folded)?;
    let map = Map::new_modern_global_u_selected_lower(cut, 21, folded.envelope.exponent, lower)?;
    if map.binding().parent_root.is_some() { return Err("Eligible08 cut Map must remain rootless".into()); }
    Ok((map, lower))
}

fn inputs_from_exports(map: &Map, owner: u64,
    exports: &crate::native_owner_exports::NativeExports<'_>)
    -> Result<crate::legacy_envelope_map::Inputs, String> {
    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for import in map.imports(owner)? {
        let mut value = BigUint::from(0u8);
        for bit in 0..import.width {
            if exports.bit(map.input_index(import, bit)?)? { value |= BigUint::from(1u8) << bit; }
        }
        inputs.put(map, import, &BigInt::from(value))?;
    }
    Ok(inputs)
}

fn native_candidate(source: CandidateSource, prefix: &NativePrefix,
    exports: &crate::native_owner_exports::NativeExports<'_>, historical_b: &Map)
    -> Result<BigUint, String> {
    match source {
        CandidateSource::HeaderDifficulty { height, work_owner } => {
            if work_owner != height - 2 { return Err("Eligible08 D owner".into()); }
            prefix.compact_n_bits(height as usize).and_then(crate::work_tree_work::native_decode)
        }
        CandidateSource::LegacyBound { q, endpoint, map_owner, ell } => {
            if endpoint != 1024 * (q + 1) || map_owner != q * 1024 + 959
                || ell != q.min(8) as usize { return Err("Eligible08 B tuple".into()); }
            let inputs = inputs_from_exports(historical_b, map_owner, exports)?;
            historical_b.generate(map_owner, &inputs)?.bound(historical_b)?
                .to_biguint().ok_or_else(|| "Eligible08 negative historical B".into())
        }
    }
}

fn native_map_for_cut(cut: u64, prefix: &NativePrefix,
    exports: &crate::native_owner_exports::NativeExports<'_>, historical_b: &Map)
    -> Result<(Map, GlobalEnvelope), String> {
    let folded = fold_cut_with(cut, |source| native_candidate(source, prefix, exports, historical_b))?;
    let (map, lower) = map_for_fold(cut, &folded)?;
    match lower.source {
        LowerSource::HeaderDifficulty { height } => {
            if height != folded.max_d.0 { return Err("Eligible08 selected D winner".into()); }
            let owner = height.checked_sub(2).ok_or("Eligible08 selected D owner underflow")?;
            let decoded = prefix.compact_n_bits(height as usize)
                .and_then(crate::work_tree_work::native_decode)?;
            if decoded != folded.max_d.1 { return Err("Eligible08 selected D reread".into()); }
            let import = map.imports(owner)?.into_iter()
                .find(|item| item.kind == Kind::Difficulty && item.owner == owner)
                .ok_or("Eligible08 selected D import missing")?;
            if import.local != crate::legacy_envelope_map::D_LOCAL || import.width != 224 {
                return Err("Eligible08 selected D import geometry".into());
            }
            let mut imported = BigUint::from(0u8);
            for bit in 0..import.width {
                if exports.bit(map.input_index(import, bit)?)? { imported |= BigUint::from(1u8) << bit; }
            }
            if imported != decoded { return Err("Eligible08 selected D import mismatch".into()); }
        }
        LowerSource::LegacyBound { q } => {
            if q != folded.max_b.0 { return Err("Eligible08 selected B winner".into()); }
            let source = Schedule::new(cut)?.legacy_items().find(|item|
                matches!(item, CandidateSource::LegacyBound { q: found, .. } if *found == q))
                .ok_or("Eligible08 selected B missing from cut schedule")?;
            if native_candidate(source, prefix, exports, historical_b)? != folded.max_b.1 {
                return Err("Eligible08 selected historical B reread".into());
            }
        }
        LowerSource::InitialI | LowerSource::Reset417792 | LowerSource::Reset417793 => {
            let expected = match lower.source {
                LowerSource::InitialI => global_u_roster::INITIAL_I,
                _ => global_u_roster::RESET_CHILD_417792,
            };
            if BigUint::from(expected) != folded.envelope.maximum_candidate {
                return Err("Eligible08 selected literal mismatch".into());
            }
        }
    }
    Ok((map, folded.envelope))
}

/// A reusable source context. Its public constructor has no supplied U, lower
/// selector, Map binding, B candidate or witness bit argument.
#[allow(dead_code)]
pub(crate) struct H21EligibleContext<'a> {
    producer: NativeOwnerProducer<'a>,
    descriptor: crate::bank53_map::CutDescriptor,
    maps: [Map; 2],
    envelopes: [GlobalEnvelope; 2],
    parent_mask: Vec<bool>,
}

// Pure test-only checker shared by the native observation accessor and the
// no-frame falsifier. Missing envelopes cannot silently drop source binding.
// The accessor alone supplies these inputs from its authenticated context.
#[cfg(test)]
fn checked_dynamic_map_exponents(
    maps: &[Map; 2], envelopes: &[GlobalEnvelope],
    generated_bindings: &[crate::legacy_envelope_map::Binding; 2],
    descriptor: crate::bank53_map::CutDescriptor,
) -> Result<[usize; 2], String> {
    if envelopes.len() != 2 {
        return Err("C495 dynamic Map source envelope census".into());
    }
    let mut observed = [0usize; 2];
    for context in 0..2 {
        let binding = maps[context].binding();
        let envelope = &envelopes[context];
        // Full equality retains private mode, selector and contract fields.
        // No projection onto geometry/exponent establishes source identity.
        if generated_bindings[context] != binding
            || binding.n != descriptor.terminals()[context] as u64
            || binding.h != 21 || binding.parent_root.is_some()
            || envelope.n != binding.n || envelope.exponent != binding.e
            || envelope.u != BigUint::from(1u8) << binding.e
        {
            return Err("C495 complete generated Map/folded source binding".into());
        }
        observed[context] = envelope.exponent;
    }
    Ok(observed)
}

#[path = "h21_eligible_owner_sink.rs"]
mod owner_sink;
#[path = "h21_scored_owner_source.rs"]
mod scored_owner_source;
pub(crate) use scored_owner_source::{Eligible08RegularScoreOwner, OpenScoredRead, OpenScoredReadAuthor, ScoredOwnerPackedAuthor,
    ScoredOwnerPackedCell, ScoredOwnerPackingView, ScoredOwnerSourceJoin,
    C509RegularRowSourceView};
pub(crate) use scored_owner_source::C492PartialWriterCarrier;
pub(crate) use owner_sink::{Eligible08OwnerAdmission, Eligible08OwnerLease, Eligible08OwnerSink, RequiredAuthor};
pub(crate) use owner_sink::{Eligible08ForeignMaxCell, Eligible08ForeignMaxReadLease};
pub(crate) use owner_sink::{Eligible08CheckedLocalCells, Eligible08PackedOverlay};
pub(crate) use owner_sink::Eligible08MapSourceView;
pub(crate) use owner_sink::{Eligible08CompleteRowSourceView, Eligible08ScoreImport,
    Eligible08ScoreImportKind, Eligible08SlackCellAuthor};
pub(crate) use owner_sink::{Bank53TypedAuthor, Bank53TypedSourceEntry, Bank53TypedSourceLease};

#[path = "h21_eligible_map_pair_lease.rs"]
mod map_pair_lease;
pub(crate) use map_pair_lease::{Eligible08MapPairCell, Eligible08MapPairImport,
    Eligible08MapPairLease, Eligible08MapSlackBundle, Eligible08MapSlackAnchorBundle,
    Eligible08MapSlackSecondAnchorBundle, MapPairSourceAuthor,
    resolve_typed_map_import};

impl<'a> H21EligibleContext<'a> {
    #[cfg(test)]
    pub(crate) fn structural_map_parameters(&self) -> Result<[structural_roster::PublicMapParameters; 2], String> {
        validate_native_plan_input(self.producer.plan, self.producer.input)?;
        let extract = |c: usize| {
            let map = &self.maps[c];
            let terminal = self.descriptor.terminals()[c];
            let exponent = self.envelopes[c].exponent;
            let lower = map.selected_lower_descriptor().ok_or("missing native Map selector")?;
            let public = Map::new_modern_global_u_selected_lower(terminal as u64, 21, exponent, lower)?;
            if public.binding() != map.binding() {
                return Err("native and structural Map descriptions differ".to_owned());
            }
            Ok(structural_roster::PublicMapParameters { terminal, exponent, lower })
        };
        Ok([extract(0)?, extract(1)?])
    }
    pub(crate) fn new(plan: &'a WorkTreeHistoryPlan, prefix: &'a NativePrefix) -> Result<Self, String> {
        let descriptor = H21EligibleMapStage::descriptor();
        if plan.headers() != crate::h21_snapshot::N as u64
            || plan.slot_log() != 21 || plan.slots() != 1 << 21 {
            return Err("Eligible08 exact H21 parent geometry".into());
        }
        let producer = NativeOwnerProducer::new_for_history(plan, prefix)?;
        let parent_mask = plan.physical_assignment_replacement_mask(0)?;
        H21EligibleMapStage::require_header_owned_map_live(&parent_mask)?;
        // One historical e64 B author is rooted in the exact full parent.
        // Both cut folds consume its canonical q rows; only their modern Map
        // consumers stay rootless and cut-specific.
        let parent_b = Map::from_parent(plan, 64)?;
        let mut cuts = Vec::with_capacity(2);
        for cut in descriptor.terminals() {
            cuts.push(native_map_for_cut(cut as u64, prefix, &producer.exports, &parent_b)?);
        }
        let [(map0, envelope0), (map1, envelope1)] = cuts.try_into()
            .map_err(|_| "Eligible08 cut pair census")?;
        Ok(Self { producer, descriptor, maps: [map0, map1],
            envelopes: [envelope0, envelope1], parent_mask })
    }

    /// Observe only the exponent pair retained by this authenticated context.
    /// Callers supply no Map, envelope, exponent or alternate source value.
    #[cfg(test)]
    pub(crate) fn checked_dynamic_map_exponents_for_test(
        &self, expected: &HeaderSourceBinding, owner: usize,
    ) -> Result<[usize; 2], String> {
        validate_native_plan_input(self.producer.plan, self.producer.input)?;
        let source_binding = HeaderSourceBinding::for_plan(self.producer.plan, owner)?;
        if expected != &source_binding || !expected.matches_sink(
            self.producer.input.root(), self.producer.input.total_be28(),
            self.producer.input.profile(), &self.descriptor.canonical_identity(), owner,
        ) {
            return Err("C495 dynamic Map exact parent/cut/layout/owner binding".into());
        }
        let (stage, _) = self.map_stage(owner)?;
        stage.validate_identity(self.producer.plan, self.producer.input.profile(),
            self.descriptor, &self.maps)?;
        if stage.owner != owner || !expected.matches_sink(stage.parent_root,
            stage.parent_total, stage.parent_profile, &stage.cut_identity, owner)
        {
            return Err("C495 dynamic Map generated owner binding".into());
        }
        checked_dynamic_map_exponents(&self.maps, &self.envelopes,
            &stage.map_bindings, self.descriptor)
    }

    /// Join the exact source and retain its installed partial together with
    /// the same checked view. Summary access must revalidate both.
    pub(crate) fn stage_c492_partial_score_slack(
        &self, owner: usize, relation: H21ClosedScoreOwnerRelation<'_>,
        closed_max: &crate::h21_scheduled_max_cap::MaxStream<'_>,
        expected: &HeaderSourceBinding,
    ) -> Result<C492PartialWriterCarrier, String> {
        let view = ScoredOwnerPackingView::from_checked_join(
            self.join_scored_owner_source(owner, relation, closed_max)?)?;
        view.into_c492_partial_score_slack(expected)
    }

    pub(crate) fn stage(&self, owner: usize) -> Result<H21EligibleMapStage, String> {
        self.map_stage(owner).map(|(stage, _)| stage)
    }

    /// Test-only direct view of freshly generated Map live spans. This path
    /// calls `map_stage` independently of the physical source lease.
    #[cfg(test)]
    pub(crate) fn generated_map_pair_for_test(
        &self,
        owner: usize,
    ) -> Result<([crate::legacy_envelope_map::Binding; 2], [Vec<bool>; 2]), String> {
        let (stage, generated) = self.map_stage(owner)?;
        let bindings = [generated[0].binding.clone(), generated[1].binding.clone()];
        if stage.owner != owner || stage.map_bindings != bindings {
            return Err("C438 direct generated Map pair stage binding".into());
        }
        if generated.iter().any(|row| row.owner != owner as u64
            || row.bits.len() != crate::legacy_envelope_map::BANK
            || row.bits[BANK53_MAP_LIVE_BITS..].iter().any(|bit| *bit))
        {
            return Err("C438 direct generated Map pair owner/live/tail".into());
        }
        let spans = [
            generated[0].bits[..BANK53_MAP_LIVE_BITS].to_vec(),
            generated[1].bits[..BANK53_MAP_LIVE_BITS].to_vec(),
        ];
        Ok((bindings, spans))
    }

    /// Produce an owner-local Map + Slack join. It is still opaque and has no
    /// serialization or completion operation.
    pub(crate) fn stage_with_slack(&self, owner: usize)
        -> Result<super::h21_eligible_slack::H21EligibleSlackStage, String> {
        H21EligibleMapStage::require_header_owned_slack_live(&self.parent_mask)?;
        let (map_stage, generated_maps) = self.map_stage(owner)?;
        let mut stage = super::h21_eligible_slack::H21EligibleSlackStage::new(map_stage);
        for (context, generated) in generated_maps.iter().enumerate() {
            let lease = super::h21_eligible_slack::SlackLease::from_generated(
                &stage.map_stage, context, generated)?;
            lease.admit_into(&mut stage)?;
        }
        Ok(stage)
    }

    /// Join a closed native Score owner with this parent's generated Map and
    /// Slack sources. The returned owner-local stage still has no HEADER/DAA
    /// retirement, global X/ROW closure, or proof export.
    pub(crate) fn stage_with_score_slack(
        &self, owner: usize, relation: H21ClosedScoreOwnerRelation<'_>,
    ) -> Result<super::h21_eligible_slack::H21EligibleSlackStage, String> {
        let mut stage = self.stage_with_slack(owner)?;
        stage.admit_score_relation(relation)?;
        Ok(stage)
    }

    fn map_stage(&self, owner: usize)
        -> Result<(H21EligibleMapStage, [crate::legacy_envelope_map::OwnerRow; 2]), String> {
        if owner >= self.producer.plan.slots() { return Err("Eligible08 stage owner outside parent".into()); }
        let class = self.producer.roster.owner_class(owner as u64)?;
        let mut stage = H21EligibleMapStage::new_bound(self.producer.plan,
            self.producer.input.profile(), owner, class, self.descriptor,
            &self.maps, &self.parent_mask)?;
        let mut generated_maps = Vec::with_capacity(2);
        for (context, map) in self.maps.iter().enumerate() {
            let inputs = inputs_from_exports(map, owner as u64, &self.producer.exports)?;
            let generated = map.generate(owner as u64, &inputs)?;
            map.check_row(&generated)?;
            if generated.owner != owner as u64 || generated.binding != stage.map_bindings[context]
                || generated.bits.len() != crate::legacy_envelope_map::BANK
                || generated.bits[BANK53_MAP_LIVE_BITS..].iter().any(|bit| *bit) {
                return Err("Eligible08 generated Map owner/binding/zero-tail".into());
            }
            let terms = crate::bank53_map::map_owner_terms_for_descriptor(
                map, owner as u64, context, self.descriptor)?;
            stage.claim_map_live(context, &generated.bits[..BANK53_MAP_LIVE_BITS])?;
            stage.map_terms[context] = terms;
            generated_maps.push(generated);
        }
        let generated_maps = generated_maps.try_into()
            .map_err(|_| "Eligible08 generated Map context census")?;
        Ok((stage, generated_maps))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn synthetic_fold(e: usize, maximum: BigUint, max_d: BigUint,
        max_b: BigUint) -> FoldedCut {
        FoldedCut {
            envelope: GlobalEnvelope { n: 1_827_840, max_difficulty: max_d.clone(),
                modern_floor: (&max_d * 3u8) / 2u8, maximum_candidate: maximum,
                exponent: e, u: BigUint::from(1u8) << e,
                header_count: 1_827_839, legacy_count: 822 },
            max_d: (2, max_d), max_b: (9, max_b),
        }
    }

    #[test]
    fn lower_witness_b_and_isolated_literal_dispatch_are_separate_from_d() {
        let b = synthetic_fold(6, 40u8.into(), 20u8.into(), 40u8.into());
        assert_eq!(selected_lower(&b).unwrap(), LowerSelector {
            source: LowerSource::LegacyBound { q: 9 }, branch: LowerBranch::Pivot(3) });
        // Literal dispatch is tested directly; an actual Eligible08 fold has
        // mandatory reset D values and cannot reach this literal branch.
        let initial = BigUint::from(global_u_roster::INITIAL_I);
        let literal = synthetic_fold(41, initial, 1u8.into(), 1u8.into());
        assert_eq!(selected_lower(&literal).unwrap(), LowerSelector {
            source: LowerSource::InitialI, branch: LowerBranch::Literal });
        let reset = BigUint::from(global_u_roster::RESET_CHILD_417792);
        let literal = synthetic_fold(47, reset, 1u8.into(), 1u8.into());
        assert_eq!(selected_lower(&literal).unwrap(), LowerSelector {
            source: LowerSource::Reset417792, branch: LowerBranch::Literal });
        assert!(global_u_roster::RESET_CHILD_417792 > global_u_roster::INITIAL_I);
        assert!(H21EligibleMapStage::descriptor().terminals().iter().all(|cut| *cut > 417_793));
    }

    #[test]
    fn supplied_candidate_error_precedes_fold_missing_item() {
        let error = fold_cut_with(3, |source| match source {
            CandidateSource::HeaderDifficulty { height: 2, .. } => Err("source read fault".into()),
            _ => Ok(BigUint::from(global_u_roster::INITIAL_I)),
        }).unwrap_err();
        assert!(error.contains("source read fault"));
        assert!(!error.contains("missing item"));
    }

    #[test]
    fn c495_dynamic_map_observation_requires_complete_source_binding() -> Result<(), String> {
        // Synthetic scheduled candidates exercise the genuine fold/Map path
        // and the same pure checker used by the native accessor. They provide
        // no native parent, owner output, destination or publication evidence.
        let descriptor = H21EligibleMapStage::descriptor();
        let mut maps = Vec::new();
        let mut envelopes = Vec::new();
        for cut in descriptor.terminals() {
            let folded = fold_cut_with(cut as u64, |source| Ok(match source {
                CandidateSource::HeaderDifficulty { height: 1_820_100, .. } =>
                    BigUint::from(1u8) << 55,
                CandidateSource::HeaderDifficulty { height: 417_792 | 417_793, .. } =>
                    BigUint::from(global_u_roster::RESET_CHILD_417792),
                _ => BigUint::from(global_u_roster::INITIAL_I),
            }))?;
            maps.push(map_for_fold(cut as u64, &folded)?.0);
            envelopes.push(folded.envelope);
        }
        let maps: [Map; 2] = maps.try_into().map_err(|_| "C495 fixture Map census")?;
        let bindings = maps.each_ref().map(|map| map.binding());
        let observed = checked_dynamic_map_exponents(&maps, &envelopes, &bindings, descriptor)?;
        assert_eq!(observed, [56, 48], "structural fixture only, never native expectation");

        // Change only the admitted exponent. All parent, owner, geometry,
        // mode, selector and contract fields remain fixed.
        let mut wrong_literal = bindings.clone();
        wrong_literal[0].e = 55;
        assert!(checked_dynamic_map_exponents(&maps, &envelopes,
            &wrong_literal, descriptor).is_err(), "isolated synthetic exponent literal");
        // Change only the retained source exponent, then omit only its second
        // record. Neither may be accepted as a complete source observation.
        let mut wrong_source = envelopes.clone();
        wrong_source[0].exponent = 55;
        assert!(checked_dynamic_map_exponents(&maps, &wrong_source,
            &bindings, descriptor).is_err(), "isolated source exponent replacement");
        assert!(checked_dynamic_map_exponents(&maps, &envelopes[..1],
            &bindings, descriptor).is_err(), "omitted source envelope");

        let mut wrong_mode = bindings.clone();
        wrong_mode[0] = Map::new_modern_global_u(bindings[0].n,
            bindings[0].h, bindings[0].e)?.binding();
        assert_eq!((wrong_mode[0].n, wrong_mode[0].h, wrong_mode[0].e,
            wrong_mode[0].parent_root), (bindings[0].n, bindings[0].h,
            bindings[0].e, bindings[0].parent_root));
        assert_ne!(wrong_mode[0], bindings[0]);
        assert!(checked_dynamic_map_exponents(&maps, &envelopes,
            &wrong_mode, descriptor).is_err(), "full mode/contract binding");

        let mut wrong_selector = bindings.clone();
        wrong_selector[0] = Map::new_modern_global_u_selected_lower(bindings[0].n,
            bindings[0].h, bindings[0].e, LowerSelector {
                source: LowerSource::HeaderDifficulty { height: 841_730 },
                branch: LowerBranch::Pivot(bindings[0].e - 1),
            })?.binding();
        assert_eq!((wrong_selector[0].n, wrong_selector[0].h, wrong_selector[0].e,
            wrong_selector[0].parent_root), (bindings[0].n, bindings[0].h,
            bindings[0].e, bindings[0].parent_root));
        assert_ne!(wrong_selector[0], bindings[0]);
        assert!(checked_dynamic_map_exponents(&maps, &envelopes,
            &wrong_selector, descriptor).is_err(), "selector-only binding");
        Ok(())
    }

    #[test]
    fn synthetic_eligible_cuts_derive_separate_e55_e48_and_admit_two_map_leases() {
        let descriptor = H21EligibleMapStage::descriptor();
        let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x65; 32], [0x66; 28]).unwrap();
        let roster = DaaHistoryRoster::compile(&plan).unwrap();
        let mask = plan.physical_assignment_replacement_mask(845_759).unwrap();
        let mut maps = Vec::new();
        let mut exponents = Vec::new();
        for cut in descriptor.terminals() {
            let folded = fold_cut_with(cut as u64, |source| Ok(match source {
                CandidateSource::HeaderDifficulty { height, .. } if height == 1_820_100 =>
                    BigUint::from(1u8) << 54,
                CandidateSource::HeaderDifficulty { height, .. } if height == 417_792 || height == 417_793 =>
                    BigUint::from(global_u_roster::RESET_CHILD_417792),
                _ => BigUint::from(global_u_roster::INITIAL_I),
            })).unwrap();
            exponents.push(folded.envelope.exponent);
            maps.push(map_for_fold(cut as u64, &folded).unwrap().0);
        }
        assert_eq!(exponents, [55, 48]);
        let maps: [Map; 2] = maps.try_into().unwrap();
        let mut stage = H21EligibleMapStage::new_bound(&plan, [0x67; 32], 845_759,
            roster.owner_class(845_759).unwrap(), descriptor, &maps, &mask).unwrap();
        stage.claim_map_live(0, &vec![false; BANK53_MAP_LIVE_BITS]).unwrap();
        stage.claim_map_live(1, &vec![false; BANK53_MAP_LIVE_BITS]).unwrap();
        assert_eq!(stage.map_bindings[0].e, 55);
        assert_eq!(stage.map_bindings[1].e, 48);
        assert_eq!(stage.claim_cell(H21StageAuthor::Map(0), 677_501, false).unwrap_err(),
            "c170 cell outside author lease");
        let mut swapped = maps.clone(); swapped.swap(0, 1);
        assert!(H21EligibleMapStage::new_bound(&plan, [0x67; 32], 845_759,
            roster.owner_class(845_759).unwrap(), descriptor, &swapped, &mask).is_err());
        let other = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x68; 32], [0x66; 28]).unwrap();
        assert!(stage.validate_identity(&other, [0x67; 32], descriptor, &maps).is_err());
        let mut changed = maps.clone();
        changed[1] = Map::new_modern_global_u_selected_lower(
            descriptor.terminals()[1] as u64, 21, 55,
            LowerSelector { source: LowerSource::HeaderDifficulty { height: 841_729 },
                branch: LowerBranch::Pivot(54) }).unwrap();
        assert!(stage.validate_identity(&plan, [0x67; 32], descriptor, &changed).is_err());
    }
}

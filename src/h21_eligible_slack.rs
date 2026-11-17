//! Owner-local Slack X/ROW admission from already generated Eligible08 Maps.
//! This is opaque and incomplete: it has no serialization or finish operation.
use super::*;
use super::h21_eligible_context::{
    H21ClosedScoreOwnerRelation, ScoreRelationReadAuthor, ScoreReplayAuthor,
};
use crate::legacy_envelope_map::{Binding, OwnerRow};
use crate::sparse::Term;
use std::collections::{BTreeMap, BTreeSet};

const SLACK_BITS: usize = 387;
const SLACK_MAP_TAIL_START: usize = BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT;

/// Map remains the source authority; Slack cells and rows are kept in a
/// separate owner-local subledger so the existing Score consumer is unchanged.
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct H21EligibleSlackStage {
    pub(super) map_stage: H21EligibleMapStage,
    slack_claims: BTreeMap<usize, (H21StageAuthor, bool)>,
    slack_terms: [Vec<Term>; 2],
    score_claims: BTreeMap<usize, (ScoreReplayAuthor, Fr)>,
    score_terms: [Vec<Term>; 2],
    score_reads: Vec<(usize, ScoreRelationReadAuthor, Fr)>,
}

impl H21EligibleSlackStage {
    // Read-only views for the context-bound owner sink. These do not create
    // source authors or permit a consumer to change an admitted source.
    pub(super) fn slack_cells(&self) -> &BTreeMap<usize, (H21StageAuthor, bool)> {
        &self.slack_claims
    }
    pub(super) fn slack_rows(&self) -> &[Vec<Term>; 2] { &self.slack_terms }
    pub(super) fn score_cells(&self) -> &BTreeMap<usize, (ScoreReplayAuthor, Fr)> {
        &self.score_claims
    }
    pub(super) fn score_rows(&self) -> &[Vec<Term>; 2] { &self.score_terms }
    pub(super) fn score_imports(&self) -> &[(usize, ScoreRelationReadAuthor, Fr)] {
        &self.score_reads
    }

    #[cfg(test)]
    pub(super) fn synthetic_owner_sink_source() -> Self {
        // Structural fixture only: no native prefix, parent admission or
        // arithmetic authentication is claimed by these selected source bits.
        let owner = 845_759;
        let mut map = H21EligibleMapStage::test_identity_only(owner).unwrap();
        map.class = crate::daa_history_roster::OwnerClass::Carry;
        for context in 0..2 {
            map.claim_map_live(context, &vec![false; BANK53_MAP_LIVE_BITS]).unwrap();
            map.map_terms[context] = vec![Term {row: owner * crate::bank53_map::ROW_STRIDE
                + crate::bank53_map::CONTEXT_ROW_BASE + context * 32_768,
                gate: crate::gkr::Gate {left: owner * WIDTH + H21EligibleMapStage::map_live(context).unwrap().start,
                    right: 0, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero()}}];
        }
        let mut stage = Self::new(map);
        let layout = crate::origin_score::Layout::new();
        for context in 0..2 {
            for local in H21EligibleMapStage::slack_live(context).unwrap() {
                stage.slack_claims.insert(local, (H21StageAuthor::Slack(context), false));
            }
            stage.slack_terms[context] = crate::bank53_slack::slack_zero_terms(owner, context).unwrap();
            let author = ScoreReplayAuthor {context, origin: owner + 1, previous_owner: owner - 1,
                max_owner: 844_670, cap_owner: owner};
            let base = H21EligibleMapStage::score_live(context).unwrap().start;
            for local in H21EligibleMapStage::score_live(context).unwrap() {
                stage.score_claims.insert(local, (author, Fr::zero()));
            }
            stage.score_terms[context] = vec![Term {row: owner * crate::bank53_map::ROW_STRIDE
                + crate::bank53_map::CONTEXT_ROW_BASE + context * 32_768 + 16_384,
                gate: crate::gkr::Gate {left: owner * WIDTH + base, right: 0,
                    c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero()}}];
            for (start, source, width) in [
                ((owner - 1) * WIDTH + base + layout.r.start,
                    ScoreRelationReadAuthor::PreviousR {context, owner: owner - 1}, 225),
                (owner * WIDTH + H21EligibleMapStage::cap_live(context).unwrap().start + 740,
                    ScoreRelationReadAuthor::Cap {context, origin: owner + 1, max_owner: 844_670, cap_owner: owner}, 65),
                ((owner - 1) * WIDTH + 987_450,
                    ScoreRelationReadAuthor::WorkUpper {owner: owner - 1, height: owner + 1}, 224),
            ] {
                stage.score_reads.extend((0..width).map(|bit| (start + bit, source, Fr::zero())));
            }
        }
        stage
    }

    /// Test-only selected-owner ROW geometry. The older synthetic Score row
    /// predates the v5 reader; keep that fixture unchanged for its other tests.
    #[cfg(test)]
    pub(super) fn synthetic_owner_sink_source_for_c455() -> Self {
        let mut stage = Self::synthetic_owner_sink_source();
        let owner = 845_759usize;
        for context in 0..2 {
            assert_eq!(stage.score_terms[context].len(), 1);
            assert_eq!(stage.score_terms[context][0].row,
                owner * crate::bank53_map::ROW_STRIDE + crate::bank53_map::CONTEXT_ROW_BASE
                    + context * 32_768 + 16_384);
            stage.score_terms[context][0].row = owner * crate::bank53_map::ROW_STRIDE
                + [487_421, 502_652][context];
        }
        stage
    }

    /// Keep the synthetic Score fixture internally consistent with the full
    /// published Cap source selected by a sink test. This does not construct a
    /// native prefix or a closed Score relation.
    #[cfg(test)]
    pub(super) fn with_cap_q_for_sink_test(mut self,q:[Vec<(usize,bool)>;2])->Self {
        let layout=crate::origin_score::Layout::new();
        for context in 0..2 {
            assert_eq!(q[context].len(),65);
            let base=H21EligibleMapStage::score_live(context).unwrap().start;
            for (bit,(wire,value)) in q[context].iter().enumerate() {
                self.score_claims.get_mut(&(base+layout.sv.start+bit)).unwrap().1=Fr::from(*value as u64);
                let read=self.score_reads.iter_mut().find(|(w,author,_)|*w==*wire
                    && matches!(author,ScoreRelationReadAuthor::Cap{context:c,..} if *c==context)).unwrap();
                read.2=Fr::from(*value as u64);
            }
        }
        self
    }

    /// Synthetic incidence rows for the C358 occurrence census only. They
    /// connect each declared Score import to its already authored local bit;
    /// they do not replace or authenticate the production Score relation.
    #[cfg(test)]
    pub(super) fn with_score_read_alias_rows_for_sink_test(mut self)->Self {
        let owner=845_759usize;
        let layout=crate::origin_score::Layout::new();
        let reads_per_context=225+65+224;
        assert_eq!(self.score_reads.len(),2*reads_per_context);
        for context in 0..2 {
            let score_base=H21EligibleMapStage::score_live(context).unwrap().start;
            let cap_base=H21EligibleMapStage::cap_live(context).unwrap().start+740;
            let row_base=owner*crate::bank53_map::ROW_STRIDE
                +crate::bank53_map::CONTEXT_ROW_BASE+context*32_768+16_384;
            for (ordinal,&(wire,author,value)) in self.score_reads
                [context*reads_per_context..(context+1)*reads_per_context].iter().enumerate() {
                let local=match author {
                    ScoreRelationReadAuthor::PreviousR{context:c,owner:previous}
                        if c==context && previous+1==owner => {
                        let bit=wire.checked_sub(previous*WIDTH+score_base+layout.r.start).unwrap();
                        assert!(bit<225);layout.p.start+bit
                    },
                    ScoreRelationReadAuthor::Cap{context:c,origin,cap_owner,..}
                        if c==context && origin==owner+1 && cap_owner==owner => {
                        let bit=wire.checked_sub(owner*WIDTH+cap_base).unwrap();
                        assert!(bit<65);layout.sv.start+bit
                    },
                    ScoreRelationReadAuthor::WorkUpper{owner:upper,height}
                        if upper+1==owner && height==owner+1 => {
                        let bit=wire.checked_sub(upper*WIDTH+987_450).unwrap();
                        assert!(bit<224);layout.sw.start+bit
                    },
                    _=>panic!("C358 synthetic Score import author/coordinate"),
                };
                assert_eq!(self.score_claims[&(score_base+local)].1,value);
                self.score_terms[context].push(Term {row:row_base+1+ordinal,
                    gate:crate::gkr::Gate {left:wire,
                        right:owner*WIDTH+score_base+local,c0:Fr::zero(),
                        c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}});
            }
            assert_eq!(self.score_terms[context].len(),1+reads_per_context);
        }
        self
    }

    pub(super) fn new(map_stage: H21EligibleMapStage) -> Self {
        Self { map_stage, slack_claims: BTreeMap::new(), slack_terms: [Vec::new(), Vec::new()],
            score_claims: BTreeMap::new(), score_terms: [Vec::new(), Vec::new()],
            score_reads: Vec::new() }
    }

    #[cfg(test)]
    pub(super) fn score_snapshot_for_test(&self) -> (
        BTreeMap<usize, (ScoreReplayAuthor, Fr)>, [Vec<Term>; 2],
        Vec<(usize, ScoreRelationReadAuthor, Fr)>,
    ) {
        (self.score_claims.clone(), self.score_terms.clone(), self.score_reads.clone())
    }

    /// Admit only a sealed, terminal-closed Score source beside the two Map
    /// and Slack authors. Foreign reads remain typed obligations for the later
    /// global merger; no complete physical row is exported here.
    pub(crate) fn admit_score_relation(
        &mut self, relation: H21ClosedScoreOwnerRelation<'_>,
    ) -> Result<(), String> {
        let owner = self.map_stage.owner;
        if relation.owner() != owner
            || relation.parent_root() != self.map_stage.parent_root
            || relation.parent_total() != self.map_stage.parent_total
            || relation.parent_profile() != self.map_stage.parent_profile
            || relation.cut_identity() != self.map_stage.cut_identity.as_slice()
            || !self.score_claims.is_empty()
            || self.score_terms.iter().any(|terms| !terms.is_empty())
            || !self.score_reads.is_empty()
        {
            return Err("Eligible08 Score relation parent/cut/owner/duplicate".into());
        }
        let authors = relation.authors();
        let mut active = 0usize;
        for (context, author) in authors.iter().enumerate() {
            let terms = relation.terms(context)?;
            match author {
                Some(author) if author.context == context && author.cap_owner == owner
                    && author.origin == owner + 1 && !terms.is_empty() => active += 1,
                None if terms.is_empty() => (),
                _ => return Err("Eligible08 Score active context/term census".into()),
            }
        }
        if active == 0 || relation.cells().len() != active * crate::origin_score::INPUT
            || relation.reads().len() != active * (225 + 224 + 65) {
            return Err("Eligible08 Score exact active source census".into());
        }
        let mut claims = BTreeMap::new();
        for &(wire, author, value) in relation.cells() {
            let context = author.context;
            let local = wire.checked_sub(owner * WIDTH)
                .ok_or("Eligible08 Score X owner underflow")?;
            if context >= BANK53_CONTEXTS || authors[context] != Some(author)
                || !H21EligibleMapStage::score_live(context)?.contains(&local)
                || !(value.is_zero() || value.is_one())
                || self.map_stage.claims.contains_key(&local)
                || self.slack_claims.contains_key(&local)
                || claims.insert(local, (author, value)).is_some() {
                return Err("Eligible08 Score X author/value/collision".into());
            }
        }
        for (context, author) in authors.iter().enumerate() {
            if author.is_some() && H21EligibleMapStage::score_live(context)?
                .any(|cell| !claims.contains_key(&cell)) {
                return Err("Eligible08 Score missing physical X author".into());
            }
        }
        let mut occupied = BTreeMap::new();
        for (writer, terms) in [
            (0usize, self.map_stage.map_terms[0].as_slice()),
            (1, self.map_stage.map_terms[1].as_slice()),
            (2, self.slack_terms[0].as_slice()),
            (3, self.slack_terms[1].as_slice()),
            (4, relation.terms(0)?),
            (5, relation.terms(1)?),
        ] {
            for term in terms {
                if term.row / crate::bank53_map::ROW_STRIDE != owner
                    || occupied.insert(term.row, writer).is_some_and(|prior| prior != writer) {
                    return Err("Eligible08 Score/Map/Slack ROW writer collision".into());
                }
            }
        }
        let mut reads = BTreeMap::new();
        let mut kinds = [0usize; 3];
        let layout = crate::origin_score::Layout::new();
        for &(wire, source, value) in relation.reads() {
            if !(value.is_zero() || value.is_one())
                || reads.insert(wire, value).is_some_and(|prior| prior != value) {
                return Err("Eligible08 Score foreign read value collision".into());
            }
            match source {
                ScoreRelationReadAuthor::PreviousR {context, owner: previous} => {
                    if context >= BANK53_CONTEXTS
                        || authors[context].is_none_or(|author| author.previous_owner != previous)
                        || previous >= owner
                        || !(previous * WIDTH + H21EligibleMapStage::score_live(context)?.start
                            + layout.r.start .. previous * WIDTH
                            + H21EligibleMapStage::score_live(context)?.start
                            + layout.r.end).contains(&wire) {
                        return Err("Eligible08 Score predecessor R read".into());
                    }
                    kinds[0] += 1;
                }
                ScoreRelationReadAuthor::WorkUpper {owner: work, height} => {
                    if work + 1 != owner || height != owner + 1
                        || !(work * WIDTH + 987_450 .. work * WIDTH + 987_674)
                            .contains(&wire) {
                        return Err("Eligible08 Score WORK W read".into());
                    }
                    kinds[1] += 1;
                }
                ScoreRelationReadAuthor::Cap {context, origin, max_owner, cap_owner} => {
                    if context >= BANK53_CONTEXTS
                        || authors[context].is_none_or(|author|
                            author.origin != origin || author.max_owner != max_owner)
                        || cap_owner != owner || origin != owner + 1
                        || !(owner * WIDTH + H21EligibleMapStage::cap_live(context)?.start + 740
                            .. owner * WIDTH + H21EligibleMapStage::cap_live(context)?.start + 805)
                            .contains(&wire) {
                        return Err("Eligible08 Score Cap V read".into());
                    }
                    kinds[2] += 1;
                }
            }
        }
        if kinds != [225 * active, 224 * active, 65 * active] {
            return Err("Eligible08 Score foreign read role census".into());
        }
        let mut staged = self.clone();
        staged.score_claims = claims;
        staged.score_terms = [relation.terms(0)?.to_vec(), relation.terms(1)?.to_vec()];
        staged.score_reads = relation.reads().to_vec();
        *self = staged;
        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct SlackLease {
    parent_root: [u8; 32],
    parent_total: [u8; 28],
    parent_profile: [u8; 32],
    cut_identity: Vec<u8>,
    binding: Binding,
    owner: usize,
    context: usize,
    bits: Vec<bool>,
    terms: Vec<Term>,
}

impl SlackLease {
    #[cfg(test)]
    pub(crate) fn remove_bit_for_test(&mut self, index: usize) -> Result<(), String> {
        if index >= self.bits.len() {
            return Err("C440 test Slack bit index outside source".into());
        }
        self.bits.remove(index);
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn remove_term_for_test(&mut self, index: usize) -> Result<(), String> {
        if index >= self.terms.len() {
            return Err("C442 test Slack term index outside source".into());
        }
        self.terms.remove(index);
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn set_bit_for_test(&mut self, index: usize, value: bool) -> Result<(), String> {
        let bit = self.bits.get_mut(index)
            .ok_or_else(|| "C440 test Slack bit index outside source".to_string())?;
        *bit = value;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn alter_row_term_for_test(&mut self, index: usize) -> Result<(), String> {
        let term = self.terms.get_mut(index)
            .ok_or_else(|| "C440 test Slack term index outside source".to_string())?;
        term.row = term.row.checked_add(1)
            .ok_or("C440 test Slack term row overflow")?;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn synthetic_for_bundle_test(
        expected: &crate::packed_owner_assembly::HeaderSourceBinding,
        binding: &Binding,
        owner: usize,
        context: usize,
    ) -> Result<Self, String> {
        if context >= BANK53_CONTEXTS || expected.owner() != owner
            || !expected.matches_sink(
                [0x51; 32], [0x52; 28], [0x53; 32],
                &H21EligibleMapStage::descriptor().canonical_identity(), owner,
            )
        {
            return Err("C440 synthetic Slack test identity only".into());
        }
        let terms = crate::bank53_slack::slack_zero_terms(owner, context)?;
        Ok(Self {
            parent_root: [0x51; 32], parent_total: [0x52; 28],
            parent_profile: [0x53; 32],
            cut_identity: H21EligibleMapStage::descriptor().canonical_identity(),
            binding: binding.clone(), owner, context,
            bits: vec![false; SLACK_BITS], terms,
        })
    }

    /// Geometry-only zero Slack fixture under the exact ordinary ROW plan.
    /// The historical diagnostic fixture above retains its original identity.
    #[cfg(test)]
    pub(crate) fn synthetic_for_plan_bundle_test(
        plan: &WorkTreeHistoryPlan,
        expected: &crate::packed_owner_assembly::HeaderSourceBinding,
        binding: &Binding,
        owner: usize,
        context: usize,
    ) -> Result<Self, String> {
        let actual = crate::packed_owner_assembly::HeaderSourceBinding::for_plan(plan, owner)?;
        if context >= BANK53_CONTEXTS || expected != &actual {
            return Err("C448 synthetic Slack exact plan binding/context".into());
        }
        let lease = Self {
            parent_root: plan.descriptor().root,
            parent_total: plan.work_profile().total_be28,
            parent_profile: actual.profile(),
            cut_identity: H21EligibleMapStage::descriptor().canonical_identity(),
            binding: binding.clone(), owner, context,
            bits: vec![false; SLACK_BITS],
            terms: crate::bank53_slack::slack_zero_terms(owner, context)?,
        };
        lease.checked_bundle_source(expected, binding, owner, context)?;
        Ok(lease)
    }

    pub(super) fn from_generated(
        map_stage: &H21EligibleMapStage,
        context: usize,
        generated: &OwnerRow,
    ) -> Result<Self, String> {
        if context >= BANK53_CONTEXTS
            || map_stage.cut_identity != H21EligibleMapStage::descriptor().canonical_identity()
            || generated.owner != map_stage.owner as u64
            || generated.binding != map_stage.map_bindings[context]
            || generated.bits.len() != crate::legacy_envelope_map::BANK
            || generated.bits[BANK53_MAP_LIVE_BITS..].iter().any(|bit| *bit)
        {
            return Err("Eligible08 Slack source parent/cut/owner/context/binding/tail".into());
        }
        let end = SLACK_MAP_TAIL_START.checked_add(SLACK_BITS)
            .ok_or("Eligible08 Slack source range overflow")?;
        if SLACK_MAP_TAIL_START < BANK53_MAP_LIVE_BITS || end != BANK53_CONTEXT_BITS {
            return Err("Eligible08 Slack context queue geometry".into());
        }
        // OwnerRow is shorter than the 8192-bit context lane. Rebuild the
        // canonical Map queue exactly as the packed Map assignment does:
        // copy its LIVE prefix and retain a zero tail through the lane end.
        let mut map_queue = vec![false; BANK53_CONTEXT_BITS];
        map_queue[..BANK53_MAP_LIVE_BITS]
            .copy_from_slice(&generated.bits[..BANK53_MAP_LIVE_BITS]);
        let bits = map_queue[SLACK_MAP_TAIL_START..end].to_vec();
        if bits.len() != SLACK_BITS || bits.iter().any(|bit| *bit) {
            return Err("Eligible08 Slack source must be exactly 387 zero bits".into());
        }
        let terms = crate::bank53_slack::slack_zero_terms(map_stage.owner, context)?;
        if terms.len() != SLACK_BITS {
            return Err("Eligible08 Slack ROW source length".into());
        }
        Ok(Self {
            parent_root: map_stage.parent_root,
            parent_total: map_stage.parent_total,
            parent_profile: map_stage.parent_profile,
            cut_identity: map_stage.cut_identity.clone(),
            binding: generated.binding.clone(),
            owner: map_stage.owner,
            context,
            bits,
            terms,
        })
    }

    fn check_identity(&self, map_stage: &H21EligibleMapStage) -> Result<(), String> {
        if self.context >= BANK53_CONTEXTS
            || self.parent_root != map_stage.parent_root
            || self.parent_total != map_stage.parent_total
            || self.parent_profile != map_stage.parent_profile
            || self.cut_identity != map_stage.cut_identity
            || self.cut_identity != H21EligibleMapStage::descriptor().canonical_identity()
            || self.owner != map_stage.owner
            || self.binding != map_stage.map_bindings[self.context]
        {
            return Err("Eligible08 Slack lease parent/cut/profile/owner/context/binding".into());
        }
        Ok(())
    }

    /// Revalidate a source lease after it has been detached into the opaque
    /// Map+Slack bundle. Callers receive only immutable, checked source data.
    pub(crate) fn checked_bundle_source<'a>(
        &'a self,
        expected: &crate::packed_owner_assembly::HeaderSourceBinding,
        expected_map_binding: &Binding,
        owner: usize,
        context: usize,
    ) -> Result<(&'a [bool], &'a [Term]), String> {
        if context >= BANK53_CONTEXTS
            || self.context != context
            || self.owner != owner
            || self.binding != *expected_map_binding
            || !expected.matches_sink(
                self.parent_root, self.parent_total, self.parent_profile,
                &self.cut_identity, owner,
            )
            || self.cut_identity != H21EligibleMapStage::descriptor().canonical_identity()
            || self.bits.len() != SLACK_BITS || self.bits.iter().any(|bit| *bit)
            || self.terms.len() != SLACK_BITS
            || self.terms != crate::bank53_slack::slack_zero_terms(owner, context)?
        {
            return Err("Eligible08 bundled Slack parent/context/zero X/ROW source".into());
        }
        Ok((&self.bits, &self.terms))
    }

    pub(super) fn admit_into(self, destination: &mut H21EligibleSlackStage) -> Result<(), String> {
        let map_stage = &destination.map_stage;
        self.check_identity(map_stage)?;
        let context = self.context;
        let domain = H21EligibleMapStage::slack_live(context)?;
        if self.bits.len() != SLACK_BITS || domain.len() != SLACK_BITS
            || self.bits.iter().any(|bit| *bit)
            || self.terms.len() != SLACK_BITS
            || self.terms != crate::bank53_slack::slack_zero_terms(self.owner, context)?
        {
            return Err("Eligible08 Slack exact zero X/ROW census".into());
        }

        // The same owner must carry all Map live cells, including authored
        // zeros, before this context's Slack cells and ROW terms are admitted.
        for cell in H21EligibleMapStage::map_live(context)? {
            if !matches!(map_stage.claims.get(&cell),
                Some((H21StageAuthor::Map(found), _)) if *found == context) {
                return Err("Eligible08 Slack missing coactive Map author".into());
            }
        }

        let mut occupied_rows = BTreeSet::new();
        for terms in &map_stage.map_terms {
            // A Map polynomial may contain several Terms for the same ROW.
            // ROW identity is unique per Map author, while overlap between
            // distinct Map authors/contexts remains a collision.
            let source_rows: BTreeSet<_> = terms.iter().map(|term| term.row).collect();
            if source_rows.iter().any(|row| occupied_rows.contains(row)) {
                return Err("Eligible08 cross-author Map ROW collision".into());
            }
            occupied_rows.extend(source_rows);
        }
        for terms in &destination.slack_terms {
            let mut source_rows = BTreeSet::new();
            for term in terms {
                if !source_rows.insert(term.row) || occupied_rows.contains(&term.row) {
                    return Err("Eligible08 duplicate Slack ROW source".into());
                }
            }
            occupied_rows.extend(source_rows);
        }
        for terms in &destination.score_terms {
            let source_rows: BTreeSet<_> = terms.iter().map(|term| term.row).collect();
            if source_rows.iter().any(|row| occupied_rows.contains(row)) {
                return Err("Eligible08 Slack/Score ROW collision".into());
            }
            occupied_rows.extend(source_rows);
        }
        let mut current_rows = BTreeSet::new();
        for term in &self.terms {
            if !current_rows.insert(term.row) || occupied_rows.contains(&term.row) {
                return Err("Eligible08 Map/Slack ROW collision".into());
            }
        }

        if domain.clone().any(|cell| destination.slack_claims.contains_key(&cell)
            || destination.score_claims.contains_key(&cell))
            || !destination.slack_terms[context].is_empty() {
            return Err("Eligible08 Slack duplicate X/ROW author".into());
        }

        // Stage into a clone and swap only after every expected X cell is present.
        let mut staged = destination.clone();
        for (cell, bit) in domain.zip(self.bits) {
            if !H21EligibleMapStage::slack_live(context)?.contains(&cell)
                || staged.slack_claims.insert(cell, (H21StageAuthor::Slack(context), bit)).is_some() {
                return Err("Eligible08 Slack X destination collision".into());
            }
        }
        staged.slack_terms[context] = self.terms;
        if H21EligibleMapStage::slack_live(context)?.any(|cell|
            !matches!(staged.slack_claims.get(&cell),
                Some((H21StageAuthor::Slack(found), false)) if *found == context)) {
            return Err("Eligible08 Slack admitted X census".into());
        }
        *destination = staged;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // This test-only stage skips full parent-plan/roster admission; Map terms
    // themselves still come from the real symbolic Map materializer.
    fn fixture(owner: usize) -> H21EligibleSlackStage {
        let descriptor = H21EligibleMapStage::descriptor();
        let maps = H21EligibleMapStage::source_maps().unwrap();
        let mut map_stage = H21EligibleMapStage::test_identity_only(owner).unwrap();
        for context in 0..BANK53_CONTEXTS {
            map_stage.claim_map_live(context, &vec![false; BANK53_MAP_LIVE_BITS]).unwrap();
            map_stage.map_terms[context] = crate::bank53_map::map_owner_terms_for_descriptor(
                &maps[context], owner as u64, context, descriptor).unwrap();
        }
        H21EligibleSlackStage::new(map_stage)
    }

    fn identity_fixture(owner: usize) -> H21EligibleSlackStage {
        H21EligibleSlackStage::new(
            H21EligibleMapStage::test_identity_only(owner).unwrap())
    }

    fn synthetic_lease(stage: &H21EligibleSlackStage, context: usize) -> SlackLease {
        let generated = OwnerRow {
            owner: stage.map_stage.owner as u64,
            binding: stage.map_stage.map_bindings[context].clone(),
            bits: vec![false; crate::legacy_envelope_map::BANK],
        };
        SlackLease::from_generated(&stage.map_stage, context, &generated).unwrap()
    }

    #[test]
    fn both_map_contexts_coactivate_with_slack_at_owner_discriminants() {
        for owner in [417_790, 845_759] {
            let mut stage = fixture(owner);
            assert!(stage.map_stage.map_terms.iter().any(|terms| {
                let mut rows = BTreeSet::new();
                terms.iter().any(|term| !rows.insert(term.row))
            }), "fixture must include real Map polynomials with multiple Terms per ROW");
            for context in 0..BANK53_CONTEXTS {
                synthetic_lease(&stage, context).admit_into(&mut stage).unwrap();
                assert_eq!(stage.slack_terms[context].len(), SLACK_BITS);
                assert_eq!(H21EligibleMapStage::slack_live(context).unwrap().len(), SLACK_BITS);
            }
            assert_eq!(stage.slack_claims.len(), BANK53_CONTEXTS * SLACK_BITS);
        }
    }

    #[test]
    fn slack_lease_rejects_each_parent_cut_profile_owner_context_and_binding_mutant() {
        let stage = fixture(845_759);
        let pristine = synthetic_lease(&stage, 0);
        let mut mutants = Vec::new();
        let mut wrong = pristine.clone(); wrong.parent_root[0] ^= 1; mutants.push(wrong);
        let mut wrong = pristine.clone(); wrong.parent_total[0] ^= 1; mutants.push(wrong);
        let mut wrong = pristine.clone(); wrong.parent_profile[0] ^= 1; mutants.push(wrong);
        let mut wrong = pristine.clone(); wrong.cut_identity.push(1); mutants.push(wrong);
        let mut wrong = pristine.clone(); wrong.owner += 1; mutants.push(wrong);
        let mut wrong = pristine.clone(); wrong.context = 2; mutants.push(wrong);
        let mut wrong = pristine.clone(); wrong.binding = stage.map_stage.map_bindings[1].clone(); mutants.push(wrong);
        for lease in mutants {
            assert!(lease.check_identity(&stage.map_stage).is_err());
        }
    }

    #[test]
    fn generated_slack_source_rejects_wrong_owner_binding_and_nonzero_tail() {
        let stage = identity_fixture(845_759);
        let mut generated = OwnerRow {
            owner: stage.map_stage.owner as u64,
            binding: stage.map_stage.map_bindings[0].clone(),
            bits: vec![false; crate::legacy_envelope_map::BANK],
        };
        generated.owner += 1;
        assert!(SlackLease::from_generated(&stage.map_stage, 0, &generated).is_err());
        generated.owner -= 1;

        generated.binding = stage.map_stage.map_bindings[1].clone();
        assert!(SlackLease::from_generated(&stage.map_stage, 0, &generated).is_err());
        generated.binding = stage.map_stage.map_bindings[0].clone();

        generated.bits[BANK53_MAP_LIVE_BITS] = true;
        assert!(SlackLease::from_generated(&stage.map_stage, 0, &generated).is_err());
        generated.bits[BANK53_MAP_LIVE_BITS] = false;

        generated.bits.pop();
        assert!(SlackLease::from_generated(&stage.map_stage, 0, &generated).is_err());
    }

    #[test]
    fn slack_rejects_nonzero_wrong_lengths_out_of_domain_and_equal_zero_duplicates_atomically() {
        let mut stage = fixture(845_759);
        let before = stage.clone();
        let mut nonzero = synthetic_lease(&stage, 0);
        nonzero.bits[0] = true;
        assert!(nonzero.admit_into(&mut stage).is_err());
        assert!(stage == before);

        let mut wrong_term_address = synthetic_lease(&stage, 0);
        wrong_term_address.terms[0].gate.left ^= 1;
        assert!(wrong_term_address.admit_into(&mut stage).is_err());
        assert!(stage == before);

        for length in [SLACK_BITS - 1, SLACK_BITS + 1] {
            let mut wrong_length = synthetic_lease(&stage, 0);
            wrong_length.bits.resize(length, false);
            assert!(wrong_length.admit_into(&mut stage).is_err());
            assert!(stage == before);
        }
        let mut short_rows = synthetic_lease(&stage, 0);
        short_rows.terms.pop();
        assert!(short_rows.admit_into(&mut stage).is_err());
        assert!(stage == before);
        let mut outside = synthetic_lease(&stage, 0);
        outside.context = BANK53_CONTEXTS;
        assert!(outside.admit_into(&mut stage).is_err());
        assert!(stage == before);

        let lease = synthetic_lease(&stage, 0);
        lease.clone().admit_into(&mut stage).unwrap();
        let admitted = stage.clone();
        assert!(lease.admit_into(&mut stage).is_err());
        assert!(stage == admitted);
    }

    #[test]
    fn slack_rejects_map_row_alias_and_missing_map_author_without_mutation() {
        let mut stage = fixture(845_759);
        let lease = synthetic_lease(&stage, 0);
        stage.map_stage.map_terms[0].push(lease.terms[0].clone());
        let before = stage.clone();
        assert!(lease.admit_into(&mut stage).is_err());
        assert!(stage == before);

        let mut cross_author = fixture(845_759);
        let lease = synthetic_lease(&cross_author, 0);
        let context_one_rows: BTreeSet<_> = cross_author.map_stage.map_terms[1]
            .iter().map(|term| term.row).collect();
        let duplicated_map_row = cross_author.map_stage.map_terms[0].iter()
            .find(|term| !context_one_rows.contains(&term.row))
            .expect("fixture has a Map ROW unique to context zero").clone();
        cross_author.map_stage.map_terms[1].push(duplicated_map_row);
        let before = cross_author.clone();
        assert!(lease.admit_into(&mut cross_author).is_err());
        assert!(cross_author == before);

        let mut missing_map = fixture(845_759);
        missing_map.map_stage.claims.remove(
            &H21EligibleMapStage::map_live(0).unwrap().start);
        let before = missing_map.clone();
        assert!(synthetic_lease(&missing_map, 0).admit_into(&mut missing_map).is_err());
        assert!(missing_map == before);
    }

    #[test]
    fn slack_domain_requires_header_owned_parent_cells() {
        let mut mask = vec![false; WIDTH];
        H21EligibleMapStage::require_header_owned_slack_live(&mask).unwrap();
        mask[H21EligibleMapStage::slack_live(1).unwrap().start] = true;
        assert!(H21EligibleMapStage::require_header_owned_slack_live(&mask).is_err());
    }
}

#[cfg(test)]
impl H21EligibleSlackStage {
    pub(super) fn c575_toggle_first_stored_score_read_wire(&mut self) -> Result<(), String> {
        let first = self.score_reads.first_mut().ok_or("C575 stored Score read absent")?;
        first.0 ^= 1;
        Ok(())
    }
}

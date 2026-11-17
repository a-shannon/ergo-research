//! Opaque, owner-local join of closed Score and scheduled Cap sources.
//! Foreign reads and the remaining HEADER/DAA authors stay unresolved.
use super::*;
use crate::h21_scheduled_family_ledger::{Admission, ScoredOwnerCapMaterial,
    ScoredOwnerCapPublication};
use crate::h21_scheduled_max_cap::{MaxReplayAuthor, MaxStream, Writer};
use crate::header_daa_row_placement::{Batch, Relation, RowPlan};
use crate::legacy_envelope_map::{Binding, Import};
use crate::packed_owner_assembly::HeaderSourceBinding;
use super::h21_eligible_score::h21_score_class_equations::ClassEquationPlan;
use ark_ff::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

#[path = "h21_source_bound_partial_writer.rs"]
mod source_bound_partial_writer;

const WIDTH: usize = 1 << 20;
const SCORE_INPUT: usize = crate::origin_score::INPUT;

/// Work accounting only, never source/proof authority. Separate from C574's
/// original four-row/225-PreviousR budget; charges precede added work.
pub(crate) struct C576MaxBudget { limits:[usize;3], used:[usize;3] }
impl C576MaxBudget {
    pub(crate) fn new(rows:usize,reads:usize,retained:usize)->Self {Self{limits:[rows,reads,retained],used:[0;3]}}
    pub(super) fn charge(&mut self,rows:usize,reads:usize,retained:usize)->Result<(),String> {
        let next=[self.used[0].checked_add(rows),self.used[1].checked_add(reads),Some(self.used[2].max(retained))];
        let mut staged=[0;3];
        for i in 0..3 {staged[i]=next[i].ok_or("C576 work budget overflow")?;
            if staged[i]>self.limits[i]{return Err(format!("C576 budget{i} exhausted/incomplete"));}}
        self.used=staged;Ok(())
    }
    pub(crate) fn usage(&self)->[usize;3]{self.used}
}

/// Added Work assembly, occurrence reads and retained/control storage only.
pub(crate) struct C578WorkBudget { limits:[usize;3], used:[usize;3] }
impl C578WorkBudget {
    pub(crate) fn new(rows:usize,reads:usize,retained:usize)->Self {Self{limits:[rows,reads,retained],used:[0;3]}}
    pub(super) fn charge(&mut self,rows:usize,reads:usize,retained:usize)->Result<(),String> {
        let next=[self.used[0].checked_add(rows),self.used[1].checked_add(reads),Some(self.used[2].max(retained))];
        let mut staged=[0;3];
        for i in 0..3 {staged[i]=next[i].ok_or("C578 work budget overflow")?;
            if staged[i]>self.limits[i]{return Err(format!("C578 budget{i} exhausted/incomplete"));}}
        self.used=staged;Ok(())
    }
    pub(crate) fn usage(&self)->[usize;3]{self.used}
}

/// The existing join owns the context order and Score.sw equality. Upper
/// addresses repeat in the two contexts; do not deduplicate occurrences.
pub(super) fn c578_check_upper_import(ordinal:usize,read:&OpenScoredRead,
    physical:(crate::packed_owner_assembly::NativeWorkEndpointAuthor,Fr)) -> Result<(),String> {
    use crate::packed_owner_assembly::NativeWorkEndpointAuthor;
    if !read.value.is_zero() && !read.value.is_one() {
        return Err("C578 expected Upper Fr is not Boolean".into());
    }
    if !physical.1.is_zero() && !physical.1.is_one() {
        return Err("C578 original Upper Fr is not Boolean".into());
    }
    if ordinal>=448 {return Err("C578 Upper occurrence extent".into());}
    let bit=ordinal%224;
    if read.wire!=846_014*WIDTH+987_450+bit
        || read.author!=(OpenScoredReadAuthor::WorkUpper{owner:846_014,height:846_016})
        || physical.0!=NativeWorkEndpointAuthor::Tree {
        return Err("C578 Upper occurrence/domain/typed author".into());
    }
    if read.value!=physical.1 {return Err("C578 physical Upper/Score.sw value mismatch".into());}
    Ok(())
}
pub(super) fn c578_require_upper_census(occurrences:usize,unique:usize)->Result<(),String> {
    if occurrences!=448 || unique!=224 {
        return Err("C578 exact448 Upper occurrences/224 coordinates".into());
    }
    Ok(())
}

// The expected value is reconstructed by the existing join from a checked
// Boolean Cap import. The physical value is its ORIGINAL retained Fr.
pub(super) fn c576_check_physical_import(ordinal:usize,read:&OpenScoredRead,
    physical:(MaxReplayAuthor,Fr))->Result<(),String> {
    if read.value!=Fr::zero() && read.value!=Fr::one(){return Err("C576 expected import Fr is not Boolean".into());}
    if physical.1!=Fr::zero() && physical.1!=Fr::one(){return Err("C576 original physical import Fr is not Boolean".into());}
    if ordinal>=448 {return Err("C576 physical import extent".into());}
    let context=ordinal/224;let bit=ordinal%224;
    let expected=Writer::Max{context,end:844_928};
    if read.wire!=844_926*WIDTH+[999_424,1_000_097][context]+bit
        || read.author!=(OpenScoredReadAuthor::Max{context,end:844_928})
        || physical.0!=MaxReplayAuthor::Scheduled(expected) {
        return Err("C576 physical import global order/coordinate/typed author".into());
    }
    if physical.1!=read.value {return Err("C576 physical/Cap import value mismatch".into());}
    Ok(())
}

/// Work accounting for this local byte consumer, not a global memory/profile
/// admission. Native prefix/templates and per-owner Fr scratch remain separate.
pub(crate) struct C574Budget {
    limits: [usize; 4], used: [usize; 4],
}
impl C574Budget {
    pub(crate) fn new(owners: usize, bytes: usize, occurrences: usize,
        retained_bytes_and_authors: usize) -> Self {
        Self { limits: [owners, bytes, occurrences, retained_bytes_and_authors], used: [0; 4] }
    }
    pub(crate) fn charge(&mut self, owners: usize, bytes: usize, occurrences: usize,
        retained: usize) -> Result<(), String> {
        let next = [self.used[0].checked_add(owners), self.used[1].checked_add(bytes),
            self.used[2].checked_add(occurrences), Some(self.used[3].max(retained))];
        let mut staged = [0; 4];
        for i in 0..4 {
            staged[i] = next[i].ok_or("C574 work counter overflow/incomplete")?;
            if staged[i] > self.limits[i] { return Err(format!("C574 budget{i} exhausted/incomplete")); }
        }
        self.used = staged;
        Ok(())
    }
    pub(crate) fn usage(&self) -> [usize; 4] { self.used }
}

fn c574_author(owner: usize) -> Result<ScoreReplayAuthor, String> {
    let (previous_owner, max_owner) = match owner {
        845_887 => (845_759, 844_798), 846_015 => (845_887, 844_926),
        _ => return Err("C574 fixed Score author owner".into()),
    };
    Ok(ScoreReplayAuthor { context: 0, origin: owner + 1,
        previous_owner, max_owner, cap_owner: owner })
}

// Original Fr is checked before any conversion. Production arguments come
// exclusively from sealed native censuses and the same closed Score stream.
pub(super) fn c574_check_read(bit: usize, read: (usize, ScoreRelationReadAuthor, Fr),
    source: (usize, ScoreReplayAuthor, bool),
    destination: (usize, ScoreReplayAuthor, bool)) -> Result<(), String> {
    if read.2 != Fr::zero() && read.2 != Fr::one() {
        return Err("C574 non-Boolean retained Fr occurrence".into());
    }
    let layout = crate::origin_score::Layout::new();
    if bit >= layout.r.len() || layout.r.len() != 225 || layout.p.len() != 225 {
        return Err("C574 predecessor bit domain".into());
    }
    let source_wire = 845_887 * WIDTH + 677_501 + layout.r.start + bit;
    let destination_wire = 846_015 * WIDTH + 677_501 + layout.p.start + bit;
    if read.0 != source_wire || source.0 != source_wire || destination.0 != destination_wire
        || read.1 != (ScoreRelationReadAuthor::PreviousR { context: 0, owner: 845_887 })
        || source.1 != c574_author(845_887)? || destination.1 != c574_author(846_015)?
        || source.2 != destination.2 || read.2 != Fr::from(source.2 as u64) {
        return Err(format!("C574 ordered PreviousR occurrence{bit}/author/address/value"));
    }
    Ok(())
}

pub(super) fn c574_require_census(count: usize, extra: bool) -> Result<(), String> {
    if count != 225 || extra { Err("C574 incomplete/extra PreviousR occurrences".into()) }
    else { Ok(()) }
}

pub(super) struct C574RowCursor { owner: usize, offset: usize }
impl C574RowCursor {
    pub(super) fn new() -> Self { Self { owner: 0, offset: 0 } }
    pub(super) fn accept(&mut self, owner: usize, offset: usize, bytes: usize) -> Result<(), String> {
        let expected = [845_887, 846_015].get(self.owner).copied()
            .ok_or("C574 row cursor extra owner/chunk")?;
        if owner != expected || offset != self.offset || bytes != 8192 {
            return Err("C574 row cursor owner/order/chunk extent".into());
        }
        self.offset += bytes;
        if self.offset == WIDTH / 8 { self.offset = 0; self.owner += 1; }
        Ok(())
    }
    pub(super) fn complete(&self) -> Result<(), String> {
        if self.owner != 2 || self.offset != 0 { Err("C574 row cursor early EOF/incomplete".into()) }
        else { Ok(()) }
    }
}

pub(super) fn c574_replay_chunk(owner: usize, offset: usize, bytes: &[u8],
    authors: &[Option<crate::packed_owner_assembly::NativeRegularPhysicalAuthor>],
    replay: &[u8], replay_authors: &[Option<crate::packed_owner_assembly::NativeRegularPhysicalAuthor>])
    -> Result<(), String> {
    if !matches!(owner, 845_887 | 846_015) || offset % 8192 != 0
        || bytes.len() != 8192 || offset.checked_add(bytes.len())
            .is_none_or(|end| end > WIDTH / 8)
        || authors.len() != bytes.len() * 8 || authors.iter().any(Option::is_none)
        || bytes != replay || authors != replay_authors {
        return Err("C574 source replay byte/zero-inclusive author/order/extent".into());
    }
    Ok(())
}

#[cfg(test)]
#[path = "h21_honest_source_tests.rs"]
mod c574_tests;

fn check_scored_binding(expected: &HeaderSourceBinding,
    published: &HeaderSourceBinding, root: [u8; 32], total: [u8; 28],
    profile: [u8; 32], cut: &[u8], owner: usize,
    class: crate::daa_history_roster::OwnerClass) -> Result<(), String> {
    if published != expected || !expected.matches_sink(root, total, profile, cut, owner)
        || class != crate::daa_history_roster::OwnerClass::Carry {
        return Err("scored join root/total/profile/cut/layout/owner/class".into());
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OpenScoredReadAuthor {
    Map { context: usize, import: Import, bit: usize },
    PreviousR { context: usize, owner: usize },
    WorkUpper { owner: usize, height: usize },
    Max { context: usize, end: usize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct OpenScoredRead {
    pub wire: usize,
    pub author: OpenScoredReadAuthor,
    pub value: Fr,
}

/// No byte or finish method: ownership outside this local join is still open.
#[allow(dead_code)]
pub(crate) struct ScoredOwnerSourceJoin {
    binding: HeaderSourceBinding,
    map_bindings: [Binding; 2],
    stage: super::super::h21_eligible_slack::H21EligibleSlackStage,
    cap: ScoredOwnerCapPublication,
    row_source: Batch,
    selected_open_reads: Vec<OpenScoredRead>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScoredOwnerPackedAuthor {
    Map(usize),
    Score(ScoreReplayAuthor),
    Slack(usize),
    Cap { context: usize, origin: usize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScoredOwnerPackedCell {
    wire: usize,
    author: ScoredOwnerPackedAuthor,
    value: bool,
}

/// Checked membership and source identities for a regular Eligible08 Score
/// endpoint. This describes the scheduled owner class only; source values
/// still come exclusively from the closed Score/MAX and Cap producers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Eligible08RegularScoreOwner {
    owner: usize,
    ordinal: usize,
    active: [bool; 2],
    previous_r_owner: usize,
    max_owner: usize,
}

impl Eligible08RegularScoreOwner {
    pub(crate) fn classify(owner: usize) -> Result<Self, String> {
        const STRIDE: usize = 128;
        let descriptor = crate::bank53_map::CutDescriptor::eligible08();
        let first = descriptor.modern_start() + STRIDE - 1;
        let delta = owner.checked_sub(first)
            .ok_or("Eligible08 regular Score owner before class")?;
        if delta % STRIDE != 0 {
            return Err("Eligible08 regular Score owner residue".into());
        }
        let ordinal = delta / STRIDE;
        let origin = owner.checked_add(1)
            .ok_or("Eligible08 regular Score origin overflow")?;
        let active = std::array::from_fn(|context| origin <= descriptor.guards()[context]);
        if !active.contains(&true) || origin > descriptor.terminals()[0] {
            return Err("Eligible08 regular Score owner outside un-clipped endpoints".into());
        }
        // The guards themselves are a separate clipped Cap path, even if a
        // future schedule revision happens to place one on the residue.
        if descriptor.guards().iter().any(|guard| owner == guard - 1) {
            return Err("Eligible08 clipped guard is not a regular Score owner".into());
        }
        let previous_r_owner = if ordinal == 0 {
            descriptor.modern_start() - 1
        } else {
            owner.checked_sub(STRIDE)
                .ok_or("Eligible08 regular Score previous-R underflow")?
        };
        let max_owner = owner.checked_sub(descriptor.offset() + 1)
            .ok_or("Eligible08 regular Score MAX owner underflow")?;
        Ok(Self { owner, ordinal, active, previous_r_owner, max_owner })
    }

    pub(crate) fn owner(self) -> usize { self.owner }
    pub(crate) fn ordinal(self) -> usize { self.ordinal }
    pub(crate) fn active(self) -> [bool; 2] { self.active }
    pub(crate) fn previous_r_owner(self) -> usize { self.previous_r_owner }
    pub(crate) fn max_owner(self) -> usize { self.max_owner }
    pub(crate) fn typed_cell_count(self) -> usize {
        12_288 + 4_096 * self.active.iter().filter(|active| **active).count()
    }
}

impl ScoredOwnerPackedCell {
    pub(crate) fn wire(&self) -> usize { self.wire }
    pub(crate) fn author(&self) -> ScoredOwnerPackedAuthor { self.author }
    pub(crate) fn value(&self) -> bool { self.value }

    #[cfg(test)]
    pub(crate) fn synthetic_for_test(
        wire: usize, author: ScoredOwnerPackedAuthor, value: bool,
    ) -> Self { Self { wire, author, value } }
}

/// Regular Eligible08 Score owner source custody for a physical packed-byte write. The checked
/// ROW/source join remains owned here, and the selected foreign reads remain
/// visible. This cannot be converted into a complete owner slice or proof.
pub(crate) struct ScoredOwnerPackingView {
    source: ScoredOwnerSourceJoin,
    cells: Vec<ScoredOwnerPackedCell>,
    selected_open_reads: Vec<OpenScoredRead>,
    source_term_counts: [usize; 4],
    retained_header_daa_active_operands: usize,
}

/// Opaque borrowed access to the exact regular-845887 Score/Slack source
/// retained by a validated packing view. This is source custody only; it does
/// not establish physical authorship of a packed ROW cell.
pub(crate) struct C509RegularRowSourceView<'a> {
    packing: &'a ScoredOwnerPackingView,
    binding: HeaderSourceBinding,
}

impl C509RegularRowSourceView<'_> {
    fn validate(&self) -> Result<(), String> {
        const OWNER: usize = 845_887;
        self.packing.validate_for_packing(&self.binding, OWNER)?;
        let source = &self.packing.source;
        let schedule = Eligible08RegularScoreOwner::classify(OWNER)?;
        if source.binding != self.binding || source.owner() != OWNER
            || source.stage.map_stage.owner != OWNER
            || source.stage.map_stage.class != crate::daa_history_roster::OwnerClass::Carry
            || source.stage.map_stage.map_bindings != source.map_bindings
            || schedule.active() != [true, true] {
            return Err("C509 regular Score/Slack source binding/class/stage".into());
        }
        check_scored_binding(&self.binding, &source.binding,
            source.stage.map_stage.parent_root, source.stage.map_stage.parent_total,
            source.stage.map_stage.parent_profile, &source.stage.map_stage.cut_identity,
            source.stage.map_stage.owner, source.stage.map_stage.class)?;
        Ok(())
    }

    pub(crate) fn owner(&self) -> Result<usize, String> {
        self.validate()?;
        Ok(845_887)
    }

    pub(crate) fn binding(&self) -> Result<&HeaderSourceBinding, String> {
        self.validate()?;
        Ok(&self.packing.source.binding)
    }

    /// Ordered ordinary ROW occurrences retained from the same checked join.
    pub(crate) fn terms(
        &self,
    ) -> Result<impl Iterator<Item = (Relation, &Term)> + '_, String> {
        self.validate()?;
        Ok(self.packing.source.row_source.terms())
    }

    /// Ordered Map occurrences retained by the same checked Score/Slack stage.
    pub(crate) fn map_terms(&self, context: usize) -> Result<&[Term], String> {
        self.validate()?;
        self.packing.source.stage.map_stage.map_terms.get(context)
            .map(Vec::as_slice).ok_or_else(|| "C509 regular Map context".into())
    }

    pub(crate) fn score_terms(&self, context: usize) -> Result<&[Term], String> {
        self.validate()?;
        self.packing.source.stage.score_rows().get(context)
            .map(Vec::as_slice).ok_or_else(|| "C509 regular Score context".into())
    }

    pub(crate) fn slack_terms(&self, context: usize) -> Result<&[Term], String> {
        self.validate()?;
        self.packing.source.stage.slack_rows().get(context)
            .map(Vec::as_slice).ok_or_else(|| "C509 regular Slack context".into())
    }

    pub(crate) fn map_bindings(&self) -> Result<&[Binding; 2], String> {
        self.validate()?;
        Ok(&self.packing.source.map_bindings)
    }

    /// Typed candidate cells; these remain source claims, not packed-row proof.
    pub(crate) fn candidate_cells(&self) -> Result<&[ScoredOwnerPackedCell], String> {
        self.validate()?;
        Ok(&self.packing.cells)
    }

    /// Selected imports remain open reads from their original source families.
    pub(crate) fn selected_open_reads(&self) -> Result<&[OpenScoredRead], String> {
        self.validate()?;
        Ok(&self.packing.selected_open_reads)
    }
}

/// Counts from the retained installed partial, exposed only after full source
/// and projection replay. HEADER/DAA operands remain unresolved obligations.
pub(crate) struct C492InstalledSummary {
    pub(crate) owner: usize,
    pub(crate) terms: usize,
    pub(crate) row_leases: usize,
    pub(crate) assignments: usize,
    pub(crate) reservations: usize,
    pub(crate) score_reads: usize,
    pub(crate) selected_reads: usize,
    pub(crate) retained_header_daa_active_operands: usize,
}

/// The same checked source view and its owned incomplete writer projection.
/// There is no raw constructor, projection accessor, finish or byte export.
pub(crate) struct C492PartialWriterCarrier {
    view: ScoredOwnerPackingView,
    installed: source_bound_partial_writer::InstalledScoreSlack,
}

impl C492PartialWriterCarrier {
    pub(crate) fn checked_installed_summary(&self, expected: &HeaderSourceBinding,
        owner: usize,
    ) -> Result<C492InstalledSummary, String> {
        self.installed.checked_summary(&self.view, expected, owner)
    }
}

fn check_open_read_projection(
    source: &[OpenScoredRead],
    projected: &[OpenScoredRead],
) -> Result<(), String> {
    if source.is_empty() || source != projected {
        return Err("C396 packed source selected open-read projection".into());
    }
    Ok(())
}

fn check_scored_open_read_families(
    schedule: Eligible08RegularScoreOwner,
    reads: &[OpenScoredRead],
) -> Result<(), String> {
    let mut map_contexts = [false; 2];
    let mut r_contexts = [false; 2];
    let mut upper = false;
    let mut max_contexts = [false; 2];
    for read in reads {
        if read.value != Fr::zero() && read.value != Fr::one() {
            return Err("C396 packed source non-Boolean open-read value".into());
        }
        match read.author {
            OpenScoredReadAuthor::Map { context, .. } if context < 2 => map_contexts[context] = true,
            OpenScoredReadAuthor::PreviousR { context, owner: read_owner }
                if context < 2 && schedule.active()[context]
                    && read_owner == schedule.previous_r_owner() => r_contexts[context] = true,
            OpenScoredReadAuthor::WorkUpper { owner: read_owner, height }
                if read_owner + 1 == schedule.owner() && height == schedule.owner() + 1 => upper = true,
            OpenScoredReadAuthor::Max { context, end }
                if context < 2 && schedule.active()[context]
                    && end == schedule.max_owner() + 2 => max_contexts[context] = true,
            _ => return Err("C396 packed source open-read author/domain".into()),
        }
    }
    // For admitted regular owners, context 1's Map terminal and Score guard
    // are the same cut. Its local zero Map cells remain, but foreign reads end.
    let expected_contexts = schedule.active();
    if map_contexts != expected_contexts || r_contexts != expected_contexts
        || !upper || max_contexts != expected_contexts {
        return Err("C396 packed source incomplete selected open-read families".into());
    }
    Ok(())
}

fn scored_packing_cells(source: &ScoredOwnerSourceJoin)
    -> Result<Vec<ScoredOwnerPackedCell>, String> {
    const WIDTH: usize = 1 << 20;
    const CAP_BASE: [usize; 2] = [1_000_770, 1_002_818];
    let schedule = Eligible08RegularScoreOwner::classify(source.owner())?;
    let owner = schedule.owner();
    if source.binding.owner() != owner || source.stage.map_stage.owner != owner
        || source.stage.map_stage.class != crate::daa_history_roster::OwnerClass::Carry {
        return Err("C396 packed source regular ordinary Carry owner".into());
    }
    let material = source.cap.checked_material()?;
    if material.active != schedule.active()
        || material.cells.len() != 2_048 * schedule.active().iter().filter(|active| **active).count() {
        return Err("C396 packed source Eligible08 active-context Cap census".into());
    }
    let mut cells = Vec::with_capacity(schedule.typed_cell_count());
    let mut seen = BTreeSet::new();
    for context in 0..2 {
        for (range, expected) in [
            (H21EligibleMapStage::map_live(context)?, 0usize),
            (H21EligibleMapStage::score_live(context)?, 1),
            (H21EligibleMapStage::slack_live(context)?, 2),
        ] {
            if expected == 1 && !schedule.active()[context] { continue; }
            for local in range {
                let (author, value) = match expected {
                    0 => {
                        let (author, value) = source.stage.map_stage.claims.get(&local)
                            .ok_or("C396 packed source missing Map cell")?;
                        if *author != H21StageAuthor::Map(context) {
                            return Err("C396 packed source Map author".into());
                        }
                        (ScoredOwnerPackedAuthor::Map(context), *value)
                    }
                    1 if schedule.active()[context] => {
                        let (author, value) = source.stage.score_cells().get(&local)
                            .ok_or("C396 packed source missing Score cell")?;
                        if author.context != context || author.origin != owner + 1
                            || author.cap_owner != owner
                            || author.previous_owner != schedule.previous_r_owner()
                            || author.max_owner != schedule.max_owner()
                            || (*value != Fr::zero() && *value != Fr::one()) {
                            return Err("C396 packed source Score author/value".into());
                        }
                        (ScoredOwnerPackedAuthor::Score(*author), value.is_one())
                    }
                    1 => return Err("C396 packed source inactive Score context".into()),
                    _ => {
                        let (author, value) = source.stage.slack_cells().get(&local)
                            .ok_or("C396 packed source missing Slack cell")?;
                        if *author != H21StageAuthor::Slack(context) {
                            return Err("C396 packed source Slack author".into());
                        }
                        (ScoredOwnerPackedAuthor::Slack(context), *value)
                    }
                };
                let wire = owner.checked_mul(WIDTH).and_then(|base| base.checked_add(local))
                    .ok_or("C396 packed source Map/Score/Slack wire overflow")?;
                if wire / WIDTH != owner || !seen.insert(wire) {
                    return Err("C396 packed source duplicate/out-of-owner Bank53 wire".into());
                }
                cells.push(ScoredOwnerPackedCell { wire, author, value });
            }
        }
        if schedule.active()[context] {
            let expected_base = owner * WIDTH + CAP_BASE[context];
            let cap_offset = schedule.active()[..context].iter().filter(|active| **active).count() * 2_048;
            for bit in 0..2_048 {
                let (wire, found_context, value) = material.cells
                    .get(cap_offset + bit).copied()
                    .ok_or("C396 packed source missing ordered Cap cell")?;
                if found_context != context || wire != expected_base + bit
                    || !seen.insert(wire) {
                    return Err("C396 packed source Cap address/context/order".into());
                }
                cells.push(ScoredOwnerPackedCell { wire,
                    author: ScoredOwnerPackedAuthor::Cap { context, origin: owner + 1 }, value });
            }
        }
    }
    if cells.len() != schedule.typed_cell_count() || cells.iter().any(|cell|
        cell.wire / WIDTH != owner || cell.wire >= (1usize << 41)) {
        return Err("C396 packed source exact cell census/domain".into());
    }
    check_scored_open_read_families(schedule, source.selected_open_reads())?;
    let row_counts = source.source_term_counts()?;
    if row_counts[0] == 0 || row_counts[2] == 0
        || (schedule.active().iter().any(|active| *active) && row_counts[1] == 0)
        || (schedule.active().iter().any(|active| *active) && row_counts[3] == 0) {
        return Err("C396 packed source Map/Score/Slack/Cap ROW counts".into());
    }
    Ok(cells)
}

impl ScoredOwnerPackingView {
    pub(crate) fn from_checked_join(source: ScoredOwnerSourceJoin)
        -> Result<Self, String> {
        let cells = scored_packing_cells(&source)?;
        let selected_open_reads = source.selected_open_reads.clone();
        check_open_read_projection(source.selected_open_reads(), &selected_open_reads)?;
        let source_term_counts = source.source_term_counts()?;
        let retained_header_daa_active_operands =
            source.retained_header_daa_active_operand_count();
        Ok(Self { source, cells, selected_open_reads, source_term_counts,
            retained_header_daa_active_operands })
    }

    pub(crate) fn owner(&self) -> usize { self.source.owner() }
    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.source.binding }
    pub(crate) fn cells(&self) -> &[ScoredOwnerPackedCell] { &self.cells }
    pub(crate) fn selected_open_reads(&self) -> &[OpenScoredRead] {
        &self.selected_open_reads
    }

    /// Borrow the exact production source retained for regular owner 845887.
    /// No caller-supplied ROW, term list, or source summary can mint this view.
    pub(crate) fn c509_regular_row_source(
        &self, expected: &HeaderSourceBinding,
    ) -> Result<C509RegularRowSourceView<'_>, String> {
        const OWNER: usize = 845_887;
        self.validate_for_packing(expected, OWNER)?;
        let schedule = Eligible08RegularScoreOwner::classify(OWNER)?;
        let source = &self.source;
        if source.binding != *expected || source.owner() != OWNER
            || source.stage.map_stage.owner != OWNER
            || source.stage.map_stage.class != crate::daa_history_roster::OwnerClass::Carry
            || source.stage.map_stage.map_bindings != source.map_bindings
            || schedule.active() != [true, true] {
            return Err("C509 regular Score/Slack source binding/class/stage".into());
        }
        check_scored_binding(expected, &source.binding,
            source.stage.map_stage.parent_root, source.stage.map_stage.parent_total,
            source.stage.map_stage.parent_profile, &source.stage.map_stage.cut_identity,
            source.stage.map_stage.owner, source.stage.map_stage.class)?;
        Ok(C509RegularRowSourceView { packing: self, binding: expected.clone() })
    }

    pub(crate) fn source_term_counts(&self) -> [usize; 4] { self.source_term_counts }
    pub(crate) fn retained_header_daa_active_operand_count(&self) -> usize {
        self.retained_header_daa_active_operands
    }

    pub(crate) fn validate_for_packing(
        &self, expected: &HeaderSourceBinding, owner: usize,
    ) -> Result<(), String> {
        if Eligible08RegularScoreOwner::classify(owner).is_err()
            || self.owner() != owner || self.binding() != expected {
            return Err("C396 packed source parent/owner binding".into());
        }
        if self.cells != scored_packing_cells(&self.source)?
            || self.source_term_counts != self.source.source_term_counts()?
            || self.retained_header_daa_active_operands
                != self.source.retained_header_daa_active_operand_count() {
            return Err("C396 packed source retained custody projection".into());
        }
        check_open_read_projection(self.source.selected_open_reads(), &self.selected_open_reads)
    }

    /// Produce only a source-borrowed partial Score/V/W/Slack slice. The
    /// writer module keeps construction and admission private to this source
    /// boundary; this does not finish or serialize an owner.
    pub(super) fn stage_partial_score_slack<'a>(
        &'a self, expected: &HeaderSourceBinding,
    ) -> Result<source_bound_partial_writer::PartialScoreSlack<'a>, String> {
        source_bound_partial_writer::stage_partial(self, expected)
    }

    /// Consume the borrowed partial before moving this same view into custody.
    /// No source clone or status-only substitute can enter the carrier.
    pub(super) fn into_c492_partial_score_slack(self, expected: &HeaderSourceBinding)
        -> Result<C492PartialWriterCarrier, String> {
        let installed = {
            let partial = self.stage_partial_score_slack(expected)?;
            partial.into_installed()
        };
        Ok(C492PartialWriterCarrier { view: self, installed })
    }

    #[cfg(test)]
    pub(crate) fn admit_structural_fixture_for_test(
        stage: &super::super::h21_eligible_slack::H21EligibleSlackStage,
        expected: &HeaderSourceBinding,
        map_bindings: &[Binding; 2],
        packed_cells: &[ScoredOwnerPackedCell],
        selected_reads: &[OpenScoredRead],
        retained_header_daa_active_operands: usize,
    ) -> Result<source_bound_partial_writer::FixtureCoreSummary,
        source_bound_partial_writer::FixtureCoreError> {
        source_bound_partial_writer::admit_fixture_core_for_test(stage, expected, map_bindings,
            packed_cells, selected_reads, retained_header_daa_active_operands)
    }

    #[cfg(test)]
    pub(crate) fn is_expected_fixture_rejection_for_test(
        outcome: &Result<source_bound_partial_writer::FixtureCoreSummary,
            source_bound_partial_writer::FixtureCoreError>,
    ) -> bool {
        matches!(outcome, Err(source_bound_partial_writer::FixtureCoreError::Rejected(_)))
    }
}

#[cfg(test)]
mod c492_retained_lifetime_tests {
    use super::*;

    // Compile-only entry: take an actual checked view supplied by a caller.
    // This test neither forges one nor claims a native source-path execution.
    fn retain_checked_view(view: ScoredOwnerPackingView, expected: &HeaderSourceBinding)
        -> Result<C492PartialWriterCarrier, String> {
        view.into_c492_partial_score_slack(expected)
    }

    #[test]
    fn c492_consuming_partial_ends_borrow_before_retaining_same_view() {
        let _entry: fn(ScoredOwnerPackingView, &HeaderSourceBinding)
            -> Result<C492PartialWriterCarrier, String> = retain_checked_view;
        let _summary: fn(&C492PartialWriterCarrier, &HeaderSourceBinding, usize)
            -> Result<C492InstalledSummary, String> =
            C492PartialWriterCarrier::checked_installed_summary;
    }
}

impl ScoredOwnerSourceJoin {
    pub(crate) fn owner(&self) -> usize { self.binding.owner() }
    /// Map, predecessor R, WorkUpper and Cap MAX only. HEADER/DAA operands
    /// remain in `row_source`; this is not a complete foreign-read census.
    pub(crate) fn selected_open_reads(&self) -> &[OpenScoredRead] {
        &self.selected_open_reads
    }
    pub(crate) fn retained_header_daa_active_operand_count(&self) -> usize {
        self.row_source.active_operands().filter(|operand|
            matches!(operand.relation, Relation::Header | Relation::DaaLane(_))).count()
    }
    pub(crate) fn source_term_counts(&self) -> Result<[usize; 4], String> {
        Ok([self.stage.map_stage.map_terms.iter().map(Vec::len).sum(),
            self.stage.score_rows().iter().map(Vec::len).sum(),
            self.stage.slack_rows().iter().map(Vec::len).sum(),
            self.cap.checked_material()?.rows.len()])
    }
}

/// A pure checker is kept separate so each alias field can be falsified without
/// replaying a complete H21 stream. Production calls it only with opaque sources.
fn check_cap_score_alias(owner: usize, material: &ScoredOwnerCapMaterial,
    score_cells: &BTreeMap<usize, (ScoreReplayAuthor, Fr)>,
    reads: &[(usize, ScoreRelationReadAuthor, Fr)]) -> Result<[bool; 2], String> {
    let layout = crate::origin_score::Layout::new();
    let mut cursor = 0;
    let mut max_authors = [None; 2];
    for context in 0..2 {
        let score_base = H21EligibleMapStage::score_live(context)?.start;
        let cap_base = H21EligibleMapStage::cap_live(context)?.start;
        let active = material.active[context];
        let count = if active { SCORE_INPUT } else { 0 };
        let author = if active {
            let &(author, _) = score_cells.get(&score_base)
                .ok_or("scored join missing written Score zero")?;
            if author.context != context || author.cap_owner != owner
                || author.origin != owner + 1 || author.previous_owner >= owner
                || author.max_owner >= owner {
                return Err("scored join Score predecessor/MAX/Cap author".into());
            }
            Some(author)
        } else { None };
        max_authors[context] = author;
        for bit in 0..count {
            let &(found, value) = score_cells.get(&(score_base + bit))
                .ok_or("scored join missing written Score X")?;
            if Some(found) != author || !(value.is_zero() || value.is_one()) {
                return Err("scored join Score X author/value".into());
            }
        }
        if !active && H21EligibleMapStage::score_live(context)?
            .any(|local| score_cells.contains_key(&local)) {
            return Err("scored join inactive Score context".into());
        }
        let cap_cells: Vec<_> = material.cells.iter().filter(|(_, c, _)| *c == context).collect();
        if cap_cells.len() != if active { 2_048 } else { 0 }
            || material.q[context].len() != if active { 65 } else { 0 } {
            return Err("scored join Cap context/cell census".into());
        }
        for (bit, &&(wire, found_context, _)) in cap_cells.iter().enumerate() {
            if found_context != context || wire != owner * WIDTH + cap_base + bit {
                return Err("scored join Cap X address/context".into());
            }
        }
        if let Some(author) = author {
            for bit in 0..225 {
                let &(wire, source, value) = reads.get(cursor)
                    .ok_or("scored join missing predecessor R read")?;
                if wire != author.previous_owner * WIDTH + score_base + layout.r.start + bit
                    || source != (ScoreRelationReadAuthor::PreviousR {
                        context, owner: author.previous_owner })
                    || score_cells.get(&(score_base + layout.p.start + bit))
                        .map(|(_, found)| *found) != Some(value) {
                    return Err("scored join predecessor R address/author/value/order".into());
                }
                cursor += 1;
            }
            for bit in 0..65 {
                let expected_wire = owner * WIDTH + cap_base + 740 + bit;
                let &(q_wire, q_value) = &material.q[context][bit];
                let &(wire, source, value) = reads.get(cursor)
                    .ok_or("scored join missing Cap q read")?;
                if q_wire != expected_wire || wire != expected_wire
                    || source != (ScoreRelationReadAuthor::Cap {
                        context, origin: author.origin, max_owner: author.max_owner,
                        cap_owner: owner })
                    || cap_cells[740 + bit].2 != q_value
                    || value != Fr::from(q_value as u64)
                    || score_cells.get(&(score_base + layout.sv.start + bit))
                        .map(|(_, found)| *found) != Some(value) {
                    return Err("scored join Cap q address/author/wire/value/order".into());
                }
                cursor += 1;
            }
            for bit in 0..224 {
                let &(wire, source, value) = reads.get(cursor)
                    .ok_or("scored join missing WorkUpper read")?;
                if wire != (owner - 1) * WIDTH + 987_450 + bit
                    || source != (ScoreRelationReadAuthor::WorkUpper {
                        owner: owner - 1, height: owner + 1 })
                    || score_cells.get(&(score_base + layout.sw.start + bit))
                        .map(|(_, found)| *found) != Some(value) {
                    return Err("scored join WorkUpper address/author/value/order".into());
                }
                cursor += 1;
            }
        }
    }
    // Candidate publishes imports sorted by physical wire, not by context.
    // The two contexts can have different MAX owners and therefore reverse
    // their order while each context still carries bits 0..223 exactly once.
    let mut max_bits = [0usize; 2];
    let mut previous_wire = None;
    for &(wire, writer, _) in &material.imports {
        let Writer::Max { context, end } = writer else {
            return Err("scored join non-MAX Cap import".into());
        };
        let author = max_authors.get(context).copied().flatten()
            .ok_or("scored join inactive MAX import context")?;
        let bit = max_bits[context];
        if bit >= 224 || end != author.max_owner + 2
            || wire != author.max_owner * WIDTH + [999_424, 1_000_097][context] + bit
            || previous_wire.is_some_and(|previous| wire <= previous) {
            return Err("scored join Cap MAX address/author/global order".into());
        }
        max_bits[context] += 1;
        previous_wire = Some(wire);
    }
    if max_bits != std::array::from_fn(|context|
        if material.active[context] { 224 } else { 0 }) {
        return Err("scored join Cap MAX exact per-context count".into());
    }
    if !material.active.contains(&true) || cursor != reads.len()
        || score_cells.len() != material.active.iter().filter(|active| **active).count() * SCORE_INPUT {
        return Err("scored join active source/read multiplicity".into());
    }
    Ok(material.active)
}

/// Bind each imported MAX bit to the closed native owner source. The prior
/// alias checker establishes the exact import census and ordering; this gate
/// establishes that the imported value has the scheduled MAX author.
fn check_cap_max_import_sources(
    imports: &[(usize, Writer, bool)],
    sources: &BTreeMap<usize, Vec<(usize, MaxReplayAuthor, Fr)>>,
) -> Result<(), String> {
    for &(wire, writer, imported_value) in imports {
        let Writer::Max { context, end } = writer else {
            return Err("scored join non-MAX Cap import source".into());
        };
        if context >= 2 {
            return Err("scored join MAX import source context".into());
        }
        let owner = end.checked_sub(2).ok_or("scored join MAX source owner")?;
        let cells = sources.get(&owner).ok_or("scored join closed MAX source missing")?;
        let (source_wire, source_author, source_value) = cells.iter()
            .find(|(source_wire, _, _)| *source_wire == wire)
            .ok_or("scored join closed MAX source cell missing")?;
        if *source_wire != wire
            || *source_author != MaxReplayAuthor::Scheduled(writer)
            || *source_value != Fr::from(imported_value as u64) {
            return Err("scored join closed MAX source wire/author/value".into());
        }
    }
    Ok(())
}

/// Exact ordinary-consumer recipe seam, shared by the production join and
/// borrowed-relation tests. This checks regular membership and source/recipe
/// agreement only; the join retains all parent, value and source-custody checks.
pub(super) fn regular_score_equation_plan(owner: usize,
    relation: &H21ClosedScoreOwnerRelation<'_>) -> Result<ClassEquationPlan, String> {
    Eligible08RegularScoreOwner::classify(owner)?;
    relation.source_equation_plan(owner)
}

impl H21EligibleContext<'_> {
    /// Both physical sources remain borrowed while the one established join
    /// constructs and validates its own imports. No caller recipe is accepted.
    pub(crate) fn join_scored_owner_source_with_physical_max_and_upper(&self,owner:usize,
        relation:H21ClosedScoreOwnerRelation<'_>,closed_max:&MaxStream<'_>,
        physical_max:&crate::packed_owner_assembly::NativeScheduledMaxRow<'_, '_, '_>,
        max_budget:&mut C576MaxBudget,
        upper:&crate::packed_owner_assembly::NativeWorkEndpointAuthorLease<'_>,
        work_budget:&mut C578WorkBudget)->Result<ScoredOwnerSourceJoin,String> {
        upper.require_live_source(&self.producer)?;
        physical_max.require_live_source(&self.producer,closed_max)?;
        if owner!=846_015 || upper.binding().owner()!=846_014 {
            return Err("C578 physical Upper requires donor846014/Score846015".into());
        }
        work_budget.charge(0,448,0)?;
        upper.check_complete()?;
        let joined=self.join_scored_owner_source_with_physical_max(
            owner,relation,closed_max,physical_max,max_budget)?;
        let mut ordinal=0usize;
        let mut seen=[false;224];let mut unique=0usize;
        for read in joined.selected_open_reads.iter().filter(|read|
            matches!(read.author,OpenScoredReadAuthor::WorkUpper{..})) {
            c578_check_upper_import(ordinal,read,upper.checked_upper_fr(read.wire)?)?;
            let bit=ordinal%224;
            if !seen[bit] {seen[bit]=true;unique+=1;}
            ordinal=ordinal.checked_add(1).ok_or("C578 Upper occurrence counter overflow")?;
        }
        c578_require_upper_census(ordinal,unique)?;
        Ok(joined)
    }
    /// Constructor-scoped physical edge for the first new honest consumer.
    /// Old join remains compatible; this variant accepts no caller read list.
    pub(crate) fn join_scored_owner_source_with_physical_max(&self,owner:usize,
        relation:H21ClosedScoreOwnerRelation<'_>,closed_max:&MaxStream<'_>,
        physical:&crate::packed_owner_assembly::NativeScheduledMaxRow<'_, '_, '_>,
        budget:&mut C576MaxBudget)->Result<ScoredOwnerSourceJoin,String> {
        // Exact live references are checked BEFORE completion or any values.
        physical.require_live_source(&self.producer,closed_max)?;
        if owner!=846_015 || physical.binding().owner()!=844_926 {
            return Err("C576 physical Cap edge requires owner846015/MAX844926".into());
        }
        budget.charge(0,448,0)?;
        physical.check_complete()?;
        let source=self.join_scored_owner_source(owner,relation,closed_max)?;
        let mut ordinal=0usize;
        for read in source.selected_open_reads.iter().filter(|read|matches!(read.author,OpenScoredReadAuthor::Max{..})) {
            c576_check_physical_import(ordinal,read,physical.checked_max_cell_fr(read.wire)?)?;
            ordinal=ordinal.checked_add(1).ok_or("C576 physical import counter overflow")?;
        }
        if ordinal!=448 {return Err("C576 physical Cap import exact448 census".into());}
        Ok(source)
    }

    /// The closed Score and MAX streams remain the only production constructors.
    /// Typed Map/R/Work/MAX and HEADER/DAA reads are retained as obligations.
    pub(crate) fn join_scored_owner_source(
        &self, owner: usize, relation: H21ClosedScoreOwnerRelation<'_>,
        closed_max: &MaxStream<'_>,
    ) -> Result<ScoredOwnerSourceJoin, String> {
        let schedule = Eligible08RegularScoreOwner::classify(owner)?;
        let equations = regular_score_equation_plan(owner, &relation)?;
        let plan = self.producer.plan;
        let prefix = self.producer.input;
        let snapshot = closed_max.closed_native_snapshot(plan, prefix)?;
        let binding = HeaderSourceBinding::for_plan(plan, owner)?;
        let cap = Admission::new(plan, prefix, snapshot)?
            .scored_owner_cap_publication(owner)?;
        let stage = self.stage_with_score_slack(owner, relation)?;
        let map_bindings = [self.maps[0].binding(), self.maps[1].binding()];
        if map_bindings != stage.map_stage.map_bindings {
            return Err("scored join exact generated Map bindings".into());
        }
        let score_active = std::array::from_fn(|context| {
            H21EligibleMapStage::score_live(context).is_ok_and(|range|
                stage.score_cells().contains_key(&range.start))
        });
        if score_active != schedule.active() {
            return Err("scored join Eligible08 schedule/Score active-context mask".into());
        }
        check_scored_binding(&binding, cap.binding(), stage.map_stage.parent_root,
            stage.map_stage.parent_total, stage.map_stage.parent_profile,
            &stage.map_stage.cut_identity, stage.map_stage.owner, stage.map_stage.class)?;
        let material = cap.checked_material()?;
        if material.active != schedule.active() {
            return Err("scored join Eligible08 schedule/Cap active-context mask".into());
        }
        check_cap_score_alias(owner, &material, stage.score_cells(), stage.score_imports())?;
        let mut max_sources = BTreeMap::new();
        for &(_, writer, _) in &material.imports {
            let Writer::Max { end, .. } = writer else {
                return Err("scored join non-MAX Cap import source".into());
            };
            let max_owner = end.checked_sub(2).ok_or("scored join MAX source owner")?;
            if !max_sources.contains_key(&max_owner) {
                max_sources.insert(max_owner, closed_max.closed_owner_cells(max_owner)?);
            }
        }
        check_cap_max_import_sources(&material.imports, &max_sources)?;
        let row_source = RowPlan::new(&self.producer.roster, snapshot.scheduled_plan())?
            .stage_owner(owner)?;
        row_source.require_owner_parent(plan, owner)?;
        for context in 0..2 {
            let published: Vec<_> = material.rows.iter()
                .filter(|(c, _)| *c == Some(context)).map(|(_, term)| term).collect();
            let placed: Vec<_> = row_source.terms().filter_map(|(relation, term)|
                if relation == Relation::Scheduled(Writer::Cap { context, origin: owner + 1 })
                    { Some(term) } else { None }).collect();
            if placed != published { return Err("scored join Cap ROW order/multiplicity".into()); }
        }
        let mut reserved = BTreeSet::new();
        for terms in stage.map_stage.map_terms.iter().chain(stage.score_rows())
            .chain(stage.slack_rows()) {
            reserved.extend(terms.iter().map(|term| term.row));
        }
        if material.rows.iter().filter(|(c, _)| c.is_some())
            .any(|(_, term)| reserved.contains(&term.row)) {
            return Err("scored join Cap/Map/Score/Slack ROW collision".into());
        }
        for &(wire, _, _) in &material.cells {
            let local = wire % WIDTH;
            if stage.map_stage.claims.contains_key(&local)
                || stage.score_cells().contains_key(&local)
                || stage.slack_cells().contains_key(&local) {
                return Err("scored join Cap/Map/Score/Slack X collision".into());
            }
        }
        let mut selected_open_reads = Vec::new();
        for (context, map) in self.maps.iter().enumerate() {
            let mut map_reads = Vec::new();
            for import in map.imports(owner as u64)? {
                for bit in 0..import.width {
                    let wire = map.input_index(import, bit)?;
                    map_reads.push(wire);
                    selected_open_reads.push(OpenScoredRead { wire,
                        author: OpenScoredReadAuthor::Map { context, import, bit },
                        value: Fr::from(self.producer.exports.bit(wire)? as u64) });
                }
            }
            if map_reads != equations.map_difficulty_reads(context)? {
                return Err(format!("Score class Map source imports owner {owner} context {context}"));
            }
        }
        for &(wire, source, value) in stage.score_imports() {
            let author = match source {
                ScoreRelationReadAuthor::PreviousR { context, owner } =>
                    OpenScoredReadAuthor::PreviousR { context, owner },
                ScoreRelationReadAuthor::WorkUpper { owner, height } =>
                    OpenScoredReadAuthor::WorkUpper { owner, height },
                ScoreRelationReadAuthor::Cap { .. } => continue,
            };
            selected_open_reads.push(OpenScoredRead { wire, author, value });
        }
        for &(wire, writer, value) in &material.imports {
            let Writer::Max { context, end } = writer else {
                return Err("scored join non-MAX Cap import".into());
            };
            selected_open_reads.push(OpenScoredRead { wire,
                author: OpenScoredReadAuthor::Max { context, end },
                value: Fr::from(value as u64) });
        }
        Ok(ScoredOwnerSourceJoin { binding, map_bindings, stage, cap, row_source,
            selected_open_reads })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const OWNER: usize = 845_887;
    const PREVIOUS: usize = 845_759;
    const MAX: usize = 844_798;

    fn alias_fixture() -> (ScoredOwnerCapMaterial,
        BTreeMap<usize, (ScoreReplayAuthor, Fr)>,
        Vec<(usize, ScoreRelationReadAuthor, Fr)>) {
        let mut cap = ScoredOwnerCapMaterial { rows: Vec::new(), cells: Vec::new(),
            q: std::array::from_fn(|_| Vec::new()), imports: Vec::new(), active: [true; 2] };
        let mut cells = BTreeMap::new();
        let mut reads = Vec::new();
        let layout = crate::origin_score::Layout::new();
        for context in 0..2 {
            let score_base = H21EligibleMapStage::score_live(context).unwrap().start;
            let cap_base = H21EligibleMapStage::cap_live(context).unwrap().start;
            let author = ScoreReplayAuthor { context, origin: OWNER + 1,
                previous_owner: PREVIOUS, max_owner: MAX, cap_owner: OWNER };
            for bit in 0..SCORE_INPUT {
                cells.insert(score_base + bit, (author, Fr::zero()));
            }
            for bit in 0..2_048 {
                let wire = OWNER * WIDTH + cap_base + bit;
                cap.cells.push((wire, context, false));
                if (740..805).contains(&bit) { cap.q[context].push((wire, false)); }
            }
            for bit in 0..225 {
                reads.push((PREVIOUS * WIDTH + score_base + layout.r.start + bit,
                    ScoreRelationReadAuthor::PreviousR { context, owner: PREVIOUS }, Fr::zero()));
            }
            for bit in 0..65 {
                reads.push((OWNER * WIDTH + cap_base + 740 + bit,
                    ScoreRelationReadAuthor::Cap { context, origin: OWNER + 1,
                        max_owner: MAX, cap_owner: OWNER }, Fr::zero()));
            }
            for bit in 0..224 {
                reads.push(((OWNER - 1) * WIDTH + 987_450 + bit,
                    ScoreRelationReadAuthor::WorkUpper { owner: OWNER - 1,
                        height: OWNER + 1 }, Fr::zero()));
                cap.imports.push((MAX * WIDTH + [999_424, 1_000_097][context] + bit,
                    Writer::Max { context, end: MAX + 2 }, false));
            }
        }
        (cap, cells, reads)
    }

    fn max_import_source_fixture(
        imports: &[(usize, Writer, bool)],
    ) -> BTreeMap<usize, Vec<(usize, MaxReplayAuthor, Fr)>> {
        let mut sources = BTreeMap::new();
        for &(wire, writer, _) in imports {
            let Writer::Max { end, .. } = writer else { panic!("MAX import fixture") };
            sources.entry(end - 2).or_insert_with(Vec::new)
                .push((wire, MaxReplayAuthor::Scheduled(writer), Fr::zero()));
        }
        sources
    }

    #[test]
    fn c392_closed_max_import_source_rejects_value_missing_and_foreign_source() {
        let (cap, _, _) = alias_fixture();
        let sources = max_import_source_fixture(&cap.imports);
        assert!(check_cap_max_import_sources(&cap.imports, &sources).is_ok());

        let mut value_mutant = cap.imports.clone();
        value_mutant[0].2 = true;
        assert!(check_cap_max_import_sources(&value_mutant, &sources).is_err());

        let mut missing = sources.clone();
        let (wire, writer, _) = cap.imports[0];
        let Writer::Max { end, .. } = writer else { unreachable!() };
        missing.get_mut(&(end - 2)).unwrap().retain(|(source_wire, _, _)| *source_wire != wire);
        assert!(check_cap_max_import_sources(&cap.imports, &missing).is_err());

        let mut foreign = sources;
        let source = foreign.get_mut(&(end - 2)).unwrap().iter_mut()
            .find(|(source_wire, _, _)| *source_wire == wire).unwrap();
        source.1 = MaxReplayAuthor::NativeWorkD { height: end };
        assert!(check_cap_max_import_sources(&cap.imports, &foreign).is_err());
    }

    #[test]
    fn c390_owner845887_cap_score_local_alias_and_isolated_faults() {
        let (cap, cells, reads) = alias_fixture();
        let first = cells[&H21EligibleMapStage::score_live(0).unwrap().start].0;
        assert_eq!((first.previous_owner, first.max_owner), (PREVIOUS, MAX));
        assert_eq!(check_cap_score_alias(OWNER, &cap, &cells, &reads).unwrap(), [true; 2]);

        let (mut cap, cells, reads) = alias_fixture();
        cap.q[0][0].1 = true;
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (mut cap, cells, reads) = alias_fixture();
        cap.q[0].swap(0, 1);
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (mut cap, cells, reads) = alias_fixture();
        cap.cells.remove(740);
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (mut cap, cells, reads) = alias_fixture();
        cap.cells.push(cap.cells[0]);
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (mut cap, cells, reads) = alias_fixture();
        cap.active[1] = false;
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (mut cap, cells, reads) = alias_fixture();
        cap.imports.swap(0, 1);
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (mut cap, cells, reads) = alias_fixture();
        cap.imports[0].1 = Writer::Max { context: 1, end: MAX + 2 };
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (cap, mut cells, reads) = alias_fixture();
        cells.remove(&H21EligibleMapStage::score_live(0).unwrap().start);
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (cap, mut cells, reads) = alias_fixture();
        let local = H21EligibleMapStage::score_live(0).unwrap().start
            + crate::origin_score::Layout::new().sv.start;
        cells.get_mut(&local).unwrap().1 = Fr::one();
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (cap, mut cells, reads) = alias_fixture();
        for (_, (author, _)) in cells.iter_mut() {
            author.previous_owner = PREVIOUS + 1;
        }
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (cap, cells, mut reads) = alias_fixture();
        reads.swap(0, 1);
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (cap, cells, mut reads) = alias_fixture();
        reads[225].1 = ScoreRelationReadAuthor::Cap { context: 1,
            origin: OWNER + 1, max_owner: MAX, cap_owner: OWNER };
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        let (cap, cells, mut reads) = alias_fixture();
        reads[290].1 = ScoreRelationReadAuthor::WorkUpper { owner: OWNER - 2,
            height: OWNER + 1 };
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
    }

    #[test]
    fn c390_max_imports_follow_global_wire_order_with_distinct_context_owners() {
        let (mut cap, mut cells, mut reads) = alias_fixture();
        let later_max = 844_926;
        let first_domain = H21EligibleMapStage::score_live(0).unwrap();
        for (local, (author, _)) in cells.iter_mut() {
            if first_domain.contains(local) { author.max_owner = later_max; }
        }
        for (_, source, _) in &mut reads {
            if matches!(source, ScoreRelationReadAuthor::Cap { context: 0, .. }) {
                *source = ScoreRelationReadAuthor::Cap { context: 0, origin: OWNER + 1,
                    max_owner: later_max, cap_owner: OWNER };
            }
        }
        for (wire, writer, _) in &mut cap.imports {
            if matches!(writer, Writer::Max { context: 0, .. }) {
                let bit = *wire - (MAX * WIDTH + 999_424);
                *wire = later_max * WIDTH + 999_424 + bit;
                *writer = Writer::Max { context: 0, end: later_max + 2 };
            }
        }
        cap.imports.sort_by_key(|(wire, _, _)| *wire);
        assert!(matches!(cap.imports[0].1, Writer::Max { context: 1, .. }));
        assert_eq!(check_cap_score_alias(OWNER, &cap, &cells, &reads).unwrap(), [true; 2]);

        cap.imports.swap(0, 1);
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        cap.imports.swap(0, 1);
        cap.imports[0].1 = Writer::Max { context: 0, end: later_max + 2 };
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
        cap.imports[0].1 = Writer::Max { context: 1, end: MAX + 2 };
        cap.imports[1].0 = cap.imports[0].0;
        assert!(check_cap_score_alias(OWNER, &cap, &cells, &reads).is_err());
    }

    #[test]
    fn c390_binding_rejects_every_identity_field_and_class() {
        let root = [7; 32];
        let total = [8; 28];
        let profile = [9; 32];
        let cut = vec![10];
        let binding = HeaderSourceBinding::from_sink_for_test(root, total, profile,
            cut.clone(), OWNER);
        let carry = crate::daa_history_roster::OwnerClass::Carry;
        assert!(check_scored_binding(&binding, &binding, root, total, profile,
            &cut, OWNER, carry).is_ok());
        for field in 0..6 {
            assert!(check_scored_binding(&binding,
                &binding.mutated_field_for_test(field), root, total, profile,
                &cut, OWNER, carry).is_err(), "field {field}");
        }
        assert!(check_scored_binding(&binding, &binding, root, total, profile,
            &cut, OWNER, crate::daa_history_roster::OwnerClass::Singleton).is_err());
    }

    #[test]
    fn c445_regular_score_cut_aware_read_families_no_frame() {
        let import = Import { owner: 0, local: 0, width: 1,
            kind: crate::legacy_envelope_map::Kind::Difficulty };
        let make_reads = |owner| {
            let schedule = Eligible08RegularScoreOwner::classify(owner).unwrap();
            let mut reads = Vec::new();
            for context in 0..2 {
                if !schedule.active()[context] { continue; }
                for author in [
                    OpenScoredReadAuthor::Map { context, import, bit: 0 },
                    OpenScoredReadAuthor::PreviousR { context,
                        owner: schedule.previous_r_owner() },
                    OpenScoredReadAuthor::Max { context,
                        end: schedule.max_owner() + 2 },
                ] {
                    reads.push(OpenScoredRead { wire: 0, author, value: Fr::zero() });
                }
            }
            reads.push(OpenScoredRead { wire: 0,
                author: OpenScoredReadAuthor::WorkUpper {
                    owner: owner - 1, height: owner + 1 }, value: Fr::zero() });
            reads
        };
        let first = Eligible08RegularScoreOwner::classify(846_015).unwrap();
        let first_reads = make_reads(first.owner());
        assert!(check_scored_open_read_families(first, &first_reads).is_ok());
        let tail = Eligible08RegularScoreOwner::classify(1_810_879).unwrap();
        let tail_reads = make_reads(tail.owner());
        assert_eq!(tail.active(), [true, false]);
        assert!(check_scored_open_read_families(tail, &tail_reads).is_ok());

        let mut missing_active_map = tail_reads.clone();
        missing_active_map.retain(|read| !matches!(read.author,
            OpenScoredReadAuthor::Map { context: 0, .. }));
        assert!(check_scored_open_read_families(tail, &missing_active_map).is_err());
        let mut extra_inactive_map = tail_reads.clone();
        extra_inactive_map.push(OpenScoredRead { wire: 0,
            author: OpenScoredReadAuthor::Map { context: 1, import, bit: 0 },
            value: Fr::zero() });
        assert!(check_scored_open_read_families(tail, &extra_inactive_map).is_err());
        let mut missing_first_map = first_reads.clone();
        missing_first_map.retain(|read| !matches!(read.author,
            OpenScoredReadAuthor::Map { context: 1, .. }));
        assert!(check_scored_open_read_families(first, &missing_first_map).is_err());
        let mut missing_r = tail_reads.clone();
        missing_r.retain(|read| !matches!(read.author,
            OpenScoredReadAuthor::PreviousR { .. }));
        assert!(check_scored_open_read_families(tail, &missing_r).is_err());
        let mut missing_max = tail_reads.clone();
        missing_max.retain(|read| !matches!(read.author,
            OpenScoredReadAuthor::Max { .. }));
        assert!(check_scored_open_read_families(tail, &missing_max).is_err());
        let mut missing_upper = tail_reads.clone();
        missing_upper.retain(|read| !matches!(read.author,
            OpenScoredReadAuthor::WorkUpper { .. }));
        assert!(check_scored_open_read_families(tail, &missing_upper).is_err());
        let mut wrong_map_context = tail_reads.clone();
        wrong_map_context[0].author = OpenScoredReadAuthor::Map { context: 2, import, bit: 0 };
        assert!(check_scored_open_read_families(tail, &wrong_map_context).is_err());
        let mut wrong_r_owner = tail_reads.clone();
        wrong_r_owner[1].author = OpenScoredReadAuthor::PreviousR { context: 0,
            owner: tail.previous_r_owner() - 1 };
        assert!(check_scored_open_read_families(tail, &wrong_r_owner).is_err());
        let mut wrong_max_end = tail_reads.clone();
        wrong_max_end[2].author = OpenScoredReadAuthor::Max { context: 0,
            end: tail.max_owner() + 3 };
        assert!(check_scored_open_read_families(tail, &wrong_max_end).is_err());
        let mut non_boolean = tail_reads.clone();
        non_boolean[0].value = Fr::from(2u64);
        assert!(check_scored_open_read_families(tail, &non_boolean).is_err());
        println!("C445_NOFRAME_CUT_AWARE_READ_FAMILIES_PASS owners=846015,1810879 tail_map_contexts=0 missing_active_rejected=true extra_inactive_rejected=true invalid_authors_rejected=true");
    }

    #[test]
    fn c396_selected_open_reads_cannot_be_omitted_or_retagged() {
        let read = OpenScoredRead { wire: PREVIOUS * WIDTH + 11,
            author: OpenScoredReadAuthor::PreviousR { context: 0, owner: PREVIOUS },
            value: Fr::zero() };
        assert!(check_open_read_projection(&[read], &[read]).is_ok());
        assert!(check_open_read_projection(&[read], &[]).is_err());
        let retagged = OpenScoredRead { author: OpenScoredReadAuthor::WorkUpper {
            owner: OWNER - 1, height: OWNER }, ..read };
        assert!(check_open_read_projection(&[read], &[retagged]).is_err());
    }
}

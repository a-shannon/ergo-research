//! Source-borrowed, structurally partial Score/V/W/Slack projection.
//!
//! This module deliberately has no row completion or byte-export operation.
//! The shared core consumes borrowed source-shaped records; only the enclosing
//! `ScoredOwnerPackingView` adapter can supply production custody.

use super::{OpenScoredRead, OpenScoredReadAuthor, ScoredOwnerPackedAuthor, ScoredOwnerPackedCell,
    ScoredOwnerPackingView};
use crate::packed_owner_assembly::{HeaderSourceBinding, H21EligibleMapStage,
    H21StageAuthor, h21_eligible_slack::H21EligibleSlackStage};
use crate::packed_owner_assembly::h21_eligible_context::{Eligible08RegularScoreOwner,
    ScoreRelationReadAuthor, ScoreReplayAuthor};
use crate::legacy_envelope_map::Binding;
use crate::sparse::Term;
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

const WIDTH: usize = 1 << 20;
const ROW_WIDTH: usize = 1 << 19;
const SCORE_X: [usize; 2] = [677_501, 685_693];
const CAP_X: [usize; 2] = [1_000_770, 1_002_818];
const SCORE_ROW: [usize; 2] = [487_421, 502_652];
const V_ROW: [usize; 2] = [491_629, 506_860];
const W_ROW: [usize; 2] = [491_694, 506_925];
const SLACK_ROW: [usize; 2] = [491_918, 507_149];
const SCORE_ROW_EXTENT: usize = 4_208;
const SCORE_TERM_COUNT: usize = 8_032;
const SCORE_ROW_COUNT: usize = 3_082;
const V_BITS: usize = 65;
const W_BITS: usize = 224;
const SLACK_BITS: usize = 387;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Family { Score, V, W, Slack }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowWriter { Map(usize), Partial(Family, usize) }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowAuthor { Score(ScoreReplayAuthor), Slack(usize) }

#[derive(Clone, Debug, PartialEq, Eq)]
struct TypedTerm { family: Family, context: usize, term: Term }

#[derive(Clone, Debug, PartialEq, Eq)]
struct RowLease { row: usize, family: Family, context: usize, author: RowAuthor }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum XAuthor { Score(ScoreReplayAuthor), Slack(usize) }

#[derive(Clone, Debug, PartialEq, Eq)]
struct XKey { address: usize, context: usize, family: Family, author: XAuthor }

#[derive(Clone, Debug, PartialEq, Eq)]
struct XAssignment { key: XKey, value: bool }

#[derive(Clone, Debug, PartialEq, Eq)]
struct Identity {
    header: HeaderSourceBinding,
    owner: usize,
    active: [bool; 2],
    maps: [Binding; 2],
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Projection {
    identity: Identity,
    terms: Vec<TypedTerm>,
    row_leases: Vec<RowLease>,
    assignments: Vec<XAssignment>,
    reservations: Vec<XKey>,
    score_reads: Vec<(usize, ScoreRelationReadAuthor, Fr)>,
    selected_reads: Vec<OpenScoredRead>,
    retained_header_daa_active_operands: usize,
}

/// Opaque production result. The borrow pins the original checked packing
/// view for its entire lifetime; the contents remain an incomplete row slice.
#[allow(dead_code)]
pub(in crate::packed_owner_assembly::h21_eligible_context) struct PartialScoreSlack<'a> {
    projection: Projection,
    _source: PhantomData<&'a ScoredOwnerPackingView>,
}

/// Owned incomplete writer slice. Only the checked-view adapter can retain it;
/// construction consumes the borrowed result without copying its projection.
pub(super) struct InstalledScoreSlack {
    projection: Projection,
}

impl PartialScoreSlack<'_> {
    pub(super) fn into_installed(self) -> InstalledScoreSlack {
        InstalledScoreSlack { projection: self.projection }
    }
}

impl InstalledScoreSlack {
    pub(super) fn checked_summary(&self, view: &ScoredOwnerPackingView,
        expected: &HeaderSourceBinding, owner: usize,
    ) -> Result<super::C492InstalledSummary, String> {
        view.validate_for_packing(expected, owner)?;
        let input = production_input(view, expected)?;
        self.summary_after_replay(&input)
    }

    fn summary_after_replay(&self, input: &BorrowedInput<'_>)
        -> Result<super::C492InstalledSummary, String> {
        replay_projection(input, &self.projection)?;
        let installed = &self.projection;
        Ok(super::C492InstalledSummary { owner: installed.identity.owner,
            terms: installed.terms.len(), row_leases: installed.row_leases.len(),
            assignments: installed.assignments.len(), reservations: installed.reservations.len(),
            score_reads: installed.score_reads.len(), selected_reads: installed.selected_reads.len(),
            retained_header_daa_active_operands: installed.retained_header_daa_active_operands })
    }
}

#[derive(Clone, Default, PartialEq, Eq)]
struct StructuralDestination { installed: Option<Projection> }

struct BorrowedInput<'a> {
    expected: &'a HeaderSourceBinding,
    published: &'a HeaderSourceBinding,
    expected_maps: &'a [Binding; 2],
    map_stage: &'a H21EligibleMapStage,
    stage: &'a H21EligibleSlackStage,
    packed_cells: &'a [ScoredOwnerPackedCell],
    selected_reads: &'a [OpenScoredRead],
    retained_header_daa_active_operands: usize,
}

fn checked_owner_base(owner: usize, width: usize, limit: usize) -> Result<usize, String> {
    if owner >= limit { return Err("C492 owner outside checked domain".into()); }
    owner.checked_mul(width).ok_or_else(|| "C492 owner base overflow".into())
}

fn check_identity(input: &BorrowedInput<'_>) -> Result<Identity, String> {
    let map = input.map_stage;
    let owner = map.owner;
    let schedule = Eligible08RegularScoreOwner::classify(owner)?;
    let descriptor = H21EligibleMapStage::descriptor();
    if schedule.owner() != owner || map.class != crate::daa_history_roster::OwnerClass::Carry
        || map.cut_identity != descriptor.canonical_identity()
        || input.published != input.expected
        || map.map_bindings != *input.expected_maps
        || !input.expected.matches_sink(map.parent_root, map.parent_total,
            map.parent_profile, &map.cut_identity, owner)
        || input.expected.owner() != owner
    {
        return Err("C492 source identity parent/class/cut/layout/owner".into());
    }
    let base = checked_owner_base(owner, WIDTH, 1 << 21)?;
    let row_base = checked_owner_base(owner, ROW_WIDTH, 1 << 21)?;
    let terminals = descriptor.terminals();
    for context in 0..2 {
        let binding = &map.map_bindings[context];
        if binding.n != terminals[context] as u64 || binding.h != 21
            || binding.parent_root.is_some()
            || map.map_reservations[context] != H21EligibleMapStage::map_live(context)?
        {
            return Err("C492 exact generated Map binding/reservation".into());
        }
    }
    if base >= 1 << 41 || row_base >= 1 << 40 {
        return Err("C492 physical address domain".into());
    }
    Ok(Identity { header: (*input.expected).clone(), owner,
        active: schedule.active(), maps: (*input.expected_maps).clone() })
}

fn classify_score_terms(owner: usize, context: usize, terms: &[Term],
    author: ScoreReplayAuthor, out: &mut Vec<TypedTerm>,
    leases: &mut BTreeMap<usize, RowLease>) -> Result<(), String> {
    let row_base = checked_owner_base(owner, ROW_WIDTH, 1 << 21)?;
    let mut counts = [0usize; 3];
    let mut rows: [BTreeSet<usize>; 3] = std::array::from_fn(|_| BTreeSet::new());
    let mut families = Vec::with_capacity(terms.len());
    for term in terms {
        if term.row >= 1usize << 40 || term.gate.left >= 1usize << 41
            || term.gate.right >= 1usize << 41 {
            return Err("C492 Score term outside checked ROW/X domains".into());
        }
        let local = term.row.checked_sub(row_base).ok_or("C492 Score ROW owner underflow")?;
        let (family, band) = if (SCORE_ROW[context]..SCORE_ROW[context] + SCORE_ROW_EXTENT).contains(&local) {
            (Family::Score, 0)
        } else if (V_ROW[context]..V_ROW[context] + V_BITS).contains(&local) {
            (Family::V, 1)
        } else if (W_ROW[context]..W_ROW[context] + W_BITS).contains(&local) {
            (Family::W, 2)
        } else { return Err("C492 Score/V/W ROW outside source bands".into()); };
        counts[band] += 1;
        rows[band].insert(local);
        families.push((family, local));
    }
    if counts != [SCORE_TERM_COUNT, V_BITS, W_BITS * 2]
        || rows[0].len() != SCORE_ROW_COUNT || rows[1].len() != V_BITS
        || rows[2].len() != W_BITS {
        return Err("C492 Score/V/W term and unique ROW census".into());
    }
    let layout = crate::origin_score::Layout::new();
    let mut v = Vec::new();
    let mut w = Vec::new();
    for (term, &(family, local)) in terms.iter().zip(&families) {
        match family {
            Family::V => v.push((term, local - V_ROW[context])),
            Family::W => w.push((term, local - W_ROW[context])),
            Family::Score => (),
            Family::Slack => unreachable!(),
        }
        out.push(TypedTerm { family, context, term: term.clone() });
        let lease = RowLease { row: term.row, family, context, author: RowAuthor::Score(author) };
        if leases.get(&term.row).is_some_and(|prior| prior != &lease) {
            return Err("C492 ROW lease author/family collision".into());
        }
        leases.insert(term.row, lease);
    }
    let owner_base = checked_owner_base(owner, WIDTH, 1 << 21)?;
    let previous_base = checked_owner_base(owner.checked_sub(1).ok_or("C492 W owner underflow")?, WIDTH, 1 << 21)?;
    for (term, bit) in v {
        if term.row != row_base + V_ROW[context] + bit
            || term.gate.left != owner_base + SCORE_X[context] + layout.sv.start + bit
            || term.gate.right != owner_base + CAP_X[context] + 740 + bit
            || term.gate.c0 != Fr::zero() || term.gate.c1 != Fr::one()
            || term.gate.c2 != -Fr::one() || term.gate.c3 != Fr::zero()
        { return Err("C492 exact V alias tuple".into()); }
    }
    for (pair, bit) in w.chunks_exact(2).zip(0..W_BITS) {
        let (local, external) = (pair[0], pair[1]);
        let row = row_base + W_ROW[context] + bit;
        let work = previous_base + 987_450 + bit;
        if local.1 != bit || external.1 != bit
            || local.0.row != row || external.0.row != row
            || local.0.gate.left != owner_base + SCORE_X[context] + layout.sw.start + bit
            || local.0.gate.right != 0 || local.0.gate.c0 != Fr::zero()
            || local.0.gate.c1 != Fr::one() || local.0.gate.c2 != Fr::zero()
            || local.0.gate.c3 != Fr::zero()
            || external.0.gate.left != work || external.0.gate.right != 0
            || external.0.gate.c0 != Fr::zero() || external.0.gate.c1 != -Fr::one()
            || external.0.gate.c2 != Fr::zero() || external.0.gate.c3 != Fr::zero()
        { return Err("C492 exact W alias tuple/orientation".into()); }
    }
    Ok(())
}

fn project(input: &BorrowedInput<'_>) -> Result<Projection, String> {
    let identity = check_identity(input)?;
    let owner = identity.owner;
    let schedule = Eligible08RegularScoreOwner::classify(owner)?;
    let stage = input.stage;
    if &stage.map_stage != input.map_stage
        || stage.score_rows().iter().zip(&identity.active).any(|(terms, active)| !*active && !terms.is_empty())
        || stage.score_cells().len() != identity.active.iter().filter(|active| **active).count()
            * crate::origin_score::INPUT
        || stage.score_imports().len() != identity.active.iter().filter(|active| **active).count() * (225 + 65 + 224)
        || stage.slack_cells().len() != 2 * SLACK_BITS
    { return Err("C492 stage/source projection census".into()); }

    let mut terms = Vec::new();
    let mut row_leases = BTreeMap::<usize, RowLease>::new();
    let mut assignments = BTreeMap::<usize, XAssignment>::new();
    let mut score_read_kinds = [0usize; 3];
    let owner_base = checked_owner_base(owner, WIDTH, 1 << 21)?;
    let row_base = checked_owner_base(owner, ROW_WIDTH, 1 << 21)?;
    for context in 0..2 {
        if identity.active[context] {
            let author = ScoreReplayAuthor { context, origin: owner + 1,
                previous_owner: schedule.previous_r_owner(), max_owner: schedule.max_owner(), cap_owner: owner };
            let score_base = H21EligibleMapStage::score_live(context)?.start;
            for bit in 0..crate::origin_score::INPUT {
                let local = score_base + bit;
                let (found, value) = stage.score_cells().get(&local)
                    .ok_or("C492 missing Score X author")?;
                if *found != author || (!value.is_zero() && !value.is_one()) {
                    return Err("C492 Score X author/value".into());
                }
                let address = owner_base.checked_add(local).ok_or("C492 Score X overflow")?;
                if address >= 1usize << 41 { return Err("C492 Score X outside address domain".into()); }
                let key = XKey { address,
                    context, family: Family::Score, author: XAuthor::Score(author) };
                if assignments.insert(address, XAssignment { key, value: value.is_one() }).is_some() {
                    return Err("C492 duplicate Score X assignment".into());
                }
            }
            classify_score_terms(owner, context, &stage.score_rows()[context], author,
                &mut terms, &mut row_leases)?;
        } else if !stage.score_cells().keys().all(|local| !H21EligibleMapStage::score_live(context)
            .is_ok_and(|range| range.contains(local))) {
            return Err("C492 inactive Score context claimed X".into());
        }
        let slack_domain = H21EligibleMapStage::slack_live(context)?;
        let slack_cells = stage.slack_cells();
        if slack_domain.clone().any(|local| !slack_cells.contains_key(&local))
            || slack_cells.keys().filter(|local| slack_domain.clone().contains(local)).count() != SLACK_BITS
        { return Err("C492 exact Slack X census".into()); }
        for bit in 0..SLACK_BITS {
            let local = slack_domain.start + bit;
            let (author, value) = slack_cells.get(&local).ok_or("C492 missing Slack X")?;
            if *author != H21StageAuthor::Slack(context) || *value {
                return Err("C492 Slack X author/value".into());
            }
            let address = owner_base.checked_add(local).ok_or("C492 Slack X overflow")?;
            if address >= 1usize << 41 { return Err("C492 Slack X outside address domain".into()); }
            let key = XKey { address,
                context, family: Family::Slack, author: XAuthor::Slack(context) };
            if assignments.insert(address, XAssignment { key, value: false }).is_some() {
                return Err("C492 duplicate zero Slack X assignment".into());
            }
        }
        let canonical = crate::bank53_slack::slack_zero_terms(owner, context)?;
        if stage.slack_rows()[context] != canonical || canonical.len() != SLACK_BITS {
            return Err("C492 canonical Slack producer mismatch".into());
        }
        for (bit, source_term) in canonical.iter().enumerate() {
            let mut placed = source_term.clone();
            placed.row = row_base.checked_add(SLACK_ROW[context] + bit)
                .ok_or("C492 Slack ROW overflow")?;
            if placed.row >= 1usize << 40 || placed.gate.left >= 1usize << 41
                || placed.gate.right >= 1usize << 41 || placed.gate != source_term.gate {
                return Err("C492 Slack relocation changed operand/coefficient".into());
            }
            terms.push(TypedTerm { family: Family::Slack, context, term: placed.clone() });
            let lease = RowLease { row: placed.row, family: Family::Slack,
                context, author: RowAuthor::Slack(context) };
            if row_leases.get(&placed.row).is_some_and(|prior| prior != &lease) {
                return Err("C492 Slack ROW lease collision".into());
            }
            row_leases.insert(placed.row, lease);
        }
    }
    if terms.len() != identity.active.iter().filter(|active| **active).count()
        * (SCORE_TERM_COUNT + V_BITS + 2 * W_BITS + SLACK_BITS)
        + (2 - identity.active.iter().filter(|active| **active).count()) * SLACK_BITS
    { return Err("C492 ordered physical term total".into()); }

    // The retained checked view publishes Score/Slack cells alongside Map and
    // Cap. Compare the exact subset this partial writer owns; never re-author
    // the other families.
    let mut packed = BTreeMap::<usize, (XAuthor, bool)>::new();
    let mut foreign_packed = BTreeSet::new();
    for cell in input.packed_cells {
        let entry = match cell.author() {
            ScoredOwnerPackedAuthor::Score(author) => Some((XAuthor::Score(author), cell.value())),
            ScoredOwnerPackedAuthor::Slack(context) => Some((XAuthor::Slack(context), cell.value())),
            _ => { foreign_packed.insert(cell.wire()); None },
        };
        if let Some(entry) = entry {
            if packed.insert(cell.wire(), entry).is_some() {
                return Err("C492 duplicate packed Score/Slack projection".into());
            }
        }
    }
    let expected_packed: BTreeMap<_, _> = assignments.iter().map(|(address, assignment)|
        (*address, (assignment.key.author, assignment.value))).collect();
    if packed != expected_packed || expected_packed.keys().any(|wire| foreign_packed.contains(wire)) {
        return Err("C492 packed Score/Slack source mismatch/collision".into());
    }
    let reservations: Vec<_> = assignments.values().map(|assignment| assignment.key.clone()).collect();

    let mut occupied = BTreeMap::<usize, RowWriter>::new();
    for context in 0..2 {
        for term in &input.map_stage.map_terms[context] {
            if term.row / ROW_WIDTH != owner {
                return Err("C492 Map ROW owner".into());
            }
            if occupied.insert(term.row, RowWriter::Map(context))
                .is_some_and(|prior| prior != RowWriter::Map(context)) {
                return Err("C492 Map ROW overlap".into());
            }
        }
    }
    for lease in row_leases.values() {
        if occupied.insert(lease.row, RowWriter::Partial(lease.family, lease.context)).is_some() {
            return Err("C492 cross-family ROW lease overlap".into());
        }
    }
    if row_leases.len() != identity.active.iter().filter(|active| **active).count()
        * (SCORE_ROW_COUNT + V_BITS + W_BITS + SLACK_BITS)
        + (2 - identity.active.iter().filter(|active| **active).count()) * SLACK_BITS
    { return Err("C492 typed ROW lease total".into()); }

    let score_reads = stage.score_imports().to_vec();
    let layout = crate::origin_score::Layout::new();
    for &(wire, author, value) in &score_reads {
        if wire >= 1usize << 41 || (!value.is_zero() && !value.is_one()) {
            return Err("C492 Score open read domain/value".into());
        }
        let (context, bit, expected_wire, source_local, kind) = match author {
            ScoreRelationReadAuthor::PreviousR { context, owner: previous }
                if context < 2 && identity.active[context] && previous == schedule.previous_r_owner() => {
                    let delta = wire.checked_sub(previous * WIDTH + SCORE_X[context] + layout.r.start)
                        .ok_or("C492 predecessor R read underflow")?;
                    if delta >= 225 { return Err("C492 predecessor R read width".into()); }
                    (context, delta, previous * WIDTH + SCORE_X[context] + layout.r.start + delta,
                        layout.p.start + delta, 0)
                },
            ScoreRelationReadAuthor::Cap { context, origin, max_owner, cap_owner }
                if context < 2 && identity.active[context] && origin == owner + 1
                    && max_owner == schedule.max_owner() && cap_owner == owner => {
                    let delta = wire.checked_sub(owner * WIDTH + CAP_X[context] + 740)
                        .ok_or("C492 Cap V read underflow")?;
                    if delta >= V_BITS { return Err("C492 Cap V read width".into()); }
                    (context, delta, owner * WIDTH + CAP_X[context] + 740 + delta,
                        layout.sv.start + delta, 2)
                },
            ScoreRelationReadAuthor::WorkUpper { owner: previous, height }
                if previous.checked_add(1) == Some(owner) && height == owner + 1 => {
                    let delta = wire.checked_sub(previous * WIDTH + 987_450)
                        .ok_or("C492 WorkUpper read underflow")?;
                    if delta >= W_BITS { return Err("C492 WorkUpper read width".into()); }
                    let active_contexts: Vec<_> = (0..2).filter(|context| identity.active[*context]).collect();
                    let context = *active_contexts.get(score_read_kinds[1] / W_BITS)
                        .ok_or("C492 WorkUpper read occurrence order")?;
                    (context, delta, previous * WIDTH + 987_450 + delta,
                        layout.sw.start + delta, 1)
                },
            _ => return Err("C492 Score open read author".into()),
        };
        if wire != expected_wire { return Err("C492 Score open read exact address".into()); }
        let cell_local = H21EligibleMapStage::score_live(context)?.start + source_local;
        let (cell_author, cell_value) = stage.score_cells().get(&cell_local)
            .ok_or("C492 Score open read source X absent")?;
        if cell_author.context != context || *cell_value != value {
            return Err("C492 Score open read source X/value".into());
        }
        if kind == 2 {
            let cap_author = ScoredOwnerPackedAuthor::Cap { context, origin: owner + 1 };
            if !input.packed_cells.iter().any(|cell| cell.wire() == wire
                && cell.author() == cap_author && cell.value() == value.is_one()) {
                return Err("C492 Cap V read not the checked packed Cap cell".into());
            }
        }
        score_read_kinds[kind] += 1;
    }
    let active_count = identity.active.iter().filter(|active| **active).count();
    if score_read_kinds != [225 * active_count, W_BITS * active_count, V_BITS * active_count] {
        return Err("C492 ordered Score read role census".into());
    }
    if input.selected_reads.is_empty() || input.selected_reads.iter().any(|read|
        read.wire >= 1usize << 41 || (!read.value.is_zero() && !read.value.is_one()))
    { return Err("C492 retained selected open-read obligations".into()); }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum SelectedKind { PreviousR { context: usize, owner: usize },
        WorkUpper { owner: usize, height: usize } }
    let mut expected_score_reads = BTreeMap::<(usize, SelectedKind, bool), usize>::new();
    for &(wire, author, value) in &score_reads {
        let kind = match author {
            ScoreRelationReadAuthor::PreviousR { context, owner } =>
                Some(SelectedKind::PreviousR { context, owner }),
            ScoreRelationReadAuthor::WorkUpper { owner, height } =>
                Some(SelectedKind::WorkUpper { owner, height }),
            ScoreRelationReadAuthor::Cap { .. } => None,
        };
        if let Some(kind) = kind {
            *expected_score_reads.entry((wire, kind, value.is_one())).or_default() += 1;
        }
    }
    let mut offered_score_reads = BTreeMap::<(usize, SelectedKind, bool), usize>::new();
    let mut map_contexts = [false; 2];
    let mut max_contexts = [false; 2];
    for read in input.selected_reads {
        match read.author {
            OpenScoredReadAuthor::Map { context, .. } if context < 2 => map_contexts[context] = true,
            OpenScoredReadAuthor::PreviousR { context, owner: previous }
                if context < 2 && identity.active[context] && previous == schedule.previous_r_owner() => {
                    let kind = SelectedKind::PreviousR { context, owner: previous };
                    *offered_score_reads.entry((read.wire, kind, read.value.is_one())).or_default() += 1;
                },
            OpenScoredReadAuthor::WorkUpper { owner: previous, height }
                if previous.checked_add(1) == Some(owner) && height == owner + 1 => {
                    let kind = SelectedKind::WorkUpper { owner: previous, height };
                    *offered_score_reads.entry((read.wire, kind, read.value.is_one())).or_default() += 1;
                },
            OpenScoredReadAuthor::Max { context, end }
                if context < 2 && identity.active[context] && end == schedule.max_owner() + 2 => {
                    max_contexts[context] = true;
                },
            _ => return Err("C492 selected open read author/domain".into()),
        }
    }
    if map_contexts != identity.active || max_contexts != identity.active
        || offered_score_reads != expected_score_reads
    { return Err("C492 selected foreign-read obligations/multiplicity".into()); }
    Ok(Projection { identity, terms, row_leases: row_leases.into_values().collect(),
        assignments: assignments.into_values().collect(),
        reservations, score_reads, selected_reads: input.selected_reads.to_vec(),
        retained_header_daa_active_operands: input.retained_header_daa_active_operands })
}

fn replay_projection(input: &BorrowedInput<'_>, installed: &Projection)
    -> Result<Projection, String> {
    let replay = project(input)?;
    if &replay != installed { return Err("C492 source replay differs from installed partial".into()); }
    Ok(replay)
}

fn admit(destination: &mut StructuralDestination, input: &BorrowedInput<'_>,
    offered: Projection) -> Result<(), String> {
    if destination.installed.is_some() { return Err("C492 partial destination occupied".into()); }
    let replay = replay_projection(input, &offered)?;
    destination.installed = Some(replay);
    Ok(())
}

#[cfg(test)]
fn reject_offered_mutants(input: &BorrowedInput<'_>) -> Result<usize, String> {
    let baseline = project(input)?;
    let mut rejected = 0usize;
    macro_rules! reject {
        ($change:expr) => {{
            let mut offered = baseline.clone();
            ($change)(&mut offered);
            // Shared revalidation core only: this fixture cannot construct an
            // authentic production packing view or its private carrier.
            let installed = InstalledScoreSlack { projection: offered.clone() };
            if installed.summary_after_replay(input).is_ok() {
                return Err("C492 retained mutant yielded installed summary".into());
            }
            let mut destination = StructuralDestination::default();
            let before = destination.clone();
            if admit(&mut destination, input, offered).is_ok() || destination != before {
                return Err("C492 candidate mutant changed/entered destination".into());
            }
            rejected += 1;
        }};
    }
    reject!(|p: &mut Projection| p.identity.header.root[0] ^= 0xff);
    reject!(|p: &mut Projection| p.identity.header.total[0] ^= 0xff);
    reject!(|p: &mut Projection| p.identity.header.profile[0] ^= 0xff);
    reject!(|p: &mut Projection| p.identity.header.cut.push(0xff));
    reject!(|p: &mut Projection| p.identity.owner += 1);
    reject!(|p: &mut Projection| p.identity.maps[0].n += 1);
    reject!(|p: &mut Projection| { p.terms.pop(); });
    reject!(|p: &mut Projection| { p.terms.swap(0, 1); });
    reject!(|p: &mut Projection| { p.terms[0].term.gate.c0 += Fr::one(); });
    reject!(|p: &mut Projection| {
        let term = p.terms.iter_mut().find(|term| term.family == Family::W
            && term.term.gate.c1 == -Fr::one()).unwrap();
        let address = term.term.gate.left;
        term.term.gate.left = 0;
        term.term.gate.right = address;
        term.term.gate.c1 = Fr::zero();
        term.term.gate.c2 = -Fr::one();
    });
    reject!(|p: &mut Projection| p.row_leases[0].row += 1);
    reject!(|p: &mut Projection| p.row_leases[0].family = Family::V);
    reject!(|p: &mut Projection| { let duplicate=p.assignments.iter()
        .find(|assignment| assignment.key.family == Family::Slack).unwrap().clone();
        p.assignments.push(duplicate); });
    reject!(|p: &mut Projection| { p.assignments.remove(0); });
    reject!(|p: &mut Projection| p.assignments[0].key.author = XAuthor::Slack(1));
    reject!(|p: &mut Projection| {
        let XAuthor::Score(mut author)=p.assignments[0].key.author else { unreachable!() };
        author.context=1;
        p.assignments[0].key.author=XAuthor::Score(author);
    });
    reject!(|p: &mut Projection| {
        let XAuthor::Score(mut author)=p.assignments[0].key.author else { unreachable!() };
        author.origin+=1;
        p.assignments[0].key.author=XAuthor::Score(author);
    });
    reject!(|p: &mut Projection| {
        let XAuthor::Score(mut author)=p.assignments[0].key.author else { unreachable!() };
        author.max_owner+=1;
        p.assignments[0].key.author=XAuthor::Score(author);
    });
    reject!(|p: &mut Projection| {
        let XAuthor::Score(mut author)=p.assignments[0].key.author else { unreachable!() };
        author.previous_owner+=1;
        p.assignments[0].key.author=XAuthor::Score(author);
    });
    reject!(|p: &mut Projection| {
        let assignment=p.assignments.iter_mut().find(|a| a.key.family == Family::Slack).unwrap();
        assignment.key.author=XAuthor::Slack(1);
    });
    reject!(|p: &mut Projection| { let duplicate=p.reservations.iter()
        .find(|key| key.family == Family::Slack).unwrap().clone();
        p.reservations.push(duplicate); });
    reject!(|p: &mut Projection| { p.reservations.remove(0); });
    reject!(|p: &mut Projection| p.score_reads[0].1 = ScoreRelationReadAuthor::WorkUpper {
        owner: input.expected.owner(), height: input.expected.owner() + 1 });
    reject!(|p: &mut Projection| { let old=p.score_reads[0].2;
        p.score_reads[0].2 = if old.is_zero() { Fr::one() } else { Fr::zero() }; });
    reject!(|p: &mut Projection| { let old=p.selected_reads[0].value;
        p.selected_reads[0].value = if old.is_zero() { Fr::one() } else { Fr::zero() }; });

    let mut occupied = StructuralDestination { installed: Some(baseline.clone()) };
    let before = occupied.clone();
    if admit(&mut occupied, input, baseline).is_ok() || occupied != before {
        return Err("C492 occupied destination was changed".into());
    }
    rejected += 1;
    Ok(rejected)
}

#[cfg(test)]
fn check_retained_read_obligations(input: &BorrowedInput<'_>) -> Result<(), String> {
    let baseline = project(input)?;
    let installed = InstalledScoreSlack { projection: baseline.clone() };
    let summary = installed.summary_after_replay(input)?;
    if summary.owner != input.expected.owner() || summary.terms != baseline.terms.len()
        || summary.row_leases != baseline.row_leases.len()
        || summary.assignments != baseline.assignments.len()
        || summary.reservations != baseline.reservations.len()
        || summary.score_reads != baseline.score_reads.len()
        || summary.selected_reads != baseline.selected_reads.len()
        || summary.retained_header_daa_active_operands != input.retained_header_daa_active_operands {
        return Err("C492 installed summary did not preserve full projection".into());
    }
    let repeated = baseline.selected_reads.iter().position(|read|
        matches!(read.author, OpenScoredReadAuthor::WorkUpper { .. })
            && baseline.selected_reads.iter().filter(|other| *other == read).count() > 1)
        .ok_or("C492 fixture lacks legitimate repeated WorkUpper read")?;
    for field in 0..4 {
        let mut changed = baseline.clone();
        match field {
            0 => { changed.selected_reads.remove(repeated); },
            1 => changed.selected_reads.push(changed.selected_reads[repeated]),
            2 => changed.retained_header_daa_active_operands += 1,
            3 => changed.assignments[0].value = !changed.assignments[0].value,
            _ => unreachable!(),
        }
        let changed = InstalledScoreSlack { projection: changed };
        let mut destination = StructuralDestination::default();
        let before = destination.clone();
        if changed.summary_after_replay(input).is_ok()
            || admit(&mut destination, input, changed.projection).is_ok()
            || destination != before {
            return Err("C492 retained obligation mutant entered destination".into());
        }
    }
    // The source-side multiplicity check also rejects a missing or extra
    // occurrence; retaining a vector must not weaken it to set membership.
    for extra in [false, true] {
        let mut reads = input.selected_reads.to_vec();
        if extra { reads.push(reads[repeated]); } else { reads.remove(repeated); }
        let changed_input = BorrowedInput { selected_reads: &reads, ..*input };
        if project(&changed_input).is_ok() {
            return Err("C492 changed source read multiplicity was accepted".into());
        }
    }
    Ok(())
}

fn production_input<'a>(view: &'a ScoredOwnerPackingView,
    expected: &'a HeaderSourceBinding) -> Result<BorrowedInput<'a>, String> {
    view.validate_for_packing(expected, view.owner())?;
    Ok(BorrowedInput { expected, published: view.binding(),
        expected_maps: &view.source.map_bindings,
        map_stage: &view.source.stage.map_stage, stage: &view.source.stage,
        packed_cells: &view.cells, selected_reads: &view.selected_open_reads,
        retained_header_daa_active_operands: view.retained_header_daa_active_operands })
}

pub(super) fn stage_partial<'a>(view: &'a ScoredOwnerPackingView,
    expected: &HeaderSourceBinding) -> Result<PartialScoreSlack<'a>, String> {
    let input = production_input(view, expected)?;
    let offered = project(&input)?;
    let mut destination = StructuralDestination::default();
    admit(&mut destination, &input, offered)?;
    Ok(PartialScoreSlack { projection: destination.installed
        .ok_or("C492 partial destination did not install")?, _source: PhantomData })
}

#[cfg(test)]
pub(crate) struct FixtureCoreSummary {
    pub(crate) terms: usize,
    pub(crate) row_leases: usize,
    pub(crate) assignments: usize,
    pub(crate) reservations: usize,
    pub(crate) score_reads: usize,
    pub(crate) selected_reads: usize,
    pub(crate) retained_header_daa_active_operands: usize,
    pub(crate) negative_cases: usize,
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FixtureCoreError {
    Rejected(String),
    InvariantFailure(String),
}

#[cfg(test)]
impl From<FixtureCoreError> for String {
    fn from(error: FixtureCoreError) -> Self {
        match error {
            FixtureCoreError::Rejected(message) => message,
            FixtureCoreError::InvariantFailure(message) => format!("C492 fixture invariant: {message}"),
        }
    }
}

#[cfg(test)]
pub(crate) fn admit_fixture_core_for_test(
    stage: &H21EligibleSlackStage,
    expected: &HeaderSourceBinding,
    expected_maps: &[Binding; 2],
    packed_cells: &[ScoredOwnerPackedCell],
    selected_reads: &[OpenScoredRead],
    retained_header_daa_active_operands: usize,
) -> Result<FixtureCoreSummary, FixtureCoreError> {
    let input = BorrowedInput { expected, published: expected, expected_maps,
        map_stage: &stage.map_stage, stage, packed_cells, selected_reads,
        retained_header_daa_active_operands };
    let mut destination = StructuralDestination::default();
    let before = destination.clone();
    let offered = match project(&input) {
        Ok(offered) => offered,
        Err(error) => {
            if destination != before {
                return Err(FixtureCoreError::InvariantFailure(
                    "rejected fixture changed destination".into()));
            }
            return Err(FixtureCoreError::Rejected(error));
        }
    };
    let negative_cases = reject_offered_mutants(&input)
        .map_err(FixtureCoreError::InvariantFailure)?;
    check_retained_read_obligations(&input).map_err(FixtureCoreError::InvariantFailure)?;
    if let Err(error) = admit(&mut destination, &input, offered) {
        if destination != before {
            return Err(FixtureCoreError::InvariantFailure(
                "failed fixture admission changed destination".into()));
        }
        return Err(FixtureCoreError::Rejected(error));
    }
    let installed = destination.installed
        .ok_or_else(|| FixtureCoreError::InvariantFailure(
            "fixture partial did not install".into()))?;
    Ok(FixtureCoreSummary { terms: installed.terms.len(),
        row_leases: installed.row_leases.len(), assignments: installed.assignments.len(),
        reservations: installed.reservations.len(), score_reads: installed.score_reads.len(),
        selected_reads: installed.selected_reads.len(),
        retained_header_daa_active_operands: installed.retained_header_daa_active_operands,
        negative_cases })
}


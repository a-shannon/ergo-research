//! Read-only diagnostic census for the common H21 ROW/X roster.
//!
//! This joins ownership/imported values and checks exported terms per role.
//! Common ROW embedding/PCS closure, proof construction, and client behavior
//! remain outside this diagnostic slice.

use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};

use crate::{
    daa_history_roster::{BANKS, WIDTH},
    h21_local_merged_ledger::RowWriter,
    h21_native_admission_tests::{
        candidate136_native_bundle::{CarryMapExport, SelectedXRole},
        candidate151_native_daa::NativeDaaStage,
    },
    h21_scheduled_max_cap::{Patch as MaxPatch, Writer as MaxWriter},
    legacy_envelope_map::Binding,
    packed_owner_assembly::{validate_native_plan_input, NativePrefix},
    score_prefix_r_anchor::{ScoreCapCellWriter, ScoreCapValueProjection},
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const HEADERS: u64 = 1_827_840;
const SLOT_LOG: usize = 21;
const OWNER_LIMIT: usize = 1 << SLOT_LOG;
const ROW_WIDTH: usize = 1 << 19;
const CARRY_OWNER: usize = 844_670;
const CROSS_OWNER: usize = 844_671;
const DAA_OWNER: usize = 844_672;
const SCORE_OWNER: usize = 845_759;
const SCORE_BOUNDARY_OWNER: usize = 845_758;
const MAX_LOOKAHEAD_OWNER: usize = 844_798;
const MAX_LOOKAHEAD_END: usize = 844_800;
const MAX_LOOKAHEAD_LOCAL_STARTS: [usize; 2] = [999_424, 1_000_097];
const MAX_LOOKAHEAD_GLOBAL_X_STARTS: [usize; 2] = [885_835_907_072, 885_835_907_745];
const MAX_LOOKAHEAD_VALUE_BITS: usize = 224;
const WORK_ROW_STRIDE: usize = 2_048;
const CROSS_ROW_STRIDE: usize = 8_192;
const CALLBACK_COUNT: usize = 1_152;
const DAA_SERIALIZER_IMPORT_COUNT: usize = 864;
const SCORE_CUTS: [u64; 2] = [1_827_840, 1_827_775];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowAuthor {
    Carry,
    Daa,
    Score,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum XAuthor {
    Carry,
    DaaBank(usize),
    Score,
    ScoreUpper2,
    ScoreSummary0,
    ScoreSummary1,
    MaxLookahead0,
    MaxLookahead1,
    HeaderSerializer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum XRole {
    Read,
    Write(XAuthor),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum TermRole {
    Work,
    Max,
    Cross,
    Map0,
    Map1,
    Daa,
    Score,
}

impl TermRole {
    fn index(self) -> usize {
        match self {
            Self::Work => 0,
            Self::Max => 1,
            Self::Cross => 2,
            Self::Map0 => 3,
            Self::Map1 => 4,
            Self::Daa => 5,
            Self::Score => 6,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Work => "Work",
            Self::Max => "MAX",
            Self::Cross => "CROSS",
            Self::Map0 => "Map0",
            Self::Map1 => "Map1",
            Self::Daa => "DAA",
            Self::Score => "Score",
        }
    }
}

struct TermGroup<'a> {
    role: TermRole,
    terms: Vec<&'a crate::sparse::Term>,
}

impl<'a> TermGroup<'a> {
    fn from_slice(role: TermRole, terms: &'a [crate::sparse::Term]) -> Self {
        Self {
            role,
            terms: terms.iter().collect(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct XClaim {
    value: Fr,
    writer: Option<XAuthor>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ResidualCensus {
    term_counts: [usize; 7],
    active_x_count: usize,
    evaluated_role_row_count: usize,
    work_row_count: usize,
    cross_row_count: usize,
    missing_row19_claims: Vec<(TermRole, usize)>,
}

fn required_map1_terms(
    terms: Option<&[crate::sparse::Term]>,
) -> Result<&[crate::sparse::Term], String> {
    let terms = terms.ok_or("c154 Map1 term slice absent")?;
    if terms.is_empty() {
        return Err("c154 Map1 term slice empty".into());
    }
    Ok(terms)
}

fn validate_separate_role_geometry(groups: &[TermGroup<'_>]) -> Result<(), String> {
    for group in groups {
        let (stride, owner) = match group.role {
            TermRole::Work => (WORK_ROW_STRIDE, CARRY_OWNER),
            TermRole::Cross => (CROSS_ROW_STRIDE, CROSS_OWNER),
            _ => continue,
        };
        if group.terms.iter().any(|term| term.row / stride != owner) {
            return Err(format!(
                "c154 {} separate ROW geometry mismatch",
                group.role.name()
            ));
        }
    }
    Ok(())
}

fn insert_row(
    rows: &mut BTreeMap<usize, RowAuthor>,
    row: usize,
    author: RowAuthor,
) -> Result<(), String> {
    if row >= OWNER_LIMIT * ROW_WIDTH {
        return Err("c154 ROW address outside H21 owner extent".into());
    }
    match rows.get(&row) {
        Some(existing) if *existing != author => Err("c154 cross-writer ROW collision".into()),
        Some(_) => Ok(()),
        None => {
            rows.insert(row, author);
            Ok(())
        }
    }
}

fn insert_placed_daa_rows(
    rows: &mut BTreeMap<usize, RowAuthor>,
    placed_terms: &[crate::sparse::Term],
) -> Result<(), String> {
    for placed in placed_terms {
        if placed.row / ROW_WIDTH != DAA_OWNER {
            return Err("c154 DAA placed ROW owner extent mismatch".into());
        }
        insert_row(rows, placed.row, RowAuthor::Daa)?;
    }
    Ok(())
}

fn score_global_x_claim_ranges(
    score: &ScoreCapValueProjection,
) -> Result<Vec<Range<usize>>, String> {
    let mut ranges = Vec::with_capacity(score.x_claims().len());
    for claim in score.x_claims() {
        if claim.owner != SCORE_OWNER
            || claim.start >= claim.end
            || claim.end > OWNER_LIMIT * WIDTH
            || claim.start / WIDTH != claim.owner
            || (claim.end - 1) / WIDTH != claim.owner
        {
            return Err("c154 Score X claim extent mismatch".into());
        }
        let range = claim.start..claim.end;
        if ranges
            .iter()
            .any(|prior: &Range<usize>| range.start < prior.end && prior.start < range.end)
        {
            return Err("c154 overlapping Score X writer claims".into());
        }
        ranges.push(range);
    }
    Ok(ranges)
}

fn score_ancestor_writer_claims() -> Vec<(usize, XAuthor)> {
    let owner_base = SCORE_BOUNDARY_OWNER * WIDTH;
    let mut claims = Vec::with_capacity(674);
    for (start, width, author) in [
        (987_450, 224, XAuthor::ScoreUpper2),
        (678_819, 225, XAuthor::ScoreSummary0),
        (687_011, 225, XAuthor::ScoreSummary1),
    ] {
        claims.extend((start..start + width).map(|local| (owner_base + local, author)));
    }
    claims
}

/// Promote only the three exact ancestor writer ranges carried by the
/// validated Score value projection. The tags attest to the staged producer;
/// matching addresses alone do not create a writer claim.
fn insert_score_ancestor_writers(
    cells: &mut BTreeMap<usize, XClaim>,
    projection_cells: &[(usize, Fr, ScoreCapCellWriter)],
    active: &BTreeSet<usize>,
) -> Result<(), String> {
    let expected = score_ancestor_writer_claims()
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    let mut observed = BTreeSet::new();
    for &(address, value, writer) in projection_cells {
        let tagged_author = match writer {
            ScoreCapCellWriter::Upper(2) => Some(XAuthor::ScoreUpper2),
            ScoreCapCellWriter::Summary(0) => Some(XAuthor::ScoreSummary0),
            ScoreCapCellWriter::Summary(1) => Some(XAuthor::ScoreSummary1),
            _ => None,
        };
        if let Some(author) = tagged_author {
            if expected.get(&address) != Some(&author) || !active.contains(&address) {
                return Err("c154 unexpected Score ancestor X writer claim".into());
            }
        }
        if let Some(author) = expected.get(&address) {
            if tagged_author != Some(*author) || !active.contains(&address) {
                return Err("c154 Score ancestor X writer address/tag mismatch".into());
            }
            if !observed.insert(address) {
                return Err("c154 duplicate Score ancestor X writer claim".into());
            }
            insert_x(cells, address, value, XRole::Write(*author))?;
        }
    }
    if observed.len() != expected.len() || observed.iter().any(|address| !expected.contains_key(address))
    {
        return Err("c154 incomplete Score ancestor X writer census".into());
    }
    Ok(())
}

type MaxPatchSnapshot = (usize, usize, MaxWriter, Vec<Fr>);

fn max_lookahead_author(context: usize) -> Result<XAuthor, String> {
    match context {
        0 => Ok(XAuthor::MaxLookahead0),
        1 => Ok(XAuthor::MaxLookahead1),
        _ => Err("c154 MAX lookahead context outside selected pair".into()),
    }
}

/// Promote the first 224 source R bits from each exact c146 lookahead MAX
/// writer span into the common global-X census.
fn insert_max_lookahead_writers(
    cells: &mut BTreeMap<usize, XClaim>,
    spans: &[MaxPatchSnapshot],
    active: &BTreeSet<usize>,
) -> Result<(), String> {
    if spans.len() != 2 {
        return Err("c154 MAX lookahead writer count mismatch".into());
    }
    for context in 0..2 {
        let (owner, start, writer, values) = &spans[context];
        let expected_writer = MaxWriter::Max {
            context,
            end: MAX_LOOKAHEAD_END,
        };
        if *owner != MAX_LOOKAHEAD_OWNER
            || *start != MAX_LOOKAHEAD_LOCAL_STARTS[context]
            || *writer != expected_writer
            || values.len() != 673
        {
            return Err("c154 MAX lookahead writer owner/tag/domain mismatch".into());
        }
        let global_start = MAX_LOOKAHEAD_OWNER
            .checked_mul(WIDTH)
            .and_then(|base| base.checked_add(*start))
            .ok_or("c154 MAX lookahead X start overflow")?;
        if global_start != MAX_LOOKAHEAD_GLOBAL_X_STARTS[context] {
            return Err("c154 MAX lookahead local/global address mismatch".into());
        }
        for bit in 0..MAX_LOOKAHEAD_VALUE_BITS {
            let address = global_start
                .checked_add(bit)
                .ok_or("c154 MAX lookahead X address overflow")?;
            if !active.contains(&address) {
                return Err("c154 MAX lookahead X writer is not an active read".into());
            }
            let value = *values
                .get(bit)
                .ok_or("c154 MAX lookahead source bit missing")?;
            insert_x(
                cells,
                address,
                value,
                XRole::Write(max_lookahead_author(context)?),
            )?;
        }
    }
    Ok(())
}

fn active_x_addresses(groups: &[TermGroup<'_>]) -> BTreeSet<usize> {
    groups
        .iter()
        .flat_map(|group| group.terms.iter())
        .flat_map(|term| {
            let gate = &term.gate;
            let mut active = Vec::with_capacity(2);
            if !gate.c1.is_zero() || !gate.c3.is_zero() {
                active.push(gate.left);
            }
            if !gate.c2.is_zero() || !gate.c3.is_zero() {
                active.push(gate.right);
            }
            active
        })
        .filter(|address| *address != 0)
        .collect()
}

fn close_active_x_values(
    cells: &mut BTreeMap<usize, XClaim>,
    active: &BTreeSet<usize>,
    daa: &NativeDaaStage,
) -> Result<(), String> {
    if cells.get(&0).is_some_and(|claim| !claim.value.is_zero()) {
        return Err("c154 distinguished X address zero is nonzero".into());
    }
    for &address in active {
        if address >= OWNER_LIMIT * WIDTH {
            return Err("c154 active X address outside H21 extent".into());
        }
        if address / WIDTH != DAA_OWNER {
            continue;
        }
        let packed = Fr::from(u64::from(daa.packed_owner_bit(address % WIDTH)?));
        match cells.get(&address) {
            Some(claim) if claim.writer.is_some() => {
                if claim.value != packed {
                    return Err("c154 active DAA owner X differs from packed owner".into());
                }
            }
            _ => insert_x(cells, address, packed, XRole::Read)?,
        }
    }
    for &address in active {
        if !cells.contains_key(&address) {
            return Err(format!("c154 missing active X value at {address}"));
        }
    }
    Ok(())
}

fn evaluate_role_residuals(
    groups: &[TermGroup<'_>],
    cells: &BTreeMap<usize, XClaim>,
    rows: &BTreeMap<usize, RowAuthor>,
    active_x_count: usize,
) -> Result<ResidualCensus, String> {
    let mut census = ResidualCensus {
        active_x_count,
        ..ResidualCensus::default()
    };
    validate_separate_role_geometry(groups)?;
    let mut missing_claims = BTreeSet::new();
    for group in groups {
        census.term_counts[group.role.index()] += group.terms.len();
        let mut role_rows = BTreeMap::<usize, Fr>::new();
        for term in &group.terms {
            let read = |address: usize| -> Result<Fr, String> {
                if address == 0 {
                    return Ok(Fr::zero());
                }
                cells
                    .get(&address)
                    .map(|claim| claim.value)
                    .ok_or_else(|| format!("c154 missing active X value at {address}"))
            };
            let a = if !term.gate.c1.is_zero() || !term.gate.c3.is_zero() {
                read(term.gate.left)?
            } else {
                Fr::zero()
            };
            let b = if !term.gate.c2.is_zero() || !term.gate.c3.is_zero() {
                read(term.gate.right)?
            } else {
                Fr::zero()
            };
            let residual =
                term.gate.c0 + term.gate.c1 * a + term.gate.c2 * b + term.gate.c3 * a * b;
            *role_rows.entry(term.row).or_insert_with(Fr::zero) += residual;
            let expected_author = match group.role {
                TermRole::Max | TermRole::Map0 | TermRole::Map1 => Some(RowAuthor::Carry),
                TermRole::Daa => Some(RowAuthor::Daa),
                TermRole::Score => Some(RowAuthor::Score),
                // Work and CROSS use distinct c136 row geometries and are not
                // embedded in the ROW19 claim map.
                TermRole::Work | TermRole::Cross => None,
            };
            match (expected_author, rows.get(&term.row)) {
                (Some(expected), Some(actual)) if expected != *actual => {
                    return Err(format!(
                        "c154 {} ROW author mismatch at {}",
                        group.role.name(),
                        term.row
                    ));
                }
                (Some(_), Some(_)) => {}
                (Some(_), None) => {
                    missing_claims.insert((group.role, term.row));
                }
                (None, _) => {}
            }
        }
        for (row, residual) in &role_rows {
            if !residual.is_zero() {
                return Err(format!(
                    "c154 {} ROW residual is nonzero at {row}",
                    group.role.name()
                ));
            }
        }
        census.evaluated_role_row_count += role_rows.len();
        match group.role {
            TermRole::Work => census.work_row_count += role_rows.len(),
            TermRole::Cross => census.cross_row_count += role_rows.len(),
            _ => {}
        }
    }
    census.missing_row19_claims = missing_claims.into_iter().collect();
    Ok(census)
}

fn insert_x(
    cells: &mut BTreeMap<usize, XClaim>,
    address: usize,
    value: Fr,
    role: XRole,
) -> Result<(), String> {
    if address >= OWNER_LIMIT * WIDTH {
        return Err("c154 X address outside H21 owner extent".into());
    }
    if !value.is_zero() && !value.is_one() {
        return Err("c154 non-Boolean X value".into());
    }
    match (cells.get_mut(&address), role) {
        (None, XRole::Read) => {
            cells.insert(
                address,
                XClaim {
                    value,
                    writer: None,
                },
            );
        }
        (None, XRole::Write(author)) => {
            cells.insert(
                address,
                XClaim {
                    value,
                    writer: Some(author),
                },
            );
        }
        (Some(claim), XRole::Read) if claim.value == value => {}
        (Some(_), XRole::Read) => return Err("c154 unequal X reads".into()),
        (Some(claim), XRole::Write(_)) if claim.writer.is_some() => {
            return Err("c154 duplicate X writer".into());
        }
        (Some(claim), XRole::Write(author)) if claim.value == value => {
            claim.writer = Some(author);
        }
        (Some(_), XRole::Write(_)) => return Err("c154 unequal X read/write".into()),
    }
    Ok(())
}

/// Promote the exact foreign timestamp/height DAA alias reads to
/// HeaderSerializer writers. The source-key census comes from the placed DAA
/// terms, while values must agree with both the retained c151 prefix map and
/// the DAA callback reads. Child nBits and other callback-only cells stay reads.
fn insert_daa_serializer_writers(
    cells: &mut BTreeMap<usize, XClaim>,
    active: &BTreeSet<usize>,
    daa_terms: &[crate::sparse::Term],
    serializer_values: &BTreeMap<usize, bool>,
    serializer_targets: &BTreeMap<usize, usize>,
    callback_values: &BTreeMap<usize, bool>,
) -> Result<(), String> {
    if serializer_values.len() != DAA_SERIALIZER_IMPORT_COUNT
        || serializer_targets.len() != DAA_SERIALIZER_IMPORT_COUNT
    {
        return Err("c154 DAA HeaderSerializer source map count mismatch".into());
    }
    let mut alias_targets = BTreeMap::new();
    for term in daa_terms {
        let gate = &term.gate;
        let left_active = !gate.c1.is_zero() || !gate.c3.is_zero();
        if !left_active || gate.left / WIDTH == DAA_OWNER {
            continue;
        }
        if gate.c0 != Fr::zero()
            || gate.c1 != Fr::one()
            || gate.c2 != -Fr::one()
            || !gate.c3.is_zero()
            || gate.right / WIDTH != DAA_OWNER
        {
            return Err("c154 DAA foreign serializer alias shape mismatch".into());
        }
        if alias_targets.insert(gate.left, gate.right).is_some() {
            return Err("c154 duplicate DAA foreign serializer alias source".into());
        }
    }
    if alias_targets.len() != DAA_SERIALIZER_IMPORT_COUNT
        || alias_targets.keys().any(|address| !serializer_values.contains_key(address))
        || serializer_values.keys().any(|address| !alias_targets.contains_key(address))
        || &alias_targets != serializer_targets
    {
        return Err("c154 DAA HeaderSerializer source/target records differ from active aliases".into());
    }
    for (&address, &value) in serializer_values {
        let target = serializer_targets
            .get(&address)
            .ok_or("c154 DAA HeaderSerializer target missing")?;
        if !active.contains(&address) || !active.contains(target) {
            return Err("c154 DAA HeaderSerializer source is inactive".into());
        }
        if callback_values.get(&address) != Some(&value) {
            return Err("c154 DAA HeaderSerializer/callback value mismatch".into());
        }
        insert_x(
            cells,
            address,
            Fr::from(u64::from(value)),
            XRole::Write(XAuthor::HeaderSerializer),
        )?;
    }
    Ok(())
}

/// A deterministic census of exported per-role residuals and selected global-X
/// claims. `scope()` excludes common ROW embedding and PCS closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CommonRoster {
    parent_root: [u8; 32],
    parent_total_be28: [u8; 28],
    frame_digest: [u8; 32],
    rows: BTreeMap<usize, RowAuthor>,
    cells: BTreeMap<usize, XClaim>,
    unresolved_reads: Vec<usize>,
    active_unresolved_reads: Vec<usize>,
    active_unresolved_role_hits: [usize; 7],
    residual_census: ResidualCensus,
    digest: [u8; 32],
}

impl CommonRoster {
    pub(super) fn scope(&self) -> &'static str {
        "diagnostic-partial-roster; partial per-role residual checked; common ROW embedding/PCS open; no proof or client"
    }

    pub(super) fn parent_root(&self) -> [u8; 32] {
        self.parent_root
    }

    pub(super) fn parent_total_be28(&self) -> [u8; 28] {
        self.parent_total_be28
    }

    pub(super) fn frame_digest(&self) -> [u8; 32] {
        self.frame_digest
    }

    pub(super) fn row_count(&self) -> usize {
        self.rows.len()
    }

    pub(super) fn x_count(&self) -> usize {
        self.cells.len()
    }

    pub(super) fn unresolved_read_addresses(&self) -> &[usize] {
        &self.unresolved_reads
    }

    pub(super) fn active_unresolved_read_addresses(&self) -> &[usize] {
        &self.active_unresolved_reads
    }

    pub(super) fn active_unresolved_role_hits(&self) -> [(&'static str, usize); 7] {
        [
            ("Work", self.active_unresolved_role_hits[0]),
            ("MAX", self.active_unresolved_role_hits[1]),
            ("CROSS", self.active_unresolved_role_hits[2]),
            ("Map0", self.active_unresolved_role_hits[3]),
            ("Map1", self.active_unresolved_role_hits[4]),
            ("DAA", self.active_unresolved_role_hits[5]),
            ("Score", self.active_unresolved_role_hits[6]),
        ]
    }

    pub(super) fn active_unresolved_by_owner(&self) -> Vec<(usize, usize)> {
        let mut owners = BTreeMap::new();
        for &address in &self.active_unresolved_reads {
            *owners.entry(address / WIDTH).or_insert(0) += 1;
        }
        let mut counts = owners.into_iter().collect::<Vec<_>>();
        counts.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
        counts
    }

    pub(super) fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub(super) fn term_counts(&self) -> [(&'static str, usize); 7] {
        [
            ("Work", self.residual_census.term_counts[0]),
            ("MAX", self.residual_census.term_counts[1]),
            ("CROSS", self.residual_census.term_counts[2]),
            ("Map0", self.residual_census.term_counts[3]),
            ("Map1", self.residual_census.term_counts[4]),
            ("DAA", self.residual_census.term_counts[5]),
            ("Score", self.residual_census.term_counts[6]),
        ]
    }

    pub(super) fn active_x_count(&self) -> usize {
        self.residual_census.active_x_count
    }

    pub(super) fn evaluated_role_row_count(&self) -> usize {
        self.residual_census.evaluated_role_row_count
    }

    pub(super) fn work_row_count(&self) -> usize {
        self.residual_census.work_row_count
    }

    pub(super) fn cross_row_count(&self) -> usize {
        self.residual_census.cross_row_count
    }

    pub(super) fn missing_row19_claims(&self) -> Vec<(&'static str, usize)> {
        self.residual_census
            .missing_row19_claims
            .iter()
            .map(|(role, row)| (role.name(), *row))
            .collect()
    }
}

fn roster_digest(
    root: [u8; 32],
    total: [u8; 28],
    frame: [u8; 32],
    rows: &BTreeMap<usize, RowAuthor>,
    cells: &BTreeMap<usize, XClaim>,
    groups: &[TermGroup<'_>],
) -> [u8; 32] {
    let mut hasher = Blake2b::<U32>::new();
    hasher.update(b"H21-COMMON-ROSTER-DIAGNOSTIC-PARTIAL-V4\0");
    hasher.update(root);
    hasher.update(total);
    hasher.update(frame);
    hasher.update((rows.len() as u64).to_le_bytes());
    for (row, author) in rows {
        hasher.update((*row as u64).to_le_bytes());
        hasher.update([match author {
            RowAuthor::Carry => 0,
            RowAuthor::Daa => 1,
            RowAuthor::Score => 2,
        }]);
    }
    hasher.update((cells.len() as u64).to_le_bytes());
    for (address, claim) in cells {
        hasher.update((*address as u64).to_le_bytes());
        hasher.update(if claim.value.is_one() { [1] } else { [0] });
        hasher.update([match claim.writer {
            None => 0,
            Some(XAuthor::Carry) => 1,
            Some(XAuthor::DaaBank(index)) => 2 + index as u8,
            Some(XAuthor::Score) => 6,
            Some(XAuthor::ScoreUpper2) => 7,
            Some(XAuthor::ScoreSummary0) => 8,
            Some(XAuthor::ScoreSummary1) => 9,
            Some(XAuthor::MaxLookahead0) => 0x20,
            Some(XAuthor::MaxLookahead1) => 0x21,
            Some(XAuthor::HeaderSerializer) => 0x22,
        }]);
    }
    hasher.update((groups.len() as u64).to_le_bytes());
    for group in groups {
        hasher.update([group.role.index() as u8]);
        hasher.update((group.terms.len() as u64).to_le_bytes());
        for term in &group.terms {
            hasher.update((term.row as u64).to_le_bytes());
            hasher.update((term.gate.left as u64).to_le_bytes());
            hasher.update((term.gate.right as u64).to_le_bytes());
            for coefficient in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
                hasher.update(coefficient.into_bigint().to_bytes_le());
            }
        }
    }
    hasher.finalize().into()
}

/// Merge the already-staged producers into one value-bearing diagnostic
/// census. All source authentication remains with the producers and caller.
pub(super) fn stage_common_roster(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    frame_digest: [u8; 32],
    carry: &CarryMapExport,
    daa: &NativeDaaStage,
    score: &ScoreCapValueProjection,
    max_lookahead: &MaxPatch,
    expected_bindings: [Binding; 2],
) -> Result<CommonRoster, String> {
    validate_native_plan_input(plan, prefix)?;
    let parent = carry.parent();
    let root = prefix.root();
    let total = prefix.total_be28();
    if plan.headers() != HEADERS
        || plan.slot_log() != SLOT_LOG
        || plan.slots() != OWNER_LIMIT
        || prefix.header_count() != HEADERS as usize
        || parent.headers() != HEADERS as usize
        || parent.slot_log() != SLOT_LOG
        || parent.root() != root
        || parent.total() != total
        || parent.profile() != prefix.profile()
        || plan.descriptor().root != root
        || plan.work_profile().total_be28 != total
    {
        return Err("c154 common parent H21 root/total/profile/geometry mismatch".into());
    }
    if daa.owner() != DAA_OWNER as u64
        || daa.parent_root() != root
        || daa.parent_total_be28() != total
    {
        return Err("c154 DAA owner/parent binding mismatch".into());
    }
    if score.owner() != SCORE_OWNER || score.bindings() != &expected_bindings {
        return Err("c154 Score owner/binding mismatch".into());
    }
    for (index, binding) in expected_bindings.iter().enumerate() {
        if binding.n != SCORE_CUTS[index] || binding.h != SLOT_LOG || binding.parent_root.is_some()
        {
            return Err("c154 Score binding geometry/rootless requirement".into());
        }
    }
    let sources = score.sources();
    if sources[0].frame != frame_digest
        || sources[1].frame != frame_digest
        || sources[0].cut != SCORE_CUTS[0]
        || sources[1].cut != SCORE_CUTS[1]
        || sources.iter().any(|source| source.parent_root.is_some())
    {
        return Err("c154 Score frame/cut/rootless source mismatch".into());
    }

    let mut rows = BTreeMap::new();
    for (&row, writer) in carry.native_row_claims() {
        if row / ROW_WIDTH != CARRY_OWNER
            || !matches!(
                writer,
                RowWriter::Header
                    | RowWriter::Daa(_)
                    | RowWriter::Scheduled(_)
                    | RowWriter::Relocated(_)
            )
        {
            return Err("c154 carry ROW owner/claim extent mismatch".into());
        }
        insert_row(&mut rows, row, RowAuthor::Carry)?;
    }

    let placed_daa = daa.placed_row_terms(plan)?;
    insert_placed_daa_rows(&mut rows, &placed_daa)?;

    for score_row in score.rows() {
        if score_row.term.row / ROW_WIDTH != SCORE_OWNER {
            return Err("c154 Score ROW owner extent mismatch".into());
        }
        insert_row(&mut rows, score_row.term.row, RowAuthor::Score)?;
    }

    let map1_terms = required_map1_terms(carry.map1_terms())?;
    let groups = vec![
        TermGroup::from_slice(TermRole::Work, carry.work_terms()),
        TermGroup {
            role: TermRole::Max,
            terms: carry.max_terms().iter().map(|(_, term)| term).collect(),
        },
        TermGroup::from_slice(TermRole::Cross, carry.cross_terms()),
        TermGroup::from_slice(TermRole::Map0, carry.map0_terms()),
        TermGroup::from_slice(TermRole::Map1, map1_terms),
        TermGroup {
            role: TermRole::Daa,
            terms: placed_daa.iter().collect(),
        },
        TermGroup {
            role: TermRole::Score,
            terms: score.rows().iter().map(|row| &row.term).collect(),
        },
    ];
    let active = active_x_addresses(&groups);

    let mut cells = BTreeMap::new();
    for claim in carry.selected_x_claims() {
        let role = match claim.role {
            SelectedXRole::Writer => XRole::Write(XAuthor::Carry),
            SelectedXRole::ImportedRead => XRole::Read,
        };
        insert_x(&mut cells, claim.address, claim.value, role)?;
    }

    insert_max_lookahead_writers(&mut cells, &max_lookahead.snapshot(), &active)?;

    if daa.bank_patches().len() != BANKS.len() {
        return Err("c154 DAA bank patch count mismatch".into());
    }
    for (index, ((range, packed), (start, end))) in
        daa.bank_patches().iter().zip(BANKS.iter()).enumerate()
    {
        if range.start != *start
            || range.end != *end
            || range.start >= range.end
            || range.end > WIDTH
            || range.start % 8 != 0
            || range.end % 8 != 0
            || packed.len() != (range.end - range.start) / 8
        {
            return Err("c154 DAA bank patch extent/order mismatch".into());
        }
        let owner_base = DAA_OWNER
            .checked_mul(WIDTH)
            .ok_or("c154 DAA X owner base overflow")?;
        for bit in range.clone() {
            let value = Fr::from(u64::from(
                (packed[(bit - range.start) / 8] >> ((bit - range.start) % 8)) & 1,
            ));
            insert_x(
                &mut cells,
                owner_base + bit,
                value,
                XRole::Write(XAuthor::DaaBank(index)),
            )?;
        }
    }

    if daa.external_values().len() != CALLBACK_COUNT {
        return Err("c154 DAA callback value count mismatch".into());
    }
    for (&address, &value) in daa.external_values() {
        if address / WIDTH == DAA_OWNER {
            return Err("c154 DAA callback import is owner-local".into());
        }
        insert_x(&mut cells, address, Fr::from(u64::from(value)), XRole::Read)?;
    }
    // placed_daa came from NativeDaaStage::placed_row_terms, which checks the
    // full source-term multiset and RowPlan placement. This join only binds
    // the retained typed source->target records to those already placed terms.
    insert_daa_serializer_writers(
        &mut cells,
        &active,
        &placed_daa,
        daa.serializer_import_values(),
        daa.serializer_import_targets(),
        daa.external_values(),
    )?;

    let score_claim_ranges = score_global_x_claim_ranges(score)?;
    let projection_cells = score
        .cells()
        .iter()
        .map(|cell| (cell.address(), cell.value(), cell.writer()))
        .collect::<Vec<_>>();
    insert_score_ancestor_writers(&mut cells, &projection_cells, &active)?;
    for cell in score.cells() {
        let address = cell.address();
        let owner = address / WIDTH;
        if owner >= OWNER_LIMIT {
            return Err("c154 Score X address outside owner extent".into());
        }
        let covering = score_claim_ranges
            .iter()
            .filter(|range| range.contains(&address))
            .count();
        if covering > 1 {
            return Err("c154 overlapping Score X writer claims".into());
        }
        let role = if covering == 1 {
            XRole::Write(XAuthor::Score)
        } else {
            XRole::Read
        };
        insert_x(&mut cells, address, cell.value(), role)?;
    }

    close_active_x_values(&mut cells, &active, daa)?;
    let residual_census = evaluate_role_residuals(&groups, &cells, &rows, active.len())?;

    let unresolved_reads = cells
        .iter()
        .filter_map(|(address, claim)| claim.writer.is_none().then_some(*address))
        .collect::<Vec<_>>();
    let active_unresolved_reads = unresolved_reads
        .iter()
        .copied()
        .filter(|address| active.contains(address))
        .collect::<Vec<_>>();
    let active_unresolved_set = active_unresolved_reads.iter().copied().collect::<BTreeSet<_>>();
    let mut active_unresolved_role_hits = [0; 7];
    for group in &groups {
        let role_active = active_x_addresses(std::slice::from_ref(group));
        active_unresolved_role_hits[group.role.index()] =
            role_active.intersection(&active_unresolved_set).count();
    }
    let digest = roster_digest(root, total, frame_digest, &rows, &cells, &groups);
    Ok(CommonRoster {
        parent_root: root,
        parent_total_be28: total,
        frame_digest,
        rows,
        cells,
        unresolved_reads,
        active_unresolved_reads,
        active_unresolved_role_hits,
        residual_census,
        digest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        c146_phase1_session::Session, daa_history_roster::DaaHistoryRoster,
        h21_scheduled_max_cap::Plan as ScheduledPlan, header_daa_row_placement::RowPlan,
        score_prefix_r_anchor::project_local_score_cap_values,
        work_tree_history_plan::WorkTreeHistoryPlan,
    };

    fn max_lookahead_fixture() -> Vec<MaxPatchSnapshot> {
        (0..2)
            .map(|context| {
                (
                    MAX_LOOKAHEAD_OWNER,
                    MAX_LOOKAHEAD_LOCAL_STARTS[context],
                    MaxWriter::Max {
                        context,
                        end: MAX_LOOKAHEAD_END,
                    },
                    vec![Fr::zero(); 673],
                )
            })
            .collect()
    }

    fn max_lookahead_active() -> BTreeSet<usize> {
        MAX_LOOKAHEAD_GLOBAL_X_STARTS
            .iter()
            .flat_map(|start| (*start..*start + MAX_LOOKAHEAD_VALUE_BITS))
            .collect()
    }

    fn daa_serializer_fixture() -> (
        Vec<crate::sparse::Term>,
        BTreeSet<usize>,
        BTreeMap<usize, bool>,
        BTreeMap<usize, usize>,
        BTreeMap<usize, bool>,
    ) {
        let mut terms = Vec::with_capacity(DAA_SERIALIZER_IMPORT_COUNT);
        let mut active = BTreeSet::new();
        let mut source_values = BTreeMap::new();
        let mut source_targets = BTreeMap::new();
        let mut callback_values = BTreeMap::new();
        for index in 0..DAA_SERIALIZER_IMPORT_COUNT {
            let source = (DAA_OWNER - 1) * WIDTH + index;
            let target = DAA_OWNER * WIDTH + 8_000 + index;
            let value = index % 2 == 0;
            terms.push(crate::sparse::Term {
                row: DAA_OWNER * ROW_WIDTH + index,
                gate: crate::gkr::Gate {
                    left: source,
                    right: target,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: -Fr::one(),
                    c3: Fr::zero(),
                },
            });
            active.insert(source);
            active.insert(target);
            source_values.insert(source, value);
            source_targets.insert(source, target);
            callback_values.insert(source, value);
        }
        for index in 0..(CALLBACK_COUNT - DAA_SERIALIZER_IMPORT_COUNT) {
            let address = (DAA_OWNER - 2) * WIDTH + 10_000 + index;
            callback_values.insert(address, index % 2 == 0);
        }
        (terms, active, source_values, source_targets, callback_values)
    }

    #[test]
    fn daa_serializer_writer_join_accepts_exact_foreign_census_without_frame() {
        let (terms, active, source_values, source_targets, callback_values) =
            daa_serializer_fixture();
        let mut cells = BTreeMap::new();
        for (&address, &value) in &callback_values {
            insert_x(&mut cells, address, Fr::from(u64::from(value)), XRole::Read).unwrap();
        }
        insert_daa_serializer_writers(
            &mut cells,
            &active,
            &terms,
            &source_values,
            &source_targets,
            &callback_values,
        )
        .unwrap();
        assert_eq!(source_values.len(), DAA_SERIALIZER_IMPORT_COUNT);
        assert_eq!(
            cells
                .values()
                .filter(|claim| claim.writer == Some(XAuthor::HeaderSerializer))
                .count(),
            DAA_SERIALIZER_IMPORT_COUNT
        );
        for (&address, &value) in &source_values {
            assert_eq!(
                cells[&address],
                XClaim {
                    value: Fr::from(u64::from(value)),
                    writer: Some(XAuthor::HeaderSerializer),
                }
            );
        }
        assert_eq!(callback_values.len(), CALLBACK_COUNT);
        assert_eq!(callback_values.len() - source_values.len(), 288);
        for address in callback_values.keys() {
            if !source_values.contains_key(address) {
                assert_eq!(cells[address].writer, None);
            }
        }
    }

    #[test]
    fn daa_serializer_writer_join_rejects_isolated_source_mutants() {
        let (terms, active, source_values, source_targets, callback_values) =
            daa_serializer_fixture();
        let first = *source_values.keys().next().unwrap();

        let mut missing = source_values.clone();
        missing.remove(&first);
        assert!(insert_daa_serializer_writers(
            &mut BTreeMap::new(),
            &active,
            &terms,
            &missing,
            &source_targets,
            &callback_values,
        )
        .is_err());

        let mut extra = source_values.clone();
        extra.remove(&first);
        extra.insert((DAA_OWNER - 2) * WIDTH + 9_000, false);
        assert!(insert_daa_serializer_writers(
            &mut BTreeMap::new(),
            &active,
            &terms,
            &extra,
            &source_targets,
            &callback_values,
        )
        .is_err());

        let mut wrong_target = source_targets.clone();
        wrong_target.insert(first, wrong_target[&first] + 1);
        assert!(insert_daa_serializer_writers(
            &mut BTreeMap::new(),
            &active,
            &terms,
            &source_values,
            &wrong_target,
            &callback_values,
        )
        .is_err());

        let mut wrong_term_target = terms.clone();
        wrong_term_target[0].gate.right += DAA_SERIALIZER_IMPORT_COUNT;
        let error = insert_daa_serializer_writers(
            &mut BTreeMap::new(),
            &active,
            &wrong_term_target,
            &source_values,
            &source_targets,
            &callback_values,
        )
        .unwrap_err();
        assert!(error.contains("source/target records"));

        let mut duplicate = terms.clone();
        duplicate.push(terms[0].clone());
        assert!(insert_daa_serializer_writers(
            &mut BTreeMap::new(),
            &active,
            &duplicate,
            &source_values,
            &source_targets,
            &callback_values,
        )
        .is_err());

        let mut wrong_value = callback_values.clone();
        wrong_value.insert(first, !wrong_value[&first]);
        assert!(insert_daa_serializer_writers(
            &mut BTreeMap::new(),
            &active,
            &terms,
            &source_values,
            &source_targets,
            &wrong_value,
        )
        .is_err());

        let mut inactive = active.clone();
        inactive.remove(&first);
        assert!(insert_daa_serializer_writers(
            &mut BTreeMap::new(),
            &inactive,
            &terms,
            &source_values,
            &source_targets,
            &callback_values,
        )
        .is_err());

        let mut collision = BTreeMap::new();
        insert_x(
            &mut collision,
            first,
            Fr::from(u64::from(source_values[&first])),
            XRole::Write(XAuthor::Carry),
        )
        .unwrap();
        assert!(insert_daa_serializer_writers(
            &mut collision,
            &active,
            &terms,
            &source_values,
            &source_targets,
            &callback_values,
        )
        .is_err());
    }

    #[test]
    fn max_lookahead_source_writers_join_without_a_frame() {
        let spans = max_lookahead_fixture();
        let active = max_lookahead_active();
        let mut cells = BTreeMap::new();
        insert_max_lookahead_writers(&mut cells, &spans, &active).unwrap();
        assert_eq!(cells.len(), 448);
        for context in 0..2 {
            let start = MAX_LOOKAHEAD_GLOBAL_X_STARTS[context];
            assert_eq!(cells[&start].writer, Some(max_lookahead_author(context).unwrap()));
            assert_eq!(cells[&(start + 223)].writer, Some(max_lookahead_author(context).unwrap()));
            assert!(!cells.contains_key(&(start + 224)));
        }
    }

    #[test]
    fn max_lookahead_source_writer_join_rejects_bad_patch_metadata_and_values() {
        let valid = max_lookahead_fixture();
        let active = max_lookahead_active();

        let mut missing = valid.clone();
        missing.pop();
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &missing, &active).is_err());

        let mut wrong_owner = valid.clone();
        wrong_owner[0].0 += 1;
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &wrong_owner, &active).is_err());

        let mut wrong_tag = valid.clone();
        wrong_tag[0].2 = MaxWriter::Max {
            context: 1,
            end: MAX_LOOKAHEAD_END,
        };
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &wrong_tag, &active).is_err());

        let mut wrong_end = valid.clone();
        wrong_end[1].2 = MaxWriter::Max {
            context: 1,
            end: MAX_LOOKAHEAD_END - 1,
        };
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &wrong_end, &active).is_err());

        let mut wrong_span = valid.clone();
        wrong_span[1].1 += 1;
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &wrong_span, &active).is_err());

        let mut wrong_length = valid.clone();
        wrong_length[0].3.pop();
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &wrong_length, &active).is_err());

        let mut extra = valid.clone();
        extra.push(valid[0].clone());
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &extra, &active).is_err());

        let mut non_boolean = valid;
        non_boolean[1].3[223] = Fr::from(2u64);
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &non_boolean, &active).is_err());

        let mut inactive = active.clone();
        inactive.remove(&MAX_LOOKAHEAD_GLOBAL_X_STARTS[1]);
        assert!(insert_max_lookahead_writers(&mut BTreeMap::new(), &max_lookahead_fixture(), &inactive).is_err());
    }

    #[test]
    fn max_lookahead_source_writer_join_preserves_x_collision_rules() {
        let spans = max_lookahead_fixture();
        let active = max_lookahead_active();
        let first = MAX_LOOKAHEAD_GLOBAL_X_STARTS[0];

        let mut equal_read = BTreeMap::new();
        insert_x(&mut equal_read, first, Fr::zero(), XRole::Read).unwrap();
        insert_max_lookahead_writers(&mut equal_read, &spans, &active).unwrap();
        assert_eq!(equal_read[&first].writer, Some(XAuthor::MaxLookahead0));

        let mut unequal_read = BTreeMap::new();
        insert_x(&mut unequal_read, first, Fr::one(), XRole::Read).unwrap();
        assert!(insert_max_lookahead_writers(&mut unequal_read, &spans, &active).is_err());

        let mut duplicate_equal_writer = BTreeMap::new();
        insert_max_lookahead_writers(&mut duplicate_equal_writer, &spans, &active).unwrap();
        assert!(insert_max_lookahead_writers(&mut duplicate_equal_writer, &spans, &active).is_err());
    }

    #[test]
    fn x_claim_primitive_rejects_duplicate_equal_writer() {
        let mut cells = BTreeMap::new();
        insert_x(&mut cells, 7, Fr::one(), XRole::Write(XAuthor::Carry)).unwrap();
        assert!(insert_x(&mut cells, 7, Fr::one(), XRole::Write(XAuthor::Carry)).is_err());
    }

    #[test]
    fn x_claim_primitive_rejects_unequal_read_write() {
        let mut cells = BTreeMap::new();
        insert_x(&mut cells, 7, Fr::zero(), XRole::Read).unwrap();
        assert!(insert_x(&mut cells, 7, Fr::one(), XRole::Write(XAuthor::DaaBank(0))).is_err());
    }

    #[test]
    fn x_claim_primitive_allows_equal_read_write() {
        let mut cells = BTreeMap::new();
        insert_x(&mut cells, 7, Fr::one(), XRole::Read).unwrap();
        insert_x(&mut cells, 7, Fr::one(), XRole::Write(XAuthor::Score)).unwrap();
        assert_eq!(cells[&7].writer, Some(XAuthor::Score));
    }

    #[test]
    fn x_claim_primitive_rejects_equal_cross_role_writers() {
        let mut cells = BTreeMap::new();
        insert_x(&mut cells, 7, Fr::one(), XRole::Write(XAuthor::Carry)).unwrap();
        assert!(insert_x(&mut cells, 7, Fr::one(), XRole::Write(XAuthor::Score)).is_err());
    }

    #[test]
    fn row_primitive_rejects_conflicting_author() {
        let mut rows = BTreeMap::new();
        insert_row(&mut rows, 11, RowAuthor::Carry).unwrap();
        assert!(insert_row(&mut rows, 11, RowAuthor::Score).is_err());
    }

    #[test]
    fn required_map1_rejects_absent_and_empty_slices() {
        assert!(required_map1_terms(None).is_err());
        assert!(required_map1_terms(Some(&[])).is_err());
        let term = crate::sparse::Term {
            row: 0,
            gate: crate::gkr::Gate {
                left: 0,
                right: 0,
                c0: Fr::zero(),
                c1: Fr::zero(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        };
        let accepted = required_map1_terms(Some(std::slice::from_ref(&term))).unwrap();
        assert_eq!(accepted.len(), 1);
        assert_eq!(accepted[0].row, term.row);
    }

    #[test]
    fn work_and_cross_residual_rows_stay_outside_row19_embedding() {
        let work = crate::sparse::Term {
            row: CARRY_OWNER * WORK_ROW_STRIDE + 7,
            gate: crate::gkr::Gate {
                left: 0,
                right: 0,
                c0: Fr::zero(),
                c1: Fr::zero(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        };
        let cross = crate::sparse::Term {
            row: CROSS_OWNER * CROSS_ROW_STRIDE + 11,
            gate: work.gate.clone(),
        };
        let groups = [
            TermGroup::from_slice(TermRole::Work, std::slice::from_ref(&work)),
            TermGroup::from_slice(TermRole::Cross, std::slice::from_ref(&cross)),
        ];
        let rows = BTreeMap::new();
        let report = evaluate_role_residuals(&groups, &BTreeMap::new(), &rows, 0).unwrap();
        assert_eq!(report.evaluated_role_row_count, 2);
        assert_eq!(report.work_row_count, 1);
        assert_eq!(report.cross_row_count, 1);
        assert!(report.missing_row19_claims.is_empty());
    }

    #[test]
    fn score_projection_ranges_are_global_and_cover_claimed_cells() {
        let (session, caller) = Session::fixture().unwrap();
        let (plan, staged) = session.stage_for_local_ledger_join(&caller).unwrap();
        let projection = project_local_score_cap_values(&plan, &staged).unwrap();
        let ranges = score_global_x_claim_ranges(&projection).unwrap();
        assert!(!ranges.is_empty());
        assert!(ranges.iter().all(|range| {
            range.start / WIDTH == SCORE_OWNER
                && (range.end - 1) / WIDTH == SCORE_OWNER
                && range.start >= SCORE_OWNER * WIDTH
                && range.end <= (SCORE_OWNER + 1) * WIDTH
        }));
        let cells = projection
            .cells()
            .iter()
            .map(|cell| cell.address())
            .collect::<std::collections::BTreeSet<_>>();
        for range in &ranges {
            assert!(range.clone().all(|address| cells.contains(&address)));
        }
    }

    #[test]
    fn c161_max_and_score_cap_consume_the_same_source_x_cell() {
        // This uses the c146 no-frame fixture. The term producers and global
        // coordinates are real; the Boolean comes from a deterministic
        // synthetic D stream and does not establish native H21 custody.
        const SHARED_X: usize = 844_670 * WIDTH + 999_424;
        const MAX_ROW: usize = 844_670 * ROW_WIDTH + 356_632;
        const SCORE_CAP_ROW: usize = 845_759 * ROW_WIDTH + 359_361;

        let (session, caller) = Session::fixture().unwrap();
        let (score_plan, staged) = session.stage_for_local_ledger_join(&caller).unwrap();
        let projection = project_local_score_cap_values(&score_plan, &staged).unwrap();

        let mut max_terms = Vec::new();
        ScheduledPlan::new()
            .visit_owner(844_670, |writer, term| {
                if writer
                    == (MaxWriter::Max {
                        context: 0,
                        end: 844_672,
                    })
                {
                    max_terms.push(term);
                }
                Ok(())
            })
            .unwrap();
        let max_term = max_terms
            .iter()
            .find(|term| {
                term.row == MAX_ROW
                    && term.gate.left == SHARED_X
                    && term.gate.right == SHARED_X
            })
            .expect("context-0 MAX bitness term at the shared X address");

        let score_relation = crate::score_prefix_r_anchor::ScoreCapRelation::Cap(
            MaxWriter::Cap {
                context: 0,
                origin: 845_760,
            },
        );
        let score_row_terms = projection
            .rows()
            .iter()
            .filter(|row| row.relation == score_relation && row.term.row == SCORE_CAP_ROW)
            .map(|row| &row.term)
            .collect::<Vec<_>>();
        assert_eq!(score_row_terms.len(), 2);
        assert!(score_row_terms.iter().any(|term| {
            term.gate.left == SHARED_X || term.gate.right == SHARED_X
        }));

        let cells = projection
            .cells()
            .iter()
            .map(|cell| (cell.address(), cell.value()))
            .collect::<BTreeMap<_, _>>();
        let shared_value = cells[&SHARED_X];
        assert!(shared_value.is_zero() || shared_value.is_one());
        assert_eq!(
            projection
                .cells()
                .iter()
                .find(|cell| cell.address() == SHARED_X)
                .unwrap()
                .writer(),
            crate::score_prefix_r_anchor::ScoreCapCellWriter::Scheduled(MaxWriter::Max {
                context: 0,
                end: 844_672,
            })
        );

        let gate_value = |term: &crate::sparse::Term, values: &BTreeMap<usize, Fr>| {
            let gate = &term.gate;
            let read = |address| {
                if address == 0 {
                    Some(Fr::zero())
                } else {
                    values.get(&address).copied()
                }
            };
            let left = read(gate.left)?;
            let right = read(gate.right)?;
            Some(gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right)
        };
        assert_eq!(gate_value(max_term, &cells), Some(Fr::zero()));
        assert_eq!(
            score_row_terms
                .iter()
                .map(|term| gate_value(term, &cells).expect("complete Score Cap row inputs"))
                .sum::<Fr>(),
            Fr::zero()
        );

        // Isolate a wrong source Boolean: MAX remains a Boolean, while the
        // Score Cap import row detects that it no longer matches its local bit.
        let mut wrong_source = cells;
        wrong_source.insert(SHARED_X, Fr::one() - shared_value);
        assert_ne!(
            score_row_terms
                .iter()
                .map(|term| gate_value(term, &wrong_source).expect("complete Score Cap row inputs"))
                .sum::<Fr>(),
            Fr::zero()
        );

        let mut missing_source = wrong_source.clone();
        missing_source.remove(&SHARED_X);
        assert!(score_row_terms
            .iter()
            .any(|term| gate_value(term, &missing_source).is_none()));
    }

    #[test]
    fn score_projection_promotes_exact_active_ancestor_writer_census() {
        let (session, caller) = Session::fixture().unwrap();
        let (plan, staged) = session.stage_for_local_ledger_join(&caller).unwrap();
        let projection = project_local_score_cap_values(&plan, &staged).unwrap();
        let projected = projection
            .cells()
            .iter()
            .map(|cell| (cell.address(), cell.value(), cell.writer()))
            .collect::<Vec<_>>();
        let expected = score_ancestor_writer_claims();
        assert_eq!(expected.len(), 674);
        let expected_active = expected
            .iter()
            .map(|(address, _)| *address)
            .collect::<BTreeSet<_>>();
        let score_group = TermGroup {
            role: TermRole::Score,
            terms: projection.rows().iter().map(|row| &row.term).collect(),
        };
        let active = active_x_addresses(std::slice::from_ref(&score_group));
        let active_ancestors = active
            .iter()
            .copied()
            .filter(|address| address / WIDTH == SCORE_BOUNDARY_OWNER)
            .collect::<BTreeSet<_>>();
        assert_eq!(active_ancestors, expected_active);

        let mut cells = BTreeMap::new();
        insert_score_ancestor_writers(&mut cells, &projected, &active).unwrap();
        assert_eq!(cells.len(), 674);
        assert_eq!(
            cells.values().filter(|claim| claim.writer == Some(XAuthor::ScoreUpper2)).count(),
            224
        );
        assert_eq!(
            cells.values().filter(|claim| claim.writer == Some(XAuthor::ScoreSummary0)).count(),
            225
        );
        assert_eq!(
            cells.values().filter(|claim| claim.writer == Some(XAuthor::ScoreSummary1)).count(),
            225
        );

        let mut missing = projected.clone();
        missing.retain(|(address, _, _)| *address != expected[0].0);
        assert!(insert_score_ancestor_writers(&mut BTreeMap::new(), &missing, &active).is_err());

        let mut wrong_context = projected.clone();
        let first_summary = expected
            .iter()
            .find(|(_, author)| *author == XAuthor::ScoreSummary0)
            .unwrap()
            .0;
        let cell = wrong_context
            .iter_mut()
            .find(|(address, _, _)| *address == first_summary)
            .unwrap();
        cell.2 = ScoreCapCellWriter::Summary(1);
        assert!(insert_score_ancestor_writers(
            &mut BTreeMap::new(),
            &wrong_context,
            &active
        )
        .is_err());

        let mut extra = projected.clone();
        extra.push((expected[0].0 + 224, Fr::zero(), ScoreCapCellWriter::Upper(2)));
        assert!(insert_score_ancestor_writers(&mut BTreeMap::new(), &extra, &active).is_err());

        let mut non_boolean = projected.clone();
        non_boolean
            .iter_mut()
            .find(|(address, _, _)| *address == expected[0].0)
            .unwrap()
            .1 = Fr::from(2u64);
        assert!(insert_score_ancestor_writers(
            &mut BTreeMap::new(),
            &non_boolean,
            &active
        )
        .is_err());

        let mut duplicate_writer = BTreeMap::new();
        insert_x(
            &mut duplicate_writer,
            expected[0].0,
            Fr::zero(),
            XRole::Write(XAuthor::Carry),
        )
        .unwrap();
        assert!(insert_score_ancestor_writers(&mut duplicate_writer, &projected, &active).is_err());
    }

    #[test]
    fn actual_daa_placement_relocates_and_inserts_placed_terms() {
        let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x54; 32], [0x55; 28]).unwrap();
        let roster = DaaHistoryRoster::compile(&plan).unwrap();
        let schedule = ScheduledPlan::new();
        let row_plan = RowPlan::new(&roster, &schedule).unwrap();
        let mut raw = None;
        roster
            .visit_owner_terms(DAA_OWNER as u64, |term| {
                if raw.is_none() {
                    raw = Some(term);
                }
                Ok(())
            })
            .unwrap();
        let raw = raw.expect("mature EIP owner must emit DAA source terms");
        let (_, placed) = row_plan
            .place_daa_source_term(DAA_OWNER, raw.clone())
            .unwrap();
        assert_ne!(raw.row, placed.row, "fixture term exercises ROW relocation");
        let mut rows = BTreeMap::new();
        insert_placed_daa_rows(&mut rows, &[placed.clone()]).unwrap();
        assert_eq!(rows.get(&placed.row), Some(&RowAuthor::Daa));
        assert!(!rows.contains_key(&raw.row));
    }

    #[test]
    fn active_x_gate_passes_then_single_bit_mutant_fails_by_role() {
        let work_row = CARRY_OWNER * WORK_ROW_STRIDE + 77;
        let zero_address_term = crate::sparse::Term {
            row: work_row,
            gate: crate::gkr::Gate {
                left: 0,
                right: 9,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        };
        let active_term = crate::sparse::Term {
            row: work_row,
            gate: crate::gkr::Gate {
                left: 2,
                right: 0,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        };
        let groups = [TermGroup {
            role: TermRole::Work,
            terms: vec![&zero_address_term, &active_term],
        }];
        let active = active_x_addresses(&groups);
        assert_eq!(active, BTreeSet::from([2]));
        let mut cells = BTreeMap::new();
        insert_x(&mut cells, 2, Fr::zero(), XRole::Read).unwrap();
        let rows = BTreeMap::new();
        let report = evaluate_role_residuals(&groups, &cells, &rows, active.len()).unwrap();
        assert_eq!(report.active_x_count, 1);
        assert_eq!(report.evaluated_role_row_count, 1);
        assert_eq!(report.work_row_count, 1);
        assert_eq!(report.term_counts[TermRole::Work.index()], 2);
        assert!(report.missing_row19_claims.is_empty());

        cells.get_mut(&2).unwrap().value = Fr::one();
        let error = evaluate_role_residuals(&groups, &cells, &rows, active.len()).unwrap_err();
        assert!(error.contains("Work ROW residual is nonzero"), "{error}");
    }
}

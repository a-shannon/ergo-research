//! Scoped, source-owned q9 Map / Work / HEADER nBits diagnostic.
//! This is not a global ROW/X merger or a proof admission path.

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;
use serde::Serialize;

use crate::{
    packed_owner_assembly::{NativeOwnerProducer, NativePackedRow, NativePrefix},
    q9_selected_raw_fixture::CheckedQ9RawFixture,
    selected_raw_map_source::{NativeQ9Binding, NativeQ9MapBatch, SelectedRawMapSource},
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self as layout, WIDTH},
    work_tree_wiring::Mapping,
    work_tree_work::LOCAL_ROW_WIDTH,
};

const MAP_OWNER: usize = 10_175;
const HEADER_OWNER: usize = MAP_OWNER + 1;
const ROW_WIDTH: usize = 1 << 19;
const MAP_ROWS: std::ops::Range<usize> = 477_074..487_421;
const WORK_ROWS: std::ops::Range<usize> = 520_726..522_774;
const ALIAS_ROWS: std::ops::Range<usize> = 522_774..522_806;
const MAP_HELPER_LOCAL: std::ops::Range<usize> = 671_744..677_501;
const MAP_READS: usize = 2_592;
const MAP_HELPERS: usize = 5_757;
const MAP_TERMS: usize = 68_233;
const ALIAS_TERMS: usize = 32;
const WORK_CLAIMS: usize = 1_184;
const WORK_TERMS: usize = 3_265;
const WORK_ACTIVE_ROWS: usize = 1_435;
const ALIAS_NAME: &str = "header_to_leaf_raw_length_nbits_height";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BatchId {
    Work,
    Map,
    HeaderAlias,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Batch {
    id: BatchId,
    terms: Vec<Term>,
    claims: Vec<(usize, Fr)>,
    reads: Vec<(usize, Fr)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Candidate {
    batches: Vec<Batch>,
}

impl Candidate {
    fn batch(&self, id: BatchId) -> Result<&Batch, String> {
        self.batches
            .iter()
            .find(|batch| batch.id == id)
            .ok_or_else(|| format!("missing scoped batch {id:?}"))
    }

    #[cfg(test)]
    fn batch_mut(&mut self, id: BatchId) -> Result<&mut Batch, String> {
        self.batches
            .iter_mut()
            .find(|batch| batch.id == id)
            .ok_or_else(|| format!("missing scoped batch {id:?}"))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Destination {
    published: bool,
    cells: BTreeMap<usize, Fr>,
    rows: BTreeMap<usize, BatchId>,
}

impl Destination {
    fn nonempty() -> Self {
        Self {
            published: false,
            cells: BTreeMap::from([(1, Fr::zero())]),
            rows: BTreeMap::from([(0, BatchId::Work)]),
        }
    }

    fn publish(
        &mut self,
        candidate: &Candidate,
        expected: &Candidate,
    ) -> Result<ScopedCounts, String> {
        if self.published {
            return Err("duplicate scoped publication".into());
        }
        let inspected = inspect(candidate)?;
        if inspected.nonzero(BatchId::Work) != 0
            || inspected.nonzero(BatchId::Map) != 0
            || inspected.nonzero(BatchId::HeaderAlias) != 0
        {
            return Err("scoped residual is nonzero".into());
        }
        if candidate != expected {
            return Err("scoped source-owned term/claim/READ census".into());
        }
        if inspected
            .claims
            .keys()
            .any(|address| self.cells.contains_key(address))
        {
            return Err("destination X collision".into());
        }
        if inspected.rows.keys().any(|row| self.rows.contains_key(row)) {
            return Err("destination ROW collision".into());
        }
        let counts = ScopedCounts::from_candidate(candidate, &inspected)?;
        // All fallible validation precedes this single publication point.
        self.cells.extend(
            inspected
                .claims
                .into_iter()
                .map(|(address, (_, value))| (address, value)),
        );
        self.rows.extend(inspected.rows);
        self.published = true;
        Ok(counts)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) struct ScopedCounts {
    pub(crate) map_reads: usize,
    pub(crate) map_helpers: usize,
    pub(crate) map_terms: usize,
    pub(crate) map_rows: usize,
    pub(crate) work_claims: usize,
    pub(crate) work_terms: usize,
    pub(crate) work_rows: usize,
    pub(crate) header_nbits_claims: usize,
    pub(crate) header_alias_terms: usize,
    pub(crate) header_alias_rows: usize,
    pub(crate) total_claims: usize,
    pub(crate) total_rows: usize,
}

impl ScopedCounts {
    fn from_candidate(candidate: &Candidate, inspected: &Inspection) -> Result<Self, String> {
        let map = candidate.batch(BatchId::Map)?;
        let work = candidate.batch(BatchId::Work)?;
        let alias = candidate.batch(BatchId::HeaderAlias)?;
        let count_rows = |id| {
            inspected
                .rows
                .values()
                .filter(|&&owner| owner == id)
                .count()
        };
        let result = Self {
            map_reads: map.reads.len(),
            map_helpers: map.claims.len(),
            map_terms: map.terms.len(),
            map_rows: count_rows(BatchId::Map),
            work_claims: work.claims.len(),
            work_terms: work.terms.len(),
            work_rows: count_rows(BatchId::Work),
            header_nbits_claims: alias.claims.len(),
            header_alias_terms: alias.terms.len(),
            header_alias_rows: count_rows(BatchId::HeaderAlias),
            total_claims: inspected.claims.len(),
            total_rows: inspected.rows.len(),
        };
        if (result.map_reads, result.map_helpers, result.map_terms)
            != (MAP_READS, MAP_HELPERS, MAP_TERMS)
            || (result.work_claims, result.work_terms, result.work_rows)
                != (WORK_CLAIMS, WORK_TERMS, WORK_ACTIVE_ROWS)
            || result.header_nbits_claims != ALIAS_TERMS
            || result.header_alias_terms != ALIAS_TERMS
            || result.header_alias_rows != ALIAS_TERMS
            || result.total_claims != result.map_helpers + result.work_claims + ALIAS_TERMS
            || result.total_rows != result.map_rows + result.work_rows + ALIAS_TERMS
        {
            return Err("scoped H21 count contract".into());
        }
        Ok(result)
    }
}

struct Inspection {
    claims: BTreeMap<usize, (BatchId, Fr)>,
    rows: BTreeMap<usize, BatchId>,
    residuals: BTreeMap<BatchId, BTreeMap<usize, Fr>>,
}

impl Inspection {
    fn nonzero(&self, id: BatchId) -> usize {
        self.residuals.get(&id).map_or(0, |rows| {
            rows.values().filter(|value| !value.is_zero()).count()
        })
    }

    #[cfg(test)]
    fn nonzero_in(&self, id: BatchId, range: std::ops::Range<usize>) -> usize {
        self.residuals.get(&id).map_or(0, |rows| {
            rows.range(range)
                .filter(|(_, value)| !value.is_zero())
                .count()
        })
    }
}

fn active_left(term: &Term) -> bool {
    !term.gate.c1.is_zero() || !term.gate.c3.is_zero()
}

fn active_right(term: &Term) -> bool {
    !term.gate.c2.is_zero() || !term.gate.c3.is_zero()
}

fn row_range(id: BatchId) -> (usize, std::ops::Range<usize>) {
    match id {
        BatchId::Work => (MAP_OWNER, WORK_ROWS),
        BatchId::Map => (MAP_OWNER, MAP_ROWS),
        BatchId::HeaderAlias => (HEADER_OWNER, ALIAS_ROWS),
    }
}

fn claim_range(id: BatchId, local: usize) -> bool {
    match id {
        BatchId::Work => {
            (layout::ENDPOINT_BASE..layout::ENDPOINT_BASE + layout::ENDPOINT_WIDTH).contains(&local)
        }
        BatchId::Map => MAP_HELPER_LOCAL.contains(&local),
        BatchId::HeaderAlias => {
            (crate::header_hash::SERIALIZER_OFFSET..layout::ENDPOINT_BASE).contains(&local)
        }
    }
}

fn inspect(candidate: &Candidate) -> Result<Inspection, String> {
    let mut kinds = BTreeSet::new();
    let mut claims = BTreeMap::new();
    let mut reads = BTreeMap::new();
    let mut rows = BTreeMap::new();
    if candidate.batches.len() != 3 {
        return Err("scoped batch count".into());
    }
    for batch in &candidate.batches {
        if !kinds.insert(batch.id) {
            return Err("duplicate scoped batch".into());
        }
        let (owner, range) = row_range(batch.id);
        for &(address, value) in &batch.claims {
            if claims.insert(address, (batch.id, value)).is_some() {
                return Err("duplicate X writer, including equal value".into());
            }
            if address / WIDTH != owner || !claim_range(batch.id, address % WIDTH) {
                return Err("scoped X writer owner or lane".into());
            }
            if !value.is_zero() && !value.is_one() {
                return Err("scoped X claim is not a bit".into());
            }
        }
        if batch.id != BatchId::Map && !batch.reads.is_empty() {
            return Err("scoped READ outside Map batch".into());
        }
        for &(address, value) in &batch.reads {
            if reads.insert(address, value).is_some() {
                return Err("duplicate scoped READ".into());
            }
            if !value.is_zero() && !value.is_one() {
                return Err("scoped READ is not a bit".into());
            }
        }
        for term in &batch.terms {
            // A relation may have several monomials in one ROW, but two semantic
            // owners may not use that ROW even when their residuals agree.
            if rows
                .get(&term.row)
                .is_some_and(|previous| *previous != batch.id)
            {
                return Err("cross-writer ROW collision".into());
            }
            rows.insert(term.row, batch.id);
            if term.row / ROW_WIDTH != owner || !range.contains(&(term.row % ROW_WIDTH)) {
                return Err("scoped ROW owner or range".into());
            }
        }
    }
    if kinds.len() != 3 {
        return Err("missing scoped batch".into());
    }
    for (&address, &value) in &reads {
        if claims
            .get(&address)
            .is_some_and(|(_, claimed)| *claimed != value)
        {
            return Err("scoped READ disagrees with X writer".into());
        }
    }
    let lookup = |address: usize| -> Result<Fr, String> {
        if address == 0 {
            return Ok(Fr::zero());
        }
        claims
            .get(&address)
            .map(|(_, value)| *value)
            .or_else(|| reads.get(&address).copied())
            .ok_or_else(|| format!("missing active scoped X {address}"))
    };
    let mut residuals = BTreeMap::<BatchId, BTreeMap<usize, Fr>>::new();
    for batch in &candidate.batches {
        let sums = residuals.entry(batch.id).or_default();
        for term in &batch.terms {
            let gate = &term.gate;
            let left = if active_left(term) {
                lookup(gate.left)?
            } else {
                Fr::zero()
            };
            let right = if active_right(term) {
                lookup(gate.right)?
            } else {
                Fr::zero()
            };
            *sums.entry(term.row).or_insert(Fr::zero()) +=
                gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
        }
    }
    Ok(Inspection {
        claims,
        rows,
        residuals,
    })
}

fn packed_bit(row: &NativePackedRow, owner: usize, address: usize) -> Result<Fr, String> {
    if row.owner() != owner || address / WIDTH != owner || row.packed_bytes().len() != WIDTH / 8 {
        return Err("scoped native producer row or address".into());
    }
    let local = address % WIDTH;
    Ok(Fr::from(
        ((row.packed_bytes()[local / 8] >> (local % 8)) & 1) as u64,
    ))
}

fn source_work(
    parent: &WorkTreeHistoryPlan,
) -> Result<(Vec<Term>, BTreeSet<usize>, usize), String> {
    if parent.work_boundary().profile() != parent.work_profile()
        || MAP_OWNER >= parent.descriptor().genuine
    {
        return Err("scoped genuine Work profile".into());
    }
    let mut terms = Vec::new();
    parent
        .work_boundary()
        .emit_slot(MAP_OWNER, |term| terms.push(term))?;
    let groups = parent.work_boundary().groups();
    let expected_terms = groups
        .iter()
        .filter(|group| group.name != "padding_arithmetic_zero")
        .map(|group| group.term_count)
        .sum::<usize>();
    let expected_rows = groups
        .iter()
        .filter(|group| group.name != "padding_arithmetic_zero")
        .map(|group| group.rows.len())
        .sum::<usize>();
    if terms.len() != expected_terms
        || expected_terms != WORK_TERMS
        || expected_rows != WORK_ACTIVE_ROWS
        || expected_rows > WORK_ROWS.len()
    {
        return Err("scoped Work source term/ROW census".into());
    }
    let mut occupied = BTreeSet::new();
    let mut operands = BTreeSet::new();
    for term in &mut terms {
        let local = term
            .row
            .checked_sub(MAP_OWNER * LOCAL_ROW_WIDTH)
            .filter(|local| *local < LOCAL_ROW_WIDTH)
            .ok_or("scoped Work source ROW")?;
        occupied.insert(local);
        for address in [
            active_left(term).then_some(term.gate.left),
            active_right(term).then_some(term.gate.right),
        ]
        .into_iter()
        .flatten()
        {
            if address != 0 {
                if address / WIDTH != MAP_OWNER
                    || !(layout::ENDPOINT_BASE..layout::ENDPOINT_BASE + layout::ENDPOINT_WIDTH)
                        .contains(&(address % WIDTH))
                {
                    return Err("scoped Work source operand owner".into());
                }
                operands.insert(address);
            }
        }
        term.row = MAP_OWNER * ROW_WIDTH + WORK_ROWS.start + local;
    }
    if occupied.len() != expected_rows || operands.len() != WORK_CLAIMS {
        return Err("scoped Work source ROW multiplicity".into());
    }
    Ok((terms, operands, expected_rows))
}

fn source_alias(parent: &WorkTreeHistoryPlan) -> Result<(Vec<Term>, BTreeSet<usize>), String> {
    let base = layout::shared_baseline()?;
    let mut families = parent
        .topology()
        .families
        .iter()
        .filter(|family| family.name == ALIAS_NAME);
    let family = families
        .next()
        .ok_or("scoped HEADER alias source missing")?;
    if families.next().is_some()
        || !matches!(family.mapping, Mapping::HeaderSuccessor { lo: 1, hi } if hi == parent.headers() as usize)
        || family.left_wires != base.header_alias_wires
        || family.right_wires != base.endpoints.header_aliases()
        || family.constants.is_some()
    {
        return Err("scoped HEADER alias source identity".into());
    }
    let first = base.endpoints.raw.len() + base.endpoints.length.len();
    if base.endpoints.n_bits.len() != ALIAS_TERMS || first + ALIAS_TERMS > family.left_wires.len() {
        return Err("scoped HEADER nBits ordinal census".into());
    }
    let mut terms = Vec::new();
    let mut operands = BTreeSet::new();
    family.emit_endpoint_terms(
        parent.descriptor(),
        true,
        HEADER_OWNER,
        |slot, ordinal, mut term| {
            if slot != HEADER_OWNER {
                return Err("scoped HEADER alias slot".into());
            }
            if !(first..first + ALIAS_TERMS).contains(&ordinal) {
                return Ok(());
            }
            let bit = ordinal - first;
            let gate = &term.gate;
            if term.row != HEADER_OWNER * family.left_wires.len().next_power_of_two() + ordinal
                || gate.left != HEADER_OWNER * WIDTH + base.header_alias_wires[ordinal]
                || gate.right != MAP_OWNER * WIDTH + base.endpoints.n_bits[bit]
                || gate.c0 != Fr::zero()
                || gate.c1 != Fr::one()
                || gate.c2 != -Fr::one()
                || gate.c3 != Fr::zero()
            {
                return Err("scoped HEADER alias source term identity".into());
            }
            operands.insert(gate.left);
            term.row = HEADER_OWNER * ROW_WIDTH + ALIAS_ROWS.start + bit;
            terms.push(term);
            Ok(())
        },
    )?;
    if terms.len() != ALIAS_TERMS || operands.len() != ALIAS_TERMS {
        return Err("scoped HEADER nBits alias census".into());
    }
    Ok((terms, operands))
}

fn map_batch(batch: &NativeQ9MapBatch) -> Result<Batch, String> {
    let (reads, helpers, terms) = batch.counts();
    if (reads, helpers, terms) != (MAP_READS, MAP_HELPERS, MAP_TERMS) {
        return Err("scoped native Map source census".into());
    }
    Ok(Batch {
        id: BatchId::Map,
        terms: batch.terms().to_vec(),
        claims: batch.helper_cells().collect(),
        reads: batch.read_cells().collect(),
    })
}

fn prepare(
    parent: &WorkTreeHistoryPlan,
    native: &NativePrefix,
    source: &SelectedRawMapSource<'_>,
    seal: &NativeQ9Binding<'_>,
) -> Result<(Candidate, usize), String> {
    let map = source.stage_native(seal)?;
    source.validate_native(&map, seal)?;
    let (work_terms, work_operands, work_rows) = source_work(parent)?;
    let (alias_terms, header_operands) = source_alias(parent)?;
    let producer = NativeOwnerProducer::new_for_history(parent, native)?;
    let work_row = producer.produce(MAP_OWNER)?;
    let header_row = producer.produce(HEADER_OWNER)?;
    let work_claims = work_operands
        .into_iter()
        .map(|address| packed_bit(&work_row, MAP_OWNER, address).map(|value| (address, value)))
        .collect::<Result<Vec<_>, _>>()?;
    let header_claims = header_operands
        .into_iter()
        .map(|address| packed_bit(&header_row, HEADER_OWNER, address).map(|value| (address, value)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((
        Candidate {
            batches: vec![
                Batch {
                    id: BatchId::Work,
                    terms: work_terms,
                    claims: work_claims,
                    reads: Vec::new(),
                },
                map_batch(&map)?,
                Batch {
                    id: BatchId::HeaderAlias,
                    terms: alias_terms,
                    claims: header_claims,
                    reads: Vec::new(),
                },
            ],
        },
        work_rows,
    ))
}

fn close_honest(candidate: &Candidate, work_rows: usize) -> Result<ScopedCounts, String> {
    let mut destination = Destination::nonempty();
    // `candidate` is private output of `prepare`: its Map, Work and alias
    // factories have independently checked source counts and immutable native
    // inputs. This equality is a post-stage mutation guard, not a second seal.
    let counts = destination.publish(candidate, candidate)?;
    if counts.work_rows != work_rows
        || destination.cells.len() != counts.total_claims + 1
        || destination.rows.len() != counts.total_rows + 1
        || !destination.published
    {
        return Err("scoped atomic destination postcondition".into());
    }
    Ok(counts)
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) struct MutantCounts {
    pub(crate) a_map_failures: usize,
    pub(crate) a_decoded_work_failures: usize,
    pub(crate) a_other_work_failures: usize,
    pub(crate) a_header_alias_failures: usize,
    pub(crate) b_map_failures: usize,
    pub(crate) b_work_failures: usize,
    pub(crate) b_header_alias_failures: usize,
}

#[cfg(test)]
fn replace_work_bits(
    candidate: &mut Candidate,
    locals: &[usize],
    value: &BigUint,
) -> Result<(), String> {
    let claims = &mut candidate.batch_mut(BatchId::Work)?.claims;
    for (bit, &local) in locals.iter().enumerate() {
        let address = MAP_OWNER * WIDTH + local;
        let cell = claims
            .iter_mut()
            .find(|(q, _)| *q == address)
            .ok_or_else(|| format!("mutant Work operand missing {address}"))?;
        cell.1 = Fr::from(u64::from(value.bit(bit as u64)));
    }
    Ok(())
}

#[cfg(test)]
fn assert_mutants(
    parent: &WorkTreeHistoryPlan,
    native: &NativePrefix,
    source: &SelectedRawMapSource<'_>,
    seal: &NativeQ9Binding<'_>,
    honest: &Candidate,
) -> Result<MutantCounts, String> {
    use crate::selected_raw_map_source::coherent_nbits_alternate_for_test;

    let alternate = coherent_nbits_alternate_for_test(source, seal)?;
    let base = layout::shared_baseline()?;
    let e = &base.endpoints;
    let (lower_bytes, _) = native.interval(MAP_OWNER + 2)?;
    let upper = BigUint::from_bytes_be(&lower_bytes) + &alternate.difficulty;
    if upper.bits() > 224 || alternate.difficulty.is_zero() {
        return Err("coherent Work alternate outside U224".into());
    }
    let mut a = honest.clone();
    *a.batch_mut(BatchId::Map)? = map_batch(&alternate.batch)?;
    replace_work_bits(&mut a, &e.work, &alternate.difficulty)?;
    replace_work_bits(
        &mut a,
        &e.work_minus_one,
        &(&alternate.difficulty - BigUint::one()),
    )?;
    replace_work_bits(&mut a, &e.upper, &upper)?;
    let a_result = inspect(&a)?;
    let decoded = parent.work_boundary().group("decoded_work")?;
    let decoded = MAP_OWNER * ROW_WIDTH + WORK_ROWS.start + decoded.start
        ..MAP_OWNER * ROW_WIDTH + WORK_ROWS.start + decoded.end;
    let a_decoded = a_result.nonzero_in(BatchId::Work, decoded);
    let a_work = a_result.nonzero(BatchId::Work);
    let a_map = a_result.nonzero(BatchId::Map);
    let a_alias = a_result.nonzero(BatchId::HeaderAlias);
    if a_map != 0 || a_decoded == 0 || a_work != a_decoded || a_alias != 0 {
        return Err("coherent D-prime fails outside isolated decoded_work".into());
    }

    let mut b = a;
    replace_work_bits(&mut b, &e.n_bits, &BigUint::from(alternate.nbits))?;
    let b_result = inspect(&b)?;
    let b_map = b_result.nonzero(BatchId::Map);
    let b_work = b_result.nonzero(BatchId::Work);
    let b_alias = b_result.nonzero(BatchId::HeaderAlias);
    if b_map != 0 || b_work != 0 || b_alias == 0 {
        return Err("coherent nBits/D-prime did not isolate HEADER alias".into());
    }
    Ok(MutantCounts {
        a_map_failures: a_map,
        a_decoded_work_failures: a_decoded,
        a_other_work_failures: a_work - a_decoded,
        a_header_alias_failures: a_alias,
        b_map_failures: b_map,
        b_work_failures: b_work,
        b_header_alias_failures: b_alias,
    })
}

/// The full-H21 hook can call this once: both coherent mutants are evaluated
/// against the same private, source-owned stage before any reseal could mask them.
#[cfg(test)]
pub(crate) fn run_live_with_mutants(
    parent: &WorkTreeHistoryPlan,
    native: &NativePrefix,
    fixture: &CheckedQ9RawFixture,
) -> Result<(ScopedCounts, MutantCounts), String> {
    let seal = NativeQ9Binding::from_native(parent, native, fixture)?;
    let source = SelectedRawMapSource::new(fixture)?;
    let (candidate, work_rows) = prepare(parent, native, &source, &seal)?;
    let counts = close_honest(&candidate, work_rows)?;
    let mutants = assert_mutants(parent, native, &source, &seal, &candidate)?;
    Ok((counts, mutants))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::Gate;

    fn linear(row: usize, left: usize, right: usize) -> Term {
        Term {
            row,
            gate: Gate {
                left,
                right,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: -Fr::one(),
                c3: Fr::zero(),
            },
        }
    }

    fn small() -> Candidate {
        let work_x = MAP_OWNER * WIDTH + layout::ENDPOINT_BASE;
        let map_x = MAP_OWNER * WIDTH + MAP_HELPER_LOCAL.start;
        let read_x = MAP_OWNER * WIDTH + layout::ENDPOINT_BASE + 1;
        let header_x = HEADER_OWNER * WIDTH + crate::header_hash::SERIALIZER_OFFSET;
        Candidate {
            batches: vec![
                Batch {
                    id: BatchId::Work,
                    terms: vec![linear(MAP_OWNER * ROW_WIDTH + WORK_ROWS.start, work_x, 0)],
                    claims: vec![(work_x, Fr::zero())],
                    reads: vec![],
                },
                Batch {
                    id: BatchId::Map,
                    terms: vec![linear(
                        MAP_OWNER * ROW_WIDTH + MAP_ROWS.start,
                        map_x,
                        read_x,
                    )],
                    claims: vec![(map_x, Fr::one())],
                    reads: vec![(read_x, Fr::one())],
                },
                Batch {
                    id: BatchId::HeaderAlias,
                    terms: vec![linear(
                        HEADER_OWNER * ROW_WIDTH + ALIAS_ROWS.start,
                        header_x,
                        work_x,
                    )],
                    claims: vec![(header_x, Fr::zero())],
                    reads: vec![],
                },
            ],
        }
    }

    #[test]
    fn scoped_registry_rejects_omissions_collisions_and_wrong_owner_without_frame() {
        let good = small();
        let inspected = inspect(&good).unwrap();
        assert_eq!(
            (
                inspected.nonzero(BatchId::Work),
                inspected.nonzero(BatchId::Map),
                inspected.nonzero(BatchId::HeaderAlias)
            ),
            (0, 0, 0)
        );
        for fault in 0..9 {
            let mut bad = good.clone();
            let mut destination = Destination::nonempty();
            let before = destination.clone();
            let expected = match fault {
                0 => {
                    bad.batches.push(bad.batches[0].clone());
                    "scoped batch count"
                }
                1 => {
                    bad.batch_mut(BatchId::Map).unwrap().terms.clear();
                    "scoped source-owned term/claim/READ census"
                }
                2 => {
                    bad.batch_mut(BatchId::Map).unwrap().claims.clear();
                    "missing active scoped X"
                }
                3 => {
                    let x = good.batch(BatchId::Work).unwrap().claims[0];
                    bad.batch_mut(BatchId::HeaderAlias).unwrap().claims.push(x);
                    "duplicate X writer"
                }
                4 => {
                    let row = good.batch(BatchId::Work).unwrap().terms[0].row;
                    bad.batch_mut(BatchId::HeaderAlias).unwrap().terms[0].row = row;
                    "cross-writer ROW collision"
                }
                5 => {
                    bad.batch_mut(BatchId::Work).unwrap().terms[0].row += ROW_WIDTH;
                    "scoped ROW owner or range"
                }
                6 => {
                    bad.batch_mut(BatchId::Map).unwrap().reads.clear();
                    "missing active scoped X"
                }
                7 => {
                    bad.batch_mut(BatchId::HeaderAlias).unwrap().terms.clear();
                    "scoped source-owned term/claim/READ census"
                }
                _ => {
                    bad.batch_mut(BatchId::Work).unwrap().claims[0].1 = Fr::from(2u64);
                    "scoped X claim is not a bit"
                }
            };
            let error = destination.publish(&bad, &good).unwrap_err();
            assert!(error.contains(expected), "fault {fault}: {error}");
            assert_eq!(destination, before, "fault {fault} changed destination");
        }
        let mut destination = Destination::nonempty();
        destination
            .cells
            .insert(good.batch(BatchId::Work).unwrap().claims[0].0, Fr::zero());
        let before = destination.clone();
        assert_eq!(
            destination.publish(&good, &good).unwrap_err(),
            "destination X collision"
        );
        assert_eq!(destination, before);
        let mut destination = Destination::nonempty();
        destination.rows.insert(
            good.batch(BatchId::Map).unwrap().terms[0].row,
            BatchId::Work,
        );
        let before = destination.clone();
        assert_eq!(
            destination.publish(&good, &good).unwrap_err(),
            "destination ROW collision"
        );
        assert_eq!(destination, before);
    }

    #[test]
    fn scoped_h21_source_row_and_count_contract_without_frame() {
        let base = layout::shared_baseline().unwrap();
        let boundary = crate::work_tree_work::compile(
            base,
            crate::work_tree_work::WorkProfile::new(1_827_840, [0; 32], [0; 28]).unwrap(),
        )
        .unwrap();
        let mut terms = Vec::new();
        boundary
            .emit_slot(MAP_OWNER, |term| terms.push(term))
            .unwrap();
        let rows = terms.iter().map(|term| term.row).collect::<BTreeSet<_>>();
        let genuine = boundary
            .groups()
            .iter()
            .filter(|group| group.name != "padding_arithmetic_zero")
            .collect::<Vec<_>>();
        assert_eq!(
            terms.len(),
            genuine.iter().map(|group| group.term_count).sum::<usize>()
        );
        assert_eq!(
            rows.len(),
            genuine.iter().map(|group| group.rows.len()).sum::<usize>()
        );
        assert_eq!(terms.len(), WORK_TERMS);
        assert_eq!(rows.len(), WORK_ACTIVE_ROWS);
        assert!(rows.iter().all(|row| (MAP_OWNER * LOCAL_ROW_WIDTH
            ..(MAP_OWNER + 1) * LOCAL_ROW_WIDTH)
            .contains(row)));
        assert_eq!(
            (
                MAP_ROWS.len(),
                WORK_ROWS.len(),
                ALIAS_ROWS.len(),
                MAP_READS,
                MAP_HELPERS,
                MAP_TERMS,
                ALIAS_TERMS
            ),
            (10_347, 2_048, 32, 2_592, 5_757, 68_233, 32)
        );
    }
}

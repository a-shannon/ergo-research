//! Test-only H21 split-member and X-read census for two selected owners.
//! It makes no witness, writer-lease, PCS, or whole-history claim.

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::Fr;
use ark_ff::{PrimeField, Zero};

use crate::daa_header_window::{self, Action};
use crate::daa_integer::Epoch;
use crate::sparse::Term;
use crate::work_tree_history_plan::WorkTreeHistoryPlan;
use crate::work_tree_layout::WIDTH;
use crate::work_tree_wiring::{
    self as wiring, full_split_cross_tensor_dimensions, full_split_cross_tensor_member_row_bits,
    full_split_local_tensor_dimensions, full_split_local_tensor_member_row_bits, Mapping,
};

const HEADERS: u64 = 1_827_840;
const OWNERS: [usize; 2] = [844_672, 845_759];

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Role {
    Local,
    Cross,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum View {
    Local,
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Side {
    Left,
    Right,
}

#[derive(Clone, Debug)]
struct Shape {
    slots: usize,
    leaves: usize,
    local_base_bits: usize,
    cross_base_bits: usize,
    local_member_bits: Vec<usize>,
    cross_member_bits: Vec<usize>,
    local_names: Vec<String>,
    cross_names: Vec<String>,
    cross_mappings: Vec<Mapping>,
}

impl Shape {
    fn from_source(plan: &WorkTreeHistoryPlan) -> Result<Self, String> {
        if plan.headers() != HEADERS || plan.slot_log() != 21 {
            return Err("H21 source plan identity".into());
        }
        let topology = plan.topology();
        let work = plan.work_boundary();
        let local = full_split_local_tensor_dimensions(topology, work)?;
        let cross = full_split_cross_tensor_dimensions(topology, work)?;
        if local != (20, 21, 14, 3) || cross != (20, 21, 13, 6) {
            return Err("H21 split dimensions".into());
        }
        let mut local_names = Vec::new();
        let mut cross_names = Vec::new();
        let mut cross_mappings = Vec::new();
        for family in &topology.families {
            if matches!(family.mapping, Mapping::Same { .. }) {
                local_names.push(family.name.clone());
            } else {
                cross_names.push(family.name.clone());
                cross_mappings.push(family.mapping.clone());
            }
        }
        local_names.extend(["fixed", "leaf", "Work"].map(str::to_owned));
        cross_names.extend(work.links().iter().map(|family| family.name.clone()));
        cross_mappings.extend(work.links().iter().map(|family| family.mapping.clone()));
        let local_member_bits = full_split_local_tensor_member_row_bits(topology, work)?;
        let cross_member_bits = full_split_cross_tensor_member_row_bits(topology, work)?;
        if local_names.len() != 6
            || cross_names.len() != 52
            || local_member_bits != [8, 8, 8, 11, 14, 11]
            || local_names.len() != local_member_bits.len()
            || cross_names.len() != cross_member_bits.len()
            || cross_mappings.len() != cross_names.len()
            || cross_names[0] != "header_to_leaf_raw_length_nbits_height"
            || !matches!(
                topology.families[0].mapping,
                Mapping::HeaderSuccessor { .. }
            )
        {
            return Err("H21 complete LOCAL/CROSS member roster".into());
        }
        Ok(Self {
            slots: topology.descriptor.slots,
            leaves: topology.descriptor.leaves,
            local_base_bits: local.2,
            cross_base_bits: cross.2,
            local_member_bits,
            cross_member_bits,
            local_names,
            cross_names,
            cross_mappings,
        })
    }

    fn member_bits(&self, role: Role) -> &[usize] {
        match role {
            Role::Local => &self.local_member_bits,
            Role::Cross => &self.cross_member_bits,
        }
    }

    fn base_bits(&self, role: Role) -> usize {
        match role {
            Role::Local => self.local_base_bits,
            Role::Cross => self.cross_base_bits,
        }
    }
}

#[derive(Clone, Debug)]
struct Observed {
    role: Role,
    view: View,
    member: usize,
    source_slot: usize,
    local_row: usize,
    term: Term,
    reads: [Option<usize>; 2],
    x_write: bool,
}

#[derive(Clone, Debug)]
struct Batch {
    owner: usize,
    records: Vec<Observed>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct OccurrenceKey {
    role: Role,
    member: usize,
    source_slot: usize,
    local_row: usize,
    left: usize,
    right: usize,
    coefficients: [[u64; 4]; 4],
}

impl Observed {
    fn key(&self) -> OccurrenceKey {
        let gate = &self.term.gate;
        OccurrenceKey {
            role: self.role,
            member: self.member,
            source_slot: self.source_slot,
            local_row: self.local_row,
            left: gate.left,
            right: gate.right,
            coefficients: [gate.c0, gate.c1, gate.c2, gate.c3].map(|v| v.into_bigint().0),
        }
    }
}

fn active(term: &Term) -> [bool; 2] {
    let gate = &term.gate;
    [
        !gate.c1.is_zero() || !gate.c3.is_zero(),
        !gate.c2.is_zero() || !gate.c3.is_zero(),
    ]
}

fn physical_reads(
    role: Role,
    owner: usize,
    slots: usize,
    term: &Term,
) -> Result<[Option<usize>; 2], String> {
    let mut reads = [None, None];
    let use_operand = active(term);
    let wires = [term.gate.left, term.gate.right];
    let global_limit = slots.checked_mul(WIDTH).ok_or("X extent overflow")?;
    for index in 0..2 {
        if !use_operand[index] {
            if role == Role::Local && wires[index] != 0 {
                return Err("inactive LOCAL X placeholder".into());
            }
            continue;
        }
        let physical = match role {
            Role::Local => {
                if wires[index] >= WIDTH {
                    return Err("active LOCAL X outside owner width".into());
                }
                owner
                    .checked_mul(WIDTH)
                    .and_then(|base| base.checked_add(wires[index]))
                    .ok_or("LOCAL physical X overflow")?
            }
            Role::Cross => wires[index],
        };
        if physical >= global_limit {
            return Err("active physical X outside split extent".into());
        }
        reads[index] = Some(physical);
    }
    Ok(reads)
}

fn mapped_cross_source(
    record: &Observed,
    owner: usize,
    shape: &Shape,
) -> Result<Option<usize>, String> {
    let mapping = shape
        .cross_mappings
        .get(record.member)
        .ok_or("CROSS mapping member outside source roster")?;
    match mapping {
        Mapping::HeaderSuccessor { .. } => Ok(Some(match record.view {
            View::Left => owner,
            View::Right => owner
                .checked_add(1)
                .ok_or("HeaderSuccessor source overflow")?,
            View::Local => return Err("HeaderSuccessor-as-Same classification".into()),
        })),
        Mapping::Child { level, branch } => {
            let width = shape
                .leaves
                .checked_shr(*level as u32)
                .filter(|width| *width != 0)
                .ok_or("Child level outside tree")?;
            let expected = match record.view {
                View::Left => owner,
                View::Right => {
                    let parent_base = shape
                        .leaves
                        .checked_sub(2 * width)
                        .ok_or("Child parent base")?;
                    let child_base = if *level == 1 {
                        0
                    } else {
                        shape.leaves.checked_sub(4 * width).ok_or("Child base")?
                    };
                    let delta = owner
                        .checked_sub(child_base)
                        .ok_or("Child endpoint before base")?;
                    if delta >= 2 * width || delta % 2 != *branch {
                        return Err("Child endpoint branch/level class".into());
                    }
                    parent_base + delta / 2
                }
                View::Local => return Err("Child-as-Same classification".into()),
            };
            Ok(Some(expected))
        }
        _ => Ok(None),
    }
}

fn validate_record(record: &Observed, owner: usize, shape: &Shape) -> Result<(), String> {
    if record.x_write {
        return Err("split alias promoted to X writer".into());
    }
    if (record.role == Role::Local) != (record.view == View::Local) {
        return Err("LOCAL/CROSS role or HeaderSuccessor-as-Same classification".into());
    }
    let bits = *shape
        .member_bits(record.role)
        .get(record.member)
        .ok_or("split member ordinal outside source roster")?;
    if record.local_row >= 1usize << bits {
        return Err("split member local ROW outside source width".into());
    }
    let tagged_row = record
        .member
        .checked_shl(shape.base_bits(record.role) as u32)
        .and_then(|base| base.checked_add(record.local_row))
        .ok_or("split tagged ROW overflow")?;
    if record.term.row != tagged_row {
        return Err("split member ordinal/tagged ROW mismatch".into());
    }
    if record.source_slot >= shape.slots {
        return Err("split source_slot outside descriptor".into());
    }
    if record.role == Role::Local && record.source_slot != owner {
        return Err("LOCAL source_slot owner mismatch".into());
    }
    if record.role == Role::Cross {
        if let Some(expected) = mapped_cross_source(record, owner, shape)? {
            if record.source_slot != expected {
                return Err("CROSS mapping exact source_slot".into());
            }
        }
    }
    let actual_reads = physical_reads(record.role, owner, shape.slots, &record.term)?;
    if record.reads != actual_reads {
        return Err("source-defined physical X projection".into());
    }
    if record.role == Role::Cross {
        if let Some(left) = actual_reads[0] {
            if left / WIDTH != record.source_slot {
                return Err("CROSS source_slot/left X mismatch".into());
            }
            if record.view == View::Left && left / WIDTH != owner {
                return Err("CROSS left endpoint owner mismatch".into());
            }
        }
        if record.view == View::Right {
            if let Some(right) = actual_reads[1] {
                if right / WIDTH != owner {
                    return Err("CROSS right endpoint owner mismatch".into());
                }
            }
        }
    }
    Ok(())
}

fn observed(
    role: Role,
    view: View,
    source_slot: usize,
    term: Term,
    owner: usize,
    shape: &Shape,
) -> Result<Observed, String> {
    let base_bits = shape.base_bits(role);
    let member = term.row >> base_bits;
    let local_row = term.row & ((1usize << base_bits) - 1);
    let reads = physical_reads(role, owner, shape.slots, &term)?;
    let record = Observed {
        role,
        view,
        member,
        source_slot,
        local_row,
        term,
        reads,
        x_write: false,
    };
    validate_record(&record, owner, shape)?;
    Ok(record)
}

fn stream_owner(plan: &WorkTreeHistoryPlan, owner: usize, shape: &Shape) -> Result<Batch, String> {
    if !OWNERS.contains(&owner) || owner >= shape.slots {
        return Err("two-owner H21 scope".into());
    }
    let topology = plan.topology();
    let engine = crate::work_tree_fixed_hash::engine()?;
    let mut batch = Batch {
        owner,
        records: Vec::new(),
    };
    wiring::full_split_visit_local_slot_terms(
        topology,
        engine,
        plan.fixed_profile(),
        plan.leaf_boundary(),
        plan.work_boundary(),
        owner,
        &mut |term| {
            batch.records.push(observed(
                Role::Local,
                View::Local,
                owner,
                term,
                owner,
                shape,
            )?);
            Ok(())
        },
    )?;
    for (left_endpoint, view) in [(true, View::Left), (false, View::Right)] {
        wiring::full_split_visit_cross_endpoint_terms(
            topology,
            plan.work_boundary(),
            left_endpoint,
            owner,
            &mut |source_slot, tagged_row, term| {
                if tagged_row != term.row {
                    return Err("CROSS source tagged ROW disagrees with term".into());
                }
                batch.records.push(observed(
                    Role::Cross,
                    view,
                    source_slot,
                    term,
                    owner,
                    shape,
                )?);
                Ok(())
            },
        )?;
    }
    Ok(batch)
}

fn occurrences(batch: &Batch, view: View) -> BTreeMap<OccurrenceKey, usize> {
    let mut out = BTreeMap::new();
    for record in batch.records.iter().filter(|record| record.view == view) {
        *out.entry(record.key()).or_insert(0) += 1;
    }
    out
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct PairCounts {
    distinct: usize,
    union: usize,
    paired: usize,
    left_only: usize,
    right_only: usize,
}

fn pair_counts(
    left: &BTreeMap<OccurrenceKey, usize>,
    right: &BTreeMap<OccurrenceKey, usize>,
) -> PairCounts {
    let mut counts = PairCounts::default();
    for (key, &n_left) in left {
        let n_right = right.get(key).copied().unwrap_or(0);
        counts.distinct += 1;
        counts.union += n_left.max(n_right);
        counts.paired += n_left.min(n_right);
        counts.left_only += n_left.saturating_sub(n_right);
        counts.right_only += n_right.saturating_sub(n_left);
    }
    for (key, &n_right) in right {
        if !left.contains_key(key) {
            counts.distinct += 1;
            counts.union += n_right;
            counts.right_only += n_right;
        }
    }
    counts
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Census {
    terms: [Vec<usize>; 3],
    row_support: [Vec<usize>; 3],
    reads: BTreeMap<(Role, View, usize, usize, usize, Side, usize), usize>,
    pair: PairCounts,
}

fn census(batch: &Batch, shape: &Shape) -> Result<Census, String> {
    let mut terms = [
        vec![0; shape.local_names.len()],
        vec![0; shape.cross_names.len()],
        vec![0; shape.cross_names.len()],
    ];
    let mut rows: [Vec<BTreeSet<(usize, usize)>>; 3] = [
        vec![BTreeSet::new(); shape.local_names.len()],
        vec![BTreeSet::new(); shape.cross_names.len()],
        vec![BTreeSet::new(); shape.cross_names.len()],
    ];
    let mut reads = BTreeMap::new();
    let mut cross_row_gates = BTreeMap::<(View, usize, usize, usize), OccurrenceKey>::new();
    for record in &batch.records {
        validate_record(record, batch.owner, shape)?;
        if record.role == Role::Cross {
            let row = (
                record.view,
                record.member,
                record.source_slot,
                record.local_row,
            );
            if let Some(first) = cross_row_gates.get(&row) {
                if *first != record.key() {
                    return Err("genuine CROSS within-member ROW collision".into());
                }
            } else {
                cross_row_gates.insert(row, record.key());
            }
        }
        let index = match record.view {
            View::Local => 0,
            View::Left => 1,
            View::Right => 2,
        };
        terms[index][record.member] += 1;
        rows[index][record.member].insert((record.source_slot, record.local_row));
        for (side, physical) in [
            (Side::Left, record.reads[0]),
            (Side::Right, record.reads[1]),
        ] {
            if let Some(physical) = physical {
                *reads
                    .entry((
                        record.role,
                        record.view,
                        record.member,
                        record.source_slot,
                        record.local_row,
                        side,
                        physical,
                    ))
                    .or_insert(0) += 1;
            }
        }
    }
    let row_support =
        rows.map(|members| members.into_iter().map(|support| support.len()).collect());
    let pair = pair_counts(
        &occurrences(batch, View::Left),
        &occurrences(batch, View::Right),
    );
    Ok(Census {
        terms,
        row_support,
        reads,
        pair,
    })
}

fn sparse_expected(
    actual: &[usize],
    expected: &[(usize, usize)],
    total: usize,
) -> Result<(), String> {
    let mut frozen = vec![0; actual.len()];
    for &(member, count) in expected {
        *frozen
            .get_mut(member)
            .ok_or("frozen member ordinal outside roster")? = count;
    }
    if actual != frozen || actual.iter().sum::<usize>() != total {
        return Err(format!(
            "frozen source member census: actual={actual:?}, expected={frozen:?}, expected_total={total}"
        ));
    }
    Ok(())
}

fn frozen_oracle(owner: usize, counts: &Census) -> Result<(), String> {
    let fixed = if owner == OWNERS[0] { 2919 } else { 2926 };
    // Every message bit emits one Gate: equal(a, b) is one Gate, and a
    // zero-filled bit emits one linear Gate. Public one-bits add 11 constants.
    sparse_expected(
        &counts.terms[0],
        &[
            (0, 256),
            (1, 256),
            (2, 256),
            (3, fixed),
            (4, 21_379),
            (5, 3265),
        ],
        if owner == OWNERS[0] { 28_331 } else { 28_338 },
    )?;
    sparse_expected(
        &counts.row_support[0],
        &[
            (0, 256),
            (1, 256),
            (2, 256),
            (3, 1857),
            (4, 8000),
            (5, 1435),
        ],
        12_060,
    )?;
    sparse_expected(
        &counts.terms[1],
        &[
            (0, 4186),
            (1, 256),
            (2, 256),
            (3, 256),
            (48, 1502),
            (50, 224),
        ],
        6680,
    )?;
    let right_children = if owner == OWNERS[0] { (2, 4) } else { (3, 5) };
    sparse_expected(
        &counts.terms[2],
        &[
            (0, 4186),
            (right_children.0, 256),
            (right_children.1, 256),
            (50, 224),
        ],
        4922,
    )?;
    // Each CROSS Family emits one term per (source_slot, local_row) in a view.
    // LOCAL fixed/leaf/Work rows may carry several terms and are not deduplicated.
    if counts.row_support[1] != counts.terms[1] || counts.row_support[2] != counts.terms[2] {
        return Err("frozen CROSS source ROW support".into());
    }
    if counts.pair.paired != 0
        || counts.pair.union != 11_602
        || counts.pair.left_only != 6680
        || counts.pair.right_only != 4922
    {
        return Err("frozen CROSS endpoint occurrence incidence".into());
    }
    Ok(())
}

struct Destination<'a> {
    expected: &'a Batch,
    shape: &'a Shape,
    published: Option<Census>,
}

struct PairDestination<'a> {
    left: &'a BTreeMap<OccurrenceKey, usize>,
    right: &'a BTreeMap<OccurrenceKey, usize>,
    published: Option<PairCounts>,
}

impl PairDestination<'_> {
    fn publish(
        &mut self,
        left: &BTreeMap<OccurrenceKey, usize>,
        right: &BTreeMap<OccurrenceKey, usize>,
    ) -> Result<(), String> {
        if self.published.is_some() || left != self.left || right != self.right {
            return Err("synthetic complete Gate endpoint occurrence multiset".into());
        }
        self.published = Some(pair_counts(left, right));
        Ok(())
    }
}

impl Destination<'_> {
    fn publish(&mut self, candidate: &Batch) -> Result<(), String> {
        if self.published.is_some() || candidate.owner != self.expected.owner {
            return Err("H21 destination owner/already published".into());
        }
        let checked = census(candidate, self.shape)?;
        let source = census(self.expected, self.shape)?;
        frozen_oracle(self.expected.owner, &source)?;
        for view in 0..3 {
            for member in 0..source.terms[view].len() {
                if source.terms[view][member] == 0 && checked.terms[view][member] != 0 {
                    return Err("source-declared empty split member forged".into());
                }
                if source.terms[view][member] != 0 && checked.terms[view][member] == 0 {
                    return Err("source-declared nonempty split member omitted".into());
                }
            }
        }
        for view in [View::Local, View::Left, View::Right] {
            if occurrences(candidate, view) != occurrences(self.expected, view) {
                return Err("complete Gate occurrence multiset".into());
            }
        }
        if checked != source {
            return Err("role member/ROW/X-read incidence census".into());
        }
        self.published = Some(checked);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plan() -> WorkTreeHistoryPlan {
        WorkTreeHistoryPlan::compile(HEADERS, 21, [0x5a; 32], [0; 28]).unwrap()
    }

    fn reject(expected: &Batch, shape: &Shape, candidate: Batch, named: &str) {
        let mut destination = Destination {
            expected,
            shape,
            published: None,
        };
        let error = destination.publish(&candidate).unwrap_err();
        assert!(error.contains(named), "expected {named:?}, got {error:?}");
        assert!(destination.published.is_none());
    }

    fn cross_left(batch: &Batch) -> usize {
        batch
            .records
            .iter()
            .position(|r| r.role == Role::Cross && r.view == View::Left && r.member == 0)
            .unwrap()
    }

    fn local_first(batch: &Batch) -> usize {
        batch
            .records
            .iter()
            .position(|r| r.role == Role::Local && r.member == 0)
            .unwrap()
    }

    #[test]
    fn two_owner_h21_source_census_and_x_read_incidence() {
        let plan = plan();
        let shape = Shape::from_source(&plan).unwrap();
        assert_eq!(shape.slots, 1usize << 21);
        for owner in OWNERS {
            let class = daa_header_window::for_child_height((owner + 1) as u32).unwrap();
            if owner == OWNERS[0] {
                assert_eq!(class.action(), Action::Retarget(Epoch::Eip));
                assert_eq!(class.sample_heights().len(), 9);
            } else {
                assert_eq!(class.action(), Action::Carry);
                assert!(class.sample_heights().is_empty());
            }
            let source = stream_owner(&plan, owner, &shape).unwrap();
            let source_counts = census(&source, &shape).unwrap();
            frozen_oracle(owner, &source_counts).unwrap();
            let candidate = stream_owner(&plan, owner, &shape).unwrap();
            let mut destination = Destination {
                expected: &source,
                shape: &shape,
                published: None,
            };
            destination.publish(&candidate).unwrap();
            assert_eq!(destination.published, Some(source_counts));
        }
    }

    #[test]
    fn isolated_source_roster_gate_and_x_projection_mutants() {
        let plan = plan();
        let shape = Shape::from_source(&plan).unwrap();
        let source = stream_owner(&plan, OWNERS[0], &shape).unwrap();
        frozen_oracle(OWNERS[0], &census(&source, &shape).unwrap()).unwrap();

        let mut omitted = source.clone();
        omitted
            .records
            .retain(|r| !(r.role == Role::Local && r.member == 5));
        reject(&source, &shape, omitted, "nonempty split member omitted");

        let mut empty = source.clone();
        let mut forged = empty.records[cross_left(&empty)].clone();
        forged.member = 49;
        forged.local_row = 0;
        forged.term.row = 49usize << shape.cross_base_bits;
        empty.records.push(forged);
        reject(&source, &shape, empty, "empty split member forged");

        let mut ordinal = source.clone();
        let index = local_first(&ordinal);
        ordinal.records[index].member = 1;
        ordinal.records[index].term.row =
            (1usize << shape.local_base_bits) + ordinal.records[index].local_row;
        reject(
            &source,
            &shape,
            ordinal,
            "complete Gate occurrence multiset",
        );

        let mut source_slot = source.clone();
        let index = cross_left(&source_slot);
        source_slot.records[index].source_slot += 1;
        source_slot.records[index].term.gate.left += WIDTH;
        source_slot.records[index].reads[0] =
            source_slot.records[index].reads[0].map(|x| x + WIDTH);
        reject(
            &source,
            &shape,
            source_slot,
            "CROSS mapping exact source_slot",
        );

        let mut child_slot = source.clone();
        let child = child_slot
            .records
            .iter()
            .position(|r| {
                r.view == View::Right
                    && matches!(shape.cross_mappings[r.member], Mapping::Child { .. })
            })
            .unwrap();
        child_slot.records[child].source_slot += 1;
        child_slot.records[child].term.gate.left += WIDTH;
        child_slot.records[child].reads[0] = child_slot.records[child].reads[0].map(|x| x + WIDTH);
        reject(
            &source,
            &shape,
            child_slot,
            "CROSS mapping exact source_slot",
        );

        let mut row_collision = source.clone();
        let first = cross_left(&row_collision);
        let second = first + 1;
        assert_eq!(
            row_collision.records[first].member,
            row_collision.records[second].member
        );
        assert_eq!(
            row_collision.records[first].source_slot,
            row_collision.records[second].source_slot
        );
        row_collision.records[second].local_row = row_collision.records[first].local_row;
        row_collision.records[second].term.row = row_collision.records[first].term.row;
        reject(
            &source,
            &shape,
            row_collision,
            "genuine CROSS within-member ROW collision",
        );

        let mut same = source.clone();
        let index = cross_left(&same);
        same.records[index].role = Role::Local;
        reject(
            &source,
            &shape,
            same,
            "HeaderSuccessor-as-Same classification",
        );

        let mut alias_writer = source.clone();
        let index = cross_left(&alias_writer);
        alias_writer.records[index].x_write = true;
        reject(
            &source,
            &shape,
            alias_writer,
            "split alias promoted to X writer",
        );

        let mut local_x = source.clone();
        let index = local_first(&local_x);
        local_x.records[index].reads[0] = local_x.records[index].reads[0].map(|x| x + 1);
        reject(
            &source,
            &shape,
            local_x,
            "source-defined physical X projection",
        );

        let mut cross_x = source.clone();
        let index = cross_left(&cross_x);
        cross_x.records[index].term.gate.left += 1;
        reject(
            &source,
            &shape,
            cross_x,
            "source-defined physical X projection",
        );

        let mut coefficient = source.clone();
        let index = local_first(&coefficient);
        coefficient.records[index].term.gate.c0 += Fr::from(1u64);
        reject(
            &source,
            &shape,
            coefficient,
            "complete Gate occurrence multiset",
        );

        let mut duplicate = source.clone();
        duplicate
            .records
            .push(duplicate.records[cross_left(&duplicate)].clone());
        reject(
            &source,
            &shape,
            duplicate,
            "complete Gate occurrence multiset",
        );
    }

    #[test]
    fn synthetic_cross_endpoint_overlap_preserves_per_view_multiplicity() {
        let key = OccurrenceKey {
            role: Role::Cross,
            member: 0,
            source_slot: OWNERS[0],
            local_row: 0,
            left: OWNERS[0] * WIDTH + 1,
            right: OWNERS[0] * WIDTH + 2,
            coefficients: [[0; 4], [1, 0, 0, 0], [2, 0, 0, 0], [0; 4]],
        };
        let mut left = BTreeMap::from([(key.clone(), 2usize)]);
        let mut right = BTreeMap::from([(key.clone(), 1usize)]);
        let exact_left = left.clone();
        let exact_right = right.clone();
        let expected = PairCounts {
            distinct: 1,
            union: 2,
            paired: 1,
            left_only: 1,
            right_only: 0,
        };
        let mut accepted = PairDestination {
            left: &exact_left,
            right: &exact_right,
            published: None,
        };
        accepted.publish(&left, &right).unwrap();
        assert_eq!(accepted.published, Some(expected));
        left.insert(key.clone(), 1);
        let mut dropped = PairDestination {
            left: &exact_left,
            right: &exact_right,
            published: None,
        };
        assert!(dropped
            .publish(&left, &right)
            .unwrap_err()
            .contains("complete Gate endpoint occurrence"));
        assert!(dropped.published.is_none());
        left = exact_left;
        let mut changed_coefficient = key.clone();
        changed_coefficient.coefficients[0][0] ^= 1;
        right = BTreeMap::from([(changed_coefficient, 1)]);
        let mut substituted = PairDestination {
            left: &left,
            right: &exact_right,
            published: None,
        };
        assert!(substituted
            .publish(&left, &right)
            .unwrap_err()
            .contains("complete Gate endpoint occurrence"));
        assert!(substituted.published.is_none());
    }
}

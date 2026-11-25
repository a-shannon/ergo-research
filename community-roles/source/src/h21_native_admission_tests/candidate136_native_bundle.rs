//! One-parent diagnostic publication across separate H21-local, Work, and
//! HeaderSuccessor roles. This does not construct a proof or a PCS witness.

use std::{
    collections::{BTreeMap, BTreeSet},
    io::Write,
    ops::Range,
};

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;

use super::{
    candidate135_native_values::{active_addresses, evaluate, Origin, X},
    *,
};
use crate::{
    h21_local_merged_ledger::{close_native_carry, NativeCarryLedger},
    h21_scheduled_max_cap::{Prepared, Writer},
    sparse::Term,
    work_tree_layout::WIDTH,
};

const OWNER: usize = 844_670;
const HEADER_OWNER: usize = OWNER + 1;
const NEXT_OWNER: usize = 844_798;
const MAX_BASE: [usize; 2] = [999_424, 1_000_097];

#[path = "candidate145_map_max_composite.rs"]
mod candidate145_map_max_composite;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ParentId {
    headers: usize,
    slot_log: usize,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
}

#[derive(Clone, Copy)]
struct Sources<'a> {
    work: &'a NativePackedRow,
    header: &'a NativePackedRow,
    max: &'a BTreeMap<usize, Fr>,
}

impl ParentId {
    pub(super) fn headers(self) -> usize {
        self.headers
    }

    pub(super) fn slot_log(self) -> usize {
        self.slot_log
    }

    pub(super) fn root(self) -> [u8; 32] {
        self.root
    }

    pub(super) fn total(self) -> [u8; 28] {
        self.total
    }

    pub(super) fn profile(self) -> [u8; 32] {
        self.profile
    }

    fn from_source(plan: &WorkTreeHistoryPlan, prefix: &NativePrefix) -> Result<Self, String> {
        validate_native_plan_input(plan, prefix)?;
        if plan.headers() != N as u64 || plan.slot_log() != H || prefix.header_count() != N {
            return Err("c136 parent H21 geometry".into());
        }
        Ok(Self {
            headers: N,
            slot_log: H,
            root: prefix.root(),
            total: prefix.total_be28(),
            profile: prefix.profile(),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SelectedXRole {
    Writer,
    ImportedRead,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SelectedXValueClaim {
    pub(super) address: usize,
    pub(super) value: Fr,
    pub(super) role: SelectedXRole,
}

/// Validated, read-only handoff for later common-ledger composition.
/// Fields stay private so consumers can only inspect the completed census.
pub(super) struct CarryMapExport {
    parent: ParentId,
    local: NativeCarryLedger,
    local_rows: BTreeMap<usize, crate::h21_local_merged_ledger::RowWriter>,
    work: Vec<Term>,
    max: Vec<(Writer, Term)>,
    cross: Vec<Term>,
    map0: Vec<Term>,
    map1: Option<Vec<Term>>,
    selected_x: Vec<SelectedXValueClaim>,
}

impl CarryMapExport {
    pub(super) fn parent(&self) -> ParentId {
        self.parent
    }

    pub(super) fn native_carry(&self) -> &NativeCarryLedger {
        &self.local
    }

    pub(super) fn native_row_claims(
        &self,
    ) -> &BTreeMap<usize, crate::h21_local_merged_ledger::RowWriter> {
        &self.local_rows
    }

    pub(super) fn work_terms(&self) -> &[Term] {
        &self.work
    }

    pub(super) fn max_terms(&self) -> &[(Writer, Term)] {
        &self.max
    }

    pub(super) fn cross_terms(&self) -> &[Term] {
        &self.cross
    }

    pub(super) fn map0_terms(&self) -> &[Term] {
        &self.map0
    }

    pub(super) fn map1_terms(&self) -> Option<&[Term]> {
        self.map1.as_deref()
    }

    pub(super) fn selected_x_claims(&self) -> &[SelectedXValueClaim] {
        &self.selected_x
    }
}

#[derive(Clone)]
struct Candidate {
    parent: ParentId,
    local: NativeCarryLedger,
    work_row: NativePackedRow,
    header_row: NativePackedRow,
    work: Vec<Term>,
    max: Vec<(Writer, Term)>,
    cross: Vec<Term>,
    x: X,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Destination {
    parent: Option<ParentId>,
    local: Option<NativeCarryLedger>,
    local_rows: BTreeSet<usize>,
    occupied_x: Vec<Range<usize>>,
    work: Vec<Term>,
    cross: Vec<Term>,
    x: X,
}

fn global(owner: usize, local: usize) -> usize {
    owner * WIDTH + local
}

fn phase(name: &str) {
    println!("C136B_PHASE phase={name}");
    std::io::stdout().flush().expect("c136b phase marker flush");
}

fn packed_bit(row: &NativePackedRow, address: usize) -> Result<Fr, String> {
    if address / WIDTH != row.owner() || row.packed_bytes().len() != WIDTH / 8 {
        return Err("c136 native packed address/row identity".into());
    }
    let local = address % WIDTH;
    Ok(Fr::from(
        ((row.packed_bytes()[local / 8] >> (local % 8)) & 1) as u64,
    ))
}

fn expected_max_cells(prepared: &Prepared) -> Result<BTreeMap<usize, Fr>, String> {
    let mut expected = BTreeMap::new();
    let local = {
        let mut cells = crate::h21_scheduled_max_cap::OwnerCells::new(OWNER)?;
        prepared.owner_patch(OWNER)?.apply(&mut cells)?;
        cells
    };
    let foreign = {
        let mut cells = crate::h21_scheduled_max_cap::OwnerCells::new(NEXT_OWNER)?;
        prepared.owner_patch(NEXT_OWNER)?.apply(&mut cells)?;
        cells
    };
    let mut local_writers = BTreeSet::new();
    prepared.plan().visit_owner(OWNER, |writer, _| {
        local_writers.insert(writer);
        Ok(())
    })?;
    let mut foreign_writers = BTreeSet::new();
    prepared.plan().visit_owner(NEXT_OWNER, |writer, _| {
        foreign_writers.insert(writer);
        Ok(())
    })?;
    if local_writers
        != BTreeSet::from([
            Writer::Max {
                context: 0,
                end: OWNER + 2,
            },
            Writer::Max {
                context: 1,
                end: OWNER + 2,
            },
        ])
        || foreign_writers
            != BTreeSet::from([
                Writer::Max {
                    context: 0,
                    end: NEXT_OWNER + 2,
                },
                Writer::Max {
                    context: 1,
                    end: NEXT_OWNER + 2,
                },
            ])
    {
        return Err("c136 local/foreign MAX writer identity".into());
    }
    for context in 0..2 {
        for bit in 0..673 {
            expected.insert(
                global(OWNER, MAX_BASE[context] + bit),
                local.read(MAX_BASE[context] + bit)?,
            );
        }
        for bit in 0..224 {
            expected.insert(
                global(NEXT_OWNER, MAX_BASE[context] + bit),
                foreign.read(MAX_BASE[context] + bit)?,
            );
        }
    }
    if expected.len() != 1_346 + 448 {
        return Err("c136 local/foreign MAX value census".into());
    }
    Ok(expected)
}

impl Candidate {
    fn stage(
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
        source_max: &BTreeMap<usize, Fr>,
        work_row: &NativePackedRow,
        header_row: &NativePackedRow,
        work: &[Term],
        max: &[(Writer, Term)],
        cross: &[Term],
        x: &X,
    ) -> Result<Self, String> {
        let parent = ParentId::from_source(plan, prefix)?;
        work_row.validate_identity_for_history_test(plan, prefix, OWNER)?;
        header_row.validate_identity_for_history_test(plan, prefix, HEADER_OWNER)?;
        phase("source_rows_validated");
        let local = close_native_carry(plan)?;
        phase("local_ledger_closed");
        let candidate = Self {
            parent,
            local,
            work_row: work_row.clone(),
            header_row: header_row.clone(),
            work: work.to_vec(),
            max: max.to_vec(),
            cross: cross.to_vec(),
            x: x.clone(),
        };
        candidate.validate(
            plan,
            prefix,
            parent,
            Sources {
                work: work_row,
                header: header_row,
                max: source_max,
            },
        )?;
        phase("candidate_validated");
        Ok(candidate)
    }

    fn validate(
        &self,
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
        expected: ParentId,
        sources: Sources<'_>,
    ) -> Result<(), String> {
        if self.parent != expected || ParentId::from_source(plan, prefix)? != expected {
            return Err("c136 parent identity".into());
        }
        if self.local.owner() != OWNER
            || self.local.class() != crate::daa_history_roster::OwnerClass::Carry
            || self.local.root() != expected.root
            || self.local.total() != expected.total
        {
            return Err("c136 local ledger parent/owner/class".into());
        }
        self.work_row.validate_source_copy_for_history_test(
            sources.work,
            OWNER,
            expected.root,
            expected.total,
        )?;
        self.header_row.validate_source_copy_for_history_test(
            sources.header,
            HEADER_OWNER,
            expected.root,
            expected.total,
        )?;
        if self.work.len() != 3_265 || self.max.len() != 5_380 || self.cross.len() != 32 {
            return Err("c136 source role term census".into());
        }
        if self.work.iter().any(|term| term.row / 2_048 != OWNER)
            || self
                .cross
                .iter()
                .any(|term| term.row / 8_192 != HEADER_OWNER)
        {
            return Err("c136 separate LOCAL/CROSS row owner".into());
        }
        let mut source_work = Vec::new();
        plan.work_boundary()
            .emit_slot(OWNER, |term| source_work.push(term))?;
        if self.work != source_work {
            return Err("c136 Work source tuple mismatch".into());
        }
        let (source_cross, _) =
            super::candidate135_native_values::collect_header_nbits_terms(plan)?;
        if self.cross != source_cross {
            return Err("c136 CROSS source tuple mismatch".into());
        }
        if self.local.scheduled_max_terms() != self.max.as_slice() {
            return Err("c136 local/MAX full source tuple mismatch".into());
        }
        if sources.max.len() != 1_794 {
            return Err("c136 MAX assignment census".into());
        }
        let max_terms = self
            .max
            .iter()
            .map(|(_, term)| term.clone())
            .collect::<Vec<_>>();
        let all_active = active_addresses(&self.work)
            .union(&active_addresses(&max_terms))
            .copied()
            .collect::<BTreeSet<_>>()
            .union(&active_addresses(&self.cross))
            .copied()
            .collect::<BTreeSet<_>>();
        if self.x.cells.keys().copied().collect::<BTreeSet<_>>() != all_active {
            return Err("c136 selected active X claim census".into());
        }
        for (&address, &(value, origin)) in &self.x.cells {
            match origin {
                Origin::Native { owner } if owner == OWNER || owner == HEADER_OWNER => {
                    let row = if owner == OWNER {
                        &self.work_row
                    } else {
                        &self.header_row
                    };
                    if address / WIDTH != owner || value != packed_bit(row, address)? {
                        return Err("c136 selected native X identity/value".into());
                    }
                }
                Origin::MaxLocal {
                    owner: OWNER,
                    context,
                } if context < 2 => {
                    if !self.local.is_max(context, address)
                        || sources.max.get(&address) != Some(&value)
                    {
                        return Err("c136 local MAX X provenance/value".into());
                    }
                }
                Origin::MaxForeignRead {
                    owner: NEXT_OWNER,
                    context,
                } if context < 2 => {
                    let local = address % WIDTH;
                    if address / WIDTH != NEXT_OWNER
                        || !(MAX_BASE[context]..MAX_BASE[context] + 224).contains(&local)
                        || sources.max.get(&address) != Some(&value)
                    {
                        return Err("c136 foreign next-R read provenance/value".into());
                    }
                }
                _ => return Err("c136 selected X writer identity".into()),
            }
        }
        for context in 0..2 {
            for bit in 0..673 {
                let address = global(OWNER, MAX_BASE[context] + bit);
                if self.x.cells.get(&address).map(|cell| cell.1)
                    != Some(Origin::MaxLocal {
                        owner: OWNER,
                        context,
                    })
                {
                    return Err("c136 missing local MAX assignment".into());
                }
            }
            for bit in 0..224 {
                let address = global(NEXT_OWNER, MAX_BASE[context] + bit);
                if self.x.cells.get(&address).map(|cell| cell.1)
                    != Some(Origin::MaxForeignRead {
                        owner: NEXT_OWNER,
                        context,
                    })
                {
                    return Err("c136 missing foreign next-R import".into());
                }
            }
        }
        for bit in 0..224 {
            if !self.local.is_worktree(global(OWNER, 987_674 + bit))
                || self
                    .x
                    .cells
                    .get(&global(OWNER, 987_674 + bit))
                    .map(|cell| cell.1)
                    != Some(Origin::Native { owner: OWNER })
            {
                return Err("c136 Work D exclusive source".into());
            }
        }
        for terms in [&self.work, &max_terms, &self.cross] {
            if evaluate(terms, &self.x)?
                .values()
                .any(|residual| !residual.is_zero())
            {
                return Err("c136 joined LOCAL/MAX/CROSS residual".into());
            }
        }
        Ok(())
    }
}

impl Destination {
    fn publish(
        &mut self,
        candidate: &Candidate,
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
        expected: ParentId,
        sources: Sources<'_>,
    ) -> Result<(), String> {
        candidate.validate(plan, prefix, expected, sources)?;
        if self.parent.is_some_and(|parent| parent != expected) {
            return Err("c136 destination parent identity".into());
        }
        if self.local.is_some() || !self.work.is_empty() || !self.cross.is_empty() {
            return Err("c136 duplicate native bundle".into());
        }
        if self.parent.is_none()
            && (!self.local_rows.is_empty()
                || !self.occupied_x.is_empty()
                || !self.x.cells.is_empty())
        {
            return Err("c136 unbound nonempty destination".into());
        }
        let rows = candidate.local.row_addresses();
        if rows.iter().any(|row| self.local_rows.contains(row)) {
            return Err("c136 destination local ROW collision".into());
        }
        let domains = candidate.local.x_domains();
        if domains.iter().any(|(_, domain)| {
            self.occupied_x
                .iter()
                .any(|prior| domain.start < prior.end && prior.start < domain.end)
        }) {
            return Err("c136 destination X domain collision".into());
        }
        if candidate
            .x
            .cells
            .keys()
            .any(|address| self.x.cells.contains_key(address))
        {
            return Err("c136 destination selected X collision".into());
        }
        let mut next = self.clone();
        next.parent = Some(candidate.parent);
        next.local_rows.extend(rows);
        next.occupied_x
            .extend(domains.into_iter().map(|(_, domain)| domain));
        next.local = Some(candidate.local.clone());
        next.work = candidate.work.clone();
        next.cross = candidate.cross.clone();
        next.x.cells.extend(
            candidate
                .x
                .cells
                .iter()
                .map(|(address, cell)| (*address, *cell)),
        );
        *self = next;
        Ok(())
    }
}

fn rejected(
    candidate: &Candidate,
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    expected: ParentId,
    sources: Sources<'_>,
    destination: &mut Destination,
    needle: &str,
) -> Result<(), String> {
    let before = destination.clone();
    let error = destination
        .publish(candidate, plan, prefix, expected, sources)
        .unwrap_err();
    if !error.contains(needle) || *destination != before {
        return Err(format!("c136 negative did not isolate {needle}: {error}"));
    }
    Ok(())
}

pub(super) fn join_and_falsify(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    prepared: &Prepared,
    work_row: &NativePackedRow,
    header_row: &NativePackedRow,
    work: &[Term],
    max: &[(Writer, Term)],
    cross: &[Term],
    x: &X,
    include_map1: bool,
) -> Result<CarryMapExport, String> {
    phase("join_start");
    let source_max = expected_max_cells(prepared)?;
    let candidate = Candidate::stage(
        plan,
        prefix,
        &source_max,
        work_row,
        header_row,
        work,
        max,
        cross,
        x,
    )?;
    let expected = ParentId::from_source(plan, prefix)?;
    let sources = Sources {
        work: work_row,
        header: header_row,
        max: &source_max,
    };
    let mut destination = Destination::default();
    destination.publish(&candidate, plan, prefix, expected, sources)?;
    if destination.parent != Some(expected)
        || destination.local.as_ref() != Some(&candidate.local)
        || destination.x != candidate.x
        || destination.work != candidate.work
        || destination.cross != candidate.cross
    {
        return Err("c136 honest bundle destination".into());
    }
    let composite = candidate145_map_max_composite::join_and_falsify(
        plan,
        prefix,
        &candidate,
        sources,
        &destination,
        include_map1,
    )?;
    if candidate.parent != expected || composite.checked_parent()? != expected {
        return Err("c153 composite parent binding mismatch".into());
    }
    phase("honest_publish_complete");
    rejected(
        &candidate,
        plan,
        prefix,
        expected,
        sources,
        &mut destination,
        "duplicate native bundle",
    )?;
    drop(destination);

    let sentinel = global(OWNER + 5, 7);
    let mut nonempty = Destination {
        parent: Some(expected),
        ..Destination::default()
    };
    nonempty
        .x
        .cells
        .insert(sentinel, (Fr::one(), Origin::Native { owner: OWNER + 5 }));
    let mut destination = nonempty.clone();
    destination.publish(&candidate, plan, prefix, expected, sources)?;
    if destination.x.cells.len() != candidate.x.cells.len() + 1
        || destination.x.cells.get(&sentinel) != nonempty.x.cells.get(&sentinel)
        || candidate
            .x
            .cells
            .iter()
            .any(|(address, cell)| destination.x.cells.get(address) != Some(cell))
    {
        return Err("c136 disjoint prior selected X was not preserved".into());
    }
    drop(destination);
    drop(nonempty);

    let mut wrong_bound = Destination {
        parent: Some(expected),
        ..Destination::default()
    };
    wrong_bound
        .parent
        .as_mut()
        .ok_or("c136 bound parent absent")?
        .root[0] ^= 1;
    rejected(
        &candidate,
        plan,
        prefix,
        expected,
        sources,
        &mut wrong_bound,
        "destination parent identity",
    )?;
    drop(wrong_bound);

    let mut unbound = Destination::default();
    unbound.x.cells.insert(
        global(OWNER + 5, 7),
        (Fr::one(), Origin::Native { owner: OWNER + 5 }),
    );
    rejected(
        &candidate,
        plan,
        prefix,
        expected,
        sources,
        &mut unbound,
        "unbound nonempty destination",
    )?;

    let mut wrong_parent = candidate.clone();
    wrong_parent.parent.root[0] ^= 1;
    rejected(
        &wrong_parent,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "parent identity",
    )?;
    drop(wrong_parent);

    let mut wrong_total = candidate.clone();
    wrong_total.parent.total[0] ^= 1;
    rejected(
        &wrong_total,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "parent identity",
    )?;
    drop(wrong_total);

    let mut wrong_profile = candidate.clone();
    wrong_profile.parent.profile[0] ^= 1;
    rejected(
        &wrong_profile,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "parent identity",
    )?;
    drop(wrong_profile);

    let mut wrong_row = candidate.clone();
    crate::packed_owner_assembly::mutate_native_row_parent_for_test(&mut wrong_row.work_row);
    rejected(
        &wrong_row,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "parent/owner identity",
    )?;
    drop(wrong_row);

    // The joined equations alone also accept a coherent interval translation.
    // The original producer rows, not the mutable candidate copies, are authority.
    let mut translated = candidate.clone();
    let endpoints = &crate::work_tree_layout::shared_baseline()?.endpoints;
    let (lower, upper) = prefix.interval(OWNER + 2)?;
    for (locals, bytes) in [(&endpoints.lower, lower), (&endpoints.upper, upper)] {
        let original = BigUint::from_bytes_be(&bytes);
        let changed = &original + BigUint::from(1u8);
        if changed.bits() > 224 {
            return Err("c136 interval translation escaped U224".into());
        }
        for (bit, &local) in locals.iter().enumerate() {
            let old = original.bit(bit as u64);
            let new = changed.bit(bit as u64);
            if old != new {
                crate::packed_owner_assembly::flip_native_row_bit_for_test(
                    &mut translated.work_row,
                    local,
                )?;
                let cell = translated
                    .x
                    .cells
                    .get_mut(&global(OWNER, local))
                    .ok_or("c136 translated native X absent")?;
                if cell.1 != (Origin::Native { owner: OWNER }) {
                    return Err("c136 translated native X origin".into());
                }
                cell.0 = Fr::from(u64::from(new));
            }
        }
    }
    let translated_max = translated
        .max
        .iter()
        .map(|(_, term)| term.clone())
        .collect::<Vec<_>>();
    for terms in [&translated.work, &translated_max, &translated.cross] {
        if evaluate(terms, &translated.x)?
            .values()
            .any(|value| !value.is_zero())
        {
            return Err("c136 coherent interval translation changed joined residual".into());
        }
    }
    rejected(
        &translated,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "native source row bytes mismatch",
    )?;
    drop(translated);

    let mut wrong_work = candidate.clone();
    wrong_work.work[0].gate.c0 += Fr::one();
    rejected(
        &wrong_work,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "Work source tuple mismatch",
    )?;
    drop(wrong_work);

    let mut wrong_cross = candidate.clone();
    let gate = &mut wrong_cross.cross[0].gate;
    gate.c0 = Fr::zero();
    gate.c1 = -Fr::one();
    gate.c2 = Fr::zero();
    gate.c3 = Fr::one();
    gate.right = gate.left;
    if evaluate(&wrong_cross.cross, &wrong_cross.x)?
        .values()
        .any(|residual| !residual.is_zero())
    {
        return Err("c136 Boolean alias mutant must retain zero residual".into());
    }
    rejected(
        &wrong_cross,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "CROSS source tuple mismatch",
    )?;
    drop(wrong_cross);

    let mut missing_import = candidate.clone();
    missing_import
        .x
        .cells
        .remove(&global(NEXT_OWNER, MAX_BASE[0]));
    rejected(
        &missing_import,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "selected active X claim census",
    )?;
    drop(missing_import);

    let mut wrong_origin = candidate.clone();
    wrong_origin
        .x
        .cells
        .get_mut(&global(NEXT_OWNER, MAX_BASE[0]))
        .ok_or("c136 selected R absent")?
        .1 = Origin::MaxForeignRead {
        owner: NEXT_OWNER,
        context: 1,
    };
    rejected(
        &wrong_origin,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "foreign next-R read provenance",
    )?;
    drop(wrong_origin);

    let mut wrong_max = candidate.clone();
    let mut native_d = BigUint::from(0u8);
    for bit in 0..224 {
        if wrong_max
            .x
            .cells
            .get(&global(OWNER, 987_674 + bit))
            .ok_or("c136 native D absent")?
            .0
            .is_one()
        {
            native_d += BigUint::from(1u8) << bit;
        }
    }
    if native_d == BigUint::from(0u8)
        || (0..224)
            .all(|bit| sources.max.get(&global(NEXT_OWNER, MAX_BASE[0] + bit)) == Some(&Fr::zero()))
    {
        return Err("c136 coherent MAX mutant needs positive D and source foreign R".into());
    }
    for bit in 0..224 {
        let d_bit = Fr::from(u64::from(native_d.bit(bit as u64)));
        for (address, value) in [
            (global(OWNER, MAX_BASE[0] + bit), d_bit),
            (global(OWNER, MAX_BASE[0] + 224 + bit), Fr::zero()),
            (global(OWNER, MAX_BASE[0] + 448 + bit), d_bit),
            (global(NEXT_OWNER, MAX_BASE[0] + bit), Fr::zero()),
        ] {
            wrong_max
                .x
                .cells
                .get_mut(&address)
                .ok_or("c136 coherent MAX selected X absent")?
                .0 = value;
        }
    }
    wrong_max
        .x
        .cells
        .get_mut(&global(OWNER, MAX_BASE[0] + 672))
        .ok_or("c136 coherent MAX less bit absent")?
        .0 = Fr::zero();
    let wrong_max_terms = wrong_max
        .max
        .iter()
        .map(|(_, term)| term.clone())
        .collect::<Vec<_>>();
    for terms in [&wrong_max.work, &wrong_max_terms, &wrong_max.cross] {
        if evaluate(terms, &wrong_max.x)?
            .values()
            .any(|value| !value.is_zero())
        {
            return Err("c136 coherent MAX mutant changed joined residual".into());
        }
    }
    rejected(
        &wrong_max,
        plan,
        prefix,
        expected,
        sources,
        &mut Destination::default(),
        "local MAX X provenance/value",
    )?;
    drop(wrong_max);

    let mut occupied = Destination::default();
    occupied.parent = Some(expected);
    occupied.local_rows.insert(
        *candidate
            .local
            .row_addresses()
            .first()
            .ok_or("c136 no local ROW")?,
    );
    rejected(
        &candidate,
        plan,
        prefix,
        expected,
        sources,
        &mut occupied,
        "local ROW collision",
    )?;
    let mut occupied = Destination::default();
    occupied.parent = Some(expected);
    occupied
        .occupied_x
        .push(global(OWNER, MAX_BASE[0])..global(OWNER, MAX_BASE[0] + 1));
    rejected(
        &candidate,
        plan,
        prefix,
        expected,
        sources,
        &mut occupied,
        "X domain collision",
    )?;
    let mut occupied = Destination::default();
    occupied.parent = Some(expected);
    occupied.x.cells.insert(
        global(NEXT_OWNER, MAX_BASE[0]),
        (Fr::from(1u64), Origin::Native { owner: NEXT_OWNER }),
    );
    rejected(
        &candidate,
        plan,
        prefix,
        expected,
        sources,
        &mut occupied,
        "selected X collision",
    )?;

    phase("atomic_negatives_complete");
    phase("join_complete");

    let map0 = composite.map0_terms()?.to_vec();
    if map0.is_empty() {
        return Err("c153 Map0 term census is empty".into());
    }
    let map1 = if include_map1 {
        let terms = composite.map1_terms()?.to_vec();
        if terms.is_empty() {
            return Err("c153 requested Map1 term census is empty".into());
        }
        Some(terms)
    } else {
        if composite.map1_terms().is_ok() {
            return Err("c153 unrequested Map1 was published".into());
        }
        None
    };
    let local_rows = candidate.local.rows().clone();
    let row_addresses = candidate
        .local
        .row_addresses()
        .into_iter()
        .collect::<BTreeSet<_>>();
    if local_rows.len() != row_addresses.len()
        || local_rows.keys().copied().collect::<BTreeSet<_>>() != row_addresses
        || candidate.local.owner() != OWNER
        || candidate.local.class() != crate::daa_history_roster::OwnerClass::Carry
    {
        return Err("c153 native Carry ROW claim census".into());
    }
    let selected_x = composite
        .selected_x_claims()?
        .into_iter()
        .map(|claim| SelectedXValueClaim {
            address: claim.address,
            value: claim.value,
            role: match claim.classification {
                candidate145_map_max_composite::SelectedXClassification::Writer => {
                    SelectedXRole::Writer
                }
                candidate145_map_max_composite::SelectedXClassification::ImportedRead => {
                    SelectedXRole::ImportedRead
                }
            },
        })
        .collect::<Vec<_>>();
    let selected_addresses = selected_x
        .iter()
        .map(|claim| claim.address)
        .collect::<BTreeSet<_>>();
    if selected_x.len() != selected_addresses.len() {
        return Err("c153 selected X claim duplicate address".into());
    }
    let max_terms = candidate
        .max
        .iter()
        .map(|(_, term)| term.clone())
        .collect::<Vec<_>>();
    let mut expected_x = active_addresses(&candidate.work);
    expected_x.extend(active_addresses(&max_terms));
    expected_x.extend(active_addresses(&candidate.cross));
    expected_x.extend(active_addresses(&map0));
    if let Some(map1_terms) = &map1 {
        expected_x.extend(active_addresses(map1_terms));
    }
    if selected_addresses != expected_x
        || candidate.work.len() != 3_265
        || candidate.max.len() != 5_380
        || candidate.cross.len() != 32
    {
        return Err("c153 common selected X/term census".into());
    }

    println!("C136_NATIVE_BUNDLE_PASS owner={OWNER} parent_root={} local_rows={} local_max_terms={} local_domains={} work_terms={} max_terms={} cross_nbits={} selected_x={} foreign_next_r=448 role_namespaces=separate atomic_negatives=16 prior_disjoint_x_preserved=true proof=false client=false", hex(&expected.root), candidate.local.rows().len(), candidate.local.scheduled_max_terms().len(), candidate.local.x_domains().len(), candidate.work.len(), candidate.max.len(), candidate.cross.len(), candidate.x.cells.len());
    Ok(CarryMapExport {
        parent: expected,
        local: candidate.local,
        local_rows,
        work: candidate.work,
        max: candidate.max,
        cross: candidate.cross,
        map0,
        map1,
        selected_x,
    })
}

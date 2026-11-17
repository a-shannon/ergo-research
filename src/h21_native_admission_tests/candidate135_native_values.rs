//! Bounded native Work/MAX/HEADER value join for one admitted H21 parent.
//! This test is diagnostic only; it does not construct a proof or client.

use super::*;
use ark_ff::{One, Zero};
use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
};

use crate::{
    h21_scheduled_max_cap::{OwnerCells, Prepared, Writer},
    sparse::Term,
    work_tree_layout::{self as layout, WIDTH},
    work_tree_wiring::Mapping,
};

const OWNER: usize = 844_670;
const HEADER_OWNER: usize = OWNER + 1;
const NEXT_OWNER: usize = 844_798;
const FIRST_D: usize = 844_672;
const LAST_D: usize = 1_827_840;
const D_BASE: usize = 987_674;
const MAX_BASE: [usize; 2] = [999_424, 1_000_097];
const TERMINAL: [usize; 2] = [1_827_840, 1_827_775];
const MAX_TERMS_PER_CONTEXT: usize = 2_690;
const MAX_ROWS_PER_CONTEXT: usize = 1_122;
const HEADER_ALIAS_NAME: &str = "header_to_leaf_raw_length_nbits_height";
const HEADER_ALIAS_TERMS: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Origin {
    Native { owner: usize },
    MaxLocal { owner: usize, context: usize },
    MaxForeignRead { owner: usize, context: usize },
}

/// Only selected addresses enter this projection. Missing active operands fail closed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct X {
    pub(super) cells: BTreeMap<usize, (Fr, Origin)>,
}

impl X {
    fn insert(&mut self, address: usize, value: Fr, origin: Origin) -> Result<(), String> {
        if self.cells.contains_key(&address) {
            return Err(format!("duplicate selected X assignment {address}"));
        }
        self.cells.insert(address, (value, origin));
        Ok(())
    }

    fn insert_or_match_native(
        &mut self,
        address: usize,
        value: Fr,
        owner: usize,
    ) -> Result<(), String> {
        if address / WIDTH != owner {
            return Err(format!("selected native X owner mismatch {address}"));
        }
        if let Some((previous, _)) = self.cells.get(&address) {
            if *previous != value {
                return Err(format!("selected native X value mismatch {address}"));
            }
            if self.origin(address)? != (Origin::Native { owner }) {
                return Err(format!("selected native X provenance mismatch {address}"));
            }
            return Ok(());
        }
        self.insert(address, value, Origin::Native { owner })
    }

    fn replace(&mut self, address: usize, value: Fr) -> Result<(), String> {
        let cell = self
            .cells
            .get_mut(&address)
            .ok_or_else(|| format!("cannot replace absent selected X={address}"))?;
        cell.0 = value;
        Ok(())
    }

    fn read(&self, address: usize) -> Result<Fr, String> {
        self.cells
            .get(&address)
            .map(|cell| cell.0)
            .ok_or_else(|| format!("missing active selected X={address}"))
    }

    fn origin(&self, address: usize) -> Result<Origin, String> {
        self.cells
            .get(&address)
            .map(|cell| cell.1)
            .ok_or_else(|| format!("missing selected X source {address}"))
    }
}

fn global(owner: usize, local: usize) -> usize {
    owner * WIDTH + local
}

fn packed(row: &NativePackedRow, owner: usize, address: usize) -> Result<Fr, String> {
    if row.owner() != owner || address / WIDTH != owner || row.packed_bytes().len() != WIDTH / 8 {
        return Err("native selected row/address identity".into());
    }
    let local = address % WIDTH;
    Ok(Fr::from(
        ((row.packed_bytes()[local / 8] >> (local % 8)) & 1) as u64,
    ))
}

fn active_left(term: &Term) -> bool {
    !term.gate.c1.is_zero() || !term.gate.c3.is_zero()
}

fn active_right(term: &Term) -> bool {
    !term.gate.c2.is_zero() || !term.gate.c3.is_zero()
}

pub(super) fn active_addresses(terms: &[Term]) -> std::collections::BTreeSet<usize> {
    terms
        .iter()
        .flat_map(|term| {
            [
                active_left(term).then_some(term.gate.left),
                active_right(term).then_some(term.gate.right),
            ]
            .into_iter()
            .flatten()
        })
        .filter(|address| *address != 0)
        .collect()
}

pub(super) fn evaluate(terms: &[Term], x: &X) -> Result<BTreeMap<usize, Fr>, String> {
    let mut rows = BTreeMap::<usize, Fr>::new();
    for term in terms {
        let gate = &term.gate;
        let left = if active_left(term) {
            x.read(gate.left)?
        } else {
            Fr::zero()
        };
        let right = if active_right(term) {
            x.read(gate.right)?
        } else {
            Fr::zero()
        };
        *rows.entry(term.row).or_insert_with(Fr::zero) +=
            gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
    }
    Ok(rows)
}

fn nonzero_rows(rows: &BTreeMap<usize, Fr>) -> usize {
    rows.values().filter(|value| !value.is_zero()).count()
}

fn nonzero_rows_in(rows: &BTreeMap<usize, Fr>, range: std::ops::Range<usize>) -> usize {
    rows.iter()
        .filter(|(row, value)| range.contains(row) && !value.is_zero())
        .count()
}

fn replace_bits(x: &mut X, owner: usize, locals: &[usize], value: &BigUint) -> Result<(), String> {
    for (bit, &local) in locals.iter().enumerate() {
        x.replace(
            global(owner, local),
            Fr::from(u64::from(value.bit(bit as u64))),
        )?;
    }
    Ok(())
}

fn project_native(
    x: &mut X,
    addresses: &std::collections::BTreeSet<usize>,
    rows: &[&NativePackedRow],
) -> Result<(), String> {
    let by_owner = rows
        .iter()
        .map(|row| (row.owner(), *row))
        .collect::<BTreeMap<_, _>>();
    for &address in addresses {
        let owner = address / WIDTH;
        let row = by_owner
            .get(&owner)
            .ok_or_else(|| format!("no selected native producer row for X={address}"))?;
        x.insert_or_match_native(address, packed(row, owner, address)?, owner)?;
    }
    Ok(())
}

fn native_d_stream<'a>(
    prefix: &'a NativePrefix,
    last_height: &'a Cell<usize>,
    error: &'a RefCell<Option<String>>,
    override_nbits: Option<(usize, u32)>,
) -> impl Iterator<Item = (usize, BigUint)> + 'a {
    struct Ds<'a> {
        prefix: &'a NativePrefix,
        next: usize,
        last_height: &'a Cell<usize>,
        error: &'a RefCell<Option<String>>,
        override_nbits: Option<(usize, u32)>,
    }
    impl Iterator for Ds<'_> {
        type Item = (usize, BigUint);

        fn next(&mut self) -> Option<Self::Item> {
            if self.next > LAST_D {
                return None;
            }
            let height = self.next;
            self.next += 1;
            self.last_height.set(height);
            let result = self
                .override_nbits
                .filter(|(override_height, _)| *override_height == height)
                .map(|(_, nbits)| Ok(nbits))
                .unwrap_or_else(|| self.prefix.compact_n_bits(height))
                .and_then(crate::work_tree_work::native_decode);
            match result {
                Ok(value) => Some((height, value)),
                Err(failure) => {
                    *self.error.borrow_mut() = Some(format!("native D height={height}: {failure}"));
                    self.next = LAST_D + 1;
                    None
                }
            }
        }
    }

    Ds {
        prefix,
        next: FIRST_D,
        last_height,
        error,
        override_nbits,
    }
}

pub(super) fn collect_header_nbits_terms(
    plan: &WorkTreeHistoryPlan,
) -> Result<(Vec<Term>, Vec<(usize, usize)>), String> {
    let base = layout::shared_baseline()?;
    let mut matches = plan
        .topology()
        .families
        .iter()
        .filter(|family| family.name == HEADER_ALIAS_NAME);
    let family = matches.next().ok_or("HEADER successor family missing")?;
    if matches.next().is_some()
        || !matches!(family.mapping, Mapping::HeaderSuccessor { lo: 1, hi } if hi == N)
        || family.left_wires != base.header_alias_wires
        || family.right_wires != base.endpoints.header_aliases()
        || family.constants.is_some()
    {
        return Err("HEADER successor family identity".into());
    }
    let first_nbits = base.endpoints.raw.len() + base.endpoints.length.len();
    if base.endpoints.n_bits.len() != HEADER_ALIAS_TERMS
        || first_nbits + HEADER_ALIAS_TERMS > family.left_wires.len()
    {
        return Err("HEADER nBits ordinal range".into());
    }

    let mut terms = Vec::with_capacity(HEADER_ALIAS_TERMS);
    let mut bit_addresses = Vec::with_capacity(HEADER_ALIAS_TERMS);
    family.emit_endpoint_terms(
        plan.descriptor(),
        true,
        HEADER_OWNER,
        |slot, ordinal, term| {
            if slot != HEADER_OWNER {
                return Err("HEADER successor source slot".into());
            }
            if !(first_nbits..first_nbits + HEADER_ALIAS_TERMS).contains(&ordinal) {
                return Ok(());
            }
            let bit = ordinal - first_nbits;
            let gate = &term.gate;
            if term.row != slot * family.left_wires.len().next_power_of_two() + ordinal
                || gate.left != global(slot, base.header_alias_wires[ordinal])
                || gate.right != global(OWNER, base.endpoints.n_bits[bit])
                || gate.c0 != Fr::zero()
                || gate.c1 != Fr::one()
                || gate.c2 != -Fr::one()
                || gate.c3 != Fr::zero()
            {
                return Err("HEADER nBits successor term identity".into());
            }
            bit_addresses.push((gate.left, gate.right));
            terms.push(term);
            Ok(())
        },
    )?;
    if terms.len() != HEADER_ALIAS_TERMS
        || bit_addresses.len() != HEADER_ALIAS_TERMS
        || bit_addresses
            .iter()
            .map(|pair| pair.0)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != HEADER_ALIAS_TERMS
        || bit_addresses
            .iter()
            .map(|pair| pair.1)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != HEADER_ALIAS_TERMS
    {
        return Err("HEADER nBits source census".into());
    }
    Ok((terms, bit_addresses))
}

fn patch_cells(
    prepared: &Prepared,
    owner: usize,
) -> Result<(OwnerCells, std::collections::BTreeSet<Writer>), String> {
    let mut cells = OwnerCells::new(owner)?;
    prepared.owner_patch(owner)?.apply(&mut cells)?;
    let mut writers = std::collections::BTreeSet::new();
    prepared.plan().visit_owner(owner, |writer, _| {
        writers.insert(writer);
        Ok(())
    })?;
    Ok((cells, writers))
}

fn project_max_cells(
    x: &mut X,
    cells: &OwnerCells,
    owner: usize,
    contexts: &[usize],
    local: bool,
) -> Result<usize, String> {
    let mut count = 0;
    for &context in contexts {
        for offset in 0..673 {
            let address = global(owner, MAX_BASE[context] + offset);
            let origin = if local {
                Origin::MaxLocal { owner, context }
            } else {
                Origin::MaxForeignRead { owner, context }
            };
            x.insert(address, cells.read(MAX_BASE[context] + offset)?, origin)?;
            count += 1;
        }
    }
    Ok(count)
}

fn replace_max_projection(
    x: &mut X,
    cells: &OwnerCells,
    owner: usize,
    contexts: &[usize],
    local: bool,
) -> Result<(), String> {
    for &context in contexts {
        for offset in 0..if local { 673 } else { 224 } {
            x.replace(
                global(owner, MAX_BASE[context] + offset),
                cells.read(MAX_BASE[context] + offset)?,
            )?;
        }
    }
    Ok(())
}

#[test]
fn candidate135_native_projection_identity_and_atomic_negatives() {
    let owner = 844_670;
    let address = global(owner, 7);
    let value = Fr::from(1u64);

    let mut wrong_origin = X::default();
    wrong_origin
        .insert(address, value, Origin::MaxLocal { owner, context: 0 })
        .unwrap();
    let before = wrong_origin.cells.clone();
    assert!(wrong_origin
        .insert_or_match_native(address, value, owner)
        .unwrap_err()
        .contains("provenance"));
    assert_eq!(
        wrong_origin.cells, before,
        "equal-value provenance rejection mutated X"
    );

    assert!(wrong_origin
        .insert_or_match_native(address, value, owner + 1)
        .unwrap_err()
        .contains("owner"));
    assert_eq!(wrong_origin.cells, before, "owner rejection mutated X");

    let mut native = X::default();
    native
        .insert(address, value, Origin::Native { owner })
        .unwrap();
    native
        .insert_or_match_native(address, value, owner)
        .expect("equal native value with exact owner provenance should match");
    assert_eq!(native.cells.len(), 1);
    let before = native.cells.clone();
    assert!(native
        .insert(address, value, Origin::Native { owner })
        .unwrap_err()
        .contains("duplicate"));
    assert_eq!(native.cells, before, "duplicate collision mutated X");
    assert!(native
        .insert_or_match_native(address, Fr::from(2u64), owner)
        .unwrap_err()
        .contains("value mismatch"));
    assert_eq!(native.cells, before, "value mismatch rejection mutated X");
}

#[test]
#[ignore = "full pinned ERFV native H21 Work/MAX/HEADER join; no proof or client claim"]
fn candidate135_native_work_max_header_value_join() -> Result<(), String> {
    run_native_work_max_header_value_join(false)
}

#[test]
#[ignore = "one-use pinned ERFV native owner844670 Work/MAX/CROSS/Map0/Map1 composite; no proof or client claim"]
fn h21_candidate150_native_carry_owner_composite() -> Result<(), String> {
    run_native_work_max_header_value_join(true)
}

fn run_native_work_max_header_value_join(include_map1: bool) -> Result<(), String> {
    let started = Instant::now();
    let path = std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned frame path missing")?;
    let path = Path::new(&path);
    if !path.is_absolute() {
        return Err("pinned frame path must be absolute".into());
    }
    let before = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != FRAME_BYTES {
        return Err("pinned frame type/length mismatch".into());
    }
    let file = File::open(path).map_err(|error| error.to_string())?;
    if file.metadata().map_err(|error| error.to_string())?.len() != FRAME_BYTES {
        return Err("opened pinned frame length mismatch".into());
    }
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
    preamble(&mut frame, 1_827_839, N as u32)?;
    phase("C135_NATIVE_PREFIX_START");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("not all pinned ERFV records were consumed".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("pinned H21 frame prefix census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
    let after = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !after.is_file()
        || after.file_type().is_symlink()
        || after.len() != FRAME_BYTES
        || after.modified().map_err(|error| error.to_string())?
            != before.modified().map_err(|error| error.to_string())?
    {
        return Err("pinned frame changed during full SHA256 read".into());
    }
    phase("C135_FRAME_SHA256_OK");
    println!(
        "C135_PHASE frame_parse_sha_s={:.6} records={N} extensions={extensions} frame_sha256={FRAME_SHA256}",
        started.elapsed().as_secs_f64()
    );

    let compile_started = Instant::now();
    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
    validate_native_plan_input(&plan, &prefix)?;
    if plan.descriptor().root != prefix.root()
        || plan.work_profile().total_be28 != prefix.total_be28()
        || plan.headers() != N as u64
        || plan.slot_log() != H
    {
        return Err("compiled parent root/total/profile geometry mismatch".into());
    }
    phase("C135_PARENT_BOUND");
    println!(
        "C135_PHASE parent_compile_validate_s={:.6} root={} total={} profile={}",
        compile_started.elapsed().as_secs_f64(),
        hex(&prefix.root()),
        hex(&prefix.total_be28()),
        hex(&prefix.profile()),
    );

    run_native_work_max_header_value_join_from_verified(&plan, &prefix, include_map1, started)?;
    Ok(())
}

pub(super) fn run_native_work_max_header_value_join_from_verified(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    include_map1: bool,
    started: Instant,
) -> Result<super::candidate136_native_bundle::CarryMapExport, String> {
    let prepare_started = Instant::now();
    let last_height = Cell::new(0usize);
    let stream_error = RefCell::new(None);
    let prepared_result =
        Prepared::from_d_iter(native_d_stream(prefix, &last_height, &stream_error, None));
    if let Some(error) = stream_error.into_inner() {
        return Err(error);
    }
    let prepared = prepared_result?;
    if last_height.get() != LAST_D {
        return Err(format!("native D stream stopped at {}", last_height.get()));
    }
    let d_count = LAST_D - FIRST_D + 1;
    if d_count != 983_169 {
        return Err("native D source height count constant".into());
    }
    phase("C135_D_PREPARED");
    println!(
        "C135_PHASE prepared_from_d_iter_s={:.6} native_d_values={d_count} first={FIRST_D} last={LAST_D} duplicate_d_vector=false",
        prepare_started.elapsed().as_secs_f64()
    );

    let source_started = Instant::now();
    let producer = NativeOwnerProducer::new_for_history(plan, prefix)?;
    let work_row = producer.produce(OWNER)?;
    let header_row = producer.produce(HEADER_OWNER)?;
    drop(producer);
    if work_row.owner() != OWNER || header_row.owner() != HEADER_OWNER {
        return Err("native packed producer owner identity".into());
    }
    let compact = prefix.compact_n_bits(FIRST_D)?;
    let native_d = crate::work_tree_work::native_decode(compact)?;
    let mut work_terms = Vec::new();
    plan.work_boundary()
        .emit_slot(OWNER, |term| work_terms.push(term))?;
    let groups = plan.work_boundary().groups();
    let expected_work_terms = groups
        .iter()
        .filter(|group| group.name != "padding_arithmetic_zero")
        .map(|group| group.term_count)
        .sum::<usize>();
    let expected_work_rows = groups
        .iter()
        .filter(|group| group.name != "padding_arithmetic_zero")
        .map(|group| group.rows.len())
        .sum::<usize>();
    if work_terms.len() != expected_work_terms {
        return Err("Work source term census differs from the profile".into());
    }
    let work_rows = work_terms
        .iter()
        .map(|term| term.row)
        .collect::<std::collections::BTreeSet<_>>();
    if work_rows.len() != expected_work_rows {
        return Err("Work source active ROW census differs from the profile".into());
    }

    let (max_cells, max_writers) = patch_cells(&prepared, OWNER)?;
    let expected_writers = std::collections::BTreeSet::from([
        Writer::Max {
            context: 0,
            end: FIRST_D,
        },
        Writer::Max {
            context: 1,
            end: FIRST_D,
        },
    ]);
    if max_writers != expected_writers {
        return Err("Carry owner typed context/end census".into());
    }
    let max_terms = {
        let mut out = Vec::new();
        let counts = prepared.plan().visit_owner(OWNER, |writer, term| {
            if !expected_writers.contains(&writer) {
                return Err("unexpected MAX source writer".into());
            }
            out.push((writer, term));
            Ok(())
        })?;
        if counts.max != [MAX_TERMS_PER_CONTEXT; 2] || counts.cap != [0; 2] {
            return Err("Carry MAX/Cap term census".into());
        }
        out
    };
    let max_rows_by_context = [0, 1].map(|context| {
        max_terms
            .iter()
            .filter(|(writer, _)| matches!(writer, Writer::Max { context: c, .. } if *c == context))
            .map(|(_, term)| term.row)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
    });
    if max_rows_by_context != [MAX_ROWS_PER_CONTEXT; 2] {
        return Err("Carry MAX active ROW census".into());
    }

    let (next_cells, next_writers) = patch_cells(&prepared, NEXT_OWNER)?;
    let expected_next_writers = std::collections::BTreeSet::from([
        Writer::Max {
            context: 0,
            end: FIRST_D + 128,
        },
        Writer::Max {
            context: 1,
            end: FIRST_D + 128,
        },
    ]);
    if next_writers != expected_next_writers {
        return Err("foreign next-R typed context/end census".into());
    }
    for context in 0..2 {
        let mut terminal_owners = std::collections::BTreeSet::new();
        prepared
            .plan()
            .visit_owner(TERMINAL[context] - 2, |writer, _| {
                terminal_owners.insert(writer);
                Ok(())
            })?;
        if !terminal_owners.contains(&Writer::Max {
            context,
            end: TERMINAL[context],
        }) {
            return Err("distinct MAX terminal context census".into());
        }
    }

    let (header_terms, header_pairs) = collect_header_nbits_terms(plan)?;
    let mut x = X::default();
    project_native(
        &mut x,
        &active_addresses(&work_terms),
        &[&work_row, &header_row],
    )?;
    let header_left = header_pairs.iter().map(|pair| pair.0).collect();
    project_native(&mut x, &header_left, &[&header_row])?;
    let local_cells = project_max_cells(&mut x, &max_cells, OWNER, &[0, 1], true)?;
    let mut next_read_count = 0;
    for context in 0..2 {
        for bit in 0..224 {
            let address = global(NEXT_OWNER, MAX_BASE[context] + bit);
            x.insert(
                address,
                next_cells.read(MAX_BASE[context] + bit)?,
                Origin::MaxForeignRead {
                    owner: NEXT_OWNER,
                    context,
                },
            )?;
            next_read_count += 1;
        }
    }
    if local_cells != 1_346 || next_read_count != 448 {
        return Err("MAX local/foreign selected value census".into());
    }
    phase("C135_SOURCE_PROJECTION_READY");
    println!(
        "C135_PHASE producer_terms_projection_s={:.6} native_rows=2 work_terms={} max_terms={} header_terms={} max_local_values={local_cells} foreign_r_reads={next_read_count}",
        source_started.elapsed().as_secs_f64(),
        work_terms.len(),
        max_terms.len(),
        header_terms.len(),
    );
    let expected_max_addresses = active_addresses(
        &max_terms
            .iter()
            .map(|(_, term)| term.clone())
            .collect::<Vec<_>>(),
    );
    let expected_max_count = 1_346 + 224 + 448;
    if expected_max_addresses.len() != expected_max_count {
        return Err("MAX selected active-X address census".into());
    }
    for address in &expected_max_addresses {
        x.read(*address)?;
        match address / WIDTH {
            OWNER if (D_BASE..D_BASE + 224).contains(&(address % WIDTH)) => {
                if x.origin(*address)? != (Origin::Native { owner: OWNER }) {
                    return Err("MAX D source is not the native Work row".into());
                }
            }
            OWNER if (MAX_BASE[0]..MAX_BASE[0] + 673).contains(&(address % WIDTH)) => {
                if x.origin(*address)?
                    != (Origin::MaxLocal {
                        owner: OWNER,
                        context: 0,
                    })
                {
                    return Err("MAX context 0 local source identity".into());
                }
            }
            OWNER if (MAX_BASE[1]..MAX_BASE[1] + 673).contains(&(address % WIDTH)) => {
                if x.origin(*address)?
                    != (Origin::MaxLocal {
                        owner: OWNER,
                        context: 1,
                    })
                {
                    return Err("MAX context 1 local source identity".into());
                }
            }
            NEXT_OWNER if (MAX_BASE[0]..MAX_BASE[0] + 224).contains(&(address % WIDTH)) => {
                if x.origin(*address)?
                    != (Origin::MaxForeignRead {
                        owner: NEXT_OWNER,
                        context: 0,
                    })
                {
                    return Err("MAX context 0 next-R read identity".into());
                }
            }
            NEXT_OWNER if (MAX_BASE[1]..MAX_BASE[1] + 224).contains(&(address % WIDTH)) => {
                if x.origin(*address)?
                    != (Origin::MaxForeignRead {
                        owner: NEXT_OWNER,
                        context: 1,
                    })
                {
                    return Err("MAX context 1 next-R read identity".into());
                }
            }
            _ => return Err(format!("MAX read escaped selected X projection: {address}")),
        }
    }
    let mut missing_r = x.clone();
    missing_r.cells.remove(&global(NEXT_OWNER, MAX_BASE[0]));
    if !evaluate(
        &max_terms
            .iter()
            .map(|(_, term)| term.clone())
            .collect::<Vec<_>>(),
        &missing_r,
    )
    .unwrap_err()
    .contains("missing active selected X")
    {
        return Err("missing foreign next-R import did not fail closed".into());
    }
    drop(missing_r);
    for (header_address, work_address) in &header_pairs {
        if x.origin(*header_address)?
            != (Origin::Native {
                owner: HEADER_OWNER,
            })
            || x.origin(*work_address)? != (Origin::Native { owner: OWNER })
        {
            return Err("HEADER nBits alias source ownership".into());
        }
    }

    let mut d_from_work = BigUint::from(0u8);
    for bit in 0..224 {
        if x.read(global(OWNER, D_BASE + bit))?.is_one() {
            d_from_work += BigUint::from(1u8) << bit;
        }
    }
    if d_from_work != native_d {
        return Err("Work.D(844672) differs from native compact nBits decode".into());
    }
    let baseline = layout::shared_baseline()?;
    if baseline.endpoints.work != (0..224).map(|bit| D_BASE + bit).collect::<Vec<_>>() {
        return Err("Work difficulty wire identity changed".into());
    }
    let residual_started = Instant::now();
    let work_residuals = evaluate(&work_terms, &x)?;
    let max_term_values = max_terms
        .iter()
        .map(|(_, term)| term.clone())
        .collect::<Vec<_>>();
    let max_residuals = evaluate(&max_term_values, &x)?;
    let header_residuals = evaluate(&header_terms, &x)?;
    if nonzero_rows(&work_residuals) != 0
        || nonzero_rows(&max_residuals) != 0
        || nonzero_rows(&header_residuals) != 0
    {
        return Err(format!(
            "native join residuals Work={} MAX={} HEADER={}",
            nonzero_rows(&work_residuals),
            nonzero_rows(&max_residuals),
            nonzero_rows(&header_residuals)
        ));
    }
    if header_terms.len() != HEADER_ALIAS_TERMS {
        return Err("HEADER nBits residual source census".into());
    }
    phase("C135_HONEST_RESIDUALS_ZERO");

    let export = super::candidate136_native_bundle::join_and_falsify(
        plan,
        prefix,
        &prepared,
        &work_row,
        &header_row,
        &work_terms,
        &max_terms,
        &header_terms,
        &x,
        include_map1,
    )?;

    let native_nbits = compact;
    let exponent = native_nbits >> 24;
    let lower_bytes = prefix.interval(FIRST_D)?.0;
    let lower = BigUint::from_bytes_be(&lower_bytes);
    let alternate = (0..23)
        .find_map(|bit| {
            let nbits = native_nbits ^ (1u32 << bit);
            if nbits >> 24 != exponent {
                return None;
            }
            let difficulty = crate::work_tree_work::native_decode(nbits).ok()?;
            if difficulty == native_d || (&lower + &difficulty).bits() > 224 {
                return None;
            }
            Some((nbits, difficulty))
        })
        .ok_or("no valid same-exponent alternate compact nBits")?;
    let (alternate_nbits, alternate_d) = alternate;
    if alternate_d.is_zero() || alternate_d.bits() > 224 {
        return Err("alternate native difficulty outside positive U224".into());
    }
    let alternate_upper = &lower + &alternate_d;
    if alternate_upper.bits() > 224 {
        return Err("alternate native upper interval outside U224".into());
    }
    phase("C135_ALTERNATE_NBITS_SELECTED");
    println!(
        "C135_PHASE alternate_nbits original={native_nbits:#010x} alternate={alternate_nbits:#010x} exponent={exponent} d_bits={} d_prime_bits={}",
        native_d.bits(),
        alternate_d.bits(),
    );

    drop(prepared);
    let mutant_prepare_started = Instant::now();
    let mutant_last_height = Cell::new(0usize);
    let mutant_stream_error = RefCell::new(None);
    let mutant_prepared_result = Prepared::from_d_iter(native_d_stream(
        prefix,
        &mutant_last_height,
        &mutant_stream_error,
        Some((FIRST_D, alternate_nbits)),
    ));
    if let Some(error) = mutant_stream_error.into_inner() {
        return Err(error);
    }
    let mutant_prepared = mutant_prepared_result?;
    if mutant_last_height.get() != LAST_D {
        return Err(format!(
            "alternate native D stream stopped at {}",
            mutant_last_height.get()
        ));
    }
    let (mutant_local_cells, mutant_local_writers) = patch_cells(&mutant_prepared, OWNER)?;
    let (mutant_next_cells, mutant_next_writers) = patch_cells(&mutant_prepared, NEXT_OWNER)?;
    if mutant_local_writers != expected_writers || mutant_next_writers != expected_next_writers {
        return Err("alternate MAX context/end writer census".into());
    }
    for context in 0..2 {
        for bit in 0..224 {
            if mutant_next_cells.read(MAX_BASE[context] + bit)?
                != next_cells.read(MAX_BASE[context] + bit)?
            {
                return Err("alternate first-epoch D changed suffix next-R import".into());
            }
        }
    }
    phase("C135_ALTERNATE_MAX_PREPARED");
    println!(
        "C135_PHASE alternate_prepared_from_d_iter_s={:.6} native_d_values={d_count} suffix_next_r_unchanged=true",
        mutant_prepare_started.elapsed().as_secs_f64(),
    );

    let mut a0 = x.clone();
    replace_bits(&mut a0, OWNER, &baseline.endpoints.work, &alternate_d)?;
    replace_max_projection(&mut a0, &mutant_local_cells, OWNER, &[0, 1], true)?;
    replace_max_projection(&mut a0, &mutant_next_cells, NEXT_OWNER, &[0, 1], false)?;
    let a0_work_residuals = evaluate(&work_terms, &a0)?;
    let a0_max_residuals = evaluate(&max_term_values, &a0)?;
    let a0_header_residuals = evaluate(&header_terms, &a0)?;
    let a0_work = nonzero_rows(&a0_work_residuals);
    let a0_max = nonzero_rows(&a0_max_residuals);
    let a0_header = nonzero_rows(&a0_header_residuals);
    if a0_max != 0 || a0_work == 0 || a0_header != 0 {
        return Err(format!(
            "strict D-prime/MAX-only mutant residuals MAX={a0_max} Work={a0_work} HEADER={a0_header}"
        ));
    }
    phase("C135_MUTANT_A0_RESIDUALS_MEASURED");
    println!(
        "C135_MUTANT_A0 max_nonzero_rows={a0_max} work_nonzero_rows={a0_work} header_nonzero_rows={a0_header} work_helpers=native"
    );

    let mut a1 = a0.clone();
    replace_bits(
        &mut a1,
        OWNER,
        &baseline.endpoints.work_minus_one,
        &(&alternate_d - BigUint::from(1u8)),
    )?;
    replace_bits(&mut a1, OWNER, &baseline.endpoints.upper, &alternate_upper)?;
    let a1_work_residuals = evaluate(&work_terms, &a1)?;
    let a1_max_residuals = evaluate(&max_term_values, &a1)?;
    let a1_header_residuals = evaluate(&header_terms, &a1)?;
    let decoded_group = plan.work_boundary().group("decoded_work")?;
    let decoded_rows = OWNER * 2_048 + decoded_group.start..OWNER * 2_048 + decoded_group.end;
    let a1_decoded = nonzero_rows_in(&a1_work_residuals, decoded_rows);
    let a1_work = nonzero_rows(&a1_work_residuals);
    let a1_max = nonzero_rows(&a1_max_residuals);
    let a1_header = nonzero_rows(&a1_header_residuals);
    if a1_max != 0 || a1_decoded == 0 || a1_work != a1_decoded || a1_header != 0 {
        return Err(format!(
            "decoded-work isolation mutant residuals MAX={a1_max} Work={a1_work} decoded_work={a1_decoded} HEADER={a1_header}"
        ));
    }
    phase("C135_MUTANT_A1_RESIDUALS_MEASURED");
    println!(
        "C135_MUTANT_A1 max_nonzero_rows={a1_max} work_nonzero_rows={a1_work} decoded_work_nonzero_rows={a1_decoded} header_nonzero_rows={a1_header}"
    );

    let mut b = a1;
    replace_bits(
        &mut b,
        OWNER,
        &baseline.endpoints.n_bits,
        &BigUint::from(alternate_nbits),
    )?;
    let b_work_residuals = evaluate(&work_terms, &b)?;
    let b_max_residuals = evaluate(&max_term_values, &b)?;
    let b_header_residuals = evaluate(&header_terms, &b)?;
    let b_work = nonzero_rows(&b_work_residuals);
    let b_max = nonzero_rows(&b_max_residuals);
    let b_header = nonzero_rows(&b_header_residuals);
    if b_max != 0 || b_work != 0 || b_header == 0 {
        return Err(format!(
            "D-prime/Work mutant residuals MAX={b_max} Work={b_work} HEADER={b_header}"
        ));
    }
    phase("C135_MUTANT_B_RESIDUALS_MEASURED");
    println!(
        "C135_MUTANT_B max_nonzero_rows={b_max} work_nonzero_rows={b_work} header_nonzero_rows={b_header}"
    );
    phase("C135_EXPECTED_MUTANT_RESIDUALS_MEASURED");
    println!(
        "C135_PHASE residual_evaluation_s={:.6}",
        residual_started.elapsed().as_secs_f64(),
    );
    println!(
        "C135_NATIVE_VALUES_PASS owner={OWNER} next_r_owner={NEXT_OWNER} native_d_values={d_count} max_terms={} max_rows={} max_local_values={local_cells} max_foreign_r_reads={next_read_count} header_nbits_terms={} work_terms={} work_rows={} x_cells={} residual_nonzero_work={} residual_nonzero_max={} residual_nonzero_header={} mutant_a0_max={a0_max} mutant_a0_work={a0_work} mutant_a0_header={a0_header} mutant_a1_max={a1_max} mutant_a1_work={a1_work} mutant_a1_decoded={a1_decoded} mutant_a1_header={a1_header} mutant_b_max={b_max} mutant_b_work={b_work} mutant_b_header={b_header} elapsed_s={:.6} proof=false client=false",
        max_terms.len(),
        max_residuals.len(),
        header_terms.len(),
        work_terms.len(),
        work_residuals.len(),
        x.cells.len(),
        nonzero_rows(&work_residuals),
        nonzero_rows(&max_residuals),
        nonzero_rows(&header_residuals),
        started.elapsed().as_secs_f64(),
    );
    Ok(export)
}

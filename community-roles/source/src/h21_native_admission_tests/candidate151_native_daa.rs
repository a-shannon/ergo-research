//! Binds the mature EIP owner window to the already admitted native H21 prefix.
//! This stages one DAA ROW/X source for a later common-union consumer; it does
//! not publish a proof or claim a complete light client.

use std::collections::BTreeMap;

use ark_ff::One;
use ark_ff::PrimeField;
use ark_ff::Zero;

use crate::{
    daa_history_producer::{self, RawWindow, Receipt},
    daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS},
    daa_integer::Epoch,
    h21_scheduled_max_cap::Plan as Scheduled,
    header_daa_row_placement::{Producer, Relation, RowPlan},
    native_owner_exports::NativeExports,
    packed_owner_assembly::{validate_native_plan_input, NativePrefix},
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH,
};

const OWNER: u64 = 844_672;
const CHILD_HEIGHT: usize = 844_673;
const SAMPLE_HEIGHTS: [usize; 9] = [
    843_648, 843_776, 843_904, 844_032, 844_160, 844_288, 844_416, 844_544, 844_672,
];
const HISTORY_HEADERS: u64 = 1_827_840;
const HISTORY_SLOT_LOG: usize = 21;

/// A staged DAA row. `packed_owner` is seeded from the native child header and
/// patched by the DAA writer; only `bank_patches` are DAA-owned X claims. The
/// ROW terms and foreign imports are source-derived and ready for a later join.
pub(crate) struct NativeDaaStage {
    owner: u64,
    packed_owner: Vec<u8>,
    row_terms: Vec<Term>,
    bank_patches: Vec<(std::ops::Range<usize>, Vec<u8>)>,
    external_values: BTreeMap<usize, bool>,
    serializer_import_values: BTreeMap<usize, bool>,
    serializer_import_targets: BTreeMap<usize, usize>,
    receipt: Receipt,
    plan_root: [u8; 32],
    plan_total_be28: [u8; 28],
}

impl NativeDaaStage {
    pub(super) fn owner(&self) -> u64 {
        self.owner
    }

    pub(super) fn parent_root(&self) -> [u8; 32] {
        self.plan_root
    }

    pub(super) fn parent_total_be28(&self) -> [u8; 28] {
        self.plan_total_be28
    }

    pub(super) fn row_terms(&self) -> &[Term] {
        &self.row_terms
    }

    /// Only these four source patches are DAA-owned writes. The remaining
    /// packed-owner bits come from the native child header.
    pub(super) fn bank_patches(&self) -> &[(std::ops::Range<usize>, Vec<u8>)] {
        &self.bank_patches
    }

    pub(super) fn external_values(&self) -> &BTreeMap<usize, bool> {
        &self.external_values
    }

    /// Typed foreign timestamp/height imports already validated against the
    /// admitted native prefix. This is a read-only source map for the later
    /// HeaderSerializer X-writer diagnostic; nBits cells remain callback reads.
    pub(super) fn serializer_import_values(&self) -> &BTreeMap<usize, bool> {
        &self.serializer_import_values
    }

    /// Exact DAA alias target for each validated foreign serializer source.
    pub(super) fn serializer_import_targets(&self) -> &BTreeMap<usize, usize> {
        &self.serializer_import_targets
    }

    /// Read one validated owner-local bit for the downstream diagnostic X
    /// closure. This exposes no mutable packed storage or foreign addresses.
    pub(super) fn packed_owner_bit(&self, local: usize) -> Result<bool, String> {
        if self.owner != OWNER
            || self.packed_owner.len() != daa_history_producer::PACKED_OWNER_BYTES
            || local >= WIDTH
        {
            return Err("c151 packed owner bit extent/identity".into());
        }
        Ok((self.packed_owner[local / 8] >> (local % 8)) & 1 != 0)
    }

    /// Return the exact DAA rows after common ROW placement. The independent
    /// RowPlan batch check binds this result to the declared DAA lanes.
    pub(super) fn placed_row_terms(&self, plan: &WorkTreeHistoryPlan) -> Result<Vec<Term>, String> {
        if plan.headers() != HISTORY_HEADERS
            || plan.slot_log() != HISTORY_SLOT_LOG
            || plan.slots() != 1usize << HISTORY_SLOT_LOG
            || self.plan_root != plan.descriptor().root
            || self.plan_total_be28 != plan.work_profile().total_be28
        {
            return Err("c151 DAA source/placement plan binding mismatch".into());
        }
        if self.owner != OWNER {
            return Err("c151 DAA placement owner mismatch".into());
        }

        let roster = DaaHistoryRoster::compile(plan)?;
        if roster.owner_class(OWNER)? != OwnerClass::Mature(Epoch::Eip)
            || self.receipt.owner != OWNER
            || self.receipt.class != OwnerClass::Mature(Epoch::Eip)
        {
            return Err("c151 DAA placement source class mismatch".into());
        }

        let mut roster_terms = Vec::new();
        let roster_counts = roster.visit_owner_terms(OWNER, |term| {
            roster_terms.push(term);
            Ok(())
        })?;
        if roster_counts != self.receipt.counts {
            return Err("c151 DAA placement receipt lane counts mismatch".into());
        }

        let owner_rows = 1usize << 19;
        let owner_base = (OWNER as usize)
            .checked_mul(owner_rows)
            .ok_or("c151 DAA placement owner base overflow")?;
        let mut source_lane_counts = [0usize; 4];
        for term in &self.row_terms {
            let q = term
                .row
                .checked_sub(owner_base)
                .filter(|q| *q < owner_rows)
                .ok_or("c151 DAA source ROW owner")?;
            source_lane_counts[q >> 17] += 1;
        }
        if source_lane_counts != self.receipt.counts.lanes
            || term_multiset(self.row_terms.iter().cloned())
                != term_multiset(roster_terms.iter().cloned())
        {
            return Err("c151 DAA source ROW terms differ from roster".into());
        }

        let scheduled = Scheduled::new();
        let row_plan = RowPlan::new(&roster, &scheduled)?;
        let batch = row_plan.stage_owner(OWNER as usize)?;
        let mut placed_terms = Vec::with_capacity(roster_terms.len());
        for term in roster_terms {
            let (relation, placed) = row_plan.place_daa_source_term(OWNER as usize, term)?;
            let Relation::DaaLane(_) = relation else {
                return Err("c151 DAA source mapped outside DAA relation".into());
            };
            placed_terms.push(placed);
        }
        let expected_rows = batch.terms().filter_map(|(relation, term)| match relation {
            Relation::DaaLane(_) => Some(term.clone()),
            _ => None,
        });
        if term_multiset(placed_terms.iter().cloned()) != term_multiset(expected_rows) {
            return Err("c151 DAA placed ROW multiset differs from plan".into());
        }
        Ok(placed_terms)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TermKey {
    row: usize,
    left: usize,
    right: usize,
    coefficients: [[u64; 4]; 4],
}

fn term_key(term: &Term) -> TermKey {
    TermKey {
        row: term.row,
        left: term.gate.left,
        right: term.gate.right,
        coefficients: [
            term.gate.c0.into_bigint().0,
            term.gate.c1.into_bigint().0,
            term.gate.c2.into_bigint().0,
            term.gate.c3.into_bigint().0,
        ],
    }
}

fn term_multiset(terms: impl IntoIterator<Item = Term>) -> BTreeMap<TermKey, usize> {
    let mut counts = BTreeMap::new();
    for term in terms {
        *counts.entry(term_key(&term)).or_insert(0) += 1;
    }
    counts
}

const MATURE_EIP_IMPORTS: usize = 896;
const MATURE_EIP_EXTERNAL_IMPORTS: usize = 864;
const MATURE_EIP_LOCAL_NBITS: usize = 32;
const MATURE_EIP_RAW_EXTERNAL_READS: usize = SAMPLE_HEIGHTS.len() * (64 + 32 + 32);

struct MatureEipImports {
    values: BTreeMap<usize, bool>,
    targets: BTreeMap<usize, usize>,
}

/// Derive mature-EIP import coordinates from the typed physical serializer-to-DAA
/// alias relation, then read their values from the independently admitted prefix.
/// This checks the producer's callback census; it does not obtain bit values from
/// the structural ROW/X ledger.
fn expected_mature_eip_imports(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    owner: usize,
    packed_owner: &[u8],
) -> Result<MatureEipImports, String> {
    if owner != OWNER as usize {
        return Err("c151 DAA import owner mismatch".into());
    }
    let layout = plan.header_boundary().mature_layout(Epoch::Eip);
    let mut aliases = Vec::with_capacity(MATURE_EIP_IMPORTS);
    let reported = layout.visit_alias_terms(owner as u64, |term| {
        aliases.push(term);
        Ok(())
    })?;
    if reported != MATURE_EIP_IMPORTS || aliases.len() != MATURE_EIP_IMPORTS {
        return Err("c151 DAA EIP alias import census mismatch".into());
    }

    // A retarget owner has no numeric carry relation. Fail closed if that
    // schedule ever changes, since such a relation can read GLOBAL0 as well.
    let numeric = crate::daa_work_actions::DaaWorkActions::new(plan)?;
    let numeric_terms = numeric.visit_owner(owner, |_| Ok(()))?;
    if numeric_terms != 0 {
        return Err("c151 DAA import census gained numeric-owner terms".into());
    }

    let wiring = crate::daa_schedule_wiring::DaaScheduleWiring::compile()?;
    let ports = wiring.ports(Epoch::Eip);
    let exports = crate::native_owner_exports::NativeExports::new_for_history(plan, prefix)?;
    collect_mature_eip_import_records(owner, aliases, ports, packed_owner, |wire| {
        exports.bit(wire)
    })
}

fn collect_mature_eip_imports(
    owner: usize,
    aliases: Vec<Term>,
    ports: &[crate::daa_schedule_wiring::FieldPort],
    packed_owner: &[u8],
    read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<BTreeMap<usize, bool>, String> {
    Ok(collect_mature_eip_import_records(owner, aliases, ports, packed_owner, read_bit)?.values)
}

fn collect_mature_eip_import_records(
    owner: usize,
    aliases: Vec<Term>,
    ports: &[crate::daa_schedule_wiring::FieldPort],
    packed_owner: &[u8],
    mut read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<MatureEipImports, String> {
    if owner != OWNER as usize
        || aliases.len() != MATURE_EIP_IMPORTS
        || ports.len() != MATURE_EIP_IMPORTS
        || packed_owner.len() != daa_history_producer::PACKED_OWNER_BYTES
    {
        return Err("c151 DAA EIP alias import census mismatch".into());
    }
    let owner_base = owner
        .checked_mul(WIDTH)
        .ok_or("c151 DAA import owner base overflow")?;
    let owner_end = owner_base
        .checked_add(WIDTH)
        .ok_or("c151 DAA import owner end overflow")?;
    let mut expected = BTreeMap::new();
    let mut targets = BTreeMap::new();
    let mut source_addresses = std::collections::BTreeSet::new();
    let mut target_addresses = std::collections::BTreeSet::new();
    let mut local_nbits = std::collections::BTreeSet::new();
    let mut external_count = 0usize;
    for (term, port) in aliases.into_iter().zip(ports) {
        if !term.gate.c0.is_zero()
            || term.gate.c1 != ark_bn254::Fr::one()
            || term.gate.c2 != -ark_bn254::Fr::one()
            || !term.gate.c3.is_zero()
        {
            return Err("c151 DAA EIP alias equality gate changed".into());
        }
        let offset = usize::try_from(port.offset(Epoch::Eip))
            .map_err(|_| "c151 DAA EIP source offset width")?;
        let source_owner = owner
            .checked_sub(offset)
            .ok_or("c151 DAA EIP source underflow")?;
        let serializer_local = crate::header_hash::SERIALIZER_OFFSET
            .checked_add(port.serializer_wire())
            .ok_or("c151 DAA EIP serializer coordinate overflow")?;
        let source = source_owner
            .checked_mul(WIDTH)
            .and_then(|base| base.checked_add(serializer_local))
            .ok_or("c151 DAA EIP source coordinate overflow")?;
        let target = term.gate.right;
        if port.serializer_wire() >= crate::header_hash::SERIALIZER_WIDTH
            || serializer_local >= WIDTH
            || port.daa_wire() >= WIDTH
            || term.gate.left != source
            || source == 0
            || !(owner_base..owner_end).contains(&target)
            || term.gate.left / WIDTH != source_owner
        {
            return Err(format!(
                "c151 DAA EIP alias import provenance mismatch family={:?} left={} expected_left={source} right={target} owner_base={owner_base} source_owner={source_owner}",
                port.family(), term.gate.left,
            ));
        }
        if !source_addresses.insert(source) || !target_addresses.insert(target) {
            return Err("c151 DAA duplicate EIP alias address".into());
        }
        let value = read_bit(source)?;
        let local = port.family() == crate::daa_schedule_wiring::PortFamily::ChildNBits;
        if local {
            if offset != 0
                || source_owner != owner
                || port.field_index() >= MATURE_EIP_LOCAL_NBITS
                || !local_nbits.insert(port.field_index())
                || packed_owner_bit(packed_owner, serializer_local)? != value
            {
                return Err("c151 DAA local ChildNBits source mismatch".into());
            }
        } else {
            if offset == 0 || source_owner >= owner {
                return Err("c151 DAA foreign import source owner mismatch".into());
            }
            external_count += 1;
            if expected.insert(source, value).is_some() {
                return Err(format!("c151 DAA duplicate EIP import address {source}"));
            }
            if targets.insert(source, target).is_some() {
                return Err(format!("c151 DAA duplicate EIP import target {source}"));
            }
        }
        let target_local = target - owner_base;
        if packed_owner_bit(packed_owner, target_local)? != value {
            return Err(format!(
                "c151 DAA alias target value mismatch at {target_local}"
            ));
        }
    }
    if external_count != MATURE_EIP_EXTERNAL_IMPORTS
        || expected.len() != MATURE_EIP_EXTERNAL_IMPORTS
        || targets.len() != MATURE_EIP_EXTERNAL_IMPORTS
        || local_nbits.len() != MATURE_EIP_LOCAL_NBITS
        || !(0..MATURE_EIP_LOCAL_NBITS).all(|index| local_nbits.contains(&index))
        || source_addresses.len() != MATURE_EIP_IMPORTS
        || target_addresses.len() != MATURE_EIP_IMPORTS
    {
        return Err("c151 DAA foreign/local EIP import census mismatch".into());
    }
    Ok(MatureEipImports {
        values: expected,
        targets,
    })
}

fn packed_owner_bit(owner: &[u8], wire: usize) -> Result<bool, String> {
    if wire >= WIDTH {
        return Err("c151 DAA packed-owner wire outside owner".into());
    }
    let byte = owner
        .get(wire / 8)
        .ok_or("c151 DAA packed-owner byte outside buffer")?;
    Ok((*byte >> (wire % 8)) & 1 != 0)
}

/// The writer first checks timestamp, nBits, and height on every RAW header.
/// All nine samples are foreign; the child is owner-local. The subsequent DAA
/// alias reads must be a subset of these same source coordinates.
fn collect_mature_eip_raw_reads(
    owner: usize,
    fields: &crate::serializer::FieldLayout,
    mut read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<BTreeMap<usize, bool>, String> {
    if owner != OWNER as usize {
        return Err("c151 DAA RAW read owner mismatch".into());
    }
    let mut expected = BTreeMap::new();
    for height in SAMPLE_HEIGHTS
        .into_iter()
        .chain(std::iter::once(CHILD_HEIGHT))
    {
        let source_owner = height.checked_sub(1).ok_or("c151 DAA RAW height zero")?;
        if source_owner > owner {
            return Err("c151 DAA RAW source after owner".into());
        }
        for wires in [
            &fields.timestamp[..],
            &fields.n_bits[..],
            &fields.height[..],
        ] {
            for &wire in wires {
                if wire >= crate::header_hash::SERIALIZER_WIDTH {
                    return Err("c151 DAA RAW serializer wire outside domain".into());
                }
                let address = source_owner
                    .checked_mul(WIDTH)
                    .and_then(|base| base.checked_add(crate::header_hash::SERIALIZER_OFFSET))
                    .and_then(|base| base.checked_add(wire))
                    .ok_or("c151 DAA RAW source coordinate overflow")?;
                if source_owner == owner {
                    continue;
                }
                let value = read_bit(address)?;
                if expected.insert(address, value).is_some() {
                    return Err("c151 DAA duplicate RAW external address".into());
                }
            }
        }
    }
    if expected.len() != MATURE_EIP_RAW_EXTERNAL_READS {
        return Err("c151 DAA RAW external read census mismatch".into());
    }
    Ok(expected)
}

fn validate_alias_raw_coverage(
    aliases: &BTreeMap<usize, bool>,
    raw: &BTreeMap<usize, bool>,
) -> Result<(), String> {
    if aliases.len() != MATURE_EIP_EXTERNAL_IMPORTS || raw.len() != MATURE_EIP_RAW_EXTERNAL_READS {
        return Err("c151 DAA alias/RAW import census mismatch".into());
    }
    for (&wire, &value) in aliases {
        match raw.get(&wire) {
            Some(raw_value) if *raw_value == value => {}
            _ => return Err(format!("c151 DAA alias missing from RAW reads at {wire}")),
        }
    }
    Ok(())
}

fn compare_external_import_maps(
    expected: &BTreeMap<usize, bool>,
    actual: &BTreeMap<usize, bool>,
) -> Result<(), String> {
    for (&wire, &expected_value) in expected {
        match actual.get(&wire) {
            None => return Err(format!("c151 DAA missing external import {wire}")),
            Some(actual_value) if *actual_value != expected_value => {
                return Err(format!("c151 DAA external import value mismatch at {wire}"));
            }
            Some(_) => {}
        }
    }
    if let Some(wire) = actual.keys().find(|wire| !expected.contains_key(wire)) {
        return Err(format!("c151 DAA extra external import {wire}"));
    }
    Ok(())
}

fn compare_native_daa_imports(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    source: &NativeDaaStage,
) -> Result<MatureEipImports, String> {
    if source.owner != OWNER {
        return Err("c151 DAA import source owner mismatch".into());
    }
    let aliases =
        expected_mature_eip_imports(plan, prefix, source.owner as usize, &source.packed_owner)?;
    let fields = crate::serializer::build(None)?.layout.fields;
    let exports = NativeExports::new_for_history(plan, prefix)?;
    let raw =
        collect_mature_eip_raw_reads(source.owner as usize, &fields, |wire| exports.bit(wire))?;
    validate_alias_raw_coverage(&aliases.values, &raw)?;
    compare_external_import_maps(&raw, &source.external_values)?;
    Ok(aliases)
}

/// Compare the native DAA source stage with one consumer candidate. The
/// consumer buffer is partial: only the four declared DAA banks are checked.
/// No ROW/X assignment or proof state is published here.
pub(super) fn compare_native_daa_stage_to_ledger(
    plan: &WorkTreeHistoryPlan,
    source: &NativeDaaStage,
    ledger_rows: &[Term],
    ledger_bank_patches: &[(std::ops::Range<usize>, Vec<u8>)],
    ledger_packed_owner: &[u8],
) -> Result<(), String> {
    if plan.headers() != HISTORY_HEADERS
        || plan.slot_log() != HISTORY_SLOT_LOG
        || plan.slots() != 1usize << HISTORY_SLOT_LOG
        || source.plan_root != plan.descriptor().root
        || source.plan_total_be28 != plan.work_profile().total_be28
    {
        return Err("c151 DAA source/ledger plan binding mismatch".into());
    }
    if source.owner != OWNER {
        return Err("c151 DAA ledger owner mismatch".into());
    }
    if ledger_packed_owner.len() != daa_history_producer::PACKED_OWNER_BYTES {
        return Err("c151 DAA ledger packed-owner length".into());
    }
    if source.packed_owner.len() != daa_history_producer::PACKED_OWNER_BYTES {
        return Err("c151 DAA source packed-owner length".into());
    }
    let roster = DaaHistoryRoster::compile(plan)?;
    if roster.owner_class(OWNER)? != OwnerClass::Mature(Epoch::Eip)
        || source.receipt.owner != OWNER
        || source.receipt.class != OwnerClass::Mature(Epoch::Eip)
        || source.receipt.patched_bytes != daa_history_producer::PATCH_BYTES
        || source.receipt.external_cells != source.external_values.len()
    {
        return Err("c151 DAA ledger source class mismatch".into());
    }
    let scheduled = Scheduled::new();
    let row_plan = RowPlan::new(&roster, &scheduled)?;
    let batch = row_plan.stage_owner(OWNER as usize)?;

    let mut placed_source = Vec::with_capacity(source.row_terms.len());
    let mut source_lane_counts = [0usize; 4];
    for term in &source.row_terms {
        let q = term
            .row
            .checked_sub(OWNER as usize * (1 << 19))
            .filter(|q| *q < (1 << 19))
            .ok_or("c151 DAA source ROW owner")?;
        let source_lane = q >> 17;
        if source_lane >= source_lane_counts.len() {
            return Err("c151 DAA source lane extent".into());
        }
        source_lane_counts[source_lane] += 1;
        let (relation, placed) = row_plan.place_daa_source_term(OWNER as usize, term.clone())?;
        let Relation::DaaLane(_) = relation else {
            return Err("c151 DAA source mapped outside DAA relation".into());
        };
        placed_source.push(placed);
    }
    if source_lane_counts != source.receipt.counts.lanes {
        return Err("c151 DAA source row counts differ from receipt".into());
    }
    let plan_rows = batch.terms().filter_map(|(relation, term)| match relation {
        Relation::DaaLane(_) => Some(term.clone()),
        _ => None,
    });
    let expected_rows = term_multiset(plan_rows);
    if term_multiset(placed_source) != expected_rows {
        return Err("c151 DAA source ROW multiset differs from ledger plan".into());
    }
    if term_multiset(ledger_rows.iter().cloned()) != expected_rows {
        return Err("c151 DAA ledger ROW multiset differs from source".into());
    }

    let owner_base = (OWNER as usize)
        .checked_mul(WIDTH)
        .ok_or("c151 DAA ledger owner base overflow")?;
    let expected_domains = batch
        .declared_x_domains()
        .into_iter()
        .filter(|domain| domain.producer == Producer::Daa)
        .map(|domain| {
            Ok(domain
                .start
                .checked_sub(owner_base)
                .ok_or("c151 DAA domain before owner")?
                ..domain
                    .end
                    .checked_sub(owner_base)
                    .ok_or("c151 DAA domain before owner")?)
        })
        .collect::<Result<Vec<_>, String>>()?;
    if expected_domains.len() != BANKS.len()
        || source.bank_patches.len() != BANKS.len()
        || ledger_bank_patches.len() != BANKS.len()
    {
        return Err("c151 DAA ledger requires exactly four bank patches".into());
    }
    for index in 0..BANKS.len() {
        let expected = &expected_domains[index];
        let (source_domain, source_bytes) = &source.bank_patches[index];
        let (ledger_domain, ledger_bytes) = &ledger_bank_patches[index];
        if source_domain != expected || ledger_domain != expected {
            return Err(format!("c151 DAA ledger bank {index} domain mismatch"));
        }
        let start = expected.start / 8;
        let end = expected.end / 8;
        if source_bytes.len() != end - start
            || ledger_bytes.len() != end - start
            || source_bytes != ledger_bytes
            || source_bytes.as_slice() != &source.packed_owner[start..end]
            || ledger_bytes.as_slice() != &ledger_packed_owner[start..end]
        {
            return Err(format!("c151 DAA ledger bank {index} value mismatch"));
        }
    }
    Ok(())
}

struct PinnedWindow {
    parent: Vec<u8>,
    child: Vec<u8>,
    samples: Vec<Vec<u8>>,
}

fn decode_hex(text: &str) -> Result<Vec<u8>, String> {
    if text.len() % 2 != 0 {
        return Err("c151 DAA fixture has odd-length RAW hex".into());
    }
    text.as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let pair = std::str::from_utf8(pair).map_err(|error| error.to_string())?;
            u8::from_str_radix(pair, 16).map_err(|error| error.to_string())
        })
        .collect()
}

fn pinned_window() -> Result<PinnedWindow, String> {
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("../../fixtures/mainnet-daa-windows-v1.json"))
            .map_err(|error| format!("c151 DAA fixture JSON: {error}"))?;
    let source_sha = fixture["source_frame"]["sha256"]
        .as_str()
        .ok_or("c151 DAA fixture source-frame SHA missing")?;
    if !source_sha.eq_ignore_ascii_case(super::FRAME_SHA256) {
        return Err("c151 DAA fixture source-frame SHA differs from pinned H21 frame".into());
    }

    let mut headers = BTreeMap::<usize, Vec<u8>>::new();
    for item in fixture["headers"]
        .as_array()
        .ok_or("c151 DAA fixture header list missing")?
    {
        let height = usize::try_from(
            item["height"]
                .as_u64()
                .ok_or("c151 DAA fixture header height missing")?,
        )
        .map_err(|_| "c151 DAA fixture height width")?;
        let raw = decode_hex(
            item["raw_hex"]
                .as_str()
                .ok_or("c151 DAA fixture RAW missing")?,
        )?;
        if headers.insert(height, raw).is_some() {
            return Err(format!("c151 DAA fixture duplicate height {height}"));
        }
    }

    let parent = headers
        .get(&(OWNER as usize))
        .cloned()
        .ok_or("c151 DAA fixture parent RAW missing")?;
    let child = headers
        .get(&CHILD_HEIGHT)
        .cloned()
        .ok_or("c151 DAA fixture child RAW missing")?;
    let samples = SAMPLE_HEIGHTS
        .iter()
        .map(|height| {
            headers
                .get(height)
                .cloned()
                .ok_or_else(|| format!("c151 DAA fixture sample RAW missing at {height}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if samples.last() != Some(&parent) {
        return Err("c151 DAA fixture final sample is not its parent RAW".into());
    }
    Ok(PinnedWindow {
        parent,
        child,
        samples,
    })
}

fn verify_raw_window(
    actual_parent: &[u8],
    actual_child: &[u8],
    actual_samples: &[&[u8]],
    expected: &PinnedWindow,
) -> Result<(), String> {
    if expected.samples.len() != SAMPLE_HEIGHTS.len()
        || actual_samples.len() != SAMPLE_HEIGHTS.len()
    {
        return Err("c151 DAA sample count mismatch".into());
    }
    if actual_samples.last().copied() != Some(actual_parent) {
        return Err("c151 native final sample is not the native parent RAW".into());
    }
    if actual_parent != expected.parent {
        return Err("c151 native parent RAW differs from pinned DAA fixture".into());
    }
    if actual_child != expected.child {
        return Err("c151 native child RAW differs from pinned DAA fixture".into());
    }
    for (index, height) in SAMPLE_HEIGHTS.iter().enumerate() {
        if actual_samples[index] != expected.samples[index] {
            return Err(format!("c151 native sample RAW differs at height {height}"));
        }
    }
    Ok(())
}

const FIRST_SOURCE_HEIGHT: usize = 843_648;
const FIRST_SOURCE_OWNER: usize = FIRST_SOURCE_HEIGHT - 1;
const FIRST_SOURCE_ADDRESS: usize = 884_628_522_002;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SerializerSourceAuthor {
    HeaderSerializer,
    DaaCallback,
}

/// Candidate Header/serializer writer for the first active DAA import.
/// The pinned RAW fixes this value and coordinate; full Header/root authority
/// and assignment of the global X writer remain separate obligations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SerializerSourceClaim {
    source_owner: usize,
    source_height: usize,
    serializer_wire: usize,
    address: usize,
    value: bool,
    author: SerializerSourceAuthor,
}

impl SerializerSourceClaim {
    pub(super) fn address(&self) -> usize {
        self.address
    }

    pub(super) fn value(&self) -> bool {
        self.value
    }

    pub(super) fn author(&self) -> SerializerSourceAuthor {
        self.author
    }
}

/// Rebuild all mature-EIP field reads from the exact nine pinned RAW samples.
/// The existing RAW-read census then checks the source coordinates; no caller
/// map is permitted to determine either the values or the addresses.
fn pinned_mature_eip_raw_reads(
    window: &PinnedWindow,
    serializer: &crate::serializer::Compiled,
) -> Result<BTreeMap<usize, bool>, String> {
    if window.samples.len() != SAMPLE_HEIGHTS.len() || window.samples.last() != Some(&window.parent)
    {
        return Err("c156 pinned RAW sample window shape".into());
    }
    let fields = &serializer.layout.fields;
    let mut from_raw = BTreeMap::new();
    for (&height, raw) in SAMPLE_HEIGHTS.iter().zip(&window.samples) {
        let header = ergo_header_core::Header::decode(raw, None)
            .map_err(|error| format!("c156 pinned RAW decode at {height}: {error:?}"))?;
        if header.height as usize != height
            || header
                .encode()
                .map_err(|error| format!("c156 pinned RAW encode at {height}: {error:?}"))?
                != *raw
        {
            return Err(format!("c156 pinned RAW height/canonical encoding at {height}"));
        }
        let assignment = serializer.assign(&crate::serializer::Fields::from_header(&header)?);
        for &wire in fields
            .timestamp
            .iter()
            .chain(&fields.n_bits)
            .chain(&fields.height)
        {
            if wire >= crate::header_hash::SERIALIZER_WIDTH {
                return Err("c156 pinned RAW serializer wire outside domain".into());
            }
            let address = (height - 1)
                .checked_mul(WIDTH)
                .and_then(|base| base.checked_add(crate::header_hash::SERIALIZER_OFFSET))
                .and_then(|base| base.checked_add(wire))
                .ok_or("c156 pinned RAW global coordinate overflow")?;
            let value = assignment
                .get(wire)
                .ok_or("c156 pinned RAW assignment wire absent")?;
            if !value.is_zero() && !value.is_one() {
                return Err("c156 pinned RAW assignment non-Boolean".into());
            }
            if from_raw.insert(address, value.is_one()).is_some() {
                return Err("c156 pinned RAW duplicate source coordinate".into());
            }
        }
    }
    if from_raw.len() != MATURE_EIP_RAW_EXTERNAL_READS {
        return Err("c156 pinned RAW source-read census".into());
    }
    let checked = collect_mature_eip_raw_reads(OWNER as usize, fields, |address| {
        from_raw
            .get(&address)
            .copied()
            .ok_or_else(|| format!("c156 pinned RAW missing source coordinate {address}"))
    })?;
    if checked != from_raw {
        return Err("c156 pinned RAW read manifest differs from typed census".into());
    }
    Ok(checked)
}

fn first_pinned_serializer_source_claim(
    window: &PinnedWindow,
    serializer: &crate::serializer::Compiled,
    raw_reads: &BTreeMap<usize, bool>,
) -> Result<SerializerSourceClaim, String> {
    if SAMPLE_HEIGHTS[0] != FIRST_SOURCE_HEIGHT
        || crate::header_hash::SERIALIZER_OFFSET != 524_288
        || serializer.layout.fields.timestamp[0] != 1_042
    {
        return Err("c156 first source serializer layout drift".into());
    }
    let address = FIRST_SOURCE_OWNER
        .checked_mul(WIDTH)
        .and_then(|base| base.checked_add(crate::header_hash::SERIALIZER_OFFSET))
        .and_then(|base| base.checked_add(serializer.layout.fields.timestamp[0]))
        .ok_or("c156 first source address overflow")?;
    if address != FIRST_SOURCE_ADDRESS || window.samples.is_empty() {
        return Err("c156 first source coordinate drift".into());
    }
    let value = *raw_reads
        .get(&address)
        .ok_or("c156 first source absent from pinned RAW reads")?;
    Ok(SerializerSourceClaim {
        source_owner: FIRST_SOURCE_OWNER,
        source_height: FIRST_SOURCE_HEIGHT,
        serializer_wire: serializer.layout.fields.timestamp[0],
        address,
        value,
        author: SerializerSourceAuthor::HeaderSerializer,
    })
}

/// Establish a single source-writer/DAA-import join without reading the H21
/// frame. The producer stage is independently source-built; this checks one
/// author and the complete pinned RAW/typed-alias read census, not a global
/// historical X assignment or a proof.
fn join_first_serializer_source_to_daa(
    plan: &WorkTreeHistoryPlan,
    stage: &NativeDaaStage,
    claims: &[SerializerSourceClaim],
) -> Result<(), String> {
    if plan.headers() != HISTORY_HEADERS
        || plan.slot_log() != HISTORY_SLOT_LOG
        || stage.owner != OWNER
        || stage.plan_root != plan.descriptor().root
        || stage.plan_total_be28 != plan.work_profile().total_be28
        || stage.receipt.owner != OWNER
        || stage.receipt.class != OwnerClass::Mature(Epoch::Eip)
        || stage.receipt.external_cells != stage.external_values.len()
    {
        return Err("c156 DAA stage/plan identity mismatch".into());
    }
    let [claim] = claims else {
        return Err("c156 exactly one source writer required".into());
    };
    let window = pinned_window()?;
    let serializer = crate::serializer::build(None)?;
    let raw_reads = pinned_mature_eip_raw_reads(&window, &serializer)?;
    let expected = first_pinned_serializer_source_claim(&window, &serializer, &raw_reads)?;
    if claim.author != SerializerSourceAuthor::HeaderSerializer {
        return Err("c156 source writer author mismatch".into());
    }
    if claim.source_owner != expected.source_owner
        || claim.source_height != expected.source_height
    {
        return Err("c156 source writer owner/height mismatch".into());
    }
    if claim.serializer_wire != expected.serializer_wire || claim.address != expected.address {
        return Err("c156 source writer coordinate mismatch".into());
    }
    if claim.value != expected.value {
        return Err("c156 source writer value differs from pinned RAW".into());
    }

    let layout = plan.header_boundary().mature_layout(Epoch::Eip);
    let mut aliases = Vec::with_capacity(MATURE_EIP_IMPORTS);
    let reported = layout.visit_alias_terms(OWNER, |term| {
        aliases.push(term);
        Ok(())
    })?;
    let wiring = crate::daa_schedule_wiring::DaaScheduleWiring::compile()?;
    let ports = wiring.ports(Epoch::Eip);
    if reported != MATURE_EIP_IMPORTS
        || aliases.len() != MATURE_EIP_IMPORTS
        || ports.len() != MATURE_EIP_IMPORTS
    {
        return Err("c156 DAA alias/port census mismatch".into());
    }
    let mut target = None;
    for (term, port) in aliases.iter().zip(ports) {
        if term.gate.left != claim.address {
            continue;
        }
        if target.is_some()
            || port.family() != crate::daa_schedule_wiring::PortFamily::Timestamp
            || port.field_index() != 0
            || port.serializer_wire() != claim.serializer_wire
            || OWNER as usize
                != claim
                    .source_owner
                    .checked_add(port.offset(Epoch::Eip) as usize)
                    .ok_or("c156 DAA source offset overflow")?
            || term.gate.right
                != OWNER as usize * WIDTH + layout.mapped_port_wire(port.daa_wire())?
        {
            return Err("c156 first DAA alias source/target identity mismatch".into());
        }
        target = Some(term.gate.right);
    }
    let target = target.ok_or("c156 first source absent from actual DAA aliases")?;
    let alias_reads = collect_mature_eip_imports(
        OWNER as usize,
        aliases,
        ports,
        &stage.packed_owner,
        |address| {
            if address / WIDTH == OWNER as usize {
                packed_owner_bit(&stage.packed_owner, address % WIDTH)
            } else {
                stage.external_values.get(&address).copied().ok_or_else(|| {
                    format!("c156 DAA callback missing typed alias source {address}")
                })
            }
        },
    )?;
    validate_alias_raw_coverage(&alias_reads, &raw_reads)?;
    compare_external_import_maps(&raw_reads, &stage.external_values)?;
    if alias_reads.get(&claim.address) != Some(&claim.value)
        || stage.external_values.get(&claim.address) != Some(&claim.value)
        || packed_owner_bit(&stage.packed_owner, target % WIDTH)? != claim.value
    {
        return Err("c156 first source/DAA alias value mismatch".into());
    }
    Ok(())
}

/// Obtain the source-owned claim only after its exact RAW-to-DAA join closes.
/// The caller must still assign the writer in the global X roster separately.
pub(super) fn first_native_serializer_source_claim(
    plan: &WorkTreeHistoryPlan,
    stage: &NativeDaaStage,
) -> Result<SerializerSourceClaim, String> {
    let window = pinned_window()?;
    let serializer = crate::serializer::build(None)?;
    let raw_reads = pinned_mature_eip_raw_reads(&window, &serializer)?;
    let claim = first_pinned_serializer_source_claim(&window, &serializer, &raw_reads)?;
    join_first_serializer_source_to_daa(plan, stage, &[claim])?;
    Ok(claim)
}

fn seed_native_child_serializer(destination: &mut [u8], raw: &[u8]) -> Result<(), String> {
    if destination.len() != daa_history_producer::PACKED_OWNER_BYTES {
        return Err("c151 DAA owner destination length".into());
    }
    let header = ergo_header_core::Header::decode(raw, None)
        .map_err(|error| format!("c151 native child decode: {error:?}"))?;
    if header.height as usize != CHILD_HEIGHT {
        return Err("c151 DAA child height mismatch".into());
    }
    let fields = crate::serializer::Fields::from_header(&header)?;
    let assignment = crate::serializer::build(None)?.assign(&fields);
    let base = crate::header_hash::SERIALIZER_OFFSET;
    for (wire, value) in assignment.iter().enumerate() {
        let local = base
            .checked_add(wire)
            .ok_or("c151 serializer coordinate overflow")?;
        if local >= WIDTH
            || BANKS
                .iter()
                .any(|(start, end)| (*start..*end).contains(&local))
        {
            return Err("c151 serializer seed overlaps DAA bank or owner boundary".into());
        }
        if value.is_one() {
            destination[local / 8] |= 1 << (local % 8);
        }
    }
    Ok(())
}

/// Bind and stage the native Mature(Eip) owner 844672 from the same H21 prefix
/// admitted by the caller. All fixture comparisons precede the DAA writer.
pub(crate) fn stage_native_mature_eip_844672(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
) -> Result<NativeDaaStage, String> {
    if plan.headers() != HISTORY_HEADERS
        || plan.slot_log() != HISTORY_SLOT_LOG
        || plan.slots() != 1usize << HISTORY_SLOT_LOG
    {
        return Err("c151 DAA stage requires the pinned H21 geometry".into());
    }
    validate_native_plan_input(plan, prefix)?;
    if prefix.header_count() as u64 != HISTORY_HEADERS {
        return Err("c151 DAA stage native prefix count mismatch".into());
    }

    let expected = pinned_window()?;
    let parent = prefix.raw(OWNER as usize)?;
    let child = prefix.raw(CHILD_HEIGHT)?;
    let sample_storage = SAMPLE_HEIGHTS
        .iter()
        .map(|height| prefix.raw(*height))
        .collect::<Result<Vec<_>, _>>()?;
    let samples = sample_storage
        .iter()
        .map(|raw| raw.as_ref())
        .collect::<Vec<_>>();
    verify_raw_window(parent, child, &samples, &expected)?;

    let roster = DaaHistoryRoster::compile(plan)?;
    if roster.owner_class(OWNER)? != OwnerClass::Mature(Epoch::Eip) {
        return Err("c151 DAA roster owner is not Mature(Eip)".into());
    }
    let exports = NativeExports::new_for_history(plan, prefix)?;
    let mut packed_owner = vec![0u8; daa_history_producer::PACKED_OWNER_BYTES];
    seed_native_child_serializer(&mut packed_owner, child)?;
    let raw = RawWindow {
        parent,
        child,
        samples: &samples,
    };
    let owner_base = usize::try_from(OWNER)
        .map_err(|_| "c151 DAA owner width")?
        .checked_mul(WIDTH)
        .ok_or("c151 DAA owner base overflow")?;
    let mut external_values = BTreeMap::new();
    let receipt =
        daa_history_producer::write_retarget(&roster, OWNER, raw, &mut packed_owner, |wire| {
            if (owner_base..owner_base + WIDTH).contains(&wire) {
                return Err("c151 DAA external import unexpectedly owner-local".into());
            }
            let value = exports.bit(wire)?;
            if external_values.insert(wire, value).is_some() {
                return Err(format!("c151 DAA duplicate external import {wire}"));
            }
            Ok(value)
        })?;
    if receipt.owner != OWNER
        || receipt.class != OwnerClass::Mature(Epoch::Eip)
        || receipt.patched_bytes != daa_history_producer::PATCH_BYTES
        || receipt.external_cells != external_values.len()
    {
        return Err("c151 DAA writer receipt mismatch".into());
    }

    let mut bank_patches = Vec::with_capacity(BANKS.len());
    for (start, end) in BANKS {
        if start >= end || start % 8 != 0 || end % 8 != 0 || end > WIDTH {
            return Err("c151 DAA bank geometry invalid".into());
        }
        bank_patches.push((start..end, packed_owner[start / 8..end / 8].to_vec()));
    }
    let mut row_terms = Vec::new();
    let row_counts = roster.visit_owner_terms(OWNER, |term| {
        row_terms.push(term);
        Ok(())
    })?;
    if row_counts != receipt.counts {
        return Err("c151 DAA ROW roster/writer count mismatch".into());
    }

    let staged = NativeDaaStage {
        owner: OWNER,
        packed_owner,
        row_terms,
        bank_patches,
        external_values,
        serializer_import_values: BTreeMap::new(),
        serializer_import_targets: BTreeMap::new(),
        receipt,
        plan_root: plan.descriptor().root,
        plan_total_be28: plan.work_profile().total_be28,
    };
    let serializer_imports = compare_native_daa_imports(plan, prefix, &staged)?;
    let mut staged = staged;
    staged.serializer_import_values = serializer_imports.values;
    staged.serializer_import_targets = serializer_imports.targets;
    Ok(staged)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{
        collect_mature_eip_imports, collect_mature_eip_raw_reads, compare_external_import_maps,
        compare_native_daa_stage_to_ledger, validate_alias_raw_coverage, verify_raw_window,
        first_native_serializer_source_claim, join_first_serializer_source_to_daa,
        NativeDaaStage, PinnedWindow, SerializerSourceAuthor, FIRST_SOURCE_ADDRESS,
        FIRST_SOURCE_HEIGHT, FIRST_SOURCE_OWNER, MATURE_EIP_EXTERNAL_IMPORTS,
        MATURE_EIP_IMPORTS, MATURE_EIP_RAW_EXTERNAL_READS, OWNER, SAMPLE_HEIGHTS,
    };
    use crate::{
        daa_history_producer,
        daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS},
        daa_integer::Epoch,
        header_daa_row_placement::Relation,
        work_tree_history_plan::WorkTreeHistoryPlan,
    };
    use ark_bn254::Fr;
    use ark_ff::{One, Zero};

    fn synthetic_aliases(
        ports: &[crate::daa_schedule_wiring::FieldPort],
    ) -> Vec<crate::sparse::Term> {
        let owner = OWNER as usize;
        let owner_base = owner * crate::work_tree_layout::WIDTH;
        assert_eq!(ports.len(), MATURE_EIP_IMPORTS);
        let mut terms = Vec::with_capacity(MATURE_EIP_IMPORTS);
        for (index, port) in ports.iter().enumerate() {
            let source_owner = owner - usize::try_from(port.offset(Epoch::Eip)).unwrap();
            let source = source_owner * crate::work_tree_layout::WIDTH
                + crate::header_hash::SERIALIZER_OFFSET
                + port.serializer_wire();
            terms.push(crate::sparse::Term {
                row: index,
                gate: crate::gkr::Gate {
                    left: source,
                    right: owner_base + port.daa_wire(),
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: -Fr::one(),
                    c3: Fr::zero(),
                },
            });
        }
        terms
    }

    fn typed_import_fixture() -> (
        Vec<crate::sparse::Term>,
        Vec<crate::daa_schedule_wiring::FieldPort>,
        Vec<u8>,
    ) {
        let wiring = crate::daa_schedule_wiring::DaaScheduleWiring::compile().unwrap();
        let ports = wiring.ports(Epoch::Eip).to_vec();
        let terms = synthetic_aliases(&ports);
        let owner_base = OWNER as usize * crate::work_tree_layout::WIDTH;
        let mut packed = vec![0u8; daa_history_producer::PACKED_OWNER_BYTES];
        for (term, port) in terms.iter().zip(&ports) {
            let source = term.gate.left;
            let value = synthetic_bit(source);
            if port.family() == crate::daa_schedule_wiring::PortFamily::ChildNBits {
                set_packed_bit(&mut packed, source % crate::work_tree_layout::WIDTH, value);
            }
            assert_eq!(term.gate.right, owner_base + port.daa_wire());
            set_packed_bit(&mut packed, term.gate.right - owner_base, value);
        }
        (terms, ports, packed)
    }

    fn set_packed_bit(bytes: &mut [u8], wire: usize, value: bool) {
        let mask = 1u8 << (wire % 8);
        if value {
            bytes[wire / 8] |= mask;
        } else {
            bytes[wire / 8] &= !mask;
        }
    }

    fn synthetic_bit(wire: usize) -> bool {
        wire.count_ones() & 1 != 0
    }

    #[test]
    fn mature_eip_external_import_map_is_exact_and_provenance_bound() {
        let mut reads = 0usize;
        let (aliases, ports, packed) = typed_import_fixture();
        let expected =
            collect_mature_eip_imports(OWNER as usize, aliases.clone(), &ports, &packed, |wire| {
                reads += 1;
                Ok(synthetic_bit(wire))
            })
            .unwrap();
        assert_eq!(reads, MATURE_EIP_IMPORTS);
        assert_eq!(expected.len(), MATURE_EIP_EXTERNAL_IMPORTS);
        assert!(expected.values().any(|value| *value));
        assert!(expected.values().any(|value| !*value));
        assert!(compare_external_import_maps(&expected, &expected).is_ok());

        let fields = crate::serializer::build(None).unwrap().layout.fields;
        let raw =
            collect_mature_eip_raw_reads(OWNER as usize, &fields, |wire| Ok(synthetic_bit(wire)))
                .unwrap();
        assert_eq!(raw.len(), MATURE_EIP_RAW_EXTERNAL_READS);
        assert_eq!(raw.len() - expected.len(), 288);
        validate_alias_raw_coverage(&expected, &raw).unwrap();
        assert!(compare_external_import_maps(&raw, &raw).is_ok());
        assert!(compare_external_import_maps(&expected, &raw)
            .unwrap_err()
            .contains("extra external import"));
        let raw_only = *raw
            .keys()
            .find(|wire| !expected.contains_key(wire))
            .unwrap();
        let mut missing_raw_only = raw.clone();
        missing_raw_only.remove(&raw_only);
        assert!(compare_external_import_maps(&raw, &missing_raw_only)
            .unwrap_err()
            .contains("missing external import"));
        let mut wrong_raw_only = raw.clone();
        *wrong_raw_only.get_mut(&raw_only).unwrap() = !raw[&raw_only];
        assert!(compare_external_import_maps(&raw, &wrong_raw_only)
            .unwrap_err()
            .contains("value mismatch"));

        let mut missing = expected.clone();
        let first_wire = *missing.keys().next().unwrap();
        missing.remove(&first_wire);
        assert!(compare_external_import_maps(&expected, &missing)
            .unwrap_err()
            .contains("missing external import"));

        let mut extra = expected.clone();
        extra.insert(0, false);
        assert!(compare_external_import_maps(&expected, &extra)
            .unwrap_err()
            .contains("extra external import"));

        let mut wrong_value = expected.clone();
        let wire = *expected.keys().next().unwrap();
        *wrong_value.get_mut(&wire).unwrap() = !expected[&wire];
        assert!(compare_external_import_maps(&expected, &wrong_value)
            .unwrap_err()
            .contains("value mismatch"));

        let mut wrong_provenance = expected.clone();
        let value = wrong_provenance.remove(&wire).unwrap();
        wrong_provenance.insert(0, value);
        assert!(compare_external_import_maps(&expected, &wrong_provenance).is_err());

        let mut wrong_source_owner = aliases.clone();
        wrong_source_owner[0].gate.left += crate::work_tree_layout::WIDTH;
        assert!(collect_mature_eip_imports(
            OWNER as usize,
            wrong_source_owner,
            &ports,
            &packed,
            |wire| Ok(synthetic_bit(wire)),
        )
        .unwrap_err()
        .contains("provenance mismatch"));

        let mut wrong_local_port = aliases.clone();
        wrong_local_port[MATURE_EIP_EXTERNAL_IMPORTS].gate.left -= crate::work_tree_layout::WIDTH;
        assert!(collect_mature_eip_imports(
            OWNER as usize,
            wrong_local_port,
            &ports,
            &packed,
            |wire| Ok(synthetic_bit(wire)),
        )
        .unwrap_err()
        .contains("provenance mismatch"));

        let mut missing_local = aliases.clone();
        missing_local.pop();
        assert!(collect_mature_eip_imports(
            OWNER as usize,
            missing_local,
            &ports,
            &packed,
            |wire| Ok(synthetic_bit(wire)),
        )
        .unwrap_err()
        .contains("alias import census"));

        let mut wrong_local_source_value = packed.clone();
        let local_port = &ports[MATURE_EIP_EXTERNAL_IMPORTS];
        let local_source = crate::header_hash::SERIALIZER_OFFSET + local_port.serializer_wire();
        let source_byte = local_source / 8;
        wrong_local_source_value[source_byte] ^= 1 << (local_source % 8);
        assert!(collect_mature_eip_imports(
            OWNER as usize,
            aliases.clone(),
            &ports,
            &wrong_local_source_value,
            |wire| Ok(synthetic_bit(wire)),
        )
        .unwrap_err()
        .contains("local ChildNBits source mismatch"));

        let mut wrong_local_value = packed.clone();
        let local_target =
            aliases[MATURE_EIP_EXTERNAL_IMPORTS].gate.right % crate::work_tree_layout::WIDTH;
        let target_byte = local_target / 8;
        wrong_local_value[target_byte] ^= 1 << (local_target % 8);
        assert!(collect_mature_eip_imports(
            OWNER as usize,
            aliases.clone(),
            &ports,
            &wrong_local_value,
            |wire| Ok(synthetic_bit(wire)),
        )
        .unwrap_err()
        .contains("target value mismatch"));

        let mut zero_coefficient = aliases;
        zero_coefficient[0].gate.c1 = Fr::zero();
        assert!(collect_mature_eip_imports(
            OWNER as usize,
            zero_coefficient,
            &ports,
            &packed,
            |wire| Ok(synthetic_bit(wire)),
        )
        .unwrap_err()
        .contains("equality gate changed"));
    }

    #[test]
    fn mature_eip_real_layout_aliases_match_typed_import_manifest() -> Result<(), String> {
        let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x91; 32], [0x92; 28])?;
        let layout = plan.header_boundary().mature_layout(Epoch::Eip);
        let mut aliases = Vec::new();
        let count = layout.visit_alias_terms(OWNER, |term| {
            aliases.push(term);
            Ok(())
        })?;
        if count != MATURE_EIP_IMPORTS || aliases.len() != MATURE_EIP_IMPORTS {
            return Err("c152 actual EIP layout alias count".into());
        }
        let wiring = crate::daa_schedule_wiring::DaaScheduleWiring::compile()?;
        let ports = wiring.ports(Epoch::Eip);
        let mut packed = vec![0u8; daa_history_producer::PACKED_OWNER_BYTES];
        for (term, port) in aliases.iter().zip(ports) {
            let value = synthetic_bit(term.gate.left);
            if port.family() == crate::daa_schedule_wiring::PortFamily::ChildNBits {
                set_packed_bit(
                    &mut packed,
                    term.gate.left % crate::work_tree_layout::WIDTH,
                    value,
                );
            }
            set_packed_bit(
                &mut packed,
                term.gate.right % crate::work_tree_layout::WIDTH,
                value,
            );
        }
        let expected =
            collect_mature_eip_imports(OWNER as usize, aliases, ports, &packed, |wire| {
                Ok(synthetic_bit(wire))
            })?;
        let fields = crate::serializer::build(None)?.layout.fields;
        let raw =
            collect_mature_eip_raw_reads(OWNER as usize, &fields, |wire| Ok(synthetic_bit(wire)))?;
        validate_alias_raw_coverage(&expected, &raw)?;
        let numeric = crate::daa_work_actions::DaaWorkActions::new(&plan)?;
        if numeric.visit_owner(OWNER as usize, |_| Ok(()))? != 0
            || expected.len() != MATURE_EIP_EXTERNAL_IMPORTS
            || raw.len() != MATURE_EIP_RAW_EXTERNAL_READS
            || !expected.values().any(|value| *value)
            || !expected.values().any(|value| !*value)
        {
            return Err("c152 actual EIP import manifest shape".into());
        }
        Ok(())
    }

    fn fixture() -> PinnedWindow {
        let samples = (0..SAMPLE_HEIGHTS.len())
            .map(|index| vec![index as u8, 0x5a])
            .collect::<Vec<_>>();
        let parent = samples.last().expect("fixture has pinned samples").clone();
        PinnedWindow {
            parent,
            child: b"child".to_vec(),
            samples,
        }
    }

    fn actual<'a>(fixture: &'a PinnedWindow) -> (Vec<&'a [u8]>, &'a [u8], &'a [u8]) {
        let samples = fixture.samples.iter().map(Vec::as_slice).collect();
        (samples, &fixture.parent, &fixture.child)
    }

    #[test]
    fn exact_raw_window_is_accepted() {
        let fixture = fixture();
        let (samples, parent, child) = actual(&fixture);
        assert!(verify_raw_window(parent, child, &samples, &fixture).is_ok());
    }

    #[test]
    fn isolated_raw_parent_child_and_sample_mutants_are_rejected() {
        let fixture = fixture();
        let (samples, parent, child) = actual(&fixture);

        let mut wrong_parent = parent.to_vec();
        wrong_parent[0] ^= 1;
        let mut wrong_parent_storage = fixture.samples.clone();
        let last_sample = wrong_parent_storage.len() - 1;
        wrong_parent_storage[last_sample] = wrong_parent.clone();
        let wrong_parent_samples = wrong_parent_storage
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        assert!(verify_raw_window(&wrong_parent, child, &wrong_parent_samples, &fixture).is_err());

        let mut wrong_child = child.to_vec();
        wrong_child[0] ^= 1;
        assert!(verify_raw_window(parent, &wrong_child, &samples, &fixture).is_err());

        let mut wrong_sample_storage = fixture.samples.clone();
        wrong_sample_storage[3][0] ^= 1;
        let wrong_samples = wrong_sample_storage
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        assert!(verify_raw_window(parent, child, &wrong_samples, &fixture).is_err());

        assert!(verify_raw_window(parent, child, &samples[..samples.len() - 1], &fixture).is_err());
    }

    struct LedgerFixture {
        plan: WorkTreeHistoryPlan,
        source: NativeDaaStage,
        ledger_rows: Vec<crate::sparse::Term>,
        ledger_patches: Vec<(std::ops::Range<usize>, Vec<u8>)>,
        ledger_packed: Vec<u8>,
    }

    fn ledger_fixture() -> LedgerFixture {
        let (plan, packed_owner, receipt, external_values) =
            crate::daa_history_producer_tests::mature_eip_844672_h21_detailed_case();
        assert_eq!(packed_owner.len(), daa_history_producer::PACKED_OWNER_BYTES);
        assert!(BANKS.iter().any(|(start, end)| {
            packed_owner[*start / 8..*end / 8]
                .iter()
                .any(|byte| *byte != 0)
        }));
        let roster = DaaHistoryRoster::compile(&plan).unwrap();
        assert_eq!(
            roster.owner_class(OWNER).unwrap(),
            OwnerClass::Mature(Epoch::Eip)
        );
        let mut row_terms = Vec::new();
        let counts = roster
            .visit_owner_terms(OWNER, |term| {
                row_terms.push(term);
                Ok(())
            })
            .unwrap();
        assert!(
            !row_terms.is_empty(),
            "mature-EIP fixture must emit DAA ROW terms"
        );
        assert_eq!(receipt.counts, counts);
        assert_eq!(receipt.external_cells, external_values.len());
        let bank_patches = BANKS
            .iter()
            .map(|(start, end)| (*start..*end, packed_owner[*start / 8..*end / 8].to_vec()))
            .collect::<Vec<_>>();
        let source = NativeDaaStage {
            owner: OWNER,
            packed_owner: packed_owner.clone(),
            row_terms,
            bank_patches: bank_patches.clone(),
            external_values,
            serializer_import_values: BTreeMap::new(),
            serializer_import_targets: BTreeMap::new(),
            receipt,
            plan_root: plan.descriptor().root,
            plan_total_be28: plan.work_profile().total_be28,
        };
        let (ledger_rows, ledger_domains) =
            crate::h21_local_merged_ledger::published_mature_eip_844672_claims(&plan).unwrap();
        assert!(
            !ledger_rows.is_empty(),
            "published mature-EIP ledger must expose DAA ROW terms"
        );
        let ledger_patches = ledger_domains
            .into_iter()
            .map(|domain| {
                let start = domain.start / 8;
                let end = domain.end / 8;
                (domain, packed_owner[start..end].to_vec())
            })
            .collect();
        LedgerFixture {
            plan,
            source,
            ledger_rows,
            ledger_patches,
            ledger_packed: packed_owner,
        }
    }

    #[test]
    fn first_pinned_serializer_source_joins_actual_daa_alias_and_import() {
        let fixture = ledger_fixture();
        let claim = first_native_serializer_source_claim(&fixture.plan, &fixture.source).unwrap();
        assert_eq!(claim.source_owner, FIRST_SOURCE_OWNER);
        assert_eq!(claim.source_height, FIRST_SOURCE_HEIGHT);
        assert_eq!(claim.serializer_wire, 1_042);
        assert_eq!(claim.address(), FIRST_SOURCE_ADDRESS);
        assert_eq!(claim.author(), SerializerSourceAuthor::HeaderSerializer);
        assert_eq!(
            fixture.source.external_values().get(&claim.address()),
            Some(&claim.value())
        );
        join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[claim]).unwrap();
    }

    #[test]
    fn first_serializer_source_join_rejects_isolated_writer_and_raw_mutants() {
        let mut fixture = ledger_fixture();
        let claim = first_native_serializer_source_claim(&fixture.plan, &fixture.source).unwrap();

        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[])
            .unwrap_err()
            .contains("exactly one source writer"));
        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[claim, claim])
            .unwrap_err()
            .contains("exactly one source writer"));

        let mut wrong_owner = claim;
        wrong_owner.source_owner += 1;
        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[wrong_owner])
            .unwrap_err()
            .contains("owner/height"));

        let mut wrong_height = claim;
        wrong_height.source_height += 1;
        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[wrong_height])
            .unwrap_err()
            .contains("owner/height"));

        let mut wrong_wire = claim;
        wrong_wire.serializer_wire += 1;
        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[wrong_wire])
            .unwrap_err()
            .contains("coordinate"));

        let mut wrong_address = claim;
        wrong_address.address += 1;
        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[wrong_address])
            .unwrap_err()
            .contains("coordinate"));

        let mut wrong_value = claim;
        wrong_value.value = !wrong_value.value;
        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[wrong_value])
            .unwrap_err()
            .contains("pinned RAW"));

        let mut wrong_author = claim;
        wrong_author.author = SerializerSourceAuthor::DaaCallback;
        assert!(join_first_serializer_source_to_daa(&fixture.plan, &fixture.source, &[wrong_author])
            .unwrap_err()
            .contains("author mismatch"));

        // Flip the source claim, DAA callback and target packed bit together.
        // Their internal agreement cannot override the independently decoded RAW.
        let layout = fixture.plan.header_boundary().mature_layout(Epoch::Eip);
        let mut target = None;
        layout
            .visit_alias_terms(OWNER, |term| {
                if term.gate.left == claim.address() {
                    assert!(target.replace(term.gate.right).is_none());
                }
                Ok(())
            })
            .unwrap();
        let target = target.expect("real DAA alias target");
        assert_eq!(target / crate::work_tree_layout::WIDTH, OWNER as usize);
        fixture.source.external_values.insert(claim.address(), !claim.value());
        let local = target % crate::work_tree_layout::WIDTH;
        fixture.source.packed_owner[local / 8] ^= 1 << (local % 8);
        let mut coherent_flip = claim;
        coherent_flip.value = !coherent_flip.value;
        assert!(join_first_serializer_source_to_daa(
            &fixture.plan,
            &fixture.source,
            &[coherent_flip]
        )
        .unwrap_err()
        .contains("pinned RAW"));
    }

    #[test]
    #[ignore = "bounded H21 diagnostic; run alone under Job cap"]
    fn actual_retarget_output_joins_published_ledger_and_rejects_isolated_mutants() {
        let fixture = ledger_fixture();
        assert!(
            compare_native_daa_stage_to_ledger(
                &fixture.plan,
                &fixture.source,
                &fixture.ledger_rows,
                &fixture.ledger_patches,
                &fixture.ledger_packed,
            )
            .is_ok(),
            "real retarget output must join published ledger"
        );

        {
            let wrong_root =
                WorkTreeHistoryPlan::compile(1_827_840, 21, [0x36; 32], [0x35; 28]).unwrap();
            assert!(
                compare_native_daa_stage_to_ledger(
                    &wrong_root,
                    &fixture.source,
                    &fixture.ledger_rows,
                    &fixture.ledger_patches,
                    &fixture.ledger_packed
                )
                .is_err(),
                "independent root substitution accepted"
            );
        }
        {
            let wrong_total =
                WorkTreeHistoryPlan::compile(1_827_840, 21, [0x35; 32], [0x36; 28]).unwrap();
            assert!(
                compare_native_daa_stage_to_ledger(
                    &wrong_total,
                    &fixture.source,
                    &fixture.ledger_rows,
                    &fixture.ledger_patches,
                    &fixture.ledger_packed
                )
                .is_err(),
                "independent total substitution accepted"
            );
        }

        let mut omitted = fixture.ledger_rows.clone();
        omitted.pop();
        assert!(
            compare_native_daa_stage_to_ledger(
                &fixture.plan,
                &fixture.source,
                &omitted,
                &fixture.ledger_patches,
                &fixture.ledger_packed
            )
            .is_err(),
            "ROW omission accepted"
        );

        let mut duplicated = fixture.ledger_rows.clone();
        duplicated.push(duplicated[0].clone());
        assert!(
            compare_native_daa_stage_to_ledger(
                &fixture.plan,
                &fixture.source,
                &duplicated,
                &fixture.ledger_patches,
                &fixture.ledger_packed
            )
            .is_err(),
            "ROW duplication accepted"
        );

        let mut field = fixture.ledger_rows.clone();
        field[0].gate.c0 += Fr::one();
        assert!(
            compare_native_daa_stage_to_ledger(
                &fixture.plan,
                &fixture.source,
                &field,
                &fixture.ledger_patches,
                &fixture.ledger_packed
            )
            .is_err(),
            "ROW field mutant accepted"
        );

        for index in 0..BANKS.len() {
            let mut wrong_domain = fixture.ledger_patches.clone();
            wrong_domain[index].0.start += 8;
            assert!(
                compare_native_daa_stage_to_ledger(
                    &fixture.plan,
                    &fixture.source,
                    &fixture.ledger_rows,
                    &wrong_domain,
                    &fixture.ledger_packed
                )
                .is_err(),
                "bank {index} domain mutant accepted"
            );

            let mut wrong_patch_value = fixture.ledger_patches.clone();
            wrong_patch_value[index].1[0] ^= 1;
            assert!(
                compare_native_daa_stage_to_ledger(
                    &fixture.plan,
                    &fixture.source,
                    &fixture.ledger_rows,
                    &wrong_patch_value,
                    &fixture.ledger_packed
                )
                .is_err(),
                "bank {index} patch-bit mutant accepted"
            );

            let mut wrong_packed_value = fixture.ledger_packed.clone();
            wrong_packed_value[BANKS[index].0 / 8] ^= 1;
            assert!(
                compare_native_daa_stage_to_ledger(
                    &fixture.plan,
                    &fixture.source,
                    &fixture.ledger_rows,
                    &fixture.ledger_patches,
                    &wrong_packed_value
                )
                .is_err(),
                "bank {index} packed-bit mutant accepted"
            );
        }
    }
}

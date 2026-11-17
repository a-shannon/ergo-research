//! Retained full-header adapter for the code-owned work-tree replacement set.
//!
//! This joins analytical producers and preserves every unmatched anchor. It
//! does not authenticate a history or qualify a GKR/PCS consumer.
use std::collections::{BTreeSet, HashMap, HashSet};

use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use serde::Serialize;

use crate::{
    circuit, core_pool, gkr, header_hash,
    header_history_boundary::HeaderHistoryBoundary,
    sparse::{self, Circuit, Shape, Term},
    transcript::Transcript,
    work_tree_fixed_hash::{self as fixed, FixedProfile},
    work_tree_layout::{self as layout, Baseline, Endpoints, WIDTH},
    work_tree_leaf_hash::{self as leaf, LeafProfile},
    work_tree_wiring::{self as topology, Descriptor, Topology},
    work_tree_work::{self as work, WorkProfile},
};

const PROFILE: &[u8] = b"work-tree-retained-header-adapter-v1";
const VERSION: &[u8] = b"work-tree-retained-header-adapter-v1";
const A4_RULE: &[u8] = b"mature-legacy-eip-a4-only-v1";
const INPUT_BITS: usize = 20;
const ROW_BITS: usize = 19;
const INPUT_WIDTH: usize = 1 << INPUT_BITS;
const ROW_COUNT: usize = 1 << ROW_BITS;
const FULL_TERMS: usize = 474_755;
const SERIALIZER_ROWS: std::ops::Range<usize> = 12_836..274_980;
const SERIALIZER_TERMS: usize = 315_546;
const A4_ROWS: std::ops::Range<usize> = 348_440..356_632;
const A4_TERMS: usize = 8_192;
const DUMMY_TERMS: usize = 4_806;
const DUMMY_ROWS: usize = 4_614;
const NODE_TERMS: usize = 65_268;
const ENDPOINT_TERMS: usize = 8_192;
const PROTECTED_ENDPOINTS: usize = 72;
const RETIRED_TERMS: usize = 78_194;
const RETIRED_ROWS: usize = 78_002;
const RETAINED_TERMS: usize = FULL_TERMS - RETIRED_TERMS;

const DUMMY_MESSAGE_START_ROW: usize = 4_132;
const DUMMY_STATE_START_ROW: usize = 10_772;
const DUMMY_COUNTER_START_ROW: usize = 12_308;
const DUMMY_FLAG_START_ROW: usize = 12_316;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct EmissionCounts {
    pub(crate) emitted: usize,
    pub(crate) omitted_worktree: usize,
    pub(crate) omitted_a4: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct RetirementCounts {
    pub(crate) terms: usize,
    pub(crate) rows: usize,
    pub(crate) dummy_terms: usize,
    pub(crate) dummy_rows: usize,
    pub(crate) node_terms: usize,
    pub(crate) endpoint_terms: usize,
    pub(crate) protected_endpoint_terms: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TermKey {
    row: usize,
    left: usize,
    right: usize,
    coefficients: [[u64; 4]; 4],
}

fn key(term: &Term) -> TermKey {
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

fn hash_serialized<T: Serialize>(value: &T) -> Result<String, String> {
    let bytes = serde_json::to_vec(value).map_err(|error| error.to_string())?;
    Ok(layout::hash_bytes(&bytes))
}

fn canonical_slot_log(headers: usize) -> Option<usize> {
    if headers < 2 {
        return None;
    }
    let slots = headers.checked_next_power_of_two()?;
    Some(slots.trailing_zeros() as usize)
}

fn validate_admission(headers: u64, slot_log: usize) -> Result<(usize, usize, usize), String> {
    if usize::BITS != 64 {
        return Err("work-tree history adapter requires a 64-bit target".into());
    }
    let n = usize::try_from(headers).map_err(|_| "header count does not fit usize")?;
    if !(3..=(1usize << 21)).contains(&n) {
        return Err("history size outside canonical work-tree adapter range".into());
    }
    let expected_log = canonical_slot_log(n).ok_or("canonical slot width overflow")?;
    if slot_log != expected_log || slot_log > 21 {
        return Err("work-tree adapter requires canonical slot width".into());
    }
    let slots = 1usize
        .checked_shl(slot_log as u32)
        .ok_or("work-tree slot domain overflow")?;
    let leaves = n
        .checked_sub(1)
        .and_then(usize::checked_next_power_of_two)
        .ok_or("work-tree leaf domain overflow")?;
    if slots != n.next_power_of_two() || leaves > slots {
        return Err("tree and header physical domains differ".into());
    }
    Ok((n, slots, leaves))
}

fn zero_anchor(row: usize, wire: usize) -> Term {
    Term {
        row,
        gate: gkr::Gate {
            left: wire,
            right: 0,
            c0: Fr::zero(),
            c1: Fr::one(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    }
}

fn add_expected(expected: &mut Vec<Term>, term: Term) {
    expected.push(term);
}

fn expected_dummy_terms(base: &Baseline) -> Vec<Term> {
    let compression = &base.compression;
    let initial = circuit::blake2b256_initial_state();
    let mut expected = Vec::with_capacity(DUMMY_TERMS);

    // Old eight-block BLAKE2b padding fixes the last three blocks. Rows here
    // are the canonical row schedule in header_hash::boundary.
    for copy in 5..8 {
        for byte in copy * 128..(copy + 1) * 128 {
            for bit in 0..8 {
                let wire = copy * header_hash::CORE_WIDTH
                    + compression.message[(byte % 128) / 8][(byte % 8) * 8 + bit];
                let row = DUMMY_MESSAGE_START_ROW + (byte - 514) * 8 + bit;
                add_expected(&mut expected, zero_anchor(row, wire));
            }
        }
    }
    for copy in 5..8 {
        for word in 0..8 {
            for bit in 0..64 {
                let wire = copy * header_hash::CORE_WIDTH + compression.state[word][bit];
                let value = (initial[word] >> bit) & 1;
                let row = DUMMY_STATE_START_ROW + (copy - 5) * 512 + word * 64 + bit;
                add_expected(
                    &mut expected,
                    Term {
                        row,
                        gate: gkr::Gate {
                            left: wire,
                            right: 0,
                            c0: -Fr::from(value),
                            c1: Fr::one(),
                            c2: Fr::zero(),
                            c3: Fr::zero(),
                        },
                    },
                );
            }
        }
        let row = DUMMY_COUNTER_START_ROW + copy;
        for (bit, &counter_wire) in compression.counter.iter().enumerate() {
            add_expected(
                &mut expected,
                Term {
                    row,
                    gate: gkr::Gate {
                        left: copy * header_hash::CORE_WIDTH + counter_wire,
                        right: 0,
                        c0: Fr::zero(),
                        c1: Fr::from(1u64 << bit),
                        c2: Fr::zero(),
                        c3: Fr::zero(),
                    },
                },
            );
        }
        let row = DUMMY_FLAG_START_ROW + copy;
        add_expected(
            &mut expected,
            Term {
                row,
                gate: gkr::Gate {
                    left: 0,
                    right: 0,
                    c0: -Fr::one(),
                    c1: Fr::zero(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            },
        );
        add_expected(
            &mut expected,
            Term {
                row,
                gate: gkr::Gate {
                    left: copy * header_hash::CORE_WIDTH + compression.final_flag,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            },
        );
    }
    expected
}

fn validate_endpoint_map(endpoints: &Endpoints) -> Result<String, String> {
    let canonical = Endpoints::new();
    if endpoints.used != canonical.used
        || endpoints.count.len() != 32
        || endpoints.position.len() != 32
        || endpoints.level.len() != 8
        || endpoints.count[0] != 989_658
        || endpoints.position[0] != 989_690
        || endpoints.level[0] != 989_722
        || endpoints.level[7] + 1 != 989_730
    {
        return Err("typed endpoint map or protected range changed".into());
    }
    let fields = vec![
        ("raw", endpoints.raw.clone()),
        ("length", endpoints.length.clone()),
        ("n_bits", endpoints.n_bits.clone()),
        ("height", endpoints.height.clone()),
        ("lower", endpoints.lower.clone()),
        ("upper", endpoints.upper.clone()),
        ("work", endpoints.work.clone()),
        ("exponent", endpoints.exponent.clone()),
        ("work_minus_one", endpoints.work_minus_one.clone()),
        ("leaf", endpoints.leaf.clone()),
        ("node_left", endpoints.node_left.clone()),
        ("node_right", endpoints.node_right.clone()),
        ("node", endpoints.node.clone()),
        ("profile", endpoints.profile.clone()),
        ("count", endpoints.count.clone()),
        ("position", endpoints.position.clone()),
        ("level", endpoints.level.clone()),
    ];
    let canonical_fields = vec![
        ("raw", canonical.raw),
        ("length", canonical.length),
        ("n_bits", canonical.n_bits),
        ("height", canonical.height),
        ("lower", canonical.lower),
        ("upper", canonical.upper),
        ("work", canonical.work),
        ("exponent", canonical.exponent),
        ("work_minus_one", canonical.work_minus_one),
        ("leaf", canonical.leaf),
        ("node_left", canonical.node_left),
        ("node_right", canonical.node_right),
        ("node", canonical.node),
        ("profile", canonical.profile),
        ("count", canonical.count),
        ("position", canonical.position),
        ("level", canonical.level),
    ];
    if fields != canonical_fields {
        return Err("endpoint field map differs from canonical contiguous layout".into());
    }
    let bytes = serde_json::to_vec(&(fields, endpoints.used)).map_err(|error| error.to_string())?;
    Ok(layout::hash_bytes(&bytes))
}

fn build_retirement(
    source: &Circuit,
    base: &Baseline,
) -> Result<(Circuit, HashSet<TermKey>, RetirementCounts, String), String> {
    if source.input_len != INPUT_WIDTH
        || source.row_count != ROW_COUNT
        || source.terms.len() != FULL_TERMS
    {
        return Err("full-header source shape changed before retirement".into());
    }
    let endpoints = &base.endpoints;
    let endpoint_map_hash = validate_endpoint_map(endpoints)?;
    let mut expected_dummy = expected_dummy_terms(base);
    if expected_dummy.len() != DUMMY_TERMS {
        return Err("dummy compression source schedule changed".into());
    }

    let mut expected_node = Vec::with_capacity(NODE_TERMS);
    for wire in 917_772..983_040 {
        expected_node.push(zero_anchor(274_980 + wire - 917_772, wire));
    }

    let protected_start = endpoints.count[0];
    let protected_end = endpoints.level[7] + 1;
    if protected_start != 989_658 || protected_end != 989_730 {
        return Err("protected typed endpoint range changed".into());
    }
    let mut expected_endpoint = Vec::with_capacity(ENDPOINT_TERMS - PROTECTED_ENDPOINTS);
    let mut expected_protected = Vec::with_capacity(PROTECTED_ENDPOINTS);
    for wire in 983_040..991_232 {
        let term = zero_anchor(274_980 + wire - 917_772, wire);
        if (protected_start..protected_end).contains(&wire) {
            expected_protected.push(term);
        } else {
            expected_endpoint.push(term);
        }
    }

    let mut source_counts = HashMap::<TermKey, usize>::with_capacity(source.terms.len());
    for term in &source.terms {
        *source_counts.entry(key(term)).or_default() += 1;
    }
    let mut expected_all = Vec::with_capacity(RETIRED_TERMS + PROTECTED_ENDPOINTS);
    expected_all.append(&mut expected_dummy);
    expected_all.extend(expected_node.iter().cloned());
    expected_all.extend(expected_endpoint.iter().cloned());
    expected_all.extend(expected_protected.iter().cloned());

    let mut distinct = HashSet::with_capacity(expected_all.len());
    for expected in &expected_all {
        let identity = key(expected);
        if source_counts.get(&identity) != Some(&1) || !distinct.insert(identity) {
            return Err("old zero-anchor identity missing, duplicated, or overlapped".into());
        }
    }
    validate_complete_source_rows(source, &expected_all)?;

    let release_keys: HashSet<_> = expected_all
        .iter()
        .filter(|term| {
            !((protected_start..protected_end).contains(&term.gate.left)
                && term.row == 274_980 + term.gate.left - 917_772)
        })
        .map(key)
        .collect();
    if release_keys.len() != RETIRED_TERMS {
        return Err("work-tree release set count changed".into());
    }

    let retired_terms: Vec<_> = source
        .terms
        .iter()
        .filter(|term| release_keys.contains(&key(term)))
        .cloned()
        .collect();
    validate_retired_protection(&retired_terms)?;
    let rows: BTreeSet<_> = retired_terms.iter().map(|term| term.row).collect();
    let dummy_rows: BTreeSet<_> = expected_all
        .iter()
        .take(DUMMY_TERMS)
        .map(|term| term.row)
        .collect();
    let serializer_terms = source
        .terms
        .iter()
        .filter(|term| SERIALIZER_ROWS.contains(&term.row))
        .count();
    let a4_terms = source
        .terms
        .iter()
        .filter(|term| A4_ROWS.contains(&term.row))
        .count();
    if retired_terms.len() != RETIRED_TERMS
        || rows.len() != RETIRED_ROWS
        || dummy_rows.len() != DUMMY_ROWS
        || expected_node.len() != NODE_TERMS
        || expected_endpoint.len() != ENDPOINT_TERMS - PROTECTED_ENDPOINTS
        || expected_protected.len() != PROTECTED_ENDPOINTS
        || serializer_terms != SERIALIZER_TERMS
        || a4_terms != A4_TERMS
        || retired_terms
            .iter()
            .any(|term| SERIALIZER_ROWS.contains(&term.row) || A4_ROWS.contains(&term.row))
    {
        return Err("retirement, serializer, protected endpoint, or A4 counts changed".into());
    }

    let retired = Circuit {
        input_len: source.input_len,
        row_count: source.row_count,
        terms: retired_terms,
    };
    let shape = sparse::validate(&retired, 0)
        .map_err(|error| format!("retired local wiring rejected: {error:?}"))?;
    if shape.input_bits != INPUT_BITS || shape.row_bits != ROW_BITS {
        return Err("retired local wiring dimensions changed".into());
    }
    let counts = RetirementCounts {
        terms: RETIRED_TERMS,
        rows: RETIRED_ROWS,
        dummy_terms: DUMMY_TERMS,
        dummy_rows: DUMMY_ROWS,
        node_terms: NODE_TERMS,
        endpoint_terms: ENDPOINT_TERMS - PROTECTED_ENDPOINTS,
        protected_endpoint_terms: PROTECTED_ENDPOINTS,
    };
    let retired_hash = layout::hash_terms(&retired.terms);
    Ok((
        retired,
        release_keys,
        counts,
        format!("{endpoint_map_hash}:{retired_hash}"),
    ))
}

fn validate_retired_protection(terms: &[Term]) -> Result<(), String> {
    if terms.iter().any(|term| {
        (346_866..346_938).contains(&term.row)
            || SERIALIZER_ROWS.contains(&term.row)
            || A4_ROWS.contains(&term.row)
            || (989_658..989_730).contains(&term.gate.left)
    }) {
        return Err("retirement crosses protected or retained source".into());
    }
    Ok(())
}

fn validate_complete_source_rows(source: &Circuit, expected: &[Term]) -> Result<(), String> {
    let mut expected_by_row = HashMap::<usize, Vec<TermKey>>::new();
    for term in expected {
        expected_by_row.entry(term.row).or_default().push(key(term));
    }
    for terms in expected_by_row.values_mut() {
        terms.sort_unstable();
    }
    let mut actual_by_row = HashMap::<usize, Vec<TermKey>>::new();
    for term in &source.terms {
        if expected_by_row.contains_key(&term.row) {
            actual_by_row.entry(term.row).or_default().push(key(term));
        }
    }
    for terms in actual_by_row.values_mut() {
        terms.sort_unstable();
    }
    if expected_by_row != actual_by_row {
        return Err("candidate source row contains missing, extra, or shifted terms".into());
    }
    Ok(())
}

fn same_slot_extension(r: &[Fr], u: &[Fr], v: &[Fr]) -> Fr {
    r.iter().zip(u).zip(v).fold(Fr::one(), |acc, ((r, u), v)| {
        acc * ((Fr::one() - r) * (Fr::one() - u) * (Fr::one() - v) + *r * u * v)
    })
}

fn validate_retirement_counts(counts: RetirementCounts) -> Result<(), String> {
    if counts.terms != RETIRED_TERMS
        || counts.rows != RETIRED_ROWS
        || counts.dummy_terms != DUMMY_TERMS
        || counts.dummy_rows != DUMMY_ROWS
        || counts.node_terms != NODE_TERMS
        || counts.endpoint_terms != ENDPOINT_TERMS - PROTECTED_ENDPOINTS
        || counts.protected_endpoint_terms != PROTECTED_ENDPOINTS
    {
        return Err("work-tree retirement count contract changed".into());
    }
    Ok(())
}

#[derive(Clone)]
struct StatementBinding {
    headers: u64,
    slot_log: usize,
    slots: usize,
    leaves: usize,
    input_log: usize,
    row_log: usize,
    root: [u8; 32],
    total_be28: [u8; 28],
}

impl StatementBinding {
    fn append(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"work-tree-history-profile", PROFILE);
        transcript.append_bytes(b"work-tree-history-version", VERSION);
        transcript.append_u64(b"work-tree-history-N", self.headers);
        gkr::append_usize(transcript, b"work-tree-history-h", self.slot_log);
        gkr::append_usize(transcript, b"work-tree-history-S", self.slots);
        gkr::append_usize(transcript, b"work-tree-history-B", self.leaves);
        gkr::append_usize(transcript, b"work-tree-history-input-log", self.input_log);
        gkr::append_usize(transcript, b"work-tree-history-row-log", self.row_log);
        transcript.append_bytes(b"work-tree-history-root", &self.root);
        transcript.append_bytes(b"work-tree-history-total-be28", &self.total_be28);
    }
}

fn slot_template_hashes(
    slots: &[usize],
    mut emit: impl FnMut(usize) -> Result<Vec<Term>, String>,
) -> Result<String, String> {
    let mut hashes = Vec::with_capacity(slots.len());
    for &slot in slots {
        let terms = emit(slot)?;
        hashes.push((slot, terms.len(), layout::hash_terms(&terms)));
    }
    hash_serialized(&hashes)
}

fn replacement_fingerprints(
    headers: usize,
    root: [u8; 32],
    descriptor: &Descriptor,
    fixed_profile: &FixedProfile,
    leaf_profile: &LeafProfile,
    leaf_boundary: &leaf::Boundary,
    work_profile: &WorkProfile,
    work_boundary: &work::Boundary,
    engine: &fixed::Engine,
    topology: &Topology,
    core_pool: &core_pool::Plan,
    endpoint_map_hash: &str,
) -> Result<(String, String, String, String, String), String> {
    validate_replacement_contract(
        headers,
        root,
        engine.base,
        descriptor,
        fixed_profile,
        leaf_profile,
        work_profile,
        topology,
        core_pool,
        endpoint_map_hash,
    )?;
    let fixed_counts = fixed::count(engine, fixed_profile)?;
    let fixed_hash = hash_serialized(&(
        fixed_profile.fingerprint()?,
        fixed_counts,
        engine.base.inventory.core.terms_blake2b256.clone(),
        engine.base.inventory.descriptor_blake2b256.clone(),
    ))?;
    let mut fixed_slots = BTreeSet::new();
    fixed_slots.insert(descriptor.profile_node_slot);
    fixed_slots.insert(descriptor.root_node_slot);
    if descriptor.leaves < descriptor.slots {
        fixed_slots.insert(descriptor.leaves);
    }
    for level in 1..=descriptor.leaves.trailing_zeros() as usize {
        let (base, count) = descriptor.level(level)?;
        fixed_slots.insert(base);
        fixed_slots.insert(base + count - 1);
    }
    let fixed_terms_hash =
        slot_template_hashes(&fixed_slots.into_iter().collect::<Vec<_>>(), |slot| {
            let mut terms = Vec::new();
            fixed::emit_slot(engine, fixed_profile, slot, |term| terms.push(term))?;
            Ok(terms)
        })?;

    let leaf_counts = leaf::count(engine, leaf_boundary)?;
    let mut leaf_slots = BTreeSet::new();
    leaf_slots.insert(0);
    if descriptor.genuine < descriptor.leaves {
        leaf_slots.insert(descriptor.genuine);
    }
    if descriptor.leaves < descriptor.slots {
        leaf_slots.insert(descriptor.leaves);
    }
    let leaf_terms_hash =
        slot_template_hashes(&leaf_slots.into_iter().collect::<Vec<_>>(), |slot| {
            let mut terms = Vec::new();
            leaf_boundary.emit_slot(slot, |term| terms.push(term))?;
            Ok(terms)
        })?;
    let leaf_hash = hash_serialized(&(leaf_profile, leaf_counts, leaf_terms_hash))?;

    let work_counts = work::count(work_boundary)?;
    let mut work_slots = BTreeSet::new();
    work_slots.insert(0);
    if descriptor.genuine < descriptor.leaves {
        work_slots.insert(descriptor.genuine);
    }
    let work_terms_hash =
        slot_template_hashes(&work_slots.into_iter().collect::<Vec<_>>(), |slot| {
            let mut terms = Vec::new();
            work_boundary.emit_slot(slot, |term| terms.push(term))?;
            Ok(terms)
        })?;
    let work_hash = hash_serialized(&(work_profile, work_counts, work_terms_hash))?;

    let topology_report = topology.report()?;
    let topology_hash = hash_serialized(&(descriptor, &topology.families, topology_report))?;
    let pool_cost = core_pool.cost_report()?;
    let kernel_contract = hash_serialized(&(
        headers,
        descriptor.slot_log(),
        (
            &fixed_hash,
            &fixed_terms_hash,
            &leaf_hash,
            &work_hash,
            &topology_hash,
        ),
        endpoint_map_hash,
        (
            (0usize, descriptor.genuine),
            (descriptor.genuine, descriptor.leaves),
            (descriptor.leaves, descriptor.slots),
            (1usize, headers),
            (protected_endpoint_start(), protected_endpoint_end()),
            (983_040usize, 989_658usize),
            (989_730usize, 991_232usize),
        ),
        (
            (DUMMY_TERMS, DUMMY_ROWS),
            (NODE_TERMS, 65_268usize),
            (ENDPOINT_TERMS, PROTECTED_ENDPOINTS),
            (RETIRED_TERMS, RETIRED_ROWS),
            (RETAINED_TERMS, FULL_TERMS),
        ),
        (
            (SERIALIZER_ROWS.start, SERIALIZER_ROWS.end, SERIALIZER_TERMS),
            (A4_ROWS.start, A4_ROWS.end, A4_TERMS),
        ),
        (
            pool_cost.copy_bits,
            pool_cost.global_terms,
            pool_cost.packed_trace_bytes,
            pool_cost.gkr_proof_bytes,
            pool_cost.cache_bound_bytes,
            pool_cost.full_input_field_bytes,
            pool_cost.field_bytes,
            pool_cost.sparse_entry_bytes,
            pool_cost.slot_descriptor_bytes,
        ),
        layout::CORE_OFFSETS.to_vec(),
    ))?;
    Ok((
        fixed_hash,
        leaf_hash,
        work_hash,
        topology_hash,
        kernel_contract,
    ))
}

fn protected_endpoint_start() -> usize {
    989_658
}

fn protected_endpoint_end() -> usize {
    989_730
}

fn equal_family(
    name: &str,
    mapping: topology::Mapping,
    left_wires: Vec<usize>,
    right_wires: Vec<usize>,
) -> topology::Family {
    topology::Family {
        name: name.into(),
        mapping,
        left_wires,
        right_wires,
        constants: None,
    }
}

fn zero_family(name: &str, lo: usize, hi: usize, wires: Vec<usize>) -> topology::Family {
    topology::Family {
        name: name.into(),
        mapping: topology::Mapping::FixedRight { lo, hi, target: 0 },
        right_wires: vec![0; wires.len()],
        constants: Some(vec![0; wires.len()]),
        left_wires: wires,
    }
}

fn expected_topology_families(
    descriptor: &Descriptor,
    base: &Baseline,
    root: [u8; 32],
) -> Result<Vec<topology::Family>, String> {
    let endpoints = &base.endpoints;
    if base.header_alias_wires.len() != 4_186 {
        return Err("serializer header alias map has an unexpected width".into());
    }
    let compression = &base.compression;
    let mut families = Vec::new();
    families.push(equal_family(
        "header_to_leaf_raw_length_nbits_height",
        topology::Mapping::HeaderSuccessor {
            lo: 1,
            hi: descriptor.headers,
        },
        base.header_alias_wires.clone(),
        endpoints.header_aliases(),
    ));
    families.push(equal_family(
        "node_profile_output_core_alias",
        topology::Mapping::Same {
            lo: 0,
            hi: descriptor.leaves,
        },
        endpoints.node.clone(),
        (0..256)
            .map(|bit| 917_504 + compression.output[bit / 64][bit % 64])
            .collect(),
    ));
    for branch in 0..2 {
        let bytes = 6 + 32 * branch;
        let left = if branch == 0 {
            endpoints.node_left.clone()
        } else {
            endpoints.node_right.clone()
        };
        let right = (0..256)
            .map(|bit| {
                let byte = bytes + bit / 8;
                917_504 + compression.message[byte / 8][(byte % 8) * 8 + bit % 8]
            })
            .collect();
        families.push(equal_family(
            &format!("node_message_child_{branch}"),
            topology::Mapping::Same {
                lo: 0,
                hi: descriptor.leaves - 1,
            },
            left,
            right,
        ));
    }
    families.push(equal_family(
        "profile_digest_fanout",
        topology::Mapping::FixedRight {
            lo: 0,
            hi: descriptor.leaves,
            target: descriptor.profile_node_slot,
        },
        endpoints.profile.clone(),
        endpoints.node.clone(),
    ));
    for level in 1..=descriptor.leaves.trailing_zeros() as usize {
        for branch in 0..2 {
            families.push(equal_family(
                &format!("level_{level}_child_{branch}"),
                topology::Mapping::Child { level, branch },
                if branch == 0 {
                    endpoints.node_left.clone()
                } else {
                    endpoints.node_right.clone()
                },
                if level == 1 {
                    endpoints.leaf.clone()
                } else {
                    endpoints.node.clone()
                },
            ));
        }
    }
    families.push(topology::Family {
        name: "public_root".into(),
        mapping: topology::Mapping::FixedRight {
            lo: descriptor.root_node_slot,
            hi: descriptor.root_node_slot + 1,
            target: 0,
        },
        left_wires: endpoints.node.clone(),
        right_wires: vec![0; 256],
        constants: Some(
            (0..256)
                .map(|bit| (root[bit / 8] >> (bit % 8)) & 1)
                .collect(),
        ),
    });
    families.push(zero_family(
        "inactive_tree_endpoints",
        descriptor.leaves,
        descriptor.slots,
        (layout::ENDPOINT_BASE..layout::ENDPOINT_BASE + layout::ENDPOINT_WIDTH).collect(),
    ));
    families.push(zero_family(
        "padding_leaf_unused_header_aliases",
        descriptor.genuine,
        descriptor.leaves,
        endpoints.header_aliases(),
    ));
    families.push(zero_family(
        "profile_slot_unused_child_endpoints",
        descriptor.profile_node_slot,
        descriptor.profile_node_slot + 1,
        endpoints
            .node_left
            .iter()
            .chain(&endpoints.node_right)
            .copied()
            .collect(),
    ));
    families.push(zero_family(
        "endpoint_bank_padding",
        0,
        descriptor.slots,
        (layout::ENDPOINT_BASE + endpoints.used..layout::ENDPOINT_BASE + layout::ENDPOINT_WIDTH)
            .collect(),
    ));
    Ok(families)
}

fn validate_topology_families(
    descriptor: &Descriptor,
    base: &Baseline,
    root: [u8; 32],
    families: &[topology::Family],
) -> Result<(), String> {
    let expected = expected_topology_families(descriptor, base, root)?;
    if families != expected {
        return Err("topology mappings, aliases, constants, or role wires changed".into());
    }
    Ok(())
}

fn validate_replacement_contract(
    headers: usize,
    root: [u8; 32],
    base: &Baseline,
    descriptor: &Descriptor,
    fixed_profile: &FixedProfile,
    leaf_profile: &LeafProfile,
    work_profile: &WorkProfile,
    topology: &Topology,
    core_pool: &core_pool::Plan,
    endpoint_map_hash: &str,
) -> Result<(), String> {
    descriptor.validate()?;
    fixed_profile.validate()?;
    leaf_profile.validate()?;
    work_profile.validate()?;
    topology.validate()?;
    validate_endpoint_map(&base.endpoints)?;
    validate_topology_families(descriptor, base, root, &topology.families)?;
    if descriptor.headers != headers
        || fixed_profile.tree != *descriptor
        || leaf_profile.tree != *descriptor
        || work_profile.tree != *descriptor
        || topology.descriptor != *descriptor
        || endpoint_map_hash.len() != 64
        || core_pool.copy_bits() != descriptor.slot_log()
        || core_pool.term_count() != 172_480usize * 11 * descriptor.slots
        || layout::CORE_OFFSETS.len() != 11
    {
        return Err("replacement producer descriptor or eleven-bank contract differs".into());
    }

    Ok(())
}

/// Immutable compiler-owned replacement contract and retained-header adapter.
pub(crate) struct WorkTreeHistoryPlan {
    headers: u64,
    slot_log: usize,
    descriptor: Descriptor,
    boundary: HeaderHistoryBoundary,
    fixed_profile: FixedProfile,
    leaf_profile: LeafProfile,
    leaf_boundary: leaf::Boundary,
    work_profile: WorkProfile,
    work_boundary: work::Boundary,
    topology: Topology,
    core_pool: core_pool::Plan,
    retired: Circuit,
    retired_shape: Shape,
    retired_keys: HashSet<TermKey>,
    retirement_counts: RetirementCounts,
    header_fingerprint: String,
    endpoint_map_hash: String,
    fixed_hash: String,
    leaf_hash: String,
    work_hash: String,
    topology_hash: String,
    replacement_hash: String,
    root: [u8; 32],
    total_be28: [u8; 28],
}

impl WorkTreeHistoryPlan {
    pub(crate) fn compile(
        headers: u64,
        slot_log: usize,
        root: [u8; 32],
        total_be28: [u8; 28],
    ) -> Result<Self, String> {
        // Reject every public dimension before a producer template factory.
        let (n, slots, leaves) = validate_admission(headers, slot_log)?;
        let history = HeaderHistoryBoundary::compile(headers, slot_log)?;
        let source = history.canonical_circuit();
        let header_fingerprint = history.fingerprint().to_owned();
        if history.history_slots() != headers
            || history.slot_log() != slot_log
            || header_fingerprint
                != "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76"
        {
            return Err("full-header immutable profile or fingerprint changed".into());
        }

        let engine = fixed::engine()?;
        let base = engine.base;
        let descriptor = Descriptor::new(n, root)?;
        descriptor.validate()?;
        if descriptor.slots != slots
            || descriptor.leaves != leaves
            || descriptor.genuine != n - 1
            || descriptor.slot_log() != slot_log
        {
            return Err("canonical header/tree descriptor mismatch".into());
        }

        let fixed_profile = FixedProfile::new(n, root)?;
        fixed_profile.validate()?;
        let leaf_profile = LeafProfile::new(n, root)?;
        leaf_profile.validate()?;
        let leaf_boundary = leaf::compile(engine, leaf_profile.clone())?;
        let work_profile = WorkProfile::new(n, root, total_be28)?;
        work_profile.validate()?;
        let work_boundary = work::compile(base, work_profile.clone())?;
        let topology = Topology::new(base, n, root)?;
        topology.validate()?;
        if topology.descriptor != descriptor {
            return Err("topology descriptor differs from work-tree descriptor".into());
        }
        let core_pool = core_pool::Plan::new(slot_log)?;
        if core_pool.copy_bits() != slot_log
            || core_pool.input_log() != INPUT_BITS + slot_log
            || core_pool.row_log() != ROW_BITS + 2 + slot_log
            || core_pool.input_len() != 1usize << (INPUT_BITS + slot_log)
        {
            return Err("eleven-bank core-pool tensor contract changed".into());
        }

        let (retired, retired_keys, retirement_counts, combined_map_hash) =
            build_retirement(source, base)?;
        let retired_shape = sparse::validate(&retired, 0)
            .map_err(|error| format!("retired local wiring rejected: {error:?}"))?;
        let mut hashes = combined_map_hash.split(':');
        let endpoint_map_hash = hashes.next().ok_or("missing endpoint map hash")?.to_owned();
        let retired_hash = hashes.next().ok_or("missing retired hash")?;
        if hashes.next().is_some() || retired_hash != layout::hash_terms(&retired.terms) {
            return Err("retirement source hash consistency failed".into());
        }

        let (fixed_hash, leaf_hash, work_hash, topology_hash, replacement_hash) =
            replacement_fingerprints(
                n,
                root,
                &descriptor,
                &fixed_profile,
                &leaf_profile,
                &leaf_boundary,
                &work_profile,
                &work_boundary,
                engine,
                &topology,
                &core_pool,
                &endpoint_map_hash,
            )?;
        if retirement_counts.terms != RETIRED_TERMS
            || retirement_counts.rows != RETIRED_ROWS
            || source.terms.len() - retired.terms.len() != RETAINED_TERMS
        {
            return Err("retained header count contract changed".into());
        }
        validate_retirement_counts(retirement_counts)?;

        Ok(Self {
            headers,
            slot_log,
            descriptor,
            boundary: history,
            fixed_profile,
            leaf_profile,
            leaf_boundary,
            work_profile,
            work_boundary,
            topology,
            core_pool,
            retired,
            retired_shape,
            retired_keys,
            retirement_counts,
            header_fingerprint,
            endpoint_map_hash,
            fixed_hash,
            leaf_hash,
            work_hash,
            topology_hash,
            replacement_hash,
            root,
            total_be28,
        })
    }

    pub(crate) fn headers(&self) -> u64 {
        self.headers
    }

    pub(crate) fn slot_log(&self) -> usize {
        self.slot_log
    }

    pub(crate) fn slots(&self) -> usize {
        self.descriptor.slots
    }

    pub(crate) fn descriptor(&self) -> &Descriptor {
        &self.descriptor
    }

    pub(crate) fn retirement_counts(&self) -> RetirementCounts {
        self.retirement_counts
    }

    pub(crate) fn replacement_fingerprint(&self) -> &str {
        &self.replacement_hash
    }

    /// Replacement permission for one physical owner of an admitted plan.
    /// The constructor pins the same local retirement template for every owner.
    /// This mask supplies no witness values: native producers must claim their
    /// complete domains and the joined witness must satisfy retained relations.
    pub(crate) fn physical_assignment_replacement_mask(
        &self,
        owner: u64,
    ) -> Result<Vec<bool>, String> {
        validate_retirement_counts(self.retirement_counts)?;
        self.descriptor.validate()?;
        if owner >= self.descriptor.slots as u64
            || self.headers != self.descriptor.headers as u64
            || self.slot_log != self.descriptor.slot_log()
        {
            return Err("physical assignment overlay outside admitted owner domain".into());
        }
        let endpoints = &fixed::engine()?.base.endpoints;
        let mut mask = vec![false; WIDTH];
        for base in leaf::CORES.into_iter().chain([fixed::NODE_CORE]) {
            mask[base..base + layout::CORE].fill(true);
        }
        mask[leaf::AUX..leaf::AUX + leaf::AUX_BITS].fill(true);
        mask[layout::ENDPOINT_BASE..layout::ENDPOINT_BASE + layout::ENDPOINT_WIDTH].fill(true);
        mask[endpoints.count[0]..endpoints.level[7] + 1].fill(false);
        if mask.iter().filter(|bit| **bit).count() != 401_362
            || mask[991_232..999_424].iter().any(|bit| *bit)
            || self.retirement_counts.protected_endpoint_terms != PROTECTED_ENDPOINTS
        {
            return Err("physical assignment overlay dependency changed".into());
        }
        Ok(mask)
    }

    /// The original bounded common-prefix helper keeps its N3/N4 admission.
    #[cfg(test)]
    pub(crate) fn assignment_replacement_mask(&self) -> Result<Vec<bool>, String> {
        if !matches!(self.headers, 3 | 4) || self.slot_log != 2 || self.descriptor.slots != 4 {
            return Err("prefix assignment overlay requires an N3/N4 four-slot plan".into());
        }
        self.physical_assignment_replacement_mask(0)
    }

    pub(crate) fn header_boundary(&self) -> &HeaderHistoryBoundary {
        &self.boundary
    }

    pub(crate) fn fixed_profile(&self) -> &FixedProfile {
        &self.fixed_profile
    }

    pub(crate) fn leaf_profile(&self) -> &LeafProfile {
        &self.leaf_profile
    }

    pub(crate) fn leaf_boundary(&self) -> &leaf::Boundary {
        &self.leaf_boundary
    }

    pub(crate) fn work_profile(&self) -> &WorkProfile {
        &self.work_profile
    }

    pub(crate) fn work_boundary(&self) -> &work::Boundary {
        &self.work_boundary
    }

    pub(crate) fn topology(&self) -> &Topology {
        &self.topology
    }

    pub(crate) fn core_pool(&self) -> &core_pool::Plan {
        &self.core_pool
    }

    /// Append the complete code-owned plan before deriving challenges.
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        StatementBinding {
            headers: self.headers,
            slot_log: self.slot_log,
            slots: self.descriptor.slots,
            leaves: self.descriptor.leaves,
            input_log: INPUT_BITS + self.slot_log,
            row_log: ROW_BITS + self.slot_log,
            root: self.root,
            total_be28: self.total_be28,
        }
        .append(transcript);
        transcript.append_bytes(
            b"work-tree-history-template",
            self.header_fingerprint.as_bytes(),
        );
        transcript.append_bytes(
            b"work-tree-history-endpoint-map",
            self.endpoint_map_hash.as_bytes(),
        );
        transcript.append_bytes(
            b"work-tree-history-fixed-profile",
            self.fixed_hash.as_bytes(),
        );
        transcript.append_bytes(b"work-tree-history-leaf-profile", self.leaf_hash.as_bytes());
        transcript.append_bytes(b"work-tree-history-work-profile", self.work_hash.as_bytes());
        transcript.append_bytes(b"work-tree-history-topology", self.topology_hash.as_bytes());
        transcript.append_bytes(
            b"work-tree-history-replacement",
            self.replacement_hash.as_bytes(),
        );
        transcript.append_bytes(
            b"work-tree-history-retired",
            layout::hash_terms(&self.retired.terms).as_bytes(),
        );
        transcript.append_bytes(b"work-tree-history-a4-rule", A4_RULE);
        for (label, value) in [
            (
                b"work-tree-history-retired-terms".as_slice(),
                self.retirement_counts.terms,
            ),
            (
                b"work-tree-history-retired-rows".as_slice(),
                self.retirement_counts.rows,
            ),
            (
                b"work-tree-history-dummy-terms".as_slice(),
                self.retirement_counts.dummy_terms,
            ),
            (
                b"work-tree-history-dummy-rows".as_slice(),
                self.retirement_counts.dummy_rows,
            ),
            (
                b"work-tree-history-node-terms".as_slice(),
                self.retirement_counts.node_terms,
            ),
            (
                b"work-tree-history-endpoint-terms".as_slice(),
                self.retirement_counts.endpoint_terms,
            ),
            (
                b"work-tree-history-protected-endpoints".as_slice(),
                self.retirement_counts.protected_endpoint_terms,
            ),
        ] {
            gkr::append_usize(transcript, label, value);
        }
        self.core_pool.bind(transcript);
    }

    /// Emit the retained local header boundary for one physical owner.
    pub(crate) fn visit_slot_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<EmissionCounts, String> {
        if slot >= (1u64 << self.slot_log) {
            return Err("work-tree history owner outside declared domain".into());
        }
        validate_retirement_counts(self.retirement_counts)?;
        let owner = usize::try_from(slot).map_err(|_| "owner does not fit usize")?;
        let row_base = owner
            .checked_mul(ROW_COUNT)
            .ok_or("header row translation overflow")?;
        let input_base = owner
            .checked_mul(INPUT_WIDTH)
            .ok_or("header input translation overflow")?;
        let mut counts = EmissionCounts::default();
        let original = self.boundary.visit_slot_terms(slot, |term| {
            let local = untranslate(term.clone(), row_base, input_base)?;
            if self.retired_keys.contains(&key(&local)) {
                counts.omitted_worktree = counts
                    .omitted_worktree
                    .checked_add(1)
                    .ok_or("omitted work-tree term count overflow")?;
                Ok(())
            } else {
                sink(term)?;
                counts.emitted = counts
                    .emitted
                    .checked_add(1)
                    .ok_or("retained term count overflow")?;
                Ok(())
            }
        })?;
        counts.omitted_a4 = original.omitted_a4;
        if counts.omitted_worktree != RETIRED_TERMS
            || counts.emitted + counts.omitted_worktree != original.emitted
            || counts.emitted + counts.omitted_worktree + counts.omitted_a4 != FULL_TERMS
        {
            return Err("retained header traversal count changed".into());
        }
        Ok(counts)
    }

    /// Evaluate retained header coefficients with O(h) owner extension only.
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let row_log = ROW_BITS
            .checked_add(self.slot_log)
            .ok_or("row dimension overflow")?;
        let input_log = INPUT_BITS
            .checked_add(self.slot_log)
            .ok_or("input dimension overflow")?;
        if r.len() != row_log || u.len() != input_log || v.len() != input_log {
            return Err("retained header coefficient point dimensions rejected".into());
        }
        let mut out = self.boundary.coefficients(r, u, v)?;
        let mut removed = sparse::wiring(
            &self.retired,
            &self.retired_shape,
            &r[..ROW_BITS],
            &u[..INPUT_BITS],
            &v[..INPUT_BITS],
        )
        .map_err(|error| format!("retired wiring evaluation failed: {error:?}"))?;
        let owner_factor = same_slot_extension(&r[ROW_BITS..], &u[INPUT_BITS..], &v[INPUT_BITS..]);
        for (value, retired_value) in out.iter_mut().zip(&mut removed) {
            *value -= *retired_value * owner_factor;
        }
        Ok(out)
    }
}

fn untranslate(mut term: Term, row_base: usize, input_base: usize) -> Result<Term, String> {
    term.row = term
        .row
        .checked_sub(row_base)
        .ok_or("row precedes owner base")?;
    term.gate.left = term
        .gate
        .left
        .checked_sub(input_base)
        .ok_or("left wire precedes owner base")?;
    term.gate.right = term
        .gate
        .right
        .checked_sub(input_base)
        .ok_or("right wire precedes owner base")?;
    if term.row >= ROW_COUNT || term.gate.left >= INPUT_WIDTH || term.gate.right >= INPUT_WIDTH {
        return Err("translated header term outside canonical local shape".into());
    }
    Ok(term)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::OnceLock;

    fn n3_plan() -> &'static WorkTreeHistoryPlan {
        static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
        PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(3, 2, [7; 32], [0x35; 28]).unwrap())
    }

    fn fr_point(bits: usize, seed: u64) -> Vec<Fr> {
        (0..bits)
            .map(|index| Fr::from(seed.wrapping_add((index as u64 + 1) * 13)))
            .collect()
    }

    fn eq_direct(point: &[Fr], index: usize) -> Fr {
        let mut out = Fr::one();
        for (bit, coordinate) in point.iter().enumerate() {
            out *= if (index >> bit) & 1 == 1 {
                *coordinate
            } else {
                Fr::one() - coordinate
            };
        }
        out
    }

    fn boolean_point(bits: usize, index: usize) -> Vec<Fr> {
        (0..bits)
            .map(|bit| Fr::from(((index >> bit) & 1) as u64))
            .collect()
    }

    fn owner_weight_direct(r: &[Fr], u: &[Fr], v: &[Fr], owner: usize) -> Fr {
        let mut out = Fr::one();
        for bit in 0..r.len() {
            let equality = if (owner >> bit) & 1 == 1 {
                r[bit] * u[bit] * v[bit]
            } else {
                (Fr::one() - r[bit]) * (Fr::one() - u[bit]) * (Fr::one() - v[bit])
            };
            out *= equality;
        }
        out
    }

    // Independent fixture oracle: it spells out the old header_hash rows and
    // endpoint-to-row translation. It does not use the production release set.
    fn reference_retirement(base: &Baseline) -> HashSet<TermKey> {
        let mut terms = Vec::with_capacity(RETIRED_TERMS);
        let compression = &base.compression;
        let initial = circuit::blake2b256_initial_state();
        for copy in 5..8 {
            for byte in copy * 128..(copy + 1) * 128 {
                for bit in 0..8 {
                    let wire = copy * header_hash::CORE_WIDTH
                        + compression.message[(byte % 128) / 8][(byte % 8) * 8 + bit];
                    terms.push(zero_anchor(4_132 + (byte - 514) * 8 + bit, wire));
                }
            }
            for word in 0..8 {
                for bit in 0..64 {
                    let wire = copy * header_hash::CORE_WIDTH + compression.state[word][bit];
                    terms.push(Term {
                        row: 10_772 + (copy - 5) * 512 + word * 64 + bit,
                        gate: gkr::Gate {
                            left: wire,
                            right: 0,
                            c0: -Fr::from((initial[word] >> bit) & 1),
                            c1: Fr::one(),
                            c2: Fr::zero(),
                            c3: Fr::zero(),
                        },
                    });
                }
            }
            for (bit, &wire) in compression.counter.iter().enumerate() {
                terms.push(Term {
                    row: 12_308 + copy,
                    gate: gkr::Gate {
                        left: copy * header_hash::CORE_WIDTH + wire,
                        right: 0,
                        c0: Fr::zero(),
                        c1: Fr::from(1u64 << bit),
                        c2: Fr::zero(),
                        c3: Fr::zero(),
                    },
                });
            }
            let flag_row = 12_316 + copy;
            terms.push(Term {
                row: flag_row,
                gate: gkr::Gate {
                    left: 0,
                    right: 0,
                    c0: -Fr::one(),
                    c1: Fr::zero(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            });
            terms.push(Term {
                row: flag_row,
                gate: gkr::Gate {
                    left: copy * header_hash::CORE_WIDTH + compression.final_flag,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            });
        }
        for wire in 917_772..983_040 {
            terms.push(zero_anchor(274_980 + wire - 917_772, wire));
        }
        for wire in 983_040..991_232 {
            if !(989_658..989_730).contains(&wire) {
                terms.push(zero_anchor(274_980 + wire - 917_772, wire));
            }
        }
        terms.into_iter().map(|term| key(&term)).collect()
    }

    fn normalize_owner(term: &Term, owner: usize) -> Term {
        untranslate(term.clone(), owner * ROW_COUNT, owner * INPUT_WIDTH).unwrap()
    }

    fn direct_coefficients(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let mut out = [Fr::zero(); 4];
        for term in terms {
            let gate = &term.gate;
            let weight =
                eq_direct(r, term.row) * eq_direct(u, gate.left) * eq_direct(v, gate.right);
            for (sum, coefficient) in out.iter_mut().zip([gate.c0, gate.c1, gate.c2, gate.c3]) {
                *sum += weight * coefficient;
            }
        }
        out
    }

    #[test]
    fn n3_first_full_template_matches_independent_filter_and_direct_coefficients() {
        let plan = n3_plan();
        let base = fixed::engine().unwrap().base;
        let reference = reference_retirement(base);
        assert_eq!(reference.len(), RETIRED_TERMS);
        assert_eq!(plan.retirement_counts.terms, RETIRED_TERMS);
        assert_eq!(plan.retirement_counts.rows, RETIRED_ROWS);

        let mut owner_retained = Vec::<Vec<Term>>::new();
        let mut owner_retired = Vec::<Vec<Term>>::new();
        let mut owner_extensions = Vec::new();
        let r = fr_point(ROW_BITS + 2, 19);
        let u = fr_point(INPUT_BITS + 2, 37);
        let v = fr_point(INPUT_BITS + 2, 71);
        let mut expected_global = [Fr::zero(); 4];

        for owner in 0..4usize {
            let mut expected = Vec::new();
            let mut removed = Vec::new();
            let mut omitted_reference = 0usize;
            let mut actual = Vec::new();
            let new_counts = plan
                .visit_slot_terms(owner as u64, |term| {
                    actual.push(term);
                    Ok(())
                })
                .unwrap();
            let old = plan
                .boundary
                .visit_slot_terms(owner as u64, |term| {
                    let local = normalize_owner(&term, owner);
                    if reference.contains(&key(&local)) {
                        omitted_reference += 1;
                        removed.push(local);
                    } else {
                        expected.push(term);
                    }
                    Ok(())
                })
                .unwrap();
            assert_eq!(actual, expected, "owner {owner}");
            assert_eq!(new_counts.omitted_worktree, omitted_reference);
            assert_eq!(new_counts.omitted_a4, old.omitted_a4);
            assert_eq!(new_counts.emitted, old.emitted - omitted_reference);
            assert_eq!(
                new_counts.emitted + new_counts.omitted_worktree + new_counts.omitted_a4,
                FULL_TERMS
            );
            owner_retained.push(
                expected
                    .iter()
                    .map(|term| normalize_owner(term, owner))
                    .collect(),
            );
            assert_eq!(removed.len(), RETIRED_TERMS);
            owner_retired.push(removed);
            owner_extensions.push(owner_weight_direct(
                &r[ROW_BITS..],
                &u[INPUT_BITS..],
                &v[INPUT_BITS..],
                owner,
            ));
            assert_eq!(new_counts.omitted_a4, 0, "N=3 must not mature A4");
        }

        // N=3 has no mature A4 owners. All owner templates are the same local
        // relation; direct interpolation evaluates the complete 4-owner join.
        assert!(owner_retained.windows(2).all(|pair| pair[0] == pair[1]));
        for (terms, extension) in owner_retained.iter().zip(owner_extensions) {
            let mut local =
                direct_coefficients(terms, &r[..ROW_BITS], &u[..INPUT_BITS], &v[..INPUT_BITS]);
            for (sum, value) in expected_global.iter_mut().zip(&mut local) {
                *sum += *value * extension;
            }
        }
        let removed = direct_coefficients(
            &owner_retired[0],
            &r[..ROW_BITS],
            &u[..INPUT_BITS],
            &v[..INPUT_BITS],
        );
        assert!(!removed[0].is_zero());
        assert!(!removed[1].is_zero());
        assert!(removed[2].is_zero());
        assert!(removed[3].is_zero());
        assert_eq!(plan.coefficients(&r, &u, &v).unwrap(), expected_global);
        for channel in 0..4 {
            let present = owner_retained[0].iter().any(|term| {
                let gate = &term.gate;
                ![gate.c0, gate.c1, gate.c2, gate.c3][channel].is_zero()
            });
            assert_eq!(
                !expected_global[channel].is_zero(),
                present,
                "dense oracle must observe each populated channel {channel}"
            );
        }

        let mut protected = 0usize;
        plan.visit_slot_terms(0, |term| {
            if (346_866..346_938).contains(&term.row)
                && (989_658..989_730).contains(&term.gate.left)
                && term.gate.right == 0
                && term.gate.c0.is_zero()
                && term.gate.c1 == Fr::one()
                && term.gate.c2.is_zero()
                && term.gate.c3.is_zero()
            {
                protected += 1;
            }
            Ok(())
        })
        .unwrap();
        assert_eq!(protected, PROTECTED_ENDPOINTS);

        // Boolean owner points isolate each physical slot, including the final
        // padded domain owner, without relying on the producer's shift helper.
        for selected in 0..4usize {
            let mut r = r.clone();
            let mut u = u.clone();
            let mut v = v.clone();
            for bit in 0..2 {
                let value = Fr::from(((selected >> bit) & 1) as u64);
                r[ROW_BITS + bit] = value;
                u[INPUT_BITS + bit] = value;
                v[INPUT_BITS + bit] = value;
            }
            let expected = direct_coefficients(
                &owner_retained[selected],
                &r[..ROW_BITS],
                &u[..INPUT_BITS],
                &v[..INPUT_BITS],
            );
            assert_eq!(
                plan.coefficients(&r, &u, &v).unwrap(),
                expected,
                "selected owner {selected}"
            );
        }
        let mut mixed_r = r.clone();
        let mut mixed_u = u.clone();
        let mut mixed_v = v.clone();
        mixed_r[ROW_BITS..].copy_from_slice(&boolean_point(2, 1));
        mixed_u[INPUT_BITS..].copy_from_slice(&boolean_point(2, 1));
        mixed_v[INPUT_BITS..].copy_from_slice(&boolean_point(2, 0));
        // Every old header gate, including constants, uses owner-local zero.
        // A GLOBAL0 localization mutant would leave the nonzero retired C0/C1.
        assert_eq!(
            plan.coefficients(&mixed_r, &mixed_u, &mixed_v).unwrap(),
            [Fr::zero(); 4]
        );
        assert!(!removed[0].is_zero() && !removed[1].is_zero());
    }

    #[test]
    fn n4_padding_and_n5_active_header_dummy_tree_masks_are_independent() {
        let root = [9; 32];
        let n4 = WorkTreeHistoryPlan::compile(4, 2, root, [0x44; 28]).unwrap();
        assert_eq!(n4.descriptor.genuine, 3);
        assert_eq!(n4.descriptor.leaves, 4);
        assert_eq!(n4.fixed_profile.role(3).unwrap(), fixed::Role::Profile);
        assert_eq!(n4.leaf_profile.role(3).unwrap(), leaf::Role::Padding);
        let mut padding = Vec::new();
        n4.leaf_boundary
            .emit_slot(3, |term| padding.push(term))
            .unwrap();
        assert!(!padding.is_empty());
        let mut active_header3 = 0usize;
        n4.boundary
            .visit_slot_terms(3, |_| {
                active_header3 += 1;
                Ok(())
            })
            .unwrap();
        assert!(active_header3 > 0);
        let mut padding_work = Vec::new();
        n4.work_boundary
            .emit_slot(3, |term| padding_work.push(term))
            .unwrap();
        assert!(!padding_work.is_empty());

        let n5 = WorkTreeHistoryPlan::compile(5, 3, root, [0x55; 28]).unwrap();
        assert_eq!(n5.descriptor.genuine, 4);
        assert_eq!(n5.descriptor.leaves, 4);
        assert_eq!(n5.descriptor.slots, 8);
        assert_eq!(n5.fixed_profile.role(3).unwrap(), fixed::Role::Profile);
        assert_eq!(n5.leaf_profile.role(3).unwrap(), leaf::Role::Genuine);
        assert_eq!(n5.fixed_profile.role(4).unwrap(), fixed::Role::Dummy);
        let mut dummy_tree = Vec::new();
        fixed::emit_slot(fixed::engine().unwrap(), &n5.fixed_profile, 4, |term| {
            dummy_tree.push(term)
        })
        .unwrap();
        assert!(
            !dummy_tree.is_empty(),
            "tree dummy owner must remain represented"
        );
        let mut owner4 = 0usize;
        let counts = n5
            .visit_slot_terms(4, |_| {
                owner4 += 1;
                Ok(())
            })
            .unwrap();
        assert_eq!(owner4, counts.emitted);
        assert_eq!(counts.omitted_worktree, RETIRED_TERMS);
        let mut original_owner4 = 0usize;
        n5.boundary
            .visit_slot_terms(4, |_| {
                original_owner4 += 1;
                Ok(())
            })
            .unwrap();
        assert_eq!(original_owner4, FULL_TERMS);
        let family = n5
            .topology
            .families
            .iter()
            .find(|family| family.name == "header_to_leaf_raw_length_nbits_height")
            .unwrap();
        assert!(matches!(
            family.mapping,
            topology::Mapping::HeaderSuccessor { lo: 1, hi: 5 }
        ));
        assert_eq!(family.left_wires.len(), 4_186);
        assert_eq!(family.right_wires.len(), 4_186);
        let mut selected = None;
        family
            .emit_terms(&n5.descriptor, |term| {
                if term.row / family.left_wires.len().next_power_of_two() == 4
                    && term.row % family.left_wires.len().next_power_of_two() == 0
                {
                    selected = Some(term);
                }
                Ok(())
            })
            .unwrap();
        let selected = selected.expect("header owner 4 successor term");
        assert_eq!(selected.gate.left / WIDTH, 4);
        assert_eq!(selected.gate.right / WIDTH, 3);
        assert_eq!(selected.gate.left % WIDTH, family.left_wires[0]);
        assert_eq!(selected.gate.right % WIDTH, family.right_wires[0]);

        let mut mutant = n5.topology.clone();
        mutant.families[0].mapping = topology::Mapping::HeaderSuccessor { lo: 0, hi: 5 };
        assert!(mutant.validate().is_err());
    }

    #[test]
    fn dimensions_bindings_and_transcript_fields_are_isolated() {
        assert!(validate_admission(0, 0).is_err());
        assert!(validate_admission(2, 1).is_err());
        assert!(validate_admission(3, 1).is_err());
        assert!(validate_admission(3, 22).is_err());
        assert!(validate_admission(3, 2).is_ok());
        assert!(validate_admission((1 << 21) + 1, 22).is_err());

        let a = n3_plan();
        let b = WorkTreeHistoryPlan::compile(3, 2, [8; 32], [0x35; 28]).unwrap();
        let c = WorkTreeHistoryPlan::compile(3, 2, [7; 32], [0x36; 28]).unwrap();
        let challenge = |binding: &StatementBinding| {
            let mut transcript = Transcript::new(b"history-plan-test");
            binding.append(&mut transcript);
            transcript
                .try_challenge_scalar(b"owner-separation")
                .unwrap()
        };
        let binding = StatementBinding {
            headers: a.headers,
            slot_log: a.slot_log,
            slots: a.descriptor.slots,
            leaves: a.descriptor.leaves,
            input_log: INPUT_BITS + a.slot_log,
            row_log: ROW_BITS + a.slot_log,
            root: a.root,
            total_be28: a.total_be28,
        };
        let baseline = challenge(&binding);
        let mut mutations = Vec::new();
        let mut changed = binding.clone();
        changed.headers += 1;
        mutations.push(changed);
        let mut changed = binding.clone();
        changed.slot_log += 1;
        mutations.push(changed);
        let mut changed = binding.clone();
        changed.slots += 1;
        mutations.push(changed);
        let mut changed = binding.clone();
        changed.leaves += 1;
        mutations.push(changed);
        let mut changed = binding.clone();
        changed.input_log += 1;
        mutations.push(changed);
        let mut changed = binding.clone();
        changed.row_log += 1;
        mutations.push(changed);
        for byte in 0..binding.root.len() {
            let mut changed = binding.clone();
            changed.root[byte] ^= 1;
            mutations.push(changed);
        }
        for byte in 0..binding.total_be28.len() {
            let mut changed = binding.clone();
            changed.total_be28[byte] ^= 1;
            mutations.push(changed);
        }
        for changed in mutations {
            assert_ne!(baseline, challenge(&changed));
        }
        assert_ne!(
            challenge(&binding),
            challenge(&StatementBinding {
                root: b.root,
                ..binding.clone()
            })
        );
        assert_ne!(
            challenge(&binding),
            challenge(&StatementBinding {
                total_be28: c.total_be28,
                ..binding
            })
        );
        let bound_plan = |plan: &WorkTreeHistoryPlan| {
            let mut transcript = Transcript::new(b"history-plan-production-binding-test");
            plan.bind(&mut transcript);
            transcript.try_challenge_scalar(b"bound-plan").unwrap()
        };
        assert_ne!(bound_plan(a), bound_plan(&b));
        assert_ne!(bound_plan(a), bound_plan(&c));
    }

    #[test]
    fn invalid_owner_and_sink_failure_are_fail_closed() {
        let plan = n3_plan();
        for invalid in [4, u64::MAX] {
            let calls = std::cell::Cell::new(0usize);
            assert!(plan
                .visit_slot_terms(invalid, |_| {
                    calls.set(calls.get() + 1);
                    Ok(())
                })
                .is_err());
            assert_eq!(calls.get(), 0);
        }
        let calls = std::cell::Cell::new(0usize);
        let error = plan
            .visit_slot_terms(0, |_| {
                calls.set(calls.get() + 1);
                Err("stop-at-first-sink-error".to_owned())
            })
            .unwrap_err();
        assert_eq!(error, "stop-at-first-sink-error");
        assert_eq!(calls.get(), 1);
    }

    #[test]
    fn source_rows_endpoint_maps_and_contract_counts_reject_single_mutants() {
        let plan = n3_plan();
        let base = fixed::engine().unwrap().base;
        let canonical = plan.boundary.canonical_circuit();

        let mut missing = canonical.clone();
        let remove = missing
            .terms
            .iter()
            .position(|term| term.row == DUMMY_COUNTER_START_ROW + 5)
            .unwrap();
        missing.terms[remove] = canonical.terms[0].clone();
        assert_eq!(missing.terms.len(), FULL_TERMS);
        assert!(build_retirement(&missing, base)
            .unwrap_err()
            .contains("old zero-anchor identity"));

        let mut weighted_counter = canonical.clone();
        let changed = weighted_counter
            .terms
            .iter_mut()
            .find(|term| term.row == DUMMY_COUNTER_START_ROW + 5)
            .unwrap();
        changed.gate.c1 += Fr::one();
        assert!(build_retirement(&weighted_counter, base)
            .unwrap_err()
            .contains("old zero-anchor identity"));

        let mut extra_same_row = canonical.clone();
        extra_same_row.terms[0] = Term {
            row: DUMMY_FLAG_START_ROW + 5,
            gate: gkr::Gate {
                left: 1,
                right: 0,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        };
        assert_eq!(extra_same_row.terms.len(), FULL_TERMS);
        assert!(build_retirement(&extra_same_row, base)
            .unwrap_err()
            .contains("source row contains"));

        let mut duplicate = canonical.clone();
        duplicate.terms[0] = canonical.terms[remove].clone();
        assert_eq!(duplicate.terms.len(), FULL_TERMS);
        assert!(build_retirement(&duplicate, base)
            .unwrap_err()
            .contains("old zero-anchor identity"));

        let mut shifted_row = canonical.clone();
        let shifted = shifted_row
            .terms
            .iter_mut()
            .find(|term| term.row == DUMMY_FLAG_START_ROW + 5 && term.gate.left == 0)
            .unwrap();
        shifted.row += 1;
        assert!(build_retirement(&shifted_row, base)
            .unwrap_err()
            .contains("old zero-anchor identity"));

        let mut wrong_flag = canonical.clone();
        let flag = wrong_flag
            .terms
            .iter_mut()
            .find(|term| term.row == DUMMY_FLAG_START_ROW + 5 && term.gate.left == 0)
            .unwrap();
        flag.gate.c0 = Fr::zero();
        assert!(build_retirement(&wrong_flag, base)
            .unwrap_err()
            .contains("old zero-anchor identity"));

        validate_retired_protection(&plan.retired.terms).unwrap();
        for row in [346_866, 346_898, 346_930] {
            let protected = canonical.terms.iter().find(|term| term.row == row).unwrap();
            let mut release_mutant = plan.retired.terms.clone();
            release_mutant[0] = protected.clone();
            assert_eq!(release_mutant.len(), RETIRED_TERMS);
            assert_eq!(
                validate_retired_protection(&release_mutant).unwrap_err(),
                "retirement crosses protected or retained source"
            );
        }

        for mutate in [0usize, 1, 2, 3, 4] {
            let mut endpoints = Endpoints::new();
            match mutate {
                0 => endpoints.raw[0] += 1,
                1 => endpoints.leaf[0] += 1,
                2 => endpoints.node_left[0] += 1,
                3 => endpoints.count[0] += 1,
                _ => endpoints.level[0] += 1,
            }
            assert!(
                validate_endpoint_map(&endpoints).is_err(),
                "field mutation {mutate}"
            );
        }

        let expected = plan.topology.families.clone();
        validate_topology_families(&plan.descriptor, base, plan.root, &expected).unwrap();
        for (name, mutate) in [
            ("node_profile_output_core_alias", 0usize),
            ("node_message_child_0", 1),
            ("public_root", 2),
            ("profile_slot_unused_child_endpoints", 3),
            ("padding_leaf_unused_header_aliases", 4),
            ("level_1_child_0", 5),
        ] {
            let mut families = expected.clone();
            let family = families
                .iter_mut()
                .find(|family| family.name == name)
                .unwrap();
            match mutate {
                0 => family.right_wires[0] ^= 1,
                1 => family.left_wires[0] ^= 1,
                2 => family.constants.as_mut().unwrap()[0] ^= 1,
                3 => family.left_wires[0] ^= 1,
                4 => {
                    family.mapping = topology::Mapping::FixedRight {
                        lo: 0,
                        hi: 2,
                        target: 0,
                    }
                }
                _ => {
                    family.mapping = topology::Mapping::Child {
                        level: 2,
                        branch: 0,
                    }
                }
            }
            assert!(
                validate_topology_families(&plan.descriptor, base, plan.root, &families,).is_err(),
                "family mutation {name}"
            );
        }

        let mut bad_count = plan.retirement_counts;
        bad_count.rows += 1;
        assert!(validate_retirement_counts(bad_count).is_err());
    }

    #[test]
    fn actual_family_role_and_zero_localization_mutants_are_isolated() {
        let base = fixed::engine().unwrap().base;
        for n in [4usize, 5] {
            let topology = Topology::new(base, n, [0x27; 32]).unwrap();
            let d = &topology.descriptor;
            let expected = expected_topology_families(d, base, d.root).unwrap();
            assert_eq!(expected[0].left_wires.len(), 4_186);
            assert_eq!(expected[0].right_wires.len(), 4_186);
            assert_eq!(expected[0].right_wires, base.endpoints.header_aliases());
            assert_ne!(expected[0].right_wires, base.endpoints.leaf);
            validate_topology_families(d, base, d.root, &topology.families).unwrap();
            for name in [
                "padding_leaf_unused_header_aliases",
                "inactive_tree_endpoints",
                "header_to_leaf_raw_length_nbits_height",
                "profile_digest_fanout",
                "profile_slot_unused_child_endpoints",
                "public_root",
            ] {
                let mut families = topology.families.clone();
                let family = families
                    .iter_mut()
                    .find(|family| family.name == name)
                    .unwrap();
                family.mapping = match name {
                    "padding_leaf_unused_header_aliases" => topology::Mapping::FixedRight {
                        lo: d.leaves,
                        hi: d.slots,
                        target: 0,
                    },
                    "inactive_tree_endpoints" => topology::Mapping::FixedRight {
                        lo: d.genuine,
                        hi: d.leaves,
                        target: 0,
                    },
                    "header_to_leaf_raw_length_nbits_height" => {
                        topology::Mapping::Same { lo: 1, hi: n }
                    }
                    "profile_digest_fanout" => topology::Mapping::FixedRight {
                        lo: 0,
                        hi: d.leaves,
                        target: 0,
                    },
                    "profile_slot_unused_child_endpoints" => topology::Mapping::FixedRight {
                        lo: 0,
                        hi: 1,
                        target: 0,
                    },
                    _ => topology::Mapping::FixedRight {
                        lo: d.root_node_slot,
                        hi: d.root_node_slot + 1,
                        target: 1,
                    },
                };
                assert_eq!(
                    validate_topology_families(d, base, d.root, &families).unwrap_err(),
                    "topology mappings, aliases, constants, or role wires changed",
                    "isolated semantic role mutant N={n} {name}"
                );
            }
        }
    }

    #[test]
    fn h21_is_symbolic_and_preserves_separate_a4_accounting() {
        let n = 1u64 << 21;
        let plan = WorkTreeHistoryPlan::compile(n, 21, [0x21; 32], [0x21; 28]).unwrap();
        assert_eq!(plan.slots(), 1 << 21);
        assert_eq!(plan.core_pool.input_log(), 41);
        assert_eq!(plan.core_pool.row_log(), 42);
        for (owner, expected_a4) in [
            (9_215u64, 0usize),
            (9_216, A4_TERMS),
            (844_672, A4_TERMS),
            (844_673, 0),
        ] {
            let mut ser_rows = 0usize;
            let mut protected_rows = 0usize;
            let mut a4_rows = 0usize;
            let result = plan
                .visit_slot_terms(owner, |term| {
                    let local_row = term.row % ROW_COUNT;
                    if SERIALIZER_ROWS.contains(&local_row) {
                        ser_rows += 1;
                    }
                    if (346_866..346_938).contains(&local_row) {
                        protected_rows += 1;
                    }
                    if A4_ROWS.contains(&local_row) {
                        a4_rows += 1;
                    }
                    Ok(())
                })
                .unwrap();
            let counts = result;
            assert_eq!(counts.omitted_worktree, RETIRED_TERMS);
            assert_eq!(counts.omitted_a4, expected_a4, "owner {owner}");
            assert_eq!(
                counts.emitted + counts.omitted_worktree + counts.omitted_a4,
                FULL_TERMS
            );
            assert_eq!(
                ser_rows, SERIALIZER_TERMS,
                "serializer overlay owner {owner}"
            );
            assert_eq!(
                protected_rows, PROTECTED_ENDPOINTS,
                "protected endpoint owner {owner}"
            );
            assert_eq!(a4_rows, A4_TERMS - expected_a4, "A4 owner {owner}");
        }

        let last_owner = (1u64 << 21) - 1;
        let mut selected = None;
        plan.visit_slot_terms(last_owner, |term| {
            selected.get_or_insert(term);
            Ok(())
        })
        .unwrap();
        let selected = selected.expect("maximum owner retains a first source term");
        let r = boolean_point(ROW_BITS + 21, selected.row);
        let u = boolean_point(INPUT_BITS + 21, selected.gate.left);
        let v = boolean_point(INPUT_BITS + 21, selected.gate.right);
        let actual = plan.coefficients(&r, &u, &v).unwrap();

        // Independent direct filter scans the pinned local source and applies
        // exact LSB-first owner/row/wire equalities at the selected max owner.
        let reference = reference_retirement(fixed::engine().unwrap().base);
        let mut expected = [Fr::zero(); 4];
        plan.boundary
            .visit_slot_terms(last_owner, |term| {
                let local = normalize_owner(&term, last_owner as usize);
                if !reference.contains(&key(&local))
                    && term.row == selected.row
                    && term.gate.left == selected.gate.left
                    && term.gate.right == selected.gate.right
                {
                    for (sum, coefficient) in expected.iter_mut().zip([
                        term.gate.c0,
                        term.gate.c1,
                        term.gate.c2,
                        term.gate.c3,
                    ]) {
                        *sum += coefficient;
                    }
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(actual, expected);
        assert!(actual.iter().any(|value| !value.is_zero()));

        let padded_n = (1u64 << 21) - 1;
        let descriptor = Descriptor::new(padded_n as usize, [0x22; 32]).unwrap();
        let fixed_profile = FixedProfile::new(padded_n as usize, [0x22; 32]).unwrap();
        let leaf_profile = LeafProfile::new(padded_n as usize, [0x22; 32]).unwrap();
        let first_padding_leaf = descriptor.genuine;
        let last_leaf = descriptor.leaves - 1;
        assert_eq!(first_padding_leaf, padded_n as usize - 1);
        assert_eq!(last_leaf - first_padding_leaf + 1, 2);
        assert_eq!(
            fixed_profile.role(first_padding_leaf).unwrap(),
            fixed::Role::Node {
                level: descriptor.leaves.trailing_zeros() as u8,
                position: 0,
            }
        );
        assert_eq!(
            leaf_profile.role(first_padding_leaf).unwrap(),
            leaf::Role::Padding
        );
        assert_eq!(fixed_profile.role(last_leaf).unwrap(), fixed::Role::Profile);
        assert_eq!(leaf_profile.role(last_leaf).unwrap(), leaf::Role::Padding);
    }
}

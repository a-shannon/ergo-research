//! Direct tests for the bounded two-owner native history assembly.
use crate::{
    daa_history_producer::PACKED_OWNER_BYTES,
    header_hash::SERIALIZER_OFFSET,
    header_order::MAINNET_GENESIS,
    packed_owner_assembly::{
        assemble_m1_window, assemble_m1_window_fault_for_test, assemble_window,
        assemble_window_fault_for_test, external_support_for_test, flip_native_row_bit_for_test,
        foreign_census_for_test, m2_nonlocal_edge_geometry, validate_native_plan_input,
        validate_native_row_for_test,
        validate_native_row_for_history_test, visit_m2_nonlocal_edge_endpoint, AssemblyFault,
        NativeOwnerProducer, NativePrefix,
        MAX_EXTERNAL_CELLS, MAX_M1_EXTERNAL_CELLS,
    },
    serializer::{self, Fields},
    sparse_stream_roster::{self, EdgeTerm},
    work_tree_fixed_hash::{self, Role as FixedRole},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self, WIDTH},
    work_tree_wiring::Descriptor,
    work_tree_work,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{digest::consts::U32, Blake2b, Digest};
use ergo_header_core::Header;
use num_bigint::BigUint;
use serde_json::Value;
use std::{
    collections::{BTreeMap, HashSet},
    fs::{self, File, OpenOptions},
    io::{BufReader, Read, Seek, SeekFrom, Write},
    path::PathBuf,
    sync::OnceLock,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

#[path = "candidate146_w_loan_tests.rs"]
mod candidate146_w_loan_tests;
use std::os::windows::fs::OpenOptionsExt;

const BUNDLE_BYTES: usize = 869_449;
const BUNDLE_BLAKE2B256: &str = "8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
const OWNER_ASSEMBLY_INPUT_ENV: &str = "NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR";
const OWNER_ASSEMBLY_ARTIFACT_ENV: &str = "NIPOPOW_OWNER_ASSEMBLY_ARTIFACT_DIR";
const NATIVE_HISTORY_RAW_ENV: &str = "NIPOPOW_NATIVE_HISTORY_RAW_FILE";
const NATIVE_HISTORY_N_ENV: &str = "NIPOPOW_NATIVE_HISTORY_EXPECTED_N";
const NATIVE_HISTORY_SIZE_ENV: &str = "NIPOPOW_NATIVE_HISTORY_EXPECTED_SIZE";
const NATIVE_HISTORY_BLAKE_ENV: &str = "NIPOPOW_NATIVE_HISTORY_EXPECTED_BLAKE2B256";
const NATIVE_HISTORY_OUTPUT_ENV: &str = "NIPOPOW_NATIVE_HISTORY_OUTPUT_JSON";
const NATIVE_HISTORY_FAULT_DIR_ENV: &str = "NIPOPOW_NATIVE_HISTORY_FAULT_DIR";

#[test]
fn native_owner_source_covers_all_admitted_classes_and_matches_preserved_rows() {
    use crate::daa_history_roster::OwnerClass;
    let input = prefix();
    let plan = assembly_plan();
    let producer = NativeOwnerProducer::new(plan, input).unwrap();
    let exports = crate::native_owner_exports::NativeExports::new(plan, input).unwrap();
    let e = &work_tree_layout::shared_baseline().unwrap().endpoints;
    let mut exported_wires = Vec::new();
    for ports in [
        &e.raw,
        &e.length,
        &e.n_bits,
        &e.height,
        &e.lower,
        &e.upper,
        &e.work,
        &e.exponent,
        &e.work_minus_one,
        &e.leaf,
        &e.node_left,
        &e.node_right,
        &e.node,
        &e.profile,
    ] {
        exported_wires.extend(ports.iter().copied());
    }
    let baseline_m1 = fs::read(
        std::env::var_os("NIPOPOW_NATIVE_OWNER_BASELINE_M1").expect("M1 preserved packed baseline"),
    )
    .unwrap();
    let baseline_m2 = fs::read(
        std::env::var_os("NIPOPOW_NATIVE_OWNER_BASELINE_M2").expect("M2 preserved packed baseline"),
    )
    .unwrap();
    assert_eq!(baseline_m1.len(), 2 * PACKED_OWNER_BYTES);
    assert_eq!(baseline_m2.len(), 2 * PACKED_OWNER_BYTES);
    let expected = [
        (0, OwnerClass::Genesis),
        (1, OwnerClass::Initial),
        (2, OwnerClass::Carry),
        (1024, OwnerClass::Singleton),
        (2048, OwnerClass::M1),
        (
            3072,
            OwnerClass::Short(crate::short_daa_layout::Profile::M2),
        ),
        (3073, OwnerClass::Padding),
        (4095, OwnerClass::Padding),
    ];
    let output = PathBuf::from(
        std::env::var_os(OWNER_ASSEMBLY_ARTIFACT_ENV).expect("fresh native row output"),
    );
    assert!(!output.exists(), "outputs must be new");
    fs::create_dir_all(&output).unwrap();
    let mut report = Vec::new();
    for (owner, class) in expected {
        let row = producer.produce(owner).unwrap();
        let legacy = producer.produce_legacy_header_for_test(owner).unwrap();
        assert_eq!(row.owner(), legacy.owner());
        assert_eq!(row.class(), legacy.class());
        assert_eq!(row.packed_bytes(), legacy.packed_bytes(), "owner{owner} full legacy header differential");
        assert_eq!(row.owner(), owner);
        assert_eq!(row.class(), class);
        assert_eq!(row.packed_bytes().len(), PACKED_OWNER_BYTES);
        // Differential all scalar endpoint exports against actual produced
        // packed bytes, not merely another scalar oracle.
        for &wire in &exported_wires {
            assert_eq!(
                exports.bit(owner * WIDTH + wire).unwrap(),
                byte_bit(row.packed_bytes(), wire),
                "owner{owner} endpoint{wire}"
            );
        }
        let receipt =
            validate_native_row_for_test(plan, input, &row, |wire| exports.bit(wire)).unwrap();
        assert_eq!(receipt.groups.len(), 5);
        assert!(receipt.external_cells <= receipt.foreign_census);
        let numeric = if owner == 1 {
            225
        } else if owner == 2 || owner == 1024 {
            448
        } else {
            0
        };
        let roster = crate::daa_history_roster::DaaHistoryRoster::compile(plan).unwrap();
        assert_eq!(
            roster
                .visit_owner_terms(owner as u64, |_| Ok(()))
                .unwrap()
                .lanes[2],
            numeric
        );
        if owner == 2048 {
            assert_eq!(row.packed_bytes(), &baseline_m1[PACKED_OWNER_BYTES..]);
        }
        if owner == 3072 {
            assert_eq!(row.packed_bytes(), &baseline_m2[PACKED_OWNER_BYTES..]);
        }
        let serializer_owner = (owner + 1).min(3073);
        let fields = Fields::from_header(&input.header(serializer_owner).unwrap()).unwrap();
        let canonical = serializer().assign(&fields);
        for &wire in serializer()
            .layout
            .bytes
            .iter()
            .flatten()
            .chain(&serializer().layout.length)
            .chain(&serializer().layout.fields.timestamp)
            .chain(&serializer().layout.fields.n_bits)
            .chain(&serializer().layout.fields.height)
        {
            let expected_bit = canonical[wire].is_one();
            assert_eq!(
                exports
                    .bit(owner * WIDTH + SERIALIZER_OFFSET + wire)
                    .unwrap(),
                expected_bit
            );
            assert_eq!(
                byte_bit(row.packed_bytes(), SERIALIZER_OFFSET + wire),
                expected_bit
            );
        }
        let path = output.join(format!("owner-{owner}.bits"));
        fs::write(&path, row.packed_bytes()).unwrap();
        assert_eq!(fs::read(&path).unwrap(), row.packed_bytes());
        report.push(serde_json::json!({"owner":owner,"class":format!("{class:?}"),"bytes":row.packed_bytes().len(),"local_groups":receipt.groups,"external_cells":receipt.external_cells,"foreign_census":receipt.foreign_census,"numeric_terms":numeric}));
    }
    // Exhaustive code-owned classification and descriptor role census is cheap;
    // it is not a computation or verification of all 4096 row assignments.
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(plan).unwrap();
    let mut census = BTreeMap::<String, usize>::new();
    for owner in 0..4096 {
        *census
            .entry(format!("{:?}", roster.owner_class(owner as u64).unwrap()))
            .or_default() += 1;
        let _ = plan.leaf_profile().role(owner).unwrap();
        let _ = plan.fixed_profile().role(owner).unwrap();
    }
    assert_eq!(census.get("Carry"), Some(&3068));
    assert_eq!(census.get("Padding"), Some(&1023));
    assert_eq!(census.len(), 7);
    let result = serde_json::json!({"headers":3073,"slots":4096,"produced_rows":8,"legacy_header_rows_compared":8,"cores_checked":88,"owner_local_families_checked":40,"census":census,"rows":report,"global_incident_edges_checked":false,"global_proof":false});
    fs::write(
        output.join("native-owner-result.json"),
        serde_json::to_vec_pretty(&result).unwrap(),
    )
    .unwrap();
    println!("{result}");
}

#[test]
fn native_owner_source_rejects_wrong_binding_missing_conflict_and_numeric_mutants() {
    let input = prefix();
    let plan = assembly_plan();
    let producer = NativeOwnerProducer::new(plan, input).unwrap();
    let exports = crate::native_owner_exports::NativeExports::new(plan, input).unwrap();
    assert!(producer.produce(4096).is_err());
    let mut root = input.root();
    root[0] ^= 1;
    let wrong_root = compile_plan(3073, root, input.total_be28());
    assert_eq!(
        expect_error(NativeOwnerProducer::new(&wrong_root, input)),
        "native owner source root/total mismatch"
    );
    let mut total = input.total_be28();
    total[27] ^= 1;
    let wrong_total = compile_plan(3073, input.root(), total);
    assert_eq!(
        expect_error(NativeOwnerProducer::new(&wrong_total, input)),
        "native owner source root/total mismatch"
    );
    let wrong_shape = compile_plan(3072, input.root(), input.total_be28());
    assert!(NativeOwnerProducer::new(&wrong_shape, input).is_err());
    for (fault, expected) in [
        (
            AssemblyFault::MissingClaim { owner: 0, wire: 0 },
            "missing claim",
        ),
        (
            AssemblyFault::ConflictingClaim { owner: 0, wire: 0 },
            "claim conflict",
        ),
        (
            AssemblyFault::NonBooleanClaim { owner: 0, wire: 0 },
            "non-Boolean",
        ),
    ] {
        assert!(expect_error(producer.produce_fault_for_test(0, fault)).contains(expected));
    }
    let endpoints = &work_tree_layout::shared_baseline().unwrap().endpoints;
    assert_eq!(
        expect_error(exports.bit(4096 * WIDTH)),
        format!("native export coordinate outside N3073: {}", 4096 * WIDTH)
    );
    assert!(exports.bit(2 * WIDTH + 1).is_err());
    assert!(exports.bit(2 * WIDTH + endpoints.count[0]).is_err());
    for (owner, source_owner) in [(1, 0), (1024, 1023)] {
        let row = producer.produce(owner).unwrap();
        if owner == 1 {
            let mut callback_calls = 0;
            let error = validate_native_row_for_test(&wrong_shape, input, &row, |_| {
                callback_calls += 1;
                Ok(false)
            })
            .unwrap_err();
            assert!(error.contains("requires N3073/S12"));
            assert_eq!(callback_calls, 0);
        }
        let fault = source_owner * WIDTH + endpoints.work[0];
        let mut seen = false;
        let error = validate_native_row_for_test(plan, input, &row, |wire| {
            let value = exports.bit(wire)?;
            if wire == fault {
                seen = true;
                Ok(!value)
            } else {
                Ok(value)
            }
        })
        .unwrap_err();
        assert!(seen);
        assert!(error.contains("DAA/"), "{error}");
    }
    let mut padding = producer.produce(3073).unwrap();
    // Current-height is an actual Header alias to the native serializer.
    // Previous-height belongs to the separate MetadataOrder relation, which
    // applies only to active history owners and is not checked by this lot.
    let current_height_bit = crate::header_order::ORDER_OFFSET + 256;
    flip_native_row_bit_for_test(&mut padding, current_height_bit).unwrap();
    assert!(
        validate_native_row_for_test(plan, input, &padding, |wire| exports.bit(wire))
            .unwrap_err()
            .contains("Header/")
    );
    let mut profile = producer.produce(4095).unwrap();
    flip_native_row_bit_for_test(&mut profile, endpoints.node_left[0]).unwrap();
    // Profile child-zero is a topology obligation: the local-only validator
    // must not be represented as proving that global relation.
    let family = plan
        .topology()
        .families
        .iter()
        .find(|f| f.name == "profile_slot_unused_child_endpoints")
        .unwrap();
    let mut residual = Fr::zero();
    let mut selected_terms = 0;
    family
        .emit_endpoint_terms(plan.descriptor(), true, 4095, |_, _, t| {
            if t.gate.left == 4095 * WIDTH + endpoints.node_left[0] {
                selected_terms += 1;
                residual += t.gate.c1
                    * Fr::from(byte_bit(profile.packed_bytes(), endpoints.node_left[0]) as u64);
            }
            Ok(())
        })
        .unwrap();
    assert_eq!(selected_terms, 1);
    assert!(!residual.is_zero());
}

fn fixture_dir() -> PathBuf {
    PathBuf::from(std::env::var_os(OWNER_ASSEMBLY_INPUT_ENV).expect(
        "NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR must name the frozen input-candidate-1 directory",
    ))
}

fn decode_hex(text: &str) -> Vec<u8> {
    assert_eq!(text.len() % 2, 0);
    text.as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

fn read_prefix_raws() -> Vec<Vec<u8>> {
    let directory = fixture_dir();
    let manifest_bytes = fs::read(directory.join("manifest.json")).expect("read prefix manifest");
    let manifest: Value = serde_json::from_slice(&manifest_bytes).expect("parse prefix manifest");
    assert_eq!(manifest["schema"], "mainnet-prefix-raw-bundle-v1");
    assert_eq!(
        manifest["sourceFrameSha256"],
        "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E"
    );
    assert_eq!(manifest["extractedRecords"], 3073);
    assert_eq!(manifest["bundleBytes"], BUNDLE_BYTES);
    assert_eq!(
        manifest["bundleSha256"],
        "ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2"
    );

    let bundle = fs::read(directory.join("mainnet-prefix-first-3073-u32le-v1.bin"))
        .expect("read frozen prefix bundle");
    assert_eq!(bundle.len(), BUNDLE_BYTES);
    let digest = Blake2b::<U32>::digest(&bundle);
    assert_eq!(hex_upper(&digest), BUNDLE_BLAKE2B256);

    let mut offset = 0usize;
    let mut raws = Vec::with_capacity(3073);
    let mut previous_raw: Option<Vec<u8>> = None;
    for height in 1..=3073u32 {
        let length_end = offset.checked_add(4).expect("length offset");
        let length_bytes: [u8; 4] = bundle
            .get(offset..length_end)
            .expect("prefix record length")
            .try_into()
            .unwrap();
        let length = u32::from_le_bytes(length_bytes) as usize;
        offset = length_end;
        assert!(
            (1..=514).contains(&length),
            "bounded RAW length at {height}"
        );
        let end = offset.checked_add(length).expect("RAW end");
        let raw = bundle
            .get(offset..end)
            .expect("complete prefix RAW")
            .to_vec();
        offset = end;

        let header = Header::decode(&raw, None)
            .unwrap_or_else(|error| panic!("decode height {height}: {error:?}"));
        assert_eq!(header.height, height);
        assert_eq!(
            header.encode().unwrap(),
            raw,
            "canonical RAW at height {height}"
        );
        let id = ergo_header_core::blake2b256(&raw);
        if height == 1 {
            assert_eq!(header.parent_id, [0; 32]);
            assert_eq!(id, MAINNET_GENESIS);
        } else {
            let parent = previous_raw.as_ref().expect("previous linked RAW");
            assert_eq!(
                header.parent_id,
                ergo_header_core::blake2b256(parent),
                "parent at height {height}"
            );
        }
        previous_raw = Some(raw.clone());
        raws.push(raw);
    }
    assert_eq!(offset, bundle.len(), "no trailing bundle bytes");

    let windows: Value =
        serde_json::from_str(include_str!("../fixtures/mainnet-daa-windows-v1.json")).unwrap();
    let raw_3072 = windows["headers"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["height"] == 3072)
        .expect("pinned 3072 window header");
    assert_eq!(
        raws[3071],
        decode_hex(raw_3072["raw_hex"].as_str().unwrap())
    );
    let child: Value =
        serde_json::from_str(include_str!("../fixtures/mainnet-daa-child-3073-v1.json")).unwrap();
    assert_eq!(raws[3072], decode_hex(child["raw_hex"].as_str().unwrap()));
    assert_eq!(
        hex_upper(&Blake2b::<U32>::digest(&raws[3072])),
        "CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC",
    );
    raws
}

fn hex_upper(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn canonical_edge_bytes(
    edge: &EdgeTerm,
    slot_bits: usize,
    base_row_bits: usize,
    family_bits: usize,
    member_row_bits: &[usize],
) -> Vec<u8> {
    let global = sparse_stream_roster::global_edge_row(
        edge.source_slot,
        edge.family_row,
        slot_bits,
        base_row_bits,
        family_bits,
        member_row_bits,
    )
    .unwrap();
    let mut bytes = Vec::with_capacity(8 * 5 + 4 * 32);
    for value in [
        global,
        edge.source_slot,
        edge.family_row,
        edge.term.row,
        edge.term.gate.left,
        edge.term.gate.right,
    ] {
        bytes.extend_from_slice(&(value as u64).to_le_bytes());
    }
    for coefficient in [
        edge.term.gate.c0,
        edge.term.gate.c1,
        edge.term.gate.c2,
        edge.term.gate.c3,
    ] {
        coefficient.serialize_compressed(&mut bytes).unwrap();
    }
    bytes
}

fn edge_digest(mut entries: Vec<Vec<u8>>) -> String {
    entries.sort_unstable();
    let mut digest = Blake2b::<U32>::new();
    digest.update((entries.len() as u64).to_le_bytes());
    for entry in entries {
        digest.update((entry.len() as u64).to_le_bytes());
        digest.update(entry);
    }
    hex_upper(&digest.finalize())
}

fn prefix() -> &'static NativePrefix {
    static PREFIX: OnceLock<NativePrefix> = OnceLock::new();
    PREFIX.get_or_init(|| NativePrefix::from_raw_headers(&read_prefix_raws()).unwrap())
}

fn assembly_plan() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| compile_plan(3073, prefix().root(), prefix().total_be28()))
}

// The caller must replay its scalar cap gate between these two fixture calls.
pub(crate) fn legacy_prefix_for_test() -> &'static NativePrefix { prefix() }
pub(crate) fn legacy_assembly_plan_for_test() -> &'static WorkTreeHistoryPlan { assembly_plan() }

pub(crate) fn legacy_cache_errors_for_test(
    producer: &NativeOwnerProducer<'_>, plan: &WorkTreeHistoryPlan,
) -> Result<(String, String), String> {
    let mut cache = NativePackedRowCache::new(producer, plan);
    // Deliberately invalid cached bytes prove mode checks precede both fast paths.
    cache.rows.insert(0, vec![0]);
    let ensure = cache.ensure_owner(0).err().ok_or("adapted cached owner was accepted")?;
    let read = cache.bit(0).err().ok_or("adapted cached bit was accepted")?;
    Ok((ensure, read))
}

struct ForeignProvider {
    serializers: [(u64, Vec<Fr>); 3],
    serializer_used: HashSet<usize>,
    descriptor: Descriptor,
    fixed_profile: work_tree_fixed_hash::FixedProfile,
}

impl ForeignProvider {
    fn new(input: &NativePrefix) -> Self {
        let compiled = serializer();
        let mut serializer_used = HashSet::new();
        for term in &compiled.circuit.terms {
            serializer_used.insert(term.gate.left);
            serializer_used.insert(term.gate.right);
        }
        let make = |height: usize| {
            let fields = Fields::from_header(&input.header(height).unwrap()).unwrap();
            let values = compiled.assign(&fields);
            assert!(values.iter().all(|value| value.is_zero() || value.is_one()));
            ((height - 1) as u64, values)
        };
        Self {
            serializers: [make(1024), make(2048), make(2050)],
            serializer_used,
            descriptor: Descriptor::new(3073, input.root()).unwrap(),
            fixed_profile: work_tree_fixed_hash::FixedProfile::new(3073, input.root()).unwrap(),
        }
    }

    fn bit(&self, global_wire: usize, input: &NativePrefix) -> Result<bool, String> {
        if global_wire == 0 {
            return Ok(false);
        }
        let owner = global_wire / WIDTH;
        let local = global_wire % WIDTH;
        let serializer_end = SERIALIZER_OFFSET + serializer().circuit.input_len;
        if (SERIALIZER_OFFSET..serializer_end).contains(&local) {
            let serializer_wire = local - SERIALIZER_OFFSET;
            if !self.serializer_used.contains(&serializer_wire) {
                return Err(format!("unsupported serializer input {global_wire}"));
            }
            let (_, values) = self
                .serializers
                .iter()
                .find(|(sample_owner, _)| *sample_owner == owner as u64)
                .ok_or_else(|| format!("serializer owner {owner} is not a pinned M2 sample"))?;
            return values
                .get(serializer_wire)
                .map(|value| value.is_one())
                .ok_or_else(|| format!("serializer wire {global_wire} outside assignment"));
        }
        if (work_tree_layout::ENDPOINT_BASE
            ..work_tree_layout::ENDPOINT_BASE + work_tree_layout::ENDPOINT_WIDTH)
            .contains(&local)
        {
            return endpoint_bit(input, &self.descriptor, &self.fixed_profile, owner, local)?
                .ok_or_else(|| format!("unsupported typed endpoint {global_wire}"));
        }
        Err(format!("unsupported foreign coordinate {global_wire}"))
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ProducerNamespace {
    Serializer,
    WorkEndpoint,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProducerKey {
    owner: usize,
    namespace: ProducerNamespace,
    local: usize,
    producer: usize,
}

#[derive(Clone)]
struct M2ProducerRegistry {
    values: BTreeMap<ProducerKey, bool>,
    identities: BTreeMap<(usize, ProducerNamespace, usize), usize>,
    support: std::collections::BTreeSet<usize>,
}

impl M2ProducerRegistry {
    fn classify(local: usize) -> Result<(ProducerNamespace, usize), String> {
        let serializer_end = SERIALIZER_OFFSET + serializer().circuit.input_len;
        if (SERIALIZER_OFFSET..serializer_end).contains(&local) {
            let producer = local - SERIALIZER_OFFSET;
            if !serializer()
                .circuit
                .terms
                .iter()
                .any(|term| term.gate.left == producer || term.gate.right == producer)
            {
                return Err(format!("unsupported serializer producer {local}"));
            }
            return Ok((ProducerNamespace::Serializer, producer));
        }
        let endpoint_end = work_tree_layout::ENDPOINT_BASE + work_tree_layout::ENDPOINT_WIDTH;
        if (work_tree_layout::ENDPOINT_BASE..endpoint_end).contains(&local) {
            return Ok((
                ProducerNamespace::WorkEndpoint,
                local - work_tree_layout::ENDPOINT_BASE,
            ));
        }
        Err(format!("unsupported foreign namespace {local}"))
    }

    fn from_support(
        input: &NativePrefix,
        support: &std::collections::BTreeSet<usize>,
    ) -> Result<Self, String> {
        let mut registry = Self {
            values: BTreeMap::new(),
            identities: BTreeMap::new(),
            support: support.clone(),
        };
        let provider = foreign_provider();
        for &wire in support {
            let owner = wire / WIDTH;
            let local = wire % WIDTH;
            let (namespace, producer) = Self::classify(local)?;
            let value = provider.bit(wire, input)?;
            registry.register(
                ProducerKey {
                    owner,
                    namespace,
                    local,
                    producer,
                },
                value,
            )?;
        }
        registry.preflight(support)?;
        Ok(registry)
    }

    fn register(&mut self, key: ProducerKey, value: bool) -> Result<(), String> {
        let coordinate = (key.owner, key.namespace, key.local);
        if let Some(previous) = self.identities.get(&coordinate) {
            if *previous != key.producer {
                return Err(format!(
                    "producer identity conflict owner{} local{}",
                    key.owner, key.local
                ));
            }
        }
        if let Some(previous) = self.values.get(&key) {
            if *previous != value {
                return Err(format!(
                    "producer value conflict owner{} local{}",
                    key.owner, key.local
                ));
            }
            return Ok(());
        }
        self.identities.insert(coordinate, key.producer);
        self.values.insert(key, value);
        Ok(())
    }

    fn key_for(&self, wire: usize) -> Result<ProducerKey, String> {
        let owner = wire / WIDTH;
        let local = wire % WIDTH;
        let (namespace, producer) = Self::classify(local)?;
        Ok(ProducerKey {
            owner,
            namespace,
            local,
            producer,
        })
    }

    fn read(&self, wire: usize) -> Result<bool, String> {
        if wire >= 4096 * WIDTH {
            return Err(format!("foreign coordinate outside N3073 {wire}"));
        }
        let key = self.key_for(wire)?;
        self.values
            .get(&key)
            .copied()
            .ok_or_else(|| format!("missing producer for foreign wire {wire}"))
    }

    fn preflight(&self, support: &std::collections::BTreeSet<usize>) -> Result<(), String> {
        for &wire in support {
            let _ = self.read(wire)?;
        }
        Ok(())
    }

    fn remove_for_test(&mut self, wire: usize) -> Result<(), String> {
        let key = self.key_for(wire)?;
        self.values.remove(&key);
        self.identities
            .remove(&(key.owner, key.namespace, key.local));
        Ok(())
    }

    fn digest(&self) -> String {
        let mut digest = Blake2b::<U32>::new();
        digest.update(b"nipopow-v2-m2-producer-registry-v1");
        for (key, value) in &self.values {
            digest.update([match key.namespace {
                ProducerNamespace::Serializer => 1,
                ProducerNamespace::WorkEndpoint => 2,
            }]);
            digest.update((key.owner as u64).to_le_bytes());
            digest.update((key.local as u64).to_le_bytes());
            digest.update((key.producer as u64).to_le_bytes());
            digest.update([*value as u8]);
        }
        digest.update((self.support.len() as u64).to_le_bytes());
        digest.update((self.values.len() as u64).to_le_bytes());
        hex_upper(&digest.finalize())
    }
}

fn assemble_after_registry_preflight(
    registry: &M2ProducerRegistry,
    support: &std::collections::BTreeSet<usize>,
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    callback_calls: &mut usize,
) -> Result<crate::packed_owner_assembly::PreparedOwnerWindow, String> {
    registry.preflight(support)?;
    assemble_window(plan, input, |wire| {
        *callback_calls += 1;
        registry.read(wire)
    })
}

fn foreign_provider() -> &'static ForeignProvider {
    static PROVIDER: OnceLock<ForeignProvider> = OnceLock::new();
    PROVIDER.get_or_init(|| ForeignProvider::new(prefix()))
}

fn serializer() -> &'static serializer::Compiled {
    static SERIALIZER: OnceLock<serializer::Compiled> = OnceLock::new();
    SERIALIZER.get_or_init(|| serializer::build(None).unwrap())
}

fn byte_bit(bytes: &[u8], bit: usize) -> bool {
    bytes
        .get(bit / 8)
        .is_some_and(|byte| (byte >> (bit % 8)) & 1 != 0)
}

fn be224_bit(bytes: &[u8; 28], bit: usize) -> bool {
    (bytes[27 - bit / 8] >> (bit % 8)) & 1 != 0
}

fn integer_bit(value: &BigUint, bit: usize) -> bool {
    value
        .to_bytes_le()
        .get(bit / 8)
        .is_some_and(|byte| (byte >> (bit % 8)) & 1 != 0)
}

fn array_bit(
    wires: &[usize],
    local: usize,
    value: impl FnOnce(usize) -> Result<bool, String>,
) -> Result<Option<bool>, String> {
    let Some(bit) = wires.iter().position(|wire| *wire == local) else {
        return Ok(None);
    };
    value(bit).map(Some)
}

fn endpoint_bit(
    input: &NativePrefix,
    descriptor: &Descriptor,
    fixed_profile: &work_tree_fixed_hash::FixedProfile,
    slot: usize,
    local: usize,
) -> Result<Option<bool>, String> {
    let endpoints = &work_tree_layout::shared_baseline()?.endpoints;
    // B1's typed serializer aliases are stored at the leaf owner and name
    // RAW(slot + 2); the serializer bank itself is at owner height - 1.
    if let Some(bit) = array_bit(&endpoints.raw, local, |bit| {
        if slot >= descriptor.genuine {
            return Ok(false);
        }
        Ok(byte_bit(input.raw(slot + 2)?, bit))
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.length, local, |bit| {
        let length = if slot < descriptor.genuine {
            input.raw(slot + 2)?.len()
        } else {
            0
        };
        Ok(((length >> bit) & 1) != 0)
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.n_bits, local, |bit| {
        let value = if slot < descriptor.genuine {
            input.compact_n_bits(slot + 2)?
        } else {
            0
        };
        Ok(((value >> bit) & 1) != 0)
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.height, local, |bit| {
        let value = if slot < descriptor.genuine {
            (slot + 2) as u32
        } else {
            0
        };
        Ok(((value >> bit) & 1) != 0)
    })? {
        return Ok(Some(bit));
    }

    let interval = if slot < descriptor.genuine {
        Some(input.interval(slot + 2)?)
    } else {
        None
    };
    if let Some(bit) = array_bit(&endpoints.lower, local, |bit| {
        Ok(interval.is_some_and(|(lower, _)| be224_bit(&lower, bit)))
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.upper, local, |bit| {
        Ok(interval.is_some_and(|(_, upper)| be224_bit(&upper, bit)))
    })? {
        return Ok(Some(bit));
    }

    let compact = if slot < descriptor.genuine {
        Some(input.compact_n_bits(slot + 2)?)
    } else {
        None
    };
    let native_work = compact.map(work_tree_work::native_decode).transpose()?;
    if let Some(bit) = array_bit(&endpoints.work, local, |bit| {
        Ok(native_work
            .as_ref()
            .is_some_and(|work| integer_bit(work, bit)))
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.work_minus_one, local, |bit| {
        let Some(work) = native_work.as_ref() else {
            return Ok(false);
        };
        if *work == BigUint::from(0u8) {
            return Err("native work-minus-one has zero source".into());
        }
        Ok(integer_bit(&(work - BigUint::from(1u8)), bit))
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.exponent, local, |bit| {
        Ok(compact.is_some_and(|n_bits| ((n_bits >> 24) as usize) == bit))
    })? {
        return Ok(Some(bit));
    }

    if let Some(bit) = array_bit(&endpoints.leaf, local, |bit| {
        if slot >= descriptor.leaves {
            return Err(format!("leaf endpoint slot {slot} outside descriptor"));
        }
        Ok(byte_bit(&input.leaf_digest(slot)?, bit))
    })? {
        return Ok(Some(bit));
    }
    let role = fixed_profile.role(slot).ok();
    let child_digests = || -> Result<([u8; 32], [u8; 32]), String> {
        let Some(FixedRole::Node { level, position }) = role else {
            return Err(format!("slot {slot} has no fixed node children"));
        };
        let child_base = if level == 1 {
            0
        } else {
            descriptor.level(level as usize - 1)?.0
        };
        let left_slot = child_base + 2 * position as usize;
        let right_slot = left_slot + 1;
        let digest = |child| {
            if level == 1 {
                input.leaf_digest(child)
            } else {
                input.node_digest(child)
            }
        };
        Ok((digest(left_slot)?, digest(right_slot)?))
    };
    if let Some(bit) = array_bit(&endpoints.node_left, local, |bit| {
        Ok(byte_bit(&child_digests()?.0, bit))
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.node_right, local, |bit| {
        Ok(byte_bit(&child_digests()?.1, bit))
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.node, local, |bit| {
        if !matches!(role, Some(FixedRole::Node { .. } | FixedRole::Profile)) {
            return Err(format!("slot {slot} has no fixed node digest"));
        }
        Ok(byte_bit(&input.node_digest(slot)?, bit))
    })? {
        return Ok(Some(bit));
    }
    if let Some(bit) = array_bit(&endpoints.profile, local, |bit| {
        Ok(byte_bit(&input.profile(), bit))
    })? {
        return Ok(Some(bit));
    }
    Ok(None)
}

fn compile_plan(headers: u64, root: [u8; 32], total: [u8; 28]) -> WorkTreeHistoryPlan {
    WorkTreeHistoryPlan::compile(
        headers,
        headers.next_power_of_two().trailing_zeros() as usize,
        root,
        total,
    )
    .unwrap()
}

fn expect_error<T>(result: Result<T, String>) -> String {
    match result {
        Err(error) => error,
        Ok(_) => panic!("operation unexpectedly succeeded"),
    }
}

fn rejected_fault(fault: AssemblyFault) -> String {
    let input = prefix();
    let mut reads = HashSet::new();
    let provider = foreign_provider();
    let result = assemble_window_fault_for_test(
        assembly_plan(),
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        fault,
    );
    expect_error(result)
}

fn m1_fault_error(fault: AssemblyFault) -> String {
    let input = prefix();
    let mut reads = HashSet::new();
    let provider = foreign_provider();
    let result = assemble_m1_window_fault_for_test(
        assembly_plan(),
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        fault,
    );
    expect_error(result)
}

fn m1_expected_group_counts(
    plan: &WorkTreeHistoryPlan,
    roster: &crate::daa_history_roster::DaaHistoryRoster<'_>,
) -> BTreeMap<String, usize> {
    let owners = [2047usize, 2048];
    let mut expected = BTreeMap::new();
    for owner in owners {
        let mut count = 0usize;
        roster
            .visit_header_terms(owner as u64, |term| {
                let _ = term;
                count += 1;
                Ok(())
            })
            .unwrap();
        assert!(expected.insert(format!("Header/{owner}"), count).is_none());

        count = 0;
        roster
            .visit_owner_terms(owner as u64, |term| {
                let _ = term;
                count += 1;
                Ok(())
            })
            .unwrap();
        assert!(expected.insert(format!("DAA/{owner}"), count).is_none());

        count = 0;
        crate::work_tree_leaf_hash::Boundary::emit_slot(plan.leaf_boundary(), owner, |term| {
            let _ = term;
            count += 1;
        })
        .unwrap();
        assert!(expected.insert(format!("Leaf/{owner}"), count).is_none());

        count = 0;
        crate::work_tree_fixed_hash::emit_slot(
            crate::work_tree_fixed_hash::engine().unwrap(),
            plan.fixed_profile(),
            owner,
            |term| {
                let _ = term;
                count += 1;
            },
        )
        .unwrap();
        assert!(expected.insert(format!("Fixed/{owner}"), count).is_none());

        count = 0;
        plan.work_boundary()
            .emit_slot(owner, |term| {
                let _ = term;
                count += 1;
            })
            .unwrap();
        assert!(expected.insert(format!("Work/{owner}"), count).is_none());
    }
    for (kind, families) in [
        ("Topology", plan.topology().families.as_slice()),
        ("WorkLink", plan.work_boundary().links().as_slice()),
    ] {
        for family in families {
            let mut count = 0usize;
            family
                .emit_terms(plan.descriptor(), |term| {
                    let left_owner = term.gate.left / WIDTH;
                    let right_owner = term.gate.right / WIDTH;
                    let reads_left = !term.gate.c1.is_zero() || !term.gate.c3.is_zero();
                    let reads_right = !term.gate.c2.is_zero() || !term.gate.c3.is_zero();
                    if (reads_left && owners.contains(&left_owner))
                        || (reads_right && owners.contains(&right_owner))
                    {
                        count += 1;
                    }
                    Ok(())
                })
                .unwrap();
            assert!(expected
                .insert(format!("{kind}/{}", family.name), count)
                .is_none());
        }
    }
    expected
}

fn m1_assemble_with_reader(
    mut mutate: impl FnMut(usize, bool) -> Result<bool, String>,
) -> (
    Result<crate::packed_owner_assembly::PreparedOwnerWindow, String>,
    HashSet<usize>,
) {
    let input = prefix();
    let provider = foreign_provider();
    let mut reads = HashSet::new();
    let result = assemble_m1_window(assembly_plan(), input, |wire| {
        if !reads.insert(wire) {
            return Err(format!("duplicate foreign read {wire}"));
        }
        mutate(wire, provider.bit(wire, input)?)
    });
    (result, reads)
}

#[test]
fn native_prefix_bundle_is_canonical_linked_and_pinned() {
    let native = prefix();
    assert_eq!(native.header(1).unwrap().height, 1);
    assert_eq!(native.header(3073).unwrap().height, 3073);
    assert_eq!(native.timestamp(1).unwrap(), native.header(1).unwrap().timestamp);
    assert_eq!(native.compact_n_bits(3073).unwrap(), native.header(3073).unwrap().n_bits);
    assert!(!native.header_exists(0));
    assert!(native.header_exists(3073));
    assert!(!native.header_exists(3074));
    assert_eq!(expect_error(native.header(0)), "height zero");
    assert_eq!(expect_error(native.header(3074)), "prefix header 3074 absent");
    assert_eq!(expect_error(native.timestamp(0)), "height zero");
    assert_eq!(expect_error(native.timestamp(3074)), "prefix header 3074 absent");
    assert_eq!(expect_error(native.compact_n_bits(0)), "height zero");
    assert_eq!(expect_error(native.compact_n_bits(3074)), "prefix header 3074 absent");
    assert_eq!(native.raw(3073).unwrap().len(), 279);
    assert_ne!(native.root(), [0; 32]);
    assert_ne!(native.total_be28(), [0; 28]);
}

#[test]
fn native_prefix_rejects_truncation_noncanonical_raw_and_parent_mismatch() {
    let raws = read_prefix_raws();
    assert!(NativePrefix::from_raw_headers(&raws[..3072]).is_err());

    let mut noncanonical = raws.clone();
    noncanonical[3072].push(0);
    assert!(NativePrefix::from_raw_headers(&noncanonical).is_err());

    let mut wrong_parent = raws;
    wrong_parent[3072][1] ^= 1;
    assert!(NativePrefix::from_raw_headers(&wrong_parent).is_err());
}

#[test]
fn native_history_small_prefixes_bind_producer_exports_and_consumer() {
    let all_raws = read_prefix_raws();
    for n in [3usize, 4, 5] {
        let input = NativePrefix::from_raw_iter(
            n,
            all_raws.iter().take(n).cloned().map(Ok),
        )
        .unwrap();
        let plan = compile_plan(n as u64, input.root(), input.total_be28());
        validate_native_plan_input(&plan, &input).unwrap();
        assert_eq!(input.header_count(), n);
        assert_eq!(input.genuine_count(), n - 1);
        assert_eq!(input.slot_count(), n.next_power_of_two());
        assert_eq!(input.leaf_count(), (n - 1).next_power_of_two());
        assert_eq!(input.node_count(), input.slot_count());
        if n == 4 {
            assert_eq!(input.slot_count(), n, "N4 has no physical padding");
        }

        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        let exports = crate::native_owner_exports::NativeExports::new_for_history(&plan, &input)
            .unwrap();
        let roster = crate::daa_history_roster::DaaHistoryRoster::compile(&plan).unwrap();
        let owners = [0, n - 2, n - 1, n, input.slot_count() - 1];
        let mut visited = HashSet::new();
        for owner in owners {
            if owner >= input.slot_count() {
                continue;
            }
            if !visited.insert(owner) {
                continue;
            }
            let class = roster.owner_class(owner as u64).unwrap();
            let row = producer.produce(owner).unwrap();
            assert_eq!(row.owner(), owner);
            assert_eq!(row.class(), class);
            assert_eq!(row.packed_bytes().len(), PACKED_OWNER_BYTES);
            let receipt = validate_native_row_for_history_test(&plan, &input, &row, |wire| {
                exports.bit(wire)
            })
            .unwrap();
            assert_eq!(receipt.groups.len(), 5);

            let endpoints = &work_tree_layout::shared_baseline().unwrap().endpoints;
            for wire in [
                endpoints.raw[0],
                endpoints.leaf[0],
                endpoints.profile[0],
                endpoints.node[0],
                endpoints.node_left[0],
                endpoints.node_right[0],
            ] {
                let global = owner * WIDTH + wire;
                assert_eq!(
                    exports.bit(global).unwrap(),
                    byte_bit(row.packed_bytes(), wire),
                    "N{n} owner{owner} wire{wire}"
                );
            }
            let mut known = HashSet::new();
            for ports in [
                &endpoints.raw,
                &endpoints.length,
                &endpoints.n_bits,
                &endpoints.height,
                &endpoints.lower,
                &endpoints.upper,
                &endpoints.work,
                &endpoints.work_minus_one,
                &endpoints.exponent,
                &endpoints.leaf,
                &endpoints.node_left,
                &endpoints.node_right,
                &endpoints.node,
                &endpoints.profile,
            ] {
                known.extend(ports.iter().copied());
            }
            let unknown = (work_tree_layout::ENDPOINT_BASE
                ..work_tree_layout::ENDPOINT_BASE + work_tree_layout::ENDPOINT_WIDTH)
                .find(|wire| !known.contains(wire))
                .unwrap();
            assert!(exports.bit(owner * WIDTH + unknown).is_err());
            if plan.fixed_profile().role(owner).unwrap() == FixedRole::Dummy {
                assert!(!exports.bit(owner * WIDTH + endpoints.leaf[0]).unwrap());
                assert!(!exports.bit(owner * WIDTH + endpoints.profile[0]).unwrap());
                assert!(!exports.bit(owner * WIDTH + endpoints.node[0]).unwrap());
                assert!(exports.bit(owner * WIDTH + unknown).is_err());
            }
        }
        assert!(expect_error(exports.bit(input.slot_count() * WIDTH)).contains("outside"));

        let wrong_count = compile_plan((n + 1) as u64, input.root(), input.total_be28());
        assert!(expect_error(NativeOwnerProducer::new_for_history(&wrong_count, &input))
            .contains("count mismatch"));
        assert!(expect_error(
            crate::native_owner_exports::NativeExports::new_for_history(&wrong_count, &input)
        )
        .contains("count mismatch"));
        let wrong_root = compile_plan(n as u64, [0x73; 32], input.total_be28());
        assert!(expect_error(NativeOwnerProducer::new_for_history(&wrong_root, &input))
            .contains("root, total or profile mismatch"));
        let wrong_total = compile_plan(n as u64, input.root(), [0x24; 28]);
        assert!(expect_error(
            crate::native_owner_exports::NativeExports::new_for_history(&wrong_total, &input)
        )
        .contains("root, total or profile mismatch"));
        let bound_row = producer.produce(0).unwrap();
        assert!(expect_error(validate_native_row_for_history_test(
            &wrong_count,
            &input,
            &bound_row,
            |wire| exports.bit(wire)
        ))
        .contains("count mismatch"));
        assert!(expect_error(validate_native_row_for_history_test(
            &wrong_root,
            &input,
            &bound_row,
            |wire| exports.bit(wire)
        ))
        .contains("root, total or profile mismatch"));

        let mut alternate_raws = all_raws[..n].to_vec();
        let last = alternate_raws.last_mut().unwrap();
        let mut last_header = Header::decode(last, None).unwrap();
        last_header.timestamp = last_header.timestamp.wrapping_add(1);
        *last = last_header.encode().unwrap();
        let alternate = NativePrefix::from_raw_iter(n, alternate_raws.into_iter().map(Ok)).unwrap();
        let alternate_plan = compile_plan(n as u64, alternate.root(), alternate.total_be28());
        let alternate_exports =
            crate::native_owner_exports::NativeExports::new_for_history(&alternate_plan, &alternate)
                .unwrap();
        assert_eq!(
            expect_error(validate_native_row_for_history_test(
                &alternate_plan,
                &alternate,
                &bound_row,
                |wire| alternate_exports.bit(wire)
            )),
            "native row validation binding mismatch"
        );
    }
}

#[test]
fn native_prefix_keeps_scalar_fields_and_signed_timestamp_bits() {
    let raws = read_prefix_raws();
    let input = NativePrefix::from_raw_iter(5, raws.iter().take(5).cloned().map(Ok)).unwrap();
    for height in 1..=input.header_count() {
        let decoded = Header::decode(input.raw(height).unwrap(), None).unwrap();
        assert_eq!(input.timestamp(height).unwrap(), decoded.timestamp, "height{height}");
        assert_eq!(input.compact_n_bits(height).unwrap(), decoded.n_bits, "height{height}");
    }

    for timestamp in [i64::MIN, i64::MAX] {
        let mut changed = raws[..3].to_vec();
        let mut last = Header::decode(changed.last().unwrap(), None).unwrap();
        last.timestamp = timestamp;
        *changed.last_mut().unwrap() = last.encode().unwrap();
        let signed = NativePrefix::from_raw_iter(3, changed.into_iter().map(Ok)).unwrap();
        assert_eq!(signed.timestamp(3).unwrap(), timestamp);
        assert_eq!(signed.header(3).unwrap().timestamp, timestamp);
        let plan = compile_plan(3, signed.root(), signed.total_be28());
        let exports = crate::native_owner_exports::NativeExports::new_for_history(&plan, &signed)
            .unwrap();
        for (bit, &wire) in serializer().layout.fields.timestamp.iter().enumerate() {
            assert_eq!(
                exports.bit(2 * WIDTH + SERIALIZER_OFFSET + wire).unwrap(),
                ((timestamp as u64) >> bit) & 1 != 0,
                "timestamp bit {bit} for {timestamp}"
            );
        }
    }
}

#[test]
fn native_history_raw_iterator_rejects_count_errors_and_bad_records() {
    let raws = read_prefix_raws();
    assert!(expect_error(NativePrefix::from_raw_iter(
        2,
        std::iter::empty::<Result<Vec<u8>, String>>()
    ))
    .contains("count outside"));
    assert!(expect_error(NativePrefix::from_raw_iter(
        (1usize << 21) + 1,
        std::iter::empty::<Result<Vec<u8>, String>>()
    ))
    .contains("count outside"));
    assert!(expect_error(NativePrefix::from_raw_iter(3, raws[..2].iter().cloned().map(Ok)))
        .contains("missing at height 3"));
    assert!(expect_error(NativePrefix::from_raw_iter(
        3,
        vec![Ok(raws[0].clone()), Err("injected reader failure".into()), Ok(raws[2].clone())]
    ))
    .contains("injected reader failure"));
    let mut extra = raws[..3].to_vec();
    extra.push(raws[3].clone());
    assert!(expect_error(NativePrefix::from_raw_iter(3, extra.into_iter().map(Ok)))
        .contains("extra RAW"));
    let mut empty = raws[..3].to_vec();
    empty[1].clear();
    assert!(expect_error(NativePrefix::from_raw_iter(3, empty.into_iter().map(Ok)))
        .contains("RAW length"));
    let mut oversized = raws[..3].to_vec();
    oversized[1].resize(515, 0);
    assert!(expect_error(NativePrefix::from_raw_iter(3, oversized.into_iter().map(Ok)))
        .contains("RAW length"));

    let mut wrong_height = raws[..3].to_vec();
    let mut header = Header::decode(&wrong_height[1], None).unwrap();
    header.height = 99;
    wrong_height[1] = header.encode().unwrap();
    assert!(expect_error(NativePrefix::from_raw_iter(3, wrong_height.into_iter().map(Ok)))
        .contains("not canonical"));
    let mut broken_link = raws[..3].to_vec();
    broken_link[2][1] ^= 1;
    assert!(expect_error(NativePrefix::from_raw_iter(3, broken_link.into_iter().map(Ok)))
        .contains("not canonical"));
    let mut zero_work = raws[..3].to_vec();
    let mut header = Header::decode(&zero_work[2], None).unwrap();
    header.n_bits = 0;
    zero_work[2] = header.encode().unwrap();
    assert_eq!(
        expect_error(NativePrefix::from_raw_iter(3, zero_work.into_iter().map(Ok))),
        "native zero difficulty"
    );

    let mut wrong_genesis = raws[..3].to_vec();
    let mut genesis = Header::decode(&wrong_genesis[0], None).unwrap();
    genesis.timestamp = genesis.timestamp.wrapping_add(1);
    wrong_genesis[0] = genesis.encode().unwrap();
    assert_eq!(
        expect_error(NativePrefix::from_raw_iter(3, wrong_genesis.into_iter().map(Ok))),
        "native prefix genesis identity"
    );

    let mut overflow = raws[..3].to_vec();
    for index in [1usize, 2] {
        let mut header = Header::decode(&overflow[index], None).unwrap();
        header.n_bits = 0x1e00_00ff;
        if index == 2 {
            header.parent_id = ergo_header_core::blake2b256(&overflow[1]);
        }
        overflow[index] = header.encode().unwrap();
    }
    assert_eq!(
        expect_error(NativePrefix::from_raw_iter(3, overflow.into_iter().map(Ok))),
        "native prefix cumulative work exceeds U224"
    );
}

struct NativeHistoryRawFrames<'a> {
    reader: &'a mut BufReader<File>,
    remaining: usize,
}

impl Iterator for NativeHistoryRawFrames<'_> {
    type Item = Result<Vec<u8>, String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let mut read_one = || -> Result<Vec<u8>, String> {
            let mut length = [0u8; 4];
            self.reader
                .read_exact(&mut length)
                .map_err(|error| format!("native history RAW length read: {error}"))?;
            let length = u32::from_le_bytes(length) as usize;
            if !(1..=514).contains(&length) {
                return Err("native history RAW length outside 1..=514".into());
            }
            let mut raw = vec![0u8; length];
            self.reader
                .read_exact(&mut raw)
                .map_err(|error| format!("native history RAW body read: {error}"))?;
            Ok(raw)
        };
        Some(read_one())
    }
}

fn read_native_history_file(
    path: &std::path::Path,
    expected_n: usize,
    expected_size: u64,
    expected_blake: &str,
) -> Result<(NativePrefix, BufReader<File>), String> {
    if !(3..=(1usize << 21)).contains(&expected_n) {
        return Err("native history count outside plan domain".into());
    }
    let minimum = (expected_n as u64)
        .checked_mul(5)
        .ok_or("native history minimum size overflow")?;
    let maximum = (expected_n as u64)
        .checked_mul(518)
        .ok_or("native history maximum size overflow")?;
    if !(minimum..=maximum).contains(&expected_size) {
        return Err("native history expected size outside bounds".into());
    }
    let mut reader = BufReader::with_capacity(
        64 * 1024,
        OpenOptions::new()
            .read(true)
            .share_mode(1)
            .open(path)
            .map_err(|error| format!("native history open: {error}"))?,
    );
    let actual_size = reader
        .get_ref()
        .metadata()
        .map_err(|error| format!("native history fstat: {error}"))?
        .len();
    if actual_size != expected_size {
        return Err("native history file size pin mismatch".into());
    }
    let mut hasher = Blake2b::<U32>::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = reader
            .read(&mut buffer)
            .map_err(|error| format!("native history hash read: {error}"))?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    let actual_blake = hex_upper(&hasher.finalize());
    if actual_blake != expected_blake.to_ascii_uppercase() {
        return Err("native history BLAKE2b256 pin mismatch".into());
    }
    reader
        .seek(SeekFrom::Start(0))
        .map_err(|error| format!("native history rewind: {error}"))?;
    let input = NativePrefix::from_raw_iter(
        expected_n,
        NativeHistoryRawFrames {
            reader: &mut reader,
            remaining: expected_n,
        },
    )?;
    let mut trailing = [0u8; 1];
    if reader
        .read(&mut trailing)
        .map_err(|error| format!("native history trailing-byte check: {error}"))?
        != 0
    {
        return Err("native history trailing bytes".into());
    }
    Ok((input, reader))
}

fn write_raw_fixture(path: &std::path::Path, bytes: &[u8]) {
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .expect("create unique RAW fault fixture");
    output.write_all(bytes).unwrap();
    output.sync_all().unwrap();
}

fn framed_raws(raws: &[Vec<u8>]) -> Vec<u8> {
    let mut output = Vec::new();
    for raw in raws {
        output.extend_from_slice(&(raw.len() as u32).to_le_bytes());
        output.extend_from_slice(raw);
    }
    output
}

fn fixture_blake(bytes: &[u8]) -> String {
    hex_upper(&Blake2b::<U32>::digest(bytes))
}

#[test]
fn native_history_file_reader_rejects_isolated_pin_and_frame_faults() {
    let Some(root) = std::env::var_os(NATIVE_HISTORY_FAULT_DIR_ENV) else {
        assert!(
            std::env::var_os(NATIVE_HISTORY_RAW_ENV).is_none(),
            "selected history mode requires the isolated reader-fault artifact directory"
        );
        return;
    };
    let root = PathBuf::from(root);
    let unique = format!(
        "reader-faults-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
    );
    let case_dir = root.join(unique);
    fs::create_dir_all(&root).unwrap();
    fs::create_dir(&case_dir).expect("fresh fault artifact directory");
    let raws = read_prefix_raws();
    let valid = framed_raws(&raws[..3]);

    let missing = case_dir.join("missing.u32le");
    assert!(expect_error(read_native_history_file(&missing, 2, 0, "")).contains("count outside"));
    assert!(expect_error(read_native_history_file(
        &missing,
        (1usize << 21) + 1,
        0,
        ""
    ))
    .contains("count outside"));
    assert!(expect_error(read_native_history_file(&missing, 3, 14, "")).contains("size outside"));
    assert!(expect_error(read_native_history_file(&missing, 3, 1_555, "")).contains("size outside"));
    let valid_path = case_dir.join("valid.u32le");
    write_raw_fixture(&valid_path, &valid);
    assert!(expect_error(read_native_history_file(
        &valid_path,
        4,
        valid.len() as u64 + 1,
        &fixture_blake(&valid)
    ))
        .contains("file size pin mismatch"));
    assert!(expect_error(read_native_history_file(
        &valid_path,
        3,
        valid.len() as u64,
        &"00".repeat(32)
    ))
        .contains("BLAKE2b256 pin mismatch"));

    let mut empty_raw = framed_raws(&raws[..2]);
    empty_raw.extend_from_slice(&0u32.to_le_bytes());
    let empty_path = case_dir.join("length-zero.u32le");
    write_raw_fixture(&empty_path, &empty_raw);
    assert!(expect_error(read_native_history_file(
        &empty_path,
        3,
        empty_raw.len() as u64,
        &fixture_blake(&empty_raw)
    ))
        .contains("RAW length outside"));

    let mut oversized_raw = framed_raws(&raws[..2]);
    oversized_raw.extend_from_slice(&515u32.to_le_bytes());
    oversized_raw.resize(oversized_raw.len() + 515, 0);
    let oversized_path = case_dir.join("length-515.u32le");
    write_raw_fixture(&oversized_path, &oversized_raw);
    assert!(expect_error(read_native_history_file(
        &oversized_path,
        4,
        oversized_raw.len() as u64,
        &fixture_blake(&oversized_raw)
    ))
        .contains("RAW length outside"));

    let mut short_length = framed_raws(&raws[..2]);
    short_length.extend_from_slice(&[3, 0]);
    let short_length_path = case_dir.join("truncated-length.u32le");
    write_raw_fixture(&short_length_path, &short_length);
    assert!(expect_error(read_native_history_file(
        &short_length_path,
        3,
        short_length.len() as u64,
        &fixture_blake(&short_length)
    ))
        .contains("RAW length read"));

    let mut short_body = framed_raws(&raws[..2]);
    short_body.extend_from_slice(&5u32.to_le_bytes());
    short_body.extend_from_slice(&[1, 2]);
    let short_body_path = case_dir.join("truncated-body.u32le");
    write_raw_fixture(&short_body_path, &short_body);
    assert!(expect_error(read_native_history_file(
        &short_body_path,
        3,
        short_body.len() as u64,
        &fixture_blake(&short_body)
    ))
        .contains("RAW body read"));

    let mut trailing = valid.clone();
    trailing.push(0xA5);
    let trailing_path = case_dir.join("trailing.u32le");
    write_raw_fixture(&trailing_path, &trailing);
    assert!(expect_error(read_native_history_file(
        &trailing_path,
        3,
        trailing.len() as u64,
        &fixture_blake(&trailing)
    ))
        .contains("trailing bytes"));

    let (_valid_input, locked_reader) = read_native_history_file(
        &valid_path,
        3,
        valid.len() as u64,
        &fixture_blake(&valid),
    )
    .unwrap();
    let denied_write = OpenOptions::new().write(true).open(&valid_path);
    assert!(denied_write.is_err(), "reader share mode must deny a writer");
    drop(locked_reader);
}

#[test]
fn native_history_selected_input_streams_pinned_prefix_and_rows_when_configured() {
    let Some(raw_path) = std::env::var_os(NATIVE_HISTORY_RAW_ENV) else {
        return;
    };
    let expected_n = std::env::var(NATIVE_HISTORY_N_ENV)
        .expect("root-pinned expected N")
        .parse::<usize>()
        .expect("valid expected N");
    let expected_size = std::env::var(NATIVE_HISTORY_SIZE_ENV)
        .expect("root-pinned expected size")
        .parse::<u64>()
        .expect("valid expected size");
    let expected_blake = std::env::var(NATIVE_HISTORY_BLAKE_ENV)
        .expect("root-pinned expected BLAKE2b256");
    let output_path = PathBuf::from(
        std::env::var_os(NATIVE_HISTORY_OUTPUT_ENV).expect("fresh selected-run JSON output"),
    );
    let started = Instant::now();
    let (input, _locked_reader) = read_native_history_file(
        PathBuf::from(raw_path).as_path(),
        expected_n,
        expected_size,
        &expected_blake,
    )
    .expect("build exact canonical prefix from the pinned locked stream");
    let actual_blake = expected_blake.to_ascii_uppercase();
    assert_eq!(input.header_count(), expected_n);
    if expected_n >= 3073 {
        let old = read_prefix_raws();
        for (index, raw) in old.iter().enumerate() {
            assert_eq!(input.raw(index + 1).unwrap(), raw.as_slice(), "legacy prefix height {}", index + 1);
        }
    }

    let plan = compile_plan(expected_n as u64, input.root(), input.total_be28());
    let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
    let exports = crate::native_owner_exports::NativeExports::new_for_history(&plan, &input)
        .unwrap();
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(&plan).unwrap();
    let mut selected = BTreeMap::<usize, ()>::new();
    let root_node_slot = plan.descriptor().root_node_slot;
    for owner in [
        0,
        1,
        2,
        expected_n.saturating_sub(2),
        expected_n - 1,
        expected_n,
        input.slot_count() - 1,
        root_node_slot,
        9_216,
        9_217,
        417_791,
        417_792,
        844_672,
        844_673,
    ] {
        if owner < input.slot_count() {
            selected.insert(owner, ());
        }
    }
    let mut rows = Vec::new();
    let mut mature_mutants = Vec::new();
    for owner in selected.keys().copied() {
        let class = roster.owner_class(owner as u64).unwrap();
        if owner == expected_n {
            assert!(expected_n < input.slot_count());
            assert_eq!(class, crate::daa_history_roster::OwnerClass::Padding);
        }
        if [417_791usize, 417_792].contains(&owner) {
            assert_eq!(class, crate::daa_history_roster::OwnerClass::FixedV2);
        }
        let row = producer.produce(owner).unwrap();
        let receipt = validate_native_row_for_history_test(&plan, &input, &row, |wire| {
            exports.bit(wire)
        })
        .unwrap();
        let schedule = if matches!(class, crate::daa_history_roster::OwnerClass::Mature(_)) {
            let schedule = crate::daa_header_window::for_child_height((owner + 1) as u32).unwrap();
            assert_eq!(schedule.sample_heights().len(), 9);
            Some(schedule.sample_heights().to_vec())
        } else {
            None
        };
        if schedule.is_some() {
            let mut terms = Vec::new();
            roster
                .visit_owner_terms(owner as u64, |term| {
                    terms.push(term);
                    Ok(())
                })
                .unwrap();
            let imported = terms.iter().find_map(|term| {
                let gate = &term.gate;
                if !gate.c1.is_zero() && gate.left != 0 && gate.left / WIDTH != owner {
                    Some(gate.left)
                } else if !gate.c2.is_zero() && gate.right != 0 && gate.right / WIDTH != owner {
                    Some(gate.right)
                } else if !gate.c3.is_zero() && gate.left != 0 && gate.left / WIDTH != owner {
                    Some(gate.left)
                } else if !gate.c3.is_zero() && gate.right != 0 && gate.right / WIDTH != owner {
                    Some(gate.right)
                } else {
                    None
                }
            });
            let imported = imported.expect("Mature relation has a foreign imported coordinate");
            let actual = exports.bit(imported).unwrap();
            let mut callback_seen = false;
            let error = expect_error(validate_native_row_for_history_test(
                &plan,
                &input,
                &row,
                |wire| {
                    let value = exports.bit(wire)?;
                    if wire == imported {
                        callback_seen = true;
                        Ok(!value)
                    } else {
                        Ok(value)
                    }
                },
            ));
            assert!(callback_seen, "selected import callback not reached for owner{owner}");
            assert!(error.contains(&format!("DAA/{owner}")), "{error}");
            mature_mutants.push(serde_json::json!({"owner":owner,"imported_global_coordinate":imported,"raw_value":actual,"mutated_value":!actual,"first_error":error}));
        }
        let role = plan.fixed_profile().role(owner).unwrap();
        if owner == root_node_slot {
            assert!(matches!(role, FixedRole::Node { .. }));
        }
        rows.push(serde_json::json!({
            "owner":owner,
            "class":format!("{class:?}"),
            "packed_row_hex":hex_upper(row.packed_bytes()),
            "consumer_groups":receipt.groups.iter().map(|(name,count)|serde_json::json!({"name":name,"terms":count})).collect::<Vec<_>>(),
            "foreign_census":receipt.foreign_census,
            "fixed_role":format!("{role:?}"),
            "mature_sample_heights":schedule,
        }));
    }
    if expected_n > 9_216 {
        assert!(mature_mutants.iter().any(|value| value["owner"] == 9_216));
    }
    if expected_n > 844_672 {
        assert!(mature_mutants.iter().any(|value| value["owner"] == 844_672));
    }
    if expected_n < input.slot_count() {
        let padding = rows
            .iter()
            .find(|value| value["owner"] == expected_n)
            .expect("first physical padding owner emitted");
        assert_eq!(padding["class"], "Padding");
    }
    if rows.iter().any(|value| value["owner"] == root_node_slot) {
        assert!(rows
            .iter()
            .find(|value| value["owner"] == root_node_slot)
            .unwrap()["fixed_role"]
            .as_str()
            .unwrap()
            .starts_with("Node"));
    }
    if expected_n > 417_792 {
        for owner in [417_791usize, 417_792] {
            assert!(rows.iter().any(|value| value["owner"] == owner), "FixedV2 owner{owner} row emitted");
        }
    }
    let result = serde_json::json!({
        "schema":"native-history-selected-rows-v1",
        "expected_n":expected_n,
        "expected_size":expected_size,
        "blake2b256":actual_blake,
        "root_hex":hex_upper(&input.root()),
        "total_work_be28_hex":hex_upper(&input.total_be28()),
        "slot_count":input.slot_count(),
        "genuine_count":input.genuine_count(),
        "leaf_count":input.leaf_count(),
        "node_count":input.node_count(),
        "scalar_storage_bytes":input.header_count() * (std::mem::size_of::<i64>() + std::mem::size_of::<u32>()),
        "selected_rows":rows,
        "mature_import_mutants":mature_mutants,
        "elapsed_ns":started.elapsed().as_nanos(),
    });
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(output_path)
        .expect("create new selected-run output");
    output.write_all(&serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    output.sync_all().unwrap();
}

#[test]
fn native_history_fixed_v2_compact_mutants_reach_named_daa_rows_when_configured() {
    let Some(raw_path) = std::env::var_os(NATIVE_HISTORY_RAW_ENV) else {
        return;
    };
    let expected_n = std::env::var(NATIVE_HISTORY_N_ENV)
        .expect("root-pinned expected N")
        .parse::<usize>()
        .expect("valid expected N");
    let expected_size = std::env::var(NATIVE_HISTORY_SIZE_ENV)
        .expect("root-pinned expected size")
        .parse::<u64>()
        .expect("valid expected size");
    let expected_blake = std::env::var(NATIVE_HISTORY_BLAKE_ENV)
        .expect("root-pinned expected BLAKE2b256");
    let output_path = PathBuf::from(
        std::env::var_os(NATIVE_HISTORY_OUTPUT_ENV).expect("fresh reset-mutant JSON output"),
    );
    assert!(expected_n >= 417_793, "authenticated input must cover both reset children");
    let (source, _locked_reader) = read_native_history_file(
        PathBuf::from(raw_path).as_path(),
        expected_n,
        expected_size,
        &expected_blake,
    )
    .expect("authenticate the exact selected RAW source before mutation");
    let mut mutants = Vec::new();
    for (owner, prefix_n) in [(417_791usize, 417_792usize), (417_792, 417_793)] {
        assert_eq!(source.compact_n_bits(prefix_n).unwrap(), 0x066f98d5);
        let raws = (1..=prefix_n).map(|height| {
            let raw = source.raw(height)?;
            if height == prefix_n {
                let mut header = Header::decode(raw, None)
                    .map_err(|error| format!("FixedV2 mutant decode: {error:?}"))?;
                header.n_bits = 0x066f98d4;
                Ok(header
                    .encode()
                    .map_err(|error| format!("FixedV2 mutant encode: {error:?}"))?)
            } else {
                Ok(raw.to_vec())
            }
        });
        let mutant = NativePrefix::from_raw_iter(prefix_n, raws)
            .unwrap_or_else(|error| panic!("FixedV2 owner{owner} mutant prefix: {error}"));
        let plan = compile_plan(prefix_n as u64, mutant.root(), mutant.total_be28());
        let producer = NativeOwnerProducer::new_for_history(&plan, &mutant).unwrap();
        let exports = crate::native_owner_exports::NativeExports::new_for_history(&plan, &mutant)
            .unwrap();
        let row = producer.produce(owner).unwrap();
        assert_eq!(row.class(), crate::daa_history_roster::OwnerClass::FixedV2);
        let error = expect_error(validate_native_row_for_history_test(
            &plan,
            &mutant,
            &row,
            |wire| exports.bit(wire),
        ));
        assert!(error.contains(&format!("DAA/{owner}")), "owner{owner}: {error}");
        mutants.push(serde_json::json!({
            "owner":owner,
            "prefix_n":prefix_n,
            "mutated_last_n_bits":"066F98D4",
            "first_error":error,
        }));
    }
    assert_eq!(mutants.len(), 2);
    assert!(mutants.iter().any(|record| record["owner"] == 417_791));
    assert!(mutants.iter().any(|record| record["owner"] == 417_792));
    let result = serde_json::json!({
        "schema":"native-history-fixed-v2-mutants-v1",
        "expected_n":expected_n,
        "expected_size":expected_size,
        "blake2b256":expected_blake.to_ascii_uppercase(),
        "mutants":mutants,
    });
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(output_path)
        .expect("create new FixedV2 mutant output");
    output.write_all(&serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    output.sync_all().unwrap();
}

#[test]
fn replacement_mask_preserves_small_plans_and_admits_the_two_owner_window() {
    for headers in [3u64, 4] {
        let small = compile_plan(headers, [0x31; 32], [0x42; 28]);
        let old = small.assignment_replacement_mask().unwrap();
        let direct = small.physical_assignment_replacement_mask(0).unwrap();
        assert_eq!(old, direct);
        assert_eq!(old.len(), WIDTH);
        assert_eq!(old.iter().filter(|bit| **bit).count(), 401_362);
    }

    let large = compile_plan(3073, prefix().root(), prefix().total_be28());
    assert!(large.assignment_replacement_mask().is_err());
    let first = large.physical_assignment_replacement_mask(3071).unwrap();
    let second = large.physical_assignment_replacement_mask(3072).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.iter().filter(|bit| **bit).count(), 401_362);
    assert!(first[991_232..999_424].iter().all(|bit| !bit));
    assert!(large.physical_assignment_replacement_mask(4096).is_err());

    let boundary = large.header_boundary().canonical_circuit();
    let mask = &second;
    let retired_old_anchor = boundary
        .terms
        .iter()
        .find(|term| {
            let wire = term.gate.left;
            (917_772..983_040).contains(&wire)
                && mask[wire]
                && term.gate.right == 0
                && term.gate.c0.is_zero()
                && term.gate.c1 == Fr::one()
                && term.gate.c2.is_zero()
                && term.gate.c3.is_zero()
                && term.row == 274_980 + (wire - 917_772)
        })
        .expect("retired old zero anchor overlaps a replaced coordinate");
    assert_eq!(retired_old_anchor.gate.c1, Fr::one());
}

#[test]
fn native_m1_pair_satisfies_selected_consumers_and_packed_roundtrips() {
    let input = prefix();
    let plan = assembly_plan();
    let (prepared_result, calls) = m1_assemble_with_reader(|_, value| Ok(value));
    let prepared = prepared_result.unwrap();
    assert_eq!(prepared.first_owner(), 2047);
    assert_eq!(prepared.owner_count(), 2);
    assert_eq!(prepared.packed_bytes().len(), 2 * (WIDTH / 8));
    assert_eq!(prepared.row_bytes(2047).unwrap().len(), WIDTH / 8);
    assert_eq!(prepared.row_bytes(2048).unwrap().len(), WIDTH / 8);
    assert!(prepared.row_bytes(2047).unwrap() != prepared.row_bytes(2048).unwrap());

    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(plan).unwrap();
    assert_eq!(
        roster.owner_class(2047).unwrap(),
        crate::daa_history_roster::OwnerClass::Carry
    );
    assert_eq!(
        roster.owner_class(2048).unwrap(),
        crate::daa_history_roster::OwnerClass::M1
    );
    let profile = crate::work_tree_fixed_hash::FixedProfile::new(3073, input.root()).unwrap();
    assert_eq!(
        profile.role(2047).unwrap(),
        FixedRole::Node {
            level: 1,
            position: 2047
        }
    );
    assert_eq!(
        profile.role(2048).unwrap(),
        FixedRole::Node {
            level: 2,
            position: 0
        }
    );
    assert_eq!(
        plan.leaf_profile().role(2047).unwrap(),
        crate::work_tree_leaf_hash::Role::Genuine
    );
    assert_eq!(
        plan.leaf_profile().role(2048).unwrap(),
        crate::work_tree_leaf_hash::Role::Genuine
    );
    let schedule = crate::daa_header_window::for_child_height(2049).unwrap();
    assert_eq!(schedule.sample_heights(), &[1024, 2048]);
    assert_eq!(input.header(2049).unwrap().height, 2049);
    assert_eq!(input.header(2050).unwrap().height, 2050);
    let parent_id: [u8; 32] = Blake2b::<U32>::digest(input.raw(2048).unwrap()).into();
    assert_eq!(input.header(2049).unwrap().parent_id, parent_id);

    let receipt = prepared.receipt();
    assert!(
        receipt.foreign_census >= 8_372,
        "M1 foreign B1 header support must be present"
    );
    assert!(receipt.foreign_census <= MAX_M1_EXTERNAL_CELLS);
    assert_eq!(receipt.external_cells, calls.len());
    assert_eq!(receipt.foreign_census, calls.len());
    let actual_groups = receipt.groups.iter().cloned().collect::<BTreeMap<_, _>>();
    assert_eq!(
        actual_groups.len(),
        receipt.groups.len(),
        "group names are unique"
    );
    assert_eq!(actual_groups, m1_expected_group_counts(plan, &roster));
    for owner in [2047, 2048] {
        for kind in ["Header", "DAA", "Leaf", "Fixed", "Work"] {
            assert!(actual_groups
                .get(&format!("{kind}/{owner}"))
                .is_some_and(|terms| *terms > 0));
        }
    }
    assert!(actual_groups
        .iter()
        .any(|(name, terms)| name.starts_with("Topology/") && *terms > 0));
    assert!(actual_groups
        .iter()
        .any(|(name, terms)| name.starts_with("WorkLink/") && *terms > 0));

    let carry = prepared.row_bytes(2047).unwrap();
    let m1 = prepared.row_bytes(2048).unwrap();
    for (start, end) in crate::daa_history_roster::BANKS {
        assert!((start..end).all(|wire| !byte_bit(carry, wire)));
    }
    let m1_image = 819_200..827_392;
    assert!((m1_image.clone()).any(|wire| byte_bit(m1, wire)));
    assert_eq!(crate::daa_history_roster::BANKS[2], (819_200, 851_968));
    assert!((crate::daa_history_roster::BANKS[2].0..m1_image.start)
        .chain(m1_image.end..crate::daa_history_roster::BANKS[2].1)
        .all(|wire| !byte_bit(m1, wire)));

    let replacement = plan.physical_assignment_replacement_mask(2048).unwrap();
    let retired_old_anchor = plan
        .header_boundary()
        .canonical_circuit()
        .terms
        .iter()
        .any(|term| {
            let wire = term.gate.left;
            (917_772..983_040).contains(&wire)
                && replacement[wire]
                && term.row == 274_980 + wire - 917_772
                && term.gate.right == 0
                && term.gate.c0.is_zero()
                && term.gate.c1 == Fr::one()
                && term.gate.c2.is_zero()
                && term.gate.c3.is_zero()
                && byte_bit(m1, wire)
        });
    assert!(
        retired_old_anchor,
        "M1 must activate a replaced retired old-anchor coordinate"
    );

    let directory = PathBuf::from(
        std::env::var_os(OWNER_ASSEMBLY_ARTIFACT_ENV)
            .expect("runner must supply NIPOPOW_OWNER_ASSEMBLY_ARTIFACT_DIR"),
    );
    assert!(
        directory.is_dir(),
        "runner artifact directory must already exist"
    );
    assert!(
        fs::read_dir(&directory).unwrap().next().is_none(),
        "runner artifact directory must be fresh"
    );
    let groups_json = receipt
        .groups
        .iter()
        .map(|(name, terms)| format!("{{\"name\":\"{name}\",\"terms\":{terms}}}"))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "{{\"first_owner\":{},\"owners\":{},\"external_cells\":{},\"foreign_census\":{},\"packed_bytes\":{},\"root\":\"{}\",\"total\":\"{}\",\"groups\":[{}]}}",
        prepared.first_owner(),
        prepared.owner_count(),
        receipt.external_cells,
        receipt.foreign_census,
        prepared.packed_bytes().len(),
        hex_upper(&input.root()),
        hex_upper(&input.total_be28()),
        groups_json,
    );
    let path = directory.join("owners-log21.packed");
    assert!(!path.exists());
    let packed = prepared.write_new(&path).unwrap();
    assert_eq!(packed.input_len(), 1 << 21);
    let reopened = crate::packed::PackedFile::open(&path, 21).unwrap();
    for (row, owner) in [(0usize, 2047u64), (1, 2048)] {
        let decoded = crate::packed_rows::read_row(&reopened, WIDTH, row).unwrap();
        let expected = prepared.row_bytes(owner).unwrap();
        assert_eq!(decoded.len(), WIDTH);
        for (wire, value) in decoded.iter().enumerate() {
            assert!(value.is_zero() || value.is_one());
            assert_eq!(
                value.is_one(),
                byte_bit(expected, wire),
                "owner {owner} wire {wire}"
            );
        }
    }
    drop(reopened);
    drop(packed);
    let original_file = fs::read(&path).unwrap();
    assert!(
        prepared.write_new(&path).is_err(),
        "create-new collision must fail"
    );
    assert_eq!(
        fs::read(&path).unwrap(),
        original_file,
        "collision preserves existing bytes"
    );
}

#[test]
fn m1_rejects_mutated_foreign_sample_timestamp() {
    let owner = 1023usize; // RAW/header height 1024 is outside the selected 2047/2048 pair.
    let wire = owner * WIDTH + SERIALIZER_OFFSET + serializer().layout.fields.timestamp[0];
    let mut observed = false;
    let (result, _) = m1_assemble_with_reader(|index, value| {
        if index == wire {
            observed = true;
            Ok(!value)
        } else {
            Ok(value)
        }
    });
    assert!(
        observed,
        "timestamp mutant must hit a consumed foreign coordinate"
    );
    let error = expect_error(result);
    assert!(
        error.contains("retarget producer RAW port mismatch"),
        "{error}"
    );
}

#[test]
fn m1_rejects_mutated_foreign_second_leaf_raw() {
    let wire = 2049 * WIDTH
        + work_tree_layout::shared_baseline()
            .unwrap()
            .header_alias_wires[0];
    let mut observed = false;
    let (result, _) = m1_assemble_with_reader(|index, value| {
        if index == wire {
            observed = true;
            Ok(!value)
        } else {
            Ok(value)
        }
    });
    assert!(
        observed,
        "RAW2050 B1 mutant must hit a consumed foreign coordinate"
    );
    let error = expect_error(result);
    assert!(
        error.contains("Topology/header_to_leaf_raw_length_nbits_height"),
        "{error}"
    );
}

#[test]
fn m1_rejects_inactive_complement_bit() {
    let wire = crate::daa_history_roster::BANKS[2].1 - 1;
    let error = m1_fault_error(AssemblyFault::FlipBit { owner: 2048, wire });
    assert!(error.contains("DAA/2048"), "{error}");
}

#[test]
fn m1_rejects_coherent_l1_child_mutation() {
    let input = prefix();
    let mut reads = HashSet::new();
    let provider = foreign_provider();
    let result = assemble_m1_window_fault_for_test(
        assembly_plan(),
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        AssemblyFault::FixedChildBit {
            owner: 2047,
            branch: 0,
            bit: 0,
        },
    );
    let error = expect_error(result);
    assert!(error.contains("Topology/"), "{error}");
}

#[test]
fn m1_rejects_conflicting_claim() {
    let wire = SERIALIZER_OFFSET + serializer().layout.fields.n_bits[0];
    let error = m1_fault_error(AssemblyFault::ConflictingClaim { owner: 2048, wire });
    assert!(error.contains("claim conflict"), "{error}");
}

#[test]
fn m1_rejects_missing_claim() {
    let wire = SERIALIZER_OFFSET + serializer().layout.fields.n_bits[0];
    let error = m1_fault_error(AssemblyFault::MissingClaim { owner: 2048, wire });
    assert!(error.contains("missing claim"), "{error}");
}

#[test]
fn m1_rejects_non_boolean_claim() {
    let wire = SERIALIZER_OFFSET + serializer().layout.fields.n_bits[0];
    let error = m1_fault_error(AssemblyFault::NonBooleanClaim { owner: 2048, wire });
    assert!(error.contains("non-Boolean"), "{error}");
}

#[test]
fn m1_rejects_claim_outside_selected_pair() {
    let wire = SERIALIZER_OFFSET + serializer().layout.fields.n_bits[0];
    let error = m1_fault_error(AssemblyFault::ConflictingClaim { owner: 3072, wire });
    assert!(error.contains("claim outside selected owners"), "{error}");
}

#[test]
fn m1_rejects_unadmitted_plan_before_callback() {
    let input = prefix();
    let bad_plans = [
        compile_plan(3072, input.root(), input.total_be28()),
        compile_plan(3073, [0x71; 32], input.total_be28()),
        compile_plan(3073, input.root(), [0x42; 28]),
    ];
    for plan in &bad_plans {
        let mut called = false;
        let result = assemble_m1_window(plan, input, |_| {
            called = true;
            Ok(false)
        });
        assert!(result.is_err());
        assert!(!called, "plan admission must fail before foreign reads");
    }
}

#[test]
fn selected_census_rejects_cap_overflow_and_namespace() {
    let m1 = foreign_census_for_test(true, 0..MAX_M1_EXTERNAL_CELLS).unwrap();
    assert_eq!(m1.len(), MAX_M1_EXTERNAL_CELLS);
    let m1_overflow = expect_error(foreign_census_for_test(true, 0..MAX_M1_EXTERNAL_CELLS + 1));
    assert!(
        m1_overflow.contains("foreign census exceeds 16384"),
        "{m1_overflow}"
    );

    let m2 = foreign_census_for_test(false, 0..MAX_EXTERNAL_CELLS).unwrap();
    assert_eq!(m2.len(), MAX_EXTERNAL_CELLS);
    let m2_overflow = expect_error(foreign_census_for_test(false, 0..MAX_EXTERNAL_CELLS + 1));
    assert!(
        m2_overflow.contains("foreign census exceeds 8192"),
        "{m2_overflow}"
    );

    let outside = 4096 * WIDTH;
    let m1_namespace = expect_error(foreign_census_for_test(true, [outside]));
    assert!(
        m1_namespace.contains("consumer read outside admitted namespace"),
        "{m1_namespace}"
    );
    let m2_namespace = expect_error(foreign_census_for_test(false, [outside]));
    assert!(
        m2_namespace.contains("consumer read outside admitted namespace"),
        "{m2_namespace}"
    );
}

#[test]
fn native_pair_satisfies_selected_consumers_and_packed_roundtrips() {
    let input = prefix();
    let plan = assembly_plan();
    let support = external_support_for_test(plan, input, false).unwrap();
    let registry = M2ProducerRegistry::from_support(input, &support).unwrap();
    let registry_digest = registry.digest();
    assert!(!registry_digest.is_empty());
    println!("m2_producer_registry_digest={registry_digest}");
    let mut callback_calls = 0usize;
    let prepared =
        assemble_after_registry_preflight(&registry, &support, plan, input, &mut callback_calls)
            .unwrap();

    assert_eq!(prepared.first_owner(), 3071);
    assert_eq!(prepared.owner_count(), 2);
    assert_eq!(prepared.packed_bytes().len(), 2 * (WIDTH / 8));
    assert_eq!(prepared.row_bytes(3071).unwrap().len(), WIDTH / 8);
    assert_eq!(prepared.row_bytes(3072).unwrap().len(), WIDTH / 8);
    let receipt = prepared.receipt();
    assert!(receipt.foreign_census <= MAX_EXTERNAL_CELLS);
    assert_eq!(receipt.foreign_census, support.len());
    assert_eq!(receipt.external_cells, support.len());
    assert_eq!(receipt.foreign_census, support.len());
    assert!(callback_calls > 0);
    let groups_json = receipt
        .groups
        .iter()
        .map(|(name, terms)| format!("{{\"name\":\"{name}\",\"terms\":{terms}}}"))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "{{\"first_owner\":{},\"owners\":{},\"external_cells\":{},\"foreign_census\":{},\"packed_bytes\":{},\"root\":\"{}\",\"total\":\"{}\",\"groups\":[{}]}}",
        prepared.first_owner(),
        prepared.owner_count(),
        receipt.external_cells,
        receipt.foreign_census,
        prepared.packed_bytes().len(),
        hex_upper(&input.root()),
        hex_upper(&input.total_be28()),
        groups_json,
    );
    for required in [
        "Header/3071",
        "Header/3072",
        "DAA/3071",
        "DAA/3072",
        "Leaf/3071",
        "Leaf/3072",
        "Fixed/3071",
        "Fixed/3072",
        "Work/3071",
        "Work/3072",
    ] {
        assert!(
            receipt
                .groups
                .iter()
                .any(|(name, terms)| name == required && *terms > 0),
            "{required}"
        );
    }
    assert!(receipt
        .groups
        .iter()
        .any(|(name, terms)| name.starts_with("Topology/") && *terms > 0));
    assert!(receipt
        .groups
        .iter()
        .any(|(name, terms)| name.starts_with("WorkLink/") && *terms > 0));

    let carry = prepared.row_bytes(3071).unwrap();
    let m2 = prepared.row_bytes(3072).unwrap();
    for (start, end) in crate::daa_history_roster::BANKS {
        assert!((start..end).all(|wire| !byte_bit(carry, wire)));
    }
    assert!(crate::daa_history_roster::BANKS
        .iter()
        .any(|(start, end)| (*start..*end).any(|wire| byte_bit(m2, wire))));

    let replacement = plan.physical_assignment_replacement_mask(3072).unwrap();
    let retired_anchor_violation =
        plan.header_boundary()
            .canonical_circuit()
            .terms
            .iter()
            .any(|term| {
                let wire = term.gate.left;
                (917_772..983_040).contains(&wire)
                    && replacement[wire]
                    && term.row == 274_980 + wire - 917_772
                    && term.gate.right == 0
                    && term.gate.c0.is_zero()
                    && term.gate.c1 == Fr::one()
                    && term.gate.c2.is_zero()
                    && term.gate.c3.is_zero()
                    && byte_bit(m2, wire)
            });
    assert!(
        retired_anchor_violation,
        "a removed old zero anchor must differ in the joined native owner"
    );

    let directory = PathBuf::from(
        std::env::var_os(OWNER_ASSEMBLY_ARTIFACT_ENV)
            .expect("runner must supply NIPOPOW_OWNER_ASSEMBLY_ARTIFACT_DIR"),
    );
    assert!(
        directory.is_dir(),
        "runner artifact directory must already exist"
    );
    assert!(
        fs::read_dir(&directory).unwrap().next().is_none(),
        "runner artifact directory must be fresh"
    );
    let path = directory.join("owners-log21.packed");
    assert!(!path.exists());
    let packed = prepared.write_new(&path).unwrap();
    assert_eq!(packed.input_len(), 1 << 21);
    let reopened = crate::packed::PackedFile::open(&path, 21).unwrap();
    for (row, owner) in [(0usize, 3071u64), (1, 3072)] {
        let decoded = crate::packed_rows::read_row(&reopened, WIDTH, row).unwrap();
        let expected = prepared.row_bytes(owner).unwrap();
        assert_eq!(decoded.len(), WIDTH);
        for (wire, value) in decoded.iter().enumerate() {
            assert!(value.is_zero() || value.is_one());
            assert_eq!(
                value.is_one(),
                byte_bit(expected, wire),
                "owner {owner} wire {wire}"
            );
        }
    }
    drop(reopened);
    drop(packed);
}

#[test]
fn m2_producer_registry_fails_closed_before_consumer_write() {
    let input = prefix();
    let plan = assembly_plan();
    let support = external_support_for_test(plan, input, false).unwrap();
    assert_eq!(support.len(), 7418);
    let registry = M2ProducerRegistry::from_support(input, &support).unwrap();
    assert!(!registry.digest().is_empty());
    let missing_wire = *support.iter().next().unwrap();
    let destination = vec![0xa5u8; PACKED_OWNER_BYTES];
    let before = destination.clone();
    let output = std::env::temp_dir().join(format!(
        "nipopow-v2-m2-registry-negative-{}.packed",
        std::process::id()
    ));
    if output.exists() {
        std::fs::remove_file(&output).unwrap();
    }

    let mut missing = registry.clone();
    missing.remove_for_test(missing_wire).unwrap();
    let mut missing_callbacks = 0usize;
    let missing_result =
        assemble_after_registry_preflight(&missing, &support, plan, input, &mut missing_callbacks);
    assert!(missing_result.is_err());
    assert_eq!(missing_callbacks, 0);
    assert_eq!(destination, before);
    assert!(!output.exists());

    let key = registry.key_for(missing_wire).unwrap();
    let value = *registry.values.get(&key).unwrap();
    let mut value_conflict = registry.clone();
    assert!(value_conflict.register(key, !value).is_err());
    assert_eq!(destination, before);
    assert!(!output.exists());

    let mut identity_conflict = registry.clone();
    let mut alternate = key;
    alternate.producer = alternate.producer.saturating_add(1);
    assert!(identity_conflict.register(alternate, value).is_err());
    assert_eq!(destination, before);

    let serializer_local = SERIALIZER_OFFSET + serializer().circuit.input_len;
    assert!(registry
        .read(missing_wire / WIDTH * WIDTH + serializer_local)
        .is_err());
    let endpoint_after = work_tree_layout::ENDPOINT_BASE + work_tree_layout::ENDPOINT_WIDTH;
    assert!(registry
        .read(missing_wire / WIDTH * WIDTH + endpoint_after)
        .is_err());
    let unsupported_internal = work_tree_layout::shared_baseline().unwrap().endpoints.count[0];
    assert!(registry
        .read(missing_wire / WIDTH * WIDTH + unsupported_internal)
        .is_err());
    assert_eq!(destination, before);
    assert!(!output.exists());

    let cap_result = foreign_census_for_test(false, 0..MAX_EXTERNAL_CELLS + 1);
    assert!(cap_result.is_err());
    assert_eq!(destination, before);
}

#[test]
fn m2_nonlocal_edge_stream_matches_canonical_family_emitter_for_selected_owners() {
    let plan = assembly_plan();
    let (slot_bits, base_row_bits, family_bits, member_row_bits) =
        m2_nonlocal_edge_geometry(plan).unwrap();
    assert_eq!(slot_bits, 12);
    assert!(!member_row_bits.is_empty());
    assert!(base_row_bits >= member_row_bits.iter().copied().max().unwrap());
    assert!(family_bits < usize::BITS as usize);

    let selected = [3071usize, 3072usize];
    let mut actual_by_side = Vec::new();
    let mut expected_by_side = Vec::new();
    for &left in &[true, false] {
        let mut actual = vec![Vec::<Vec<u8>>::new(); member_row_bits.len()];
        for &slot in &selected {
            visit_m2_nonlocal_edge_endpoint(plan, left, slot, &mut |edge| {
                let family = edge.family_row >> base_row_bits;
                assert!(family < member_row_bits.len());
                let global = sparse_stream_roster::global_edge_row(
                    edge.source_slot,
                    edge.family_row,
                    slot_bits,
                    base_row_bits,
                    family_bits,
                    &member_row_bits,
                )
                .unwrap();
                assert!(global < 1usize << (base_row_bits + slot_bits + family_bits));
                let endpoint = if left {
                    edge.term.gate.left
                } else {
                    edge.term.gate.right
                };
                assert_eq!(endpoint / WIDTH, slot);
                actual[family].push(canonical_edge_bytes(
                    &edge,
                    slot_bits,
                    base_row_bits,
                    family_bits,
                    &member_row_bits,
                ));
                Ok(())
            })
            .unwrap();
        }

        let mut expected = vec![Vec::<Vec<u8>>::new(); member_row_bits.len()];
        let mut family_index = 0usize;
        let mut collect = |family: &crate::work_tree_wiring::Family| {
            let index = family_index;
            let local_bits = member_row_bits[index];
            let stride = 1usize << local_bits;
            family
                .emit_terms(plan.descriptor(), |term| {
                    let endpoint = if left {
                        term.gate.left
                    } else {
                        term.gate.right
                    };
                    if selected.contains(&(endpoint / WIDTH)) {
                        let source_slot = term.gate.left / WIDTH;
                        let local_row = term.row % stride;
                        let edge = EdgeTerm {
                            source_slot,
                            family_row: (index << base_row_bits) | local_row,
                            term,
                        };
                        expected[index].push(canonical_edge_bytes(
                            &edge,
                            slot_bits,
                            base_row_bits,
                            family_bits,
                            &member_row_bits,
                        ));
                    }
                    Ok(())
                })
                .unwrap();
            family_index += 1;
        };
        for family in &plan.topology().families {
            collect(family);
        }
        for family in plan.work_boundary().links() {
            collect(family);
        }
        assert_eq!(family_index, member_row_bits.len());
        actual_by_side.push(actual);
        expected_by_side.push(expected);
    }

    for side in 0..2 {
        let actual = &actual_by_side[side];
        let expected = &expected_by_side[side];
        for family in 0..member_row_bits.len() {
            assert_eq!(
                actual[family].len(),
                expected[family].len(),
                "side {side} family {family}"
            );
            assert_eq!(
                edge_digest(actual[family].clone()),
                edge_digest(expected[family].clone()),
                "side {side} family {family}"
            );
        }
    }
    assert!(
        visit_m2_nonlocal_edge_endpoint(plan, true, 1usize << slot_bits, &mut |_| Ok(())).is_err()
    );
    let wrong_shape = compile_plan(3072, prefix().root(), prefix().total_be28());
    assert!(m2_nonlocal_edge_geometry(&wrong_shape)
        .unwrap_err()
        .contains("requires N3073/S12"));
    println!(
        "m2_nonlocal_edge_stream: families={}, left_terms={}, right_terms={}",
        member_row_bits.len(),
        actual_by_side[0].iter().map(Vec::len).sum::<usize>(),
        actual_by_side[1].iter().map(Vec::len).sum::<usize>()
    );
}

#[test]
fn assembly_faults_reject_before_returning_a_packed_window() {
    let input = prefix();
    let plan = assembly_plan();
    let provider = foreign_provider();
    let wire = SERIALIZER_OFFSET + serializer().layout.fields.n_bits[0];
    let mut reads = HashSet::new();
    let result = assemble_window_fault_for_test(
        plan,
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        AssemblyFault::ConflictingClaim { owner: 3072, wire },
    );
    assert!(expect_error(result).contains("claim conflict"));

    reads.clear();
    let missing = assemble_window_fault_for_test(
        plan,
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        AssemblyFault::MissingClaim { owner: 3072, wire },
    );
    assert!(expect_error(missing).contains("missing claim"));

    reads.clear();
    let non_boolean = assemble_window_fault_for_test(
        plan,
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        AssemblyFault::NonBooleanClaim { owner: 3072, wire },
    );
    assert!(expect_error(non_boolean).contains("non-Boolean"));

    let bad_plan = compile_plan(3073, prefix().root(), [0x7b; 28]);
    let mut should_not_read = false;
    let mismatch = assemble_window(&bad_plan, input, |_| {
        should_not_read = true;
        Ok(false)
    });
    assert!(expect_error(mismatch).contains("root/total mismatch"));
    assert!(!should_not_read);
}

#[test]
fn assembly_rejects_padding_header_alias_fault() {
    let input = prefix();
    let plan = assembly_plan();
    let provider = foreign_provider();
    let mut reads = HashSet::new();
    let padding_wire = work_tree_layout::Endpoints::new().raw[0];
    let padding = assemble_window_fault_for_test(
        plan,
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        AssemblyFault::FlipBit {
            owner: 3072,
            wire: padding_wire,
        },
    );
    let padding_error = expect_error(padding);
    assert!(
        padding_error.contains("Topology/padding_leaf_unused_header_aliases"),
        "{padding_error}"
    );
}

#[test]
fn assembly_rejects_padding_aux_zero_fault() {
    let wire = crate::work_tree_leaf_hash::AUX;
    let error = rejected_fault(AssemblyFault::FlipBit { owner: 3072, wire });
    assert!(error.contains("Leaf/3072"), "{error}");
}

#[test]
fn assembly_rejects_padding_work_zero_fault() {
    let wire = work_tree_layout::Endpoints::new().work[0];
    let error = rejected_fault(AssemblyFault::FlipBit { owner: 3072, wire });
    assert!(error.contains("Work/3072"), "{error}");
}

#[test]
fn assembly_rejects_endpoint_bank_padding_zero_fault() {
    let wire = work_tree_layout::ENDPOINT_BASE + work_tree_layout::Endpoints::new().used;
    assert!(wire < work_tree_layout::ENDPOINT_BASE + work_tree_layout::ENDPOINT_WIDTH);
    let error = rejected_fault(AssemblyFault::FlipBit { owner: 3072, wire });
    assert!(error.contains("Topology/endpoint_bank_padding"), "{error}");
}

#[test]
fn assembly_rejects_protected_header_count_zero_fault() {
    let wire = work_tree_layout::Endpoints::new().count[0];
    let error = rejected_fault(AssemblyFault::FlipBit { owner: 3072, wire });
    assert!(error.contains("Header/3072"), "{error}");
}

#[test]
fn assembly_rejects_native_exponent_zero_fault() {
    let wire = work_tree_layout::Endpoints::new().exponent[0];
    let error = rejected_fault(AssemblyFault::FlipBit { owner: 3071, wire });
    assert!(error.contains("Work/3071"), "{error}");
}

#[test]
fn assembly_rejects_m2_daa_bit_fault() {
    let input = prefix();
    let plan = assembly_plan();
    let provider = foreign_provider();
    let mut reads = HashSet::new();
    let daa_wire = crate::daa_history_roster::BANKS[0].0;
    let daa = assemble_window_fault_for_test(
        plan,
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        AssemblyFault::FlipBit {
            owner: 3072,
            wire: daa_wire,
        },
    );
    let daa_error = expect_error(daa);
    assert!(daa_error.contains("DAA/3072"), "{daa_error}");
}

fn assert_carry_bank_zero_fault(bank: usize) {
    let (wire, end) = crate::daa_history_roster::BANKS[bank];
    assert!(wire < end);
    if bank == 3 {
        // Header rejects A4 first in the joined path. Check the complete
        // independent lane-3 row as well, without claiming it ran later there.
        let roster = crate::daa_history_roster::DaaHistoryRoster::compile(assembly_plan()).unwrap();
        let before: usize = crate::daa_history_roster::BANKS[..3]
            .iter()
            .map(|(start, end)| end - start)
            .sum();
        let row = (3071 << crate::daa_history_roster::SLOT_ROW_LOG)
            + (3 << crate::daa_history_roster::LOCAL_ROW_LOG)
            + before;
        let mut terms = Vec::new();
        roster
            .visit_owner_terms(3071, |term| {
                if term.row == row {
                    terms.push(term);
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(terms.len(), 1, "complete inactive A4 row");
        let gate = &terms[0].gate;
        assert_eq!(gate.left, 3071 * WIDTH + wire);
        assert_eq!(gate.right, 3071 * WIDTH);
        assert_eq!(gate.c0, Fr::zero());
        assert_eq!(gate.c1, Fr::one());
        assert_eq!(gate.c2, Fr::zero());
        assert_eq!(gate.c3, Fr::zero());
        assert_eq!(gate.c0 + gate.c1 * Fr::zero(), Fr::zero());
        assert_eq!(gate.c0 + gate.c1 * Fr::one(), Fr::one());
    }
    let error = rejected_fault(AssemblyFault::FlipBit { owner: 3071, wire });
    let expected = if bank == 3 { "Header/3071" } else { "DAA/3071" };
    assert!(error.contains(expected), "bank {bank}: {error}");
}

#[test]
fn assembly_rejects_carry_bank0_zero_fault() {
    assert_carry_bank_zero_fault(0);
}

#[test]
fn assembly_rejects_carry_bank1_zero_fault() {
    assert_carry_bank_zero_fault(1);
}

#[test]
fn assembly_rejects_carry_bank2_zero_fault() {
    assert_carry_bank_zero_fault(2);
}

#[test]
fn assembly_rejects_carry_bank3_zero_fault() {
    assert_carry_bank_zero_fault(3);
}

#[test]
fn assembly_propagates_foreign_reader_failure() {
    let input = prefix();
    let mut reads = 0usize;
    let result = assemble_window(assembly_plan(), input, |_| {
        reads += 1;
        Err("injected foreign read failure".into())
    });
    assert_eq!(
        reads, 1,
        "reader failure must stop on the first foreign cell"
    );
    assert!(expect_error(result).contains("injected foreign read failure"));
}

#[test]
fn assembly_rejects_mutated_foreign_b1_raw_cell() {
    let input = prefix();
    let provider = foreign_provider();
    let raw_bit = crate::work_tree_layout::Endpoints::new().raw[0];
    let foreign_wire = 3070 * WIDTH + raw_bit;
    let mut observed = false;
    let result = assemble_window(assembly_plan(), input, |wire| {
        let value = provider.bit(wire, input)?;
        if wire == foreign_wire {
            observed = true;
            Ok(!value)
        } else {
            Ok(value)
        }
    });
    assert!(
        observed,
        "the falsifier must change a consumed foreign support cell"
    );
    let error = expect_error(result);
    assert!(
        error.contains("Topology/header_to_leaf_raw_length_nbits_height"),
        "{error}"
    );
}

#[test]
fn assembly_rejects_fixed_child_digest_mutation_at_topology() {
    let input = prefix();
    let plan = assembly_plan();
    let provider = foreign_provider();
    let mut reads = HashSet::new();
    let result = assemble_window_fault_for_test(
        plan,
        input,
        |index| {
            if !reads.insert(index) {
                return Err(format!("duplicate foreign read {index}"));
            }
            provider.bit(index, input)
        },
        AssemblyFault::FixedChildBit {
            owner: 3072,
            branch: 0,
            bit: 0,
        },
    );
    let error = expect_error(result);
    assert!(error.contains("Topology/"), "{error}");
}

#[test]
fn native_window16_writes_immutable_file_and_reads_all_rows() {
    let started = std::time::Instant::now();
    let input = prefix();
    let plan = assembly_plan();
    let producer = NativeOwnerProducer::new(plan, input).unwrap();
    let preparation_ns = started.elapsed().as_nanos();
    let directory =
        native_window_artifact_dir("native_window16_writes_immutable_file_and_reads_all_rows");
    let path = directory.join("owners-log24.packed");
    let mut row_receipts = Vec::new();
    let mut production_ns = 0u128;
    let window =
        crate::packed_owner_assembly::write_native_window_for_test(&producer, &path, 16, |owner| {
            let production_started = std::time::Instant::now();
            let row = producer.produce(owner)?;
            production_ns += production_started.elapsed().as_nanos();
            if row.owner() != owner || row.packed_bytes().len() != PACKED_OWNER_BYTES {
                return Err(format!("test expected complete native row {owner}"));
            }
            row_receipts.push(serde_json::json!({
                "owner": row.owner(),
                "class": format!("{:?}", row.class()),
                "bytes": row.packed_bytes().len(),
                "blake2b256": hex_upper(&Blake2b::<U32>::digest(row.packed_bytes())),
            }));
            Ok(row)
        })
        .unwrap();
    assert_eq!(std::mem::size_of::<Fr>(), 32);
    assert_eq!(window.source.input_len(), 1 << 24);
    assert_eq!(fs::metadata(&path).unwrap().len(), 1 << 21);
    assert_eq!(row_receipts.len(), 16);
    for (owner, receipt) in row_receipts.iter().enumerate() {
        assert_eq!(receipt["owner"], owner);
        assert_eq!(
            receipt["class"],
            format!(
                "{:?}",
                crate::daa_history_roster::DaaHistoryRoster::compile(plan)
                    .unwrap()
                    .owner_class(owner as u64)
                    .unwrap()
            )
        );
    }

    let immutable_bytes = fs::read(&path).unwrap();
    let mut read_ns = 0u128;
    for owner in 0..16usize {
        let read_started = std::time::Instant::now();
        let values = crate::packed_rows::read_row(&window.source, WIDTH, owner).unwrap();
        read_ns += read_started.elapsed().as_nanos();
        assert_eq!(values.len(), WIDTH);
        assert!(values.iter().all(|value| value.is_zero() || value.is_one()));
        let start = owner * PACKED_OWNER_BYTES;
        let bytes = &immutable_bytes[start..start + PACKED_OWNER_BYTES];
        let mut decoded_bytes = vec![0u8; PACKED_OWNER_BYTES];
        for (wire, value) in values.iter().enumerate() {
            assert_eq!(
                value.is_one(),
                byte_bit(bytes, wire),
                "original owner {owner}, wire {wire}"
            );
            if value.is_one() {
                decoded_bytes[wire / 8] |= 1 << (wire % 8);
            }
        }
        assert_eq!(
            hex_upper(&Blake2b::<U32>::digest(&decoded_bytes)),
            row_receipts[owner]["blake2b256"],
            "reader row {owner} must match the produced native row digest"
        );
    }
    let source_io = window.source.io_metrics_snapshot();
    assert_eq!(source_io.read_calls, 256);
    assert_eq!(source_io.read_bytes, 2 * 1024 * 1024);

    let original_file = immutable_bytes;
    let file_hash = hex_upper(&Blake2b::<U32>::digest(&original_file));
    let mut collision_callbacks = 0usize;
    let collision =
        crate::packed_owner_assembly::write_native_window_for_test(&producer, &path, 16, |owner| {
            collision_callbacks += 1;
            producer.produce(owner)
        });
    assert!(collision.is_err(), "create-new collision must fail");
    assert_eq!(
        collision_callbacks, 0,
        "collision must fail before production"
    );
    assert_eq!(
        fs::read(&path).unwrap(),
        original_file,
        "collision preserves bytes"
    );

    let result = serde_json::json!({
        "schema": "native-owner-window16-result-v1",
        "root": hex_upper(&input.root()),
        "total": hex_upper(&input.total_be28()),
        "owners": row_receipts,
        "packed_bytes": original_file.len(),
        "packed_blake2b256": file_hash,
        "preparation_ns": preparation_ns,
        "production_ns": production_ns,
        "collector_callback_ns": window.production_ns,
        "write_ns": window.write_ns,
        "finish_ns": window.finish_ns,
        "readback_ns": read_ns,
        "fr_bytes": std::mem::size_of::<Fr>(),
        "reader_calls": source_io.read_calls,
        "reader_bytes": source_io.read_bytes,
        "reader": "packed_rows::read_row; 16 chunks per 2^20-field row",
        "collision_callbacks": collision_callbacks,
        "global_proof": false,
    });
    println!("{}", result);
    fs::write(
        directory.join("stablewindow-result.json"),
        serde_json::to_vec_pretty(&result).unwrap(),
    )
    .unwrap();
}

#[test]
fn native_window16_collector_rejects_invalid_rows() {
    let input = prefix();
    let plan = assembly_plan();
    let producer = NativeOwnerProducer::new(plan, input).unwrap();
    let directory = native_window_artifact_dir("native_window16_collector_rejects_invalid_rows");
    let mut observed = Vec::new();

    for owner_count in [0usize, 15, 17, 4096] {
        let path = directory.join(format!("shape-{owner_count}.packed"));
        let mut callbacks = 0usize;
        let result = crate::packed_owner_assembly::write_native_window_for_test(
            &producer,
            &path,
            owner_count,
            |_| {
                callbacks += 1;
                producer.produce(0)
            },
        );
        assert!(expect_error(result).contains("requires original owners 0..16"));
        assert_eq!(callbacks, 0, "invalid shape must reject before callback");
        assert!(
            !path.exists(),
            "invalid shape must reject before file creation"
        );
        observed.push(serde_json::json!({"shape":owner_count,"callbacks":callbacks,"file_exists":path.exists()}));
    }

    let cases = [
        "wrong-owner",
        "late-duplicate-owner",
        "root",
        "total",
        "class",
        "length",
        "callback-failure",
    ];
    for case in cases {
        let path = directory.join(format!("{case}.packed"));
        let mut callbacks = 0usize;
        let result = crate::packed_owner_assembly::write_native_window_for_test(
            &producer,
            &path,
            16,
            |owner| {
                callbacks += 1;
                if case == "callback-failure" && owner == 4 {
                    return Err("injected row producer failure".into());
                }
                let produced_owner = if case == "wrong-owner" && owner == 0 {
                    1
                } else if case == "late-duplicate-owner" && owner == 3 {
                    2
                } else {
                    owner
                };
                let mut row = producer.produce(produced_owner)?;
                let fault = match case {
                    "root" if owner == 3 => {
                        Some(crate::packed_owner_assembly::NativeRowFileFault::Root)
                    }
                    "total" if owner == 3 => {
                        Some(crate::packed_owner_assembly::NativeRowFileFault::Total)
                    }
                    "class" if owner == 3 => {
                        Some(crate::packed_owner_assembly::NativeRowFileFault::Class)
                    }
                    "length" if owner == 3 => {
                        Some(crate::packed_owner_assembly::NativeRowFileFault::Length)
                    }
                    _ => None,
                };
                if let Some(fault) = fault {
                    row = crate::packed_owner_assembly::native_row_file_fault_for_test(row, fault);
                }
                Ok(row)
            },
        );
        let error = expect_error(result);
        match case {
            "wrong-owner" | "late-duplicate-owner" => {
                assert!(error.contains("original owner mismatch"), "{error}")
            }
            "root" => assert!(error.contains("root/total mismatch"), "{error}"),
            "total" => assert!(error.contains("root/total mismatch"), "{error}"),
            "class" => assert!(error.contains("class mismatch"), "{error}"),
            "length" => assert!(error.contains("row length mismatch"), "{error}"),
            "callback-failure" => {
                assert!(error.contains("injected row producer failure"), "{error}")
            }
            _ => unreachable!(),
        }
        assert!(!path.exists(), "failed collector left a file for {case}");
        let expected_callbacks = if case == "wrong-owner" {
            1
        } else if case == "callback-failure" {
            5
        } else {
            4
        };
        assert_eq!(
            callbacks, expected_callbacks,
            "callback boundary for {case}"
        );
        observed.push(serde_json::json!({"case":case,"error":error,"callbacks":callbacks,"file_exists":path.exists()}));
    }

    let result = serde_json::json!({
        "schema": "native-owner-window16-guards-v1",
        "cases": observed,
        "all_failed_outputs_absent": true,
    });
    fs::write(
        directory.join("window-guards-result.json"),
        serde_json::to_vec_pretty(&result).unwrap(),
    )
    .unwrap();
}

#[test]
fn native_window16_full_split_samples_resolve_native_rows() {
    let input = prefix();
    let plan = assembly_plan();
    let producer = NativeOwnerProducer::new(plan, input).unwrap();
    let topology = plan.topology();
    let engine = work_tree_fixed_hash::engine().unwrap();
    let leaf_boundary = plan.leaf_boundary();
    let work_boundary = plan.work_boundary();
    let representatives = [0usize, 1, 2, 1024, 2048, 3072, 3073, 4095];
    let directory =
        native_window_artifact_dir("native_window16_full_split_samples_resolve_native_rows");
    let mut resolver = NativePackedRowCache::new(&producer, plan);

    let local_member_bits =
        crate::work_tree_wiring::full_split_local_tensor_member_row_bits(topology, work_boundary)
            .unwrap();
    let local_base_bits = *local_member_bits.iter().max().unwrap();
    let (local_input_bits, _, _, _) =
        crate::work_tree_wiring::full_split_local_tensor_dimensions(topology, work_boundary)
            .unwrap();
    let local_input_width = 1usize << local_input_bits;
    let mut local_terms = 0usize;
    let mut local_groups = 0usize;
    for slot in representatives {
        let mut residuals = BTreeMap::<usize, Fr>::new();
        crate::work_tree_wiring::full_split_visit_local_slot_terms(
            topology,
            engine,
            plan.fixed_profile(),
            leaf_boundary,
            work_boundary,
            slot,
            &mut |term| {
                let family = term.row >> local_base_bits;
                let row_mask = (1usize << local_base_bits) - 1;
                assert!(family < local_member_bits.len());
                assert!((term.row & row_mask) < 1usize << local_member_bits[family]);
                let left = if !term.gate.c1.is_zero() || !term.gate.c3.is_zero() {
                    assert!(
                        term.gate.left < local_input_width,
                        "active local left operand bounds"
                    );
                    let wire = slot * WIDTH + term.gate.left;
                    resolver.ensure_owner(slot)?;
                    Fr::from(resolver.bit(wire)? as u64)
                } else {
                    Fr::zero()
                };
                let right = if !term.gate.c2.is_zero() || !term.gate.c3.is_zero() {
                    assert!(
                        term.gate.right < local_input_width,
                        "active local right operand bounds"
                    );
                    let wire = slot * WIDTH + term.gate.right;
                    resolver.ensure_owner(slot)?;
                    Fr::from(resolver.bit(wire)? as u64)
                } else {
                    Fr::zero()
                };
                *residuals.entry(term.row).or_insert_with(Fr::zero) += term.gate.c0
                    + term.gate.c1 * left
                    + term.gate.c2 * right
                    + term.gate.c3 * left * right;
                local_terms += 1;
                Ok(())
            },
        )
        .unwrap();
        assert!(
            residuals.values().all(Zero::is_zero),
            "local full-split slot {slot}"
        );
        local_groups += residuals.len();
    }

    let cross_member_bits =
        crate::work_tree_wiring::full_split_cross_tensor_member_row_bits(topology, work_boundary)
            .unwrap();
    let cross_base_bits = *cross_member_bits.iter().max().unwrap();
    let (cross_input_bits, cross_slot_bits, _, cross_family_bits) =
        crate::work_tree_wiring::full_split_cross_tensor_dimensions(topology, work_boundary)
            .unwrap();
    let cross_input_width = 1usize << cross_input_bits;
    let cross_topology_families = topology
        .families
        .iter()
        .filter(|family| {
            !matches!(
                &family.mapping,
                crate::work_tree_wiring::Mapping::Same { .. }
            )
        })
        .collect::<Vec<_>>();
    let profile_family_index = cross_topology_families
        .iter()
        .position(|family| family.name == "profile_digest_fanout")
        .expect("profile digest family must remain in the cross roster");
    let endpoint_padding_family_index = cross_topology_families
        .iter()
        .position(|family| family.name == "endpoint_bank_padding")
        .expect("endpoint padding family must remain in the cross roster");
    let leaf_alias_family_index = cross_topology_families
        .iter()
        .position(|family| family.name == "padding_leaf_unused_header_aliases")
        .expect("padding leaf alias family must remain in the cross roster");
    let endpoint_padding_terms_per_owner =
        work_tree_layout::ENDPOINT_WIDTH - work_tree_layout::Endpoints::new().used;
    let header_alias_terms_per_owner = work_tree_layout::Endpoints::new().header_aliases().len();
    let leaf_alias_source_count = topology.descriptor.leaves - topology.descriptor.genuine;
    let leaf_alias_full_terms = leaf_alias_source_count * header_alias_terms_per_owner;
    let leaf_alias_sampled_sources = representatives
        .iter()
        .filter(|owner| (topology.descriptor.genuine..topology.descriptor.leaves).contains(*owner))
        .count();
    let mut cross_terms = 0usize;
    let mut cross_groups = 0usize;
    let mut identity_digest = Blake2b::<U32>::new();
    let mut mutant_candidate: Option<(usize, usize, usize, usize, crate::sparse::Term)> = None;
    let mut profile_right_full_terms = 0usize;
    let mut profile_right_sampled_terms = 0usize;
    let mut profile_right_skipped_terms = 0usize;
    let mut endpoint_padding_right_full_terms = 0usize;
    let mut endpoint_padding_right_sampled_terms = 0usize;
    let mut endpoint_padding_right_skipped_terms = 0usize;
    let mut leaf_alias_right_full_terms = 0usize;
    let mut leaf_alias_right_sampled_terms = 0usize;
    let mut leaf_alias_right_skipped_terms = 0usize;
    for endpoint in representatives {
        for left_endpoint in [true, false] {
            let mut residuals = BTreeMap::<usize, Fr>::new();
            crate::work_tree_wiring::full_split_visit_cross_endpoint_terms(
                topology,
                work_boundary,
                left_endpoint,
                endpoint,
                &mut |source_slot, family_row, term| {
                    let family = family_row >> cross_base_bits;
                    let row_mask = (1usize << cross_base_bits) - 1;
                    assert!(family < cross_member_bits.len());
                    assert!((family_row & row_mask) < 1usize << cross_member_bits[family]);
                    let global_row = crate::sparse_stream_roster::global_edge_row(
                        source_slot,
                        family_row,
                        cross_slot_bits,
                        cross_base_bits,
                        cross_family_bits,
                        &cross_member_bits,
                    )?;
                    if !left_endpoint && endpoint == 4095 && family == profile_family_index {
                        profile_right_full_terms += 1;
                        if !representatives.contains(&source_slot) {
                            profile_right_skipped_terms += 1;
                            return Ok(());
                        }
                        profile_right_sampled_terms += 1;
                    }
                    if !left_endpoint && endpoint == 0 && family == endpoint_padding_family_index {
                        endpoint_padding_right_full_terms += 1;
                        if !representatives.contains(&source_slot) {
                            endpoint_padding_right_skipped_terms += 1;
                            return Ok(());
                        }
                        endpoint_padding_right_sampled_terms += 1;
                    }
                    if !left_endpoint && endpoint == 0 && family == leaf_alias_family_index {
                        leaf_alias_right_full_terms += 1;
                        if !representatives.contains(&source_slot) {
                            leaf_alias_right_skipped_terms += 1;
                            return Ok(());
                        }
                        leaf_alias_right_sampled_terms += 1;
                    }
                    identity_digest.update((source_slot as u64).to_le_bytes());
                    identity_digest.update((family_row as u64).to_le_bytes());
                    identity_digest.update((global_row as u64).to_le_bytes());
                    let (left_value, left) = if !term.gate.c1.is_zero() || !term.gate.c3.is_zero() {
                        assert!(
                            term.gate.left < 4096 * WIDTH,
                            "active cross left operand bounds"
                        );
                        assert!(
                            term.gate.left % WIDTH < cross_input_width,
                            "active cross left local bounds"
                        );
                        let owner = term.gate.left / WIDTH;
                        assert_eq!(
                            owner, source_slot,
                            "cross source_slot must retain left-row identity"
                        );
                        if left_endpoint {
                            assert_eq!(owner, endpoint, "left endpoint owner mismatch");
                        }
                        resolver.ensure_owner(owner)?;
                        let value = resolver.bit(term.gate.left)?;
                        (Some(value), Fr::from(value as u64))
                    } else {
                        (None, Fr::zero())
                    };
                    let (right_value, right) = if !term.gate.c2.is_zero() || !term.gate.c3.is_zero()
                    {
                        assert!(
                            term.gate.right < 4096 * WIDTH,
                            "active cross right operand bounds"
                        );
                        assert!(
                            term.gate.right % WIDTH < cross_input_width,
                            "active cross right local bounds"
                        );
                        let owner = term.gate.right / WIDTH;
                        if !left_endpoint {
                            assert_eq!(owner, endpoint, "right endpoint owner mismatch");
                        }
                        resolver.ensure_owner(owner)?;
                        let value = resolver.bit(term.gate.right)?;
                        (Some(value), Fr::from(value as u64))
                    } else {
                        (None, Fr::zero())
                    };
                    *residuals.entry(global_row).or_insert_with(Fr::zero) += term.gate.c0
                        + term.gate.c1 * left
                        + term.gate.c2 * right
                        + term.gate.c3 * left * right;
                    if mutant_candidate.is_none()
                        && left_endpoint
                        && term.gate.c0.is_zero()
                        && term.gate.c1 == Fr::one()
                        && term.gate.c2 == -Fr::one()
                        && term.gate.c3.is_zero()
                        && term.gate.left != term.gate.right
                        && left_value == right_value
                        && term.gate.right / WIDTH != endpoint
                    {
                        mutant_candidate = Some((
                            endpoint,
                            source_slot,
                            family_row,
                            term.gate.right,
                            term.clone(),
                        ));
                    }
                    cross_terms += 1;
                    Ok(())
                },
            )
            .unwrap();
            assert!(
                residuals.values().all(Zero::is_zero),
                "cross full-split endpoint {endpoint}, left={left_endpoint}"
            );
            cross_groups += residuals.len();
        }
    }
    assert_eq!(profile_right_full_terms, 4096 * 256);
    assert_eq!(profile_right_sampled_terms, 8 * 256);
    assert_eq!(
        profile_right_skipped_terms,
        profile_right_full_terms - profile_right_sampled_terms
    );
    assert_eq!(
        endpoint_padding_right_full_terms,
        4096 * endpoint_padding_terms_per_owner
    );
    assert_eq!(
        endpoint_padding_right_sampled_terms,
        8 * endpoint_padding_terms_per_owner
    );
    assert_eq!(
        endpoint_padding_right_skipped_terms,
        endpoint_padding_right_full_terms - endpoint_padding_right_sampled_terms
    );
    assert_eq!(leaf_alias_right_full_terms, leaf_alias_full_terms);
    assert_eq!(
        leaf_alias_right_sampled_terms,
        leaf_alias_sampled_sources * header_alias_terms_per_owner
    );
    assert_eq!(
        leaf_alias_right_skipped_terms,
        leaf_alias_right_full_terms - leaf_alias_right_sampled_terms
    );

    let mut bounds_cache = NativePackedRowCache::new(&producer, plan);
    assert!(bounds_cache
        .bit(4096 * WIDTH)
        .unwrap_err()
        .contains("outside original slot domain"));
    assert!(
        bounds_cache
            .bit(WIDTH + 1)
            .unwrap_err()
            .contains("not loaded"),
        "cache misses must fail rather than read as zero"
    );
    let (mutant_endpoint, mutant_source_slot, mutant_family_row, mutant_wire, mutant_term) =
        mutant_candidate
            .expect("sampled cross consumer must expose a consumed foreign equality bit");
    assert_ne!(mutant_wire / WIDTH, mutant_endpoint);
    assert_eq!(mutant_source_slot, mutant_term.gate.left / WIDTH);
    let mut mutant_cache = NativePackedRowCache::new(&producer, plan);
    mutant_cache
        .ensure_owner(mutant_term.gate.left / WIDTH)
        .unwrap();
    mutant_cache
        .ensure_owner(mutant_term.gate.right / WIDTH)
        .unwrap();
    let left = Fr::from(mutant_cache.bit(mutant_term.gate.left).unwrap() as u64);
    let right = Fr::from(mutant_cache.bit(mutant_term.gate.right).unwrap() as u64);
    assert_eq!(
        left, right,
        "selected equality is satisfied before mutation"
    );
    mutant_cache.flip(mutant_wire).unwrap();
    let mutant_left = Fr::from(mutant_cache.bit(mutant_term.gate.left).unwrap() as u64);
    let mutant_right = Fr::from(mutant_cache.bit(mutant_term.gate.right).unwrap() as u64);
    let mutated_residual = mutant_term.gate.c0
        + mutant_term.gate.c1 * mutant_left
        + mutant_term.gate.c2 * mutant_right
        + mutant_term.gate.c3 * mutant_left * mutant_right;
    assert!(
        !mutated_residual.is_zero(),
        "consumed foreign bit mutant must violate its exact row"
    );
    let mutant_global_row = crate::sparse_stream_roster::global_edge_row(
        mutant_source_slot,
        mutant_family_row,
        cross_slot_bits,
        cross_base_bits,
        cross_family_bits,
        &cross_member_bits,
    )
    .unwrap();

    let cache_receipt = resolver.receipt();
    let result = serde_json::json!({
        "schema": "native-full-split-consumer-samples-v1",
        "representatives": representatives,
        "local_terms": local_terms,
        "local_groups_checked": local_groups,
        "cross_terms": cross_terms,
        "cross_groups_checked": cross_groups,
        "source_slot_family_row_blake2b256": hex_upper(&identity_digest.finalize()),
        "profile_right_full_terms": profile_right_full_terms,
        "profile_right_sampled_terms": profile_right_sampled_terms,
        "profile_right_skipped_terms": profile_right_skipped_terms,
        "profile_right_full_check": false,
        "endpoint_padding_right_full_terms": endpoint_padding_right_full_terms,
        "endpoint_padding_right_sampled_terms": endpoint_padding_right_sampled_terms,
        "endpoint_padding_right_skipped_terms": endpoint_padding_right_skipped_terms,
        "endpoint_padding_right_full_check": false,
        "padding_leaf_alias_right_full_terms": leaf_alias_right_full_terms,
        "padding_leaf_alias_right_sampled_terms": leaf_alias_right_sampled_terms,
        "padding_leaf_alias_right_skipped_terms": leaf_alias_right_skipped_terms,
        "padding_leaf_alias_right_full_check": false,
        "actual_native_rows_cached": cache_receipt.0,
        "native_cache_bytes": cache_receipt.1,
        "cache_row_cap": 128,
        "cache_byte_cap": 16 * 1024 * 1024,
        "bounds_negative": "rejected outside 4096 original slots",
        "missing_owner_negative": "rejected unloaded original owner without zero fallback",
        "consumed_bit_mutant_wire": mutant_wire,
        "consumed_bit_mutant_row": mutant_global_row,
        "consumed_bit_mutant_residual": mutated_residual.to_string(),
        "gkr": false,
        "full_mle_claim": false,
    });
    fs::write(
        directory.join("consumer-result.json"),
        serde_json::to_vec_pretty(&result).unwrap(),
    )
    .unwrap();
    println!("{}", result);
}

#[test]
fn native_owner_production_phase_cost_is_measured_without_changing_rows() {
    use crate::daa_history_roster::OwnerClass;

    const WINDOW_ENV: &str = "NIPOPOW_NATIVE_PROFILE_WINDOW_FILE";
    const WINDOW_BYTES: usize = 2 * 1024 * 1024;
    const WINDOW_SHA256: &str = "5771F251321B9A1EB5B7B8438F822DC54DC79668EBD1D66443B2983C3CC9F2FF";
    const OWNERS: [(usize, OwnerClass); 8] = [
        (0, OwnerClass::Genesis),
        (1, OwnerClass::Initial),
        (2, OwnerClass::Carry),
        (1024, OwnerClass::Singleton),
        (2048, OwnerClass::M1),
        (
            3072,
            OwnerClass::Short(crate::short_daa_layout::Profile::M2),
        ),
        (3073, OwnerClass::Padding),
        (4095, OwnerClass::Padding),
    ];

    let preparation_started = std::time::Instant::now();
    let input = prefix();
    let plan = assembly_plan();
    let producer = NativeOwnerProducer::new(plan, input).unwrap();
    let exports = crate::native_owner_exports::NativeExports::new(plan, input).unwrap();
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(plan).unwrap();
    let preparation_ns = preparation_started.elapsed().as_nanos();

    let window_path = PathBuf::from(
        std::env::var_os(WINDOW_ENV).expect("runner must provide the pinned Window16 file"),
    );
    let window_bytes = fs::read(&window_path).expect("read pinned Window16 source");
    assert_eq!(window_bytes.len(), WINDOW_BYTES);
    let directory = native_window_artifact_dir(
        "native_owner_production_phase_cost_is_measured_without_changing_rows",
    );
    let endpoints = &work_tree_layout::shared_baseline().unwrap().endpoints;
    let mut endpoint_wires = Vec::new();
    for ports in [
        &endpoints.raw,
        &endpoints.length,
        &endpoints.n_bits,
        &endpoints.height,
        &endpoints.lower,
        &endpoints.upper,
        &endpoints.work,
        &endpoints.exponent,
        &endpoints.work_minus_one,
        &endpoints.leaf,
        &endpoints.node_left,
        &endpoints.node_right,
        &endpoints.node,
        &endpoints.profile,
    ] {
        endpoint_wires.extend(ports.iter().copied());
    }

    let mut rows_json = Vec::with_capacity(OWNERS.len());
    let mut rows_by_owner = BTreeMap::new();
    let mut validation_ns = 0u128;
    for (owner, expected_class) in OWNERS {
        let (row, timings) = producer.produce_profile_for_test(owner).unwrap();
        let row_validation_started = std::time::Instant::now();
        assert_eq!(row.owner(), owner);
        assert_eq!(row.class(), expected_class);
        assert_eq!(row.packed_bytes().len(), PACKED_OWNER_BYTES);
        assert_eq!(roster.owner_class(owner as u64).unwrap(), expected_class);
        assert_eq!(plan.descriptor().root, input.root());
        assert_eq!(plan.work_profile().total_be28, input.total_be28());

        for &wire in &endpoint_wires {
            assert_eq!(
                exports.bit(owner * WIDTH + wire).unwrap(),
                byte_bit(row.packed_bytes(), wire),
                "owner{owner} endpoint{wire}"
            );
        }
        let receipt =
            validate_native_row_for_test(plan, input, &row, |wire| exports.bit(wire)).unwrap();
        assert_eq!(receipt.groups.len(), 5);
        assert!(receipt.external_cells <= receipt.foreign_census);

        if owner < 3 {
            let start = owner * PACKED_OWNER_BYTES;
            let end = start + PACKED_OWNER_BYTES;
            assert_eq!(
                row.packed_bytes(),
                &window_bytes[start..end],
                "owner{owner} must match the immutable Window16 file"
            );
        }
        validation_ns = validation_ns
            .checked_add(row_validation_started.elapsed().as_nanos())
            .expect("validation timing sum must not overflow");

        let phases: [(&str, u128); 12] = [
            ("allocation_ns", timings.allocation_ns),
            ("header_fields_ns", timings.header_fields_ns),
            ("header_boundary_ns", timings.header_boundary_ns),
            ("header_order_ns", timings.header_order_ns),
            ("header_claims_ns", timings.header_claims_ns),
            ("tree_ns", timings.tree_ns),
            ("pack_initial_ns", timings.pack_initial_ns),
            ("retarget_ns", timings.retarget_ns),
            ("bank_claims_ns", timings.bank_claims_ns),
            ("completeness_ns", timings.completeness_ns),
            ("pack_final_ns", timings.pack_final_ns),
            ("total_ns", timings.total_ns),
        ];
        assert!(timings.total_ns > 0, "owner{owner} missing total timing");
        assert_eq!(
            timings.retarget_ns > 0,
            matches!(expected_class, OwnerClass::M1 | OwnerClass::Short(_)),
            "owner{owner} retarget branch timing"
        );
        let phase_sum_ns = phases[..11]
            .iter()
            .try_fold(0u128, |sum, (_, ns)| sum.checked_add(*ns))
            .expect("phase timing sum must not overflow");
        assert!(
            phase_sum_ns <= timings.total_ns,
            "owner{owner} phase overlap"
        );
        let mut phase_values = serde_json::Map::new();
        for (name, ns) in phases {
            let json_ns = u64::try_from(ns).expect("phase timing must fit JSON integer");
            phase_values.insert(name.to_owned(), serde_json::json!(json_ns));
        }
        let digest = hex_upper(&Blake2b::<U32>::digest(row.packed_bytes()));
        rows_json.push(serde_json::json!({
            "owner": owner,
            "class": format!("{:?}", expected_class),
            "bytes": row.packed_bytes().len(),
            "blake2b256": digest,
            "phases": phase_values,
            "phase_sum_ns": u64::try_from(phase_sum_ns).unwrap(),
            "unaccounted_ns": u64::try_from(timings.total_ns - phase_sum_ns).unwrap(),
            "validated_local_families": receipt.groups.len(),
            "validated_cores": 11,
        }));
        rows_by_owner.insert(owner, row.packed_bytes().to_vec());
    }
    let differential_started = std::time::Instant::now();
    for owner in [2usize, 3073] {
        let profiled = rows_by_owner.get(&owner).expect("profiled row retained");
        let unprofiled = producer.produce(owner).unwrap();
        assert_eq!(unprofiled.owner(), owner);
        assert_eq!(unprofiled.packed_bytes(), profiled.as_slice());
    }
    let differential_ns = differential_started.elapsed().as_nanos();

    let result = serde_json::json!({
        "schema": "native-owner-phase-cost-v1",
        "preparation_ns": u64::try_from(preparation_ns).expect("preparation timing fits JSON"),
        "validation_ns": u64::try_from(validation_ns).expect("validation timing fits JSON"),
        "differential_ns": u64::try_from(differential_ns).expect("differential timing fits JSON"),
        "window_source": {
            "bytes": window_bytes.len(),
            "sha256": WINDOW_SHA256,
            "checked_owners": [0, 1, 2],
        },
        "differential_owners": [2, 3073],
        "rows": rows_json,
        "global_proof": false,
        "full_native_incidence": false,
        "full_header_adjacency": false,
        "gkr": false,
        "full_mle_claim": false,
    });
    let json_path = directory.join("native-phase-result.json");
    fs::write(&json_path, serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    println!("{}", result);
}

fn native_window_artifact_dir(name: &str) -> PathBuf {
    let root = PathBuf::from(
        std::env::var_os(OWNER_ASSEMBLY_ARTIFACT_ENV)
            .expect("runner must supply NIPOPOW_OWNER_ASSEMBLY_ARTIFACT_DIR"),
    );
    assert!(
        !root.exists(),
        "runner artifact root must be absent for fresh test {name}"
    );
    fs::create_dir(&root).unwrap();
    root
}

struct NativePackedRowCache<'p, 'a> {
    producer: &'p NativeOwnerProducer<'a>,
    plan: &'p WorkTreeHistoryPlan,
    rows: BTreeMap<usize, Vec<u8>>,
}

impl<'p, 'a> NativePackedRowCache<'p, 'a> {
    fn new(producer: &'p NativeOwnerProducer<'a>, plan: &'p WorkTreeHistoryPlan) -> Self {
        Self {
            producer,
            plan,
            rows: BTreeMap::new(),
        }
    }

    fn ensure_owner(&mut self, owner: usize) -> Result<(), String> {
        self.producer.require_unadapted_cache_for_test()?;
        if owner >= 4096 {
            return Err(format!(
                "native owner outside original slot domain: {owner}"
            ));
        }
        if self.rows.contains_key(&owner) {
            return Ok(());
        }
        const ROW_CAP: usize = 128;
        const BYTE_CAP: usize = 16 * 1024 * 1024;
        if self.rows.len() >= ROW_CAP || (self.rows.len() + 1) * PACKED_OWNER_BYTES > BYTE_CAP {
            return Err("native full-split row cache bound exceeded".into());
        }
        let row = self.producer.produce(owner)?;
        if row.owner() != owner
            || row.class()
                != crate::daa_history_roster::DaaHistoryRoster::compile(self.plan)?
                    .owner_class(owner as u64)?
            || row.packed_bytes().len() != PACKED_OWNER_BYTES
        {
            return Err(format!(
                "native packed row metadata mismatch at owner {owner}"
            ));
        }
        self.rows.insert(owner, row.packed_bytes().to_vec());
        Ok(())
    }

    fn bit(&self, global_wire: usize) -> Result<bool, String> {
        self.producer.require_unadapted_cache_for_test()?;
        if global_wire >= 4096 * WIDTH {
            return Err(format!(
                "native coordinate outside original slot domain: {global_wire}"
            ));
        }
        let owner = global_wire / WIDTH;
        let row = self
            .rows
            .get(&owner)
            .ok_or_else(|| format!("native owner row not loaded: {owner}"))?;
        let local = global_wire % WIDTH;
        Ok(byte_bit(row, local))
    }

    fn flip(&mut self, global_wire: usize) -> Result<(), String> {
        if global_wire == 0 || global_wire >= 4096 * WIDTH {
            return Err("native mutant coordinate outside original slot domain".into());
        }
        let owner = global_wire / WIDTH;
        let row = self
            .rows
            .get_mut(&owner)
            .ok_or_else(|| format!("native owner row not loaded: {owner}"))?;
        let local = global_wire % WIDTH;
        row[local / 8] ^= 1 << (local % 8);
        Ok(())
    }

    fn receipt(&self) -> (usize, usize) {
        (self.rows.len(), self.rows.len() * PACKED_OWNER_BYTES)
    }
}

#[test]
#[ignore = "requires pinned N3073 fixture and fresh bounded artifact directory"]
fn native_owner_full_stream_n3073_physical_diagnostic() {
    use crate::daa_history_roster::OwnerClass;
    use crate::packed_owner_assembly::NativePhaseTimings;

    const ROWS: usize = 4096;
    const STREAM_BYTES: u64 = 536_870_912;
    const PHASE_NAMES: [&str; 12] = [
        "allocation_ns", "header_fields_ns", "header_boundary_ns", "header_order_ns",
        "header_claims_ns", "tree_ns", "pack_initial_ns", "retarget_ns",
        "bank_claims_ns", "completeness_ns", "pack_final_ns", "total_ns",
    ];
    fn ns(start: Instant) -> u64 {
        u64::try_from(start.elapsed().as_nanos()).expect("diagnostic nanoseconds fit u64")
    }
    fn phases(t: &NativePhaseTimings) -> [u128; 12] {
        [t.allocation_ns, t.header_fields_ns, t.header_boundary_ns, t.header_order_ns,
         t.header_claims_ns, t.tree_ns, t.pack_initial_ns, t.retarget_ns,
         t.bank_claims_ns, t.completeness_ns, t.pack_final_ns, t.total_ns]
    }
    fn class_name(owner: usize, actual: OwnerClass) -> &'static str {
        let (expected, name) = match owner {
            0 => (OwnerClass::Genesis, "Genesis"),
            1 => (OwnerClass::Initial, "Initial"),
            1024 => (OwnerClass::Singleton, "Singleton"),
            2048 => (OwnerClass::M1, "M1"),
            3072 => (OwnerClass::Short(crate::short_daa_layout::Profile::M2), "M2"),
            3073..=4095 => (OwnerClass::Padding, "Padding"),
            2..=3071 => (OwnerClass::Carry, "Carry"),
            _ => panic!("owner outside N3073/S12"),
        };
        assert_eq!(actual, expected, "owner {owner} native class");
        name
    }
    fn port_matches(bytes: &[u8], base: usize, expected: &[bool]) -> bool {
        base.checked_add(expected.len()).is_some_and(|end| end <= bytes.len() * 8)
            && expected.iter().enumerate().all(|(i, bit)| byte_bit(bytes, base + i) == *bit)
    }
    fn marker(text: &str) {
        let mut stdout = std::io::stdout().lock();
        writeln!(stdout, "{text}").unwrap();
        stdout.flush().unwrap();
    }

    let overall = Instant::now();
    marker("native_owner_full_stream start");
    let prepare_started = Instant::now();
    let fixture = fixture_dir().join("mainnet-prefix-first-3073-u32le-v1.bin");
    let (input, locked_reader) = read_native_history_file(
        &fixture, 3073, BUNDLE_BYTES as u64, BUNDLE_BLAKE2B256,
    ).expect("fixed locked N3073 native history");
    let plan = compile_plan(3073, input.root(), input.total_be28());
    assert_eq!(plan.headers(), 3073);
    assert_eq!(plan.slot_log(), 12);
    assert_eq!(plan.slots(), ROWS);
    validate_native_plan_input(&plan, &input).unwrap();
    let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
    producer.require_unadapted_cache_for_test().unwrap();
    let artifact = PathBuf::from(std::env::var(OWNER_ASSEMBLY_ARTIFACT_ENV)
        .expect("fresh diagnostic artifact directory required"));
    assert!(artifact.is_dir(), "caller must create the fresh artifact directory");
    assert_eq!(fs::read_dir(&artifact).unwrap().count(), 0, "artifact directory must be empty");
    let mut stream = OpenOptions::new().write(true).create_new(true)
        .open(artifact.join("stream.bits")).unwrap();
    let mut progress = OpenOptions::new().write(true).create_new(true)
        .open(artifact.join("progress.ndjson")).unwrap();
    let preparation_ns = ns(prepare_started);

    let probe_started = Instant::now();
    let ports = [
        ("D2048", 2048usize, 2046usize, 987_674usize, 224usize),
        ("D3008", 3008, 3006, 987_674, 224),
        ("T1024", 1024, 1023, 525_330, 64),
        ("T2048", 2048, 2047, 525_330, 64),
        ("T3008", 3008, 3007, 525_330, 64),
    ];
    let mut probes = Vec::with_capacity(5);
    for (name, height, owner, base, width) in ports {
        // Decode RAW independently of the factory's scalar export callbacks.
        let raw = input.raw(height).unwrap();
        let header = Header::decode(raw, None).unwrap();
        assert_eq!(header.height as usize, height);
        assert_eq!(header.encode().unwrap().as_slice(), raw);
        let expected: Vec<bool> = if width == 224 {
            let value = work_tree_work::native_decode(header.n_bits).unwrap();
            assert!(value.bits() <= 224);
            (0..224).map(|i| integer_bit(&value, i)).collect()
        } else {
            let timestamp = u64::try_from(header.timestamp).expect("native timestamp nonnegative");
            (0..64).map(|i| (timestamp >> i) & 1 != 0).collect()
        };
        let (row, _probe_phases) = producer.produce_profile_for_test(owner).unwrap();
        assert_eq!(row.owner(), owner);
        class_name(owner, row.class());
        assert_eq!(row.packed_bytes().len(), PACKED_OWNER_BYTES);
        assert!(port_matches(row.packed_bytes(), base, &expected), "{name} RAW port");
        let mut mutant = row.packed_bytes().to_vec();
        let bit = base + width - 1;
        mutant[bit / 8] ^= 1 << (bit % 8);
        assert!(!port_matches(&mutant, base, &expected), "{name} isolated bit mutant");
        drop(mutant);
        drop(row);
        probes.push(serde_json::json!({
            "name":name, "height":height, "owner":owner, "base":base, "width":width,
            "checked_bits":width, "mutant_rejected":true,
        }));
    }
    let probes_ns = ns(probe_started);
    marker(&format!("native_owner_full_stream probe-complete {}",
        serde_json::to_string(&probes).unwrap()));

    let mut phase_totals = [0u128; 12];
    let mut production_ns = 0u64;
    let mut write_ns = 0u64;
    let mut progress_ns = 0u64;
    let mut completed_bytes = 0u64;
    let mut progress_bytes = 0usize;
    let mut class_counts = BTreeMap::<&str, usize>::new();
    let mut write_hasher = Blake2b::<U32>::new();
    for owner in 0..ROWS {
        let generated = Instant::now();
        let (row, timing) = producer.produce_profile_for_test(owner).unwrap();
        production_ns = production_ns.checked_add(ns(generated)).unwrap();
        assert_eq!(row.owner(), owner);
        *class_counts.entry(class_name(owner, row.class())).or_default() += 1;
        assert_eq!(row.packed_bytes().len(), PACKED_OWNER_BYTES);
        for (total, part) in phase_totals.iter_mut().zip(phases(&timing)) {
            *total = total.checked_add(part).unwrap();
        }
        let written = Instant::now();
        stream.write_all(row.packed_bytes()).unwrap();
        write_ns = write_ns.checked_add(ns(written)).unwrap();
        write_hasher.update(row.packed_bytes());
        completed_bytes += PACKED_OWNER_BYTES as u64;
        drop(row);
        let progress_started = Instant::now();
        let record = serde_json::json!({
            "owner":owner, "rows":owner + 1, "bytes":completed_bytes,
            "generation_ns":production_ns, "write_ns":write_ns,
        });
        let mut line = serde_json::to_vec(&record).unwrap();
        line.push(b'\n');
        assert!(line.len() <= 224, "bounded progress record");
        progress_bytes = progress_bytes.checked_add(line.len()).unwrap();
        assert!(progress_bytes <= 1_048_576);
        progress.write_all(&line).unwrap();
        progress.flush().unwrap();
        progress_ns = progress_ns.checked_add(ns(progress_started)).unwrap();
    }
    assert_eq!(completed_bytes, STREAM_BYTES);
    assert_eq!(class_counts, BTreeMap::from([
        ("Genesis", 1), ("Initial", 1), ("Carry", 3068), ("Singleton", 1),
        ("M1", 1), ("M2", 1), ("Padding", 1023),
    ]));
    let synced = Instant::now();
    stream.sync_all().unwrap();
    progress.sync_all().unwrap();
    let sync_ns = ns(synced);
    drop(stream);
    drop(progress);
    let write_digest = hex_upper(&write_hasher.finalize());
    let readback_started = Instant::now();
    let mut readback = File::open(artifact.join("stream.bits")).unwrap();
    assert_eq!(readback.metadata().unwrap().len(), STREAM_BYTES);
    let mut readback_hasher = Blake2b::<U32>::new();
    let mut buffer = [0u8; 65_536];
    let mut read_bytes = 0u64;
    loop {
        let count = readback.read(&mut buffer).unwrap();
        if count == 0 { break; }
        read_bytes += count as u64;
        readback_hasher.update(&buffer[..count]);
    }
    assert_eq!(read_bytes, STREAM_BYTES);
    let readback_digest = hex_upper(&readback_hasher.finalize());
    assert_eq!(readback_digest, write_digest);
    let readback_ns = ns(readback_started);
    drop(readback);
    // Keep the authenticated input's deny-write/delete handle through readback.
    drop(locked_reader);
    let phase_ns: serde_json::Map<String, Value> = PHASE_NAMES.into_iter()
        .zip(phase_totals).map(|(name, value)|
            (name.to_owned(), Value::from(u64::try_from(value).unwrap()))).collect();
    let summary = serde_json::json!({
        "schema":"native-owner-full-stream-n3073-physical-v1",
        "headers":3073, "slot_log":12, "slots":ROWS, "rows":ROWS, "bytes":completed_bytes,
        "root_hex":hex_upper(&input.root()), "total_work_be28_hex":hex_upper(&input.total_be28()),
        "class_counts":class_counts, "probes":probes,
        "write_blake2b256":write_digest, "readback_blake2b256":readback_digest,
        "timing_ns":{
            "preparation":preparation_ns, "probes":probes_ns, "production":production_ns,
            "write":write_ns, "progress":progress_ns, "sync":sync_ns,
            "readback":readback_ns, "total":ns(overall),
        },
        "phase_ns":phase_ns,
    });
    let summary_bytes = serde_json::to_vec(&summary).unwrap();
    assert!(summary_bytes.len() <= 65_536);
    let mut summary_file = OpenOptions::new().write(true).create_new(true)
        .open(artifact.join("summary.json")).unwrap();
    summary_file.write_all(&summary_bytes).unwrap();
    summary_file.sync_all().unwrap();
    drop(summary_file);
    marker("native_owner_full_stream stream-complete");
}

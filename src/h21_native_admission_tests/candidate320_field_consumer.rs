//! C320 source-to-field diagnostic. Exact C319 pins are set; post-run review is pending.
//! This test-only consumer never builds X, emits challenges or admits B publicly.

use super::*;
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use serde::Deserialize;
use std::{fs, os::windows::fs::MetadataExt, path::Path};

const OWNERS: [usize; 4] = [1_810_840, 1_810_841, 1_810_902, 1_810_903];
const ROWS: [usize; 2] = [905_420, 905_451];
const FIXTURE_BYTES: usize = 524_288;
const OWNER_BYTES: usize = 131_072;
const ROW_BYTES: usize = 262_144;
const WIDTH: usize = 1 << 20;
const N: u64 = 1_827_840;
const TOTAL: &str = "2746808805241252741120";
const RAW_A: &[u8] = include_bytes!("../../fixtures/section3-A_control-checkpoint.raw");
const RAW_B: &[u8] = include_bytes!("../../fixtures/section3-B_candidate-checkpoint.raw");
// C319 Extract PASS pins; use only after the independent post-run review.
const C319_RUNNER_RECEIPT_SHA256: &str = "0ae8374f607f79691250c625c38d74a7f7cb659abda450859cd162dbb2724b3b";
const C319_RECEIPT_SHA256: &str = "e6b065cfced0ddb204dafa0ff16be68b48f8a2b4ce11791fe6e0835aadce093a";
const C319_FIXTURE_SHA256: &str = "e901b368a23b4356ca7752e4e9898583cecbc1c981b5ca19dd5c2676f848b65f";
const C319_SOURCE_CLOSURE_SHA256: &str = "5483945165731416c606fd351dfa3d18645e00add39857172fd42d5104050aac";
const C319_PARENT_ROOT: &str = "93f74871644f3644e8cca9579c353006cb12ff50064f82e7660ab5ac552a307b";
const C319_PARENT_PROFILE: &str = "436155070c22e58866c7f4a043eb1d3e714bbb24e67e82195663be05dbc9d9f3";

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Receipt {
    schema: String,
    status: String,
    mode: String,
    source_closure_sha256: String,
    parent: ParentReceipt,
    frame: FrameReceipt,
    fixture: FixtureReceipt,
    controls: Vec<ControlReceipt>,
    frame_seconds: f64,
    extract_seconds: f64,
    field_consumer_executed: bool,
    full_h21_witness: bool,
    pow_daa_validated: bool,
    proof_or_public_admission: bool,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FrameReceipt {
    bytes: u64,
    sha256: String,
    prefix_bytes: u64,
    tail_bytes: u64,
    extensions: u64,
    records: u64,
    anchor: u64,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ParentReceipt {
    n: u64,
    slot_log: usize,
    input_log: usize,
    width: usize,
    root: String,
    profile: String,
    total_be28: String,
    total_decimal: String,
    tip: u64,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FixtureReceipt {
    file: String,
    bytes: usize,
    sha256: String,
    popcount: u64,
    owners: Vec<OwnerReceipt>,
    rows: Vec<RowReceipt>,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct OwnerReceipt {
    owner: usize,
    sigma21_row: usize,
    half: usize,
    storage_slot: usize,
    class: String,
    bytes: usize,
    sha256: String,
    popcount: u64,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RowReceipt {
    row: usize,
    storage_slot: usize,
    owners: Vec<usize>,
    bytes: usize,
    sha256: String,
    popcount: u64,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ControlReceipt {
    label: String,
    h: usize,
    f: usize,
    depth: usize,
    header_owner: usize,
    floor_owner: usize,
    raw_bytes: usize,
    raw_sha256: String,
    floor_be28: String,
    floor_decimal: String,
    audit_decimal: String,
    source_bits_checked: usize,
}
#[derive(Clone)]
struct Admitted {
    receipt: Receipt,
    fixture: Vec<u8>,
}

fn hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{b:02x}")).collect() }
fn digest(bytes: &[u8]) -> Result<String, String> {
    Ok(hex(&crate::native_prefix_auth_plan::role0_sha256(bytes)?))
}
fn pending_pin(pin: &str) -> bool {
    pin.len() == 64 && pin.bytes().all(|b| b.is_ascii_hexdigit())
}
fn pin_hex(pin: &str) -> String { pin.to_ascii_lowercase() }
fn decode_hex<const N: usize>(value: &str) -> Result<[u8; N], String> {
    if value.len() != 2 * N { return Err("hex width".into()); }
    let mut out = [0; N];
    for (i, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let text = std::str::from_utf8(pair).map_err(|_| "hex encoding")?;
        out[i] = u8::from_str_radix(text, 16).map_err(|_| "hex encoding")?;
    }
    Ok(out)
}
fn regular(path: &Path, expected: Option<u64>) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.is_file() || meta.file_attributes() & 0x400 != 0
        || expected.is_some_and(|n| meta.len() != n)
        || (expected.is_none() && meta.len() > 65_536)
    {
        return Err("fixture input must be a regular non-reparse file".into());
    }
    Ok(())
}

fn validate_layout(r: &Receipt) -> Result<(), String> {
    if r.schema != "c319-h21-ab-native-extract-v1" || r.status != "EXTRACT_CHECKS_PASS"
        || r.mode != "extract-only" || r.source_closure_sha256.to_ascii_lowercase()
            != C319_SOURCE_CLOSURE_SHA256
        || r.field_consumer_executed || r.full_h21_witness || r.pow_daa_validated
        || r.proof_or_public_admission || !r.frame_seconds.is_finite()
        || !r.extract_seconds.is_finite() || r.frame_seconds < 0.0 || r.extract_seconds < 0.0
    { return Err("C319 receipt identity/source closure".into()); }
    let p = &r.parent;
    if p.n != N || p.slot_log != 21 || p.input_log != 41 || p.width != WIDTH || p.tip != N
        || p.root.to_ascii_lowercase() != pin_hex(C319_PARENT_ROOT)
        || p.profile.to_ascii_lowercase() != C319_PARENT_PROFILE
        || p.total_decimal != TOTAL || p.total_be28.len() != 56
    { return Err("C319 native parent identity".into()); }
    let total = decode_hex::<28>(&p.total_be28)?;
    if num_bigint::BigUint::from_bytes_be(&total).to_string() != TOTAL {
        return Err("C319 parent total decimal/bytes".into());
    }
    decode_hex::<32>(&p.root)?;
    let frame = &r.frame;
    if frame.bytes != FRAME_BYTES || frame.sha256.to_ascii_lowercase() != FRAME_SHA256
        || frame.prefix_bytes != PREFIX_BYTES || frame.tail_bytes != TAIL_BYTES
        || frame.extensions != EXTENSIONS || frame.records != N || frame.anchor != N - 1
    { return Err("C319 source frame receipt".into()); }
    if r.fixture.file != "c319-ab-sigma21.bin" || r.fixture.bytes != FIXTURE_BYTES
        || r.fixture.sha256.to_ascii_lowercase() != pin_hex(C319_FIXTURE_SHA256)
        || r.fixture.owners.len() != OWNERS.len() || r.fixture.rows.len() != ROWS.len()
    { return Err("C319 fixture typed identity".into()); }
    for (slot, (owner, item)) in OWNERS.iter().zip(&r.fixture.owners).enumerate() {
        if item.owner != *owner || item.sigma21_row != owner / 2 || item.half != owner % 2
            || item.storage_slot != slot || item.bytes != OWNER_BYTES || item.class != "Carry"
            || !pending_pin(&item.sha256)
        { return Err(format!("C319 owner row/half/slot mapping at {slot}")); }
    }
    for (slot, (row, item)) in ROWS.iter().zip(&r.fixture.rows).enumerate() {
        if item.row != *row || item.storage_slot != slot
            || item.owners != vec![row * 2, row * 2 + 1] || item.bytes != ROW_BYTES
            || !pending_pin(&item.sha256)
        { return Err(format!("C319 sigma row/owner mapping at {slot}")); }
    }
    let expected = [
        ("A", 1_810_842, 1_810_905, 1_810_841, 1_810_903, 220,
         "3af4be948ea36e8438ecb3dfcfe5863b55d8b760373cd9872c2a85b102f168dd",
         "2745402775092498268160", "1406030148754472960"),
        ("B", 1_810_841, 1_810_904, 1_810_840, 1_810_902, 220,
         "0f881c0d2546479acb69fd2970b75fb6e0789c0b28d0c515696f19da1bdef16d",
         "2745402699639720771584", "1406105601531969536"),
    ];
    if r.controls.len() != expected.len() { return Err("C319 A/B controls count".into()); }
    for (c, e) in r.controls.iter().zip(expected) {
        let floor_be28 = decode_hex::<28>(&c.floor_be28)?;
        let floor_dec = num_bigint::BigUint::from_bytes_be(&floor_be28).to_string();
        if c.label != e.0 || c.h != e.1 || c.f != e.2 || c.header_owner != e.3
            || c.floor_owner != e.4 || c.depth != 64 || c.raw_bytes != e.5
            || c.raw_sha256.to_ascii_lowercase() != e.6 || c.floor_decimal != e.7
            || floor_dec != c.floor_decimal || c.audit_decimal != e.8
            || c.source_bits_checked != 4346
        { return Err(format!("C319 {} typed control/owner mapping", e.0)); }
    }
    Ok(())
}

/// All custody and typed source mapping checks precede any fixture field read.
fn admit(directory: &Path) -> Result<Admitted, String> {
    let runner_receipt = directory.join("extract-receipt.json");
    regular(&runner_receipt, Some(2_989))?;
    if digest(&fs::read(&runner_receipt).map_err(|e| e.to_string())?)?.to_ascii_lowercase()
        != C319_RUNNER_RECEIPT_SHA256
    { return Err("C319 runner receipt digest".into()); }
    let fixture_dir = directory.join("fixture");
    let rp = fixture_dir.join("extraction.json");
    let fp = fixture_dir.join("c319-ab-sigma21.bin");
    regular(&rp, Some(3_939))?; regular(&fp, Some(FIXTURE_BYTES as u64))?;
    let receipt_bytes = fs::read(&rp).map_err(|e| e.to_string())?;
    if digest(&receipt_bytes)?.to_ascii_lowercase() != pin_hex(C319_RECEIPT_SHA256) {
        return Err("C319 extraction receipt digest".into());
    }
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes).map_err(|e| e.to_string())?;
    validate_layout(&receipt)?;
    let fixture = fs::read(&fp).map_err(|e| e.to_string())?;
    if fixture.len() != FIXTURE_BYTES || digest(&fixture)?.to_ascii_lowercase()
        != pin_hex(C319_FIXTURE_SHA256)
    { return Err("C319 fixture exact length/digest".into()); }
    let mut popcount = 0u64;
    for (slot, owner) in receipt.fixture.owners.iter().enumerate() {
        let start = slot * OWNER_BYTES;
        let bytes = &fixture[start..start + OWNER_BYTES];
        let actual_popcount = bytes.iter().map(|b| b.count_ones() as u64).sum::<u64>();
        popcount = popcount.checked_add(actual_popcount).ok_or("fixture popcount overflow")?;
        if digest(bytes)?.to_ascii_lowercase() != owner.sha256.to_ascii_lowercase()
            || actual_popcount != owner.popcount
        { return Err(format!("C319 owner storage hash at slot {slot}")); }
    }
    for (slot, row) in receipt.fixture.rows.iter().enumerate() {
        let start = slot * ROW_BYTES;
        let bytes = &fixture[start..start + ROW_BYTES];
        let actual_popcount = bytes.iter().map(|b| b.count_ones() as u64).sum::<u64>();
        if digest(bytes)?.to_ascii_lowercase() != row.sha256.to_ascii_lowercase()
            || actual_popcount != row.popcount
        { return Err(format!("C319 sigma row storage hash at slot {slot}")); }
    }
    let fixture_popcount = fixture.iter().map(|b| b.count_ones() as u64).sum::<u64>();
    if popcount != fixture_popcount || receipt.fixture.popcount != fixture_popcount {
        return Err("C319 fixture/owner population count".into());
    }
    Ok(Admitted { receipt, fixture })
}

fn fragment_bit(bytes: &[u8], owner: usize, wire: usize) -> Result<bool, String> {
    if bytes.len() != FIXTURE_BYTES || wire >= WIDTH { return Err("fixture coordinate bounds".into()); }
    let slot = OWNERS.iter().position(|x| *x == owner).ok_or("fixture owner absent")?;
    if ROWS[slot / 2] != owner / 2 || slot % 2 != owner % 2 {
        return Err("fixture original sigma21 row/half mapping".into());
    }
    let offset = (slot / 2) * ROW_BYTES + (owner % 2) * OWNER_BYTES + wire / 8;
    Ok((bytes[offset] >> (wire % 8)) & 1 == 1)
}

fn public(c: &ControlReceipt, raw: &[u8], floor: [u8; 28], audit: [u8; 28])
    -> crate::checkpoint_output_layout::CheckpointPublic
{
    crate::checkpoint_output_layout::CheckpointPublic { raw: raw.to_vec(), floor_work: floor, audit_work: audit }
}

fn audit_be28(c: &ControlReceipt) -> Result<[u8; 28], String> {
    let audit = num_bigint::BigUint::parse_bytes(c.audit_decimal.as_bytes(), 10)
        .ok_or("audit integer decimal")?;
    let bytes = audit.to_bytes_be();
    if bytes.len() > 28 { return Err("audit integer width".into()); }
    let mut result = [0; 28];
    result[28 - bytes.len()..].copy_from_slice(&bytes);
    Ok(result)
}

fn field_equations(parent: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    admitted: &Admitted, c: &ControlReceipt, raw: &[u8], floor_override: Option<[u8; 28]>,
    owners: Option<(usize, usize)>, omit_equation: Option<(usize, usize, usize)>) -> Result<(), String>
{
    let expected_owners = (c.header_owner, c.floor_owner);
    if owners.unwrap_or(expected_owners) != expected_owners {
        return Err("C319 row/owner/half mapping does not match native A/B control".into());
    }
    if raw.len() != c.raw_bytes || digest(raw)?.to_ascii_lowercase() != c.raw_sha256.to_ascii_lowercase() {
        return Err(format!("{} public RAW length/digest", c.label));
    }
    let floor = floor_override.unwrap_or(decode_hex::<28>(&c.floor_be28)?);
    let statement = public(c, raw, floor, audit_be28(c)?);
    let lane = crate::checkpoint_output_layout::CheckpointRole4Lane::new(parent, c.h as u64, statement.clone())?;
    let d = lane.descriptor();
    if d.root != parent.descriptor().root || d.total != parent.work_profile().total_be28
        || d.h != c.h as u64 || d.f != c.f as u64 || d.depth != 64
    { return Err("C320 exact descriptor/native parent mismatch".into()); }
    let row_owner = d.base >> 19;
    let mut terms = Vec::with_capacity(4346);
    let count = lane.visit_owner_terms(&d, row_owner, |term| { terms.push(term); Ok(()) })?;
    if count != 4346 || terms.len() != 4346 { return Err("C320 exact descriptor row terms".into()); }
    for (j, term) in terms.iter().enumerate() {
        if term.row != d.base + j || term.gate.right != 0 || term.gate.c1 != Fr::one()
            || term.gate.c2 != Fr::zero() || term.gate.c3 != Fr::zero()
        { return Err(format!("{label} descriptor equation shape row={j}", label=c.label)); }
        let owner = term.gate.left / WIDTH;
        let wire = term.gate.left % WIDTH;
        // Test-only omission mutant: it can skip only the exact expected coordinate.
        if omit_equation == Some((j, owner, wire)) { continue; }
        let actual = fragment_bit(&admitted.fixture, owner, wire)?;
        if Fr::from(actual as u64) + term.gate.c0 != Fr::zero() {
            return Err(format!("{} field equation row={j} owner={owner} wire={wire}", c.label));
        }
    }
    Ok(())
}

fn role4_descriptor_rejects_before_effects<'a>(
    relation: &crate::checkpoint_role4_internal::AdmittedCheckpointRole4<'_, 'a>,
    field: &str) -> Result<(), String>
{
    let mut requested = relation.descriptor();
    match field {
        "f" => requested.checkpoint.f += 1,
        "root" => requested.checkpoint.root[0] ^= 1,
        "total" => requested.checkpoint.total[27] ^= 1,
        _ => return Err("unknown descriptor fault".into()),
    }
    let prefix = crate::transcript::Transcript::new(b"c320-role4-field-consumer");
    let before = (prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries());
    let mut effects = 0;
    if relation.bind_consumer(&requested, &prefix).is_ok() { return Err("descriptor swap admitted".into()); }
    if relation.visit_owner_terms(&requested, 0, |_| { effects += 1; Ok(()) }).is_ok()
        || effects != 0
        || before != (prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries())
    { return Err("descriptor swap crossed field/challenge effects".into()); }
    Ok(())
}

#[test]
#[ignore = "requires independent C319 post-run and C320 source review before activation"]
fn c320_c319_ab_field_consumer_and_isolated_faults() -> Result<(), String> {
    let directory = std::path::PathBuf::from(std::env::var_os("C319_EXTRACT_DIR")
        .ok_or("C319_EXTRACT_DIR required")?);
    let admitted = admit(&directory)?;
    let root = decode_hex::<32>(&admitted.receipt.parent.root)?;
    let total = decode_hex::<28>(&admitted.receipt.parent.total_be28)?;
    let parent = crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(N, 21, root, total)?;
    let a = &admitted.receipt.controls[0];
    let b = &admitted.receipt.controls[1];
    let floor_a = decode_hex::<28>(&a.floor_be28)?;
    let floor_b = decode_hex::<28>(&b.floor_be28)?;
    let audit_a = audit_be28(a)?;
    let audit_b = audit_be28(b)?;
    if RAW_A == RAW_B || a.floor_decimal == b.floor_decimal {
        return Err("A/B native RAW and W(f) controls must be distinct".into());
    }
    let adapter_a = crate::checkpoint_role4_internal::CheckpointRole4Adapter::new(
        &parent, a.h as u64, public(a, RAW_A, floor_a, audit_a))?;
    let relation_a = adapter_a.admit_query((a.h as u64, a.f as u64))?;
    let binding_a = relation_a.descriptor();
    let binding_b = {
        let lane_b = crate::checkpoint_output_layout::CheckpointRole4Lane::new(
            &parent, b.h as u64, public(b, RAW_B, floor_b, audit_b))?;
        crate::checkpoint_role4_internal::CheckpointRole4Binding {
            tag: binding_a.tag,
            parent_object: binding_a.parent_object,
            checkpoint: lane_b.descriptor(),
        }
    };
    if binding_a.parent_object != binding_b.parent_object
        || binding_a.checkpoint.root != binding_b.checkpoint.root
        || binding_a.checkpoint.total != binding_b.checkpoint.total
    { return Err("A/A and B/B descriptors do not share one native parent".into()); }
    let verifier_b = (b.h as u64, b.f as u64);
    let mismatch_prefix = crate::transcript::Transcript::new(b"c320-verifier-query-ab");
    let mismatch_before = (mismatch_prefix.bytes_absorbed(), mismatch_prefix.challenges(),
        mismatch_prefix.raw_queries());
    let mut mismatch_effects = 0;
    let mut mismatch_admitted = false;
    if let Ok(mismatched) = adapter_a.admit_query(verifier_b) {
        mismatch_admitted = true;
        let descriptor = mismatched.descriptor();
        let _ = mismatched.bind_consumer(&descriptor, &mismatch_prefix);
        let _ = mismatched.visit_owner_terms(&descriptor, 0, |_| {
            mismatch_effects += 1; Ok(())
        });
    }
    if mismatch_admitted || mismatch_effects != 0
        || mismatch_before != (mismatch_prefix.bytes_absorbed(), mismatch_prefix.challenges(),
            mismatch_prefix.raw_queries())
    { return Err("verifier B tuple admitted adapter A or crossed effects".into()); }
    let mut isolated_faults = 0u32;
    let prefix = crate::transcript::Transcript::new(b"c320-ab-descriptor-swap");
    let before = (prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries());
    let mut effects = 0;
    if relation_a.bind_consumer(&binding_b, &prefix).is_ok()
        || relation_a.visit_owner_terms(&binding_b, 0, |_| { effects += 1; Ok(()) }).is_ok()
        || effects != 0
        || before != (prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries())
    { return Err("B descriptor crossed A field/challenge effects".into()); }
    isolated_faults += 1;
    for field in ["f", "root", "total"] {
        role4_descriptor_rejects_before_effects(&relation_a, field)?;
        isolated_faults += 1;
    }
    field_equations(&parent, &admitted, a, RAW_A, None, None, None)?;
    field_equations(&parent, &admitted, b, RAW_B, None, None, None)?;

    // Semantic one-fault views are cloned only after valid outer receipt admission.
    let baseline = crate::work_tree_layout::shared_baseline()?;
    for (c, raw, owner) in [(a, RAW_A, a.header_owner), (b, RAW_B, b.header_owner)] {
        let mut changed = admitted.clone();
        let wire = baseline.header_alias_wires[0];
        let slot = OWNERS.iter().position(|x| *x == owner).ok_or("header owner")?;
        let byte = (slot / 2) * ROW_BYTES + (owner % 2) * OWNER_BYTES + wire / 8;
        changed.fixture[byte] ^= 1 << (wire % 8);
        let expected_error = format!("{} field equation row=0 owner={owner} wire={wire}", c.label);
        assert_eq!(field_equations(&parent, &changed, c, raw, None, None, None).unwrap_err(), expected_error);
        // Omitting only this one equation admits this semantic test view; no other
        // source coordinate or public admission check is bypassed.
        field_equations(&parent, &changed, c, raw, None, None, Some((0, owner, wire)))?;
        isolated_faults += 1;
    }
    for (row, wire, owner) in [
        (1_760, baseline.header_alias_wires[220 * 8], a.header_owner),
        (4_112, baseline.header_alias_wires[4112], a.header_owner),
        (4_122, baseline.endpoints.upper[0], a.floor_owner),
    ] {
        let mut changed = admitted.clone();
        let slot = OWNERS.iter().position(|x| *x == owner).ok_or("mapped owner")?;
        let byte = (slot / 2) * ROW_BYTES + (owner % 2) * OWNER_BYTES + wire / 8;
        changed.fixture[byte] ^= 1 << (wire % 8);
        let expected_error = format!("A field equation row={row} owner={owner} wire={wire}");
        assert_eq!(field_equations(&parent, &changed, a, RAW_A, None, None, None).unwrap_err(), expected_error);
        field_equations(&parent, &changed, a, RAW_A, None, None, Some((row, owner, wire)))?;
        isolated_faults += 1;
    }
    assert!(field_equations(&parent, &admitted, a, RAW_A, None,
        Some((b.header_owner, a.floor_owner)), None).unwrap_err().contains("owner"));
    isolated_faults += 1;
    assert!(field_equations(&parent, &admitted, a, RAW_A, None,
        Some((a.header_owner, b.floor_owner)), None).unwrap_err().contains("owner"));
    isolated_faults += 1;
    let mut wrong_header_differs = false;
    for j in 0..4112 {
        let wire = baseline.header_alias_wires[j];
        let expected = RAW_A.get(j / 8).is_some_and(|byte| (byte >> (j % 8)) & 1 == 1);
        if fragment_bit(&admitted.fixture, b.header_owner, wire)? != expected {
            wrong_header_differs = true;
            break;
        }
    }
    if !wrong_header_differs { return Err("wrong-header-owner RAW vector was not discriminating".into()); }
    isolated_faults += 1;
    let mut wrong_floor_differs = false;
    for bit in 0..224 {
        let wire = baseline.endpoints.upper[bit];
        let expected = (floor_a[27 - bit / 8] >> (bit % 8)) & 1 == 1;
        if fragment_bit(&admitted.fixture, b.floor_owner, wire)? != expected {
            wrong_floor_differs = true;
            break;
        }
    }
    if !wrong_floor_differs { return Err("wrong-floor-owner W(f) vector was not discriminating".into()); }
    isolated_faults += 1;
    let mut wrong_floor = floor_a; wrong_floor[27] ^= 1;
    assert!(crate::checkpoint_output_layout::CheckpointRole4Lane::new(&parent, a.h as u64,
        public(a, RAW_A, wrong_floor, audit_a)).err().ok_or("floor mismatch accepted")?
        .contains("supplied audit work"));
    isolated_faults += 1;
    let at_total = total;
    assert!(crate::checkpoint_output_layout::CheckpointRole4Lane::new(&parent, a.h as u64,
        public(a, RAW_A, at_total, [0; 28])).err().ok_or("floor range accepted")?
        .contains("floor < total"));
    isolated_faults += 1;

    let mut swapped = admitted.receipt.clone();
    swapped.fixture.rows.swap(0, 1);
    assert!(validate_layout(&swapped).unwrap_err().contains("sigma row/owner mapping"));
    isolated_faults += 1;
    swapped = admitted.receipt.clone();
    swapped.fixture.owners.swap(0, 1);
    assert!(validate_layout(&swapped).unwrap_err().contains("owner row/half/slot"));
    isolated_faults += 1;
    swapped = admitted.receipt.clone();
    swapped.parent.root.replace_range(..2, "00");
    assert!(validate_layout(&swapped).unwrap_err().contains("native parent identity"));
    isolated_faults += 1;
    swapped = admitted.receipt.clone();
    swapped.parent.total_be28.replace_range(54..56, "01");
    assert!(validate_layout(&swapped).unwrap_err().contains("parent total decimal/bytes"));
    isolated_faults += 1;
    if isolated_faults != 19 { return Err(format!("C320 isolated fault count {isolated_faults}")); }
    println!("C320_FIELD_CONSUMER_PASS controls=A/A,B/B equations=8692 isolated_faults={isolated_faults}");
    Ok(())
}

#[test]
#[ignore = "measure one-adapter setup under the C320 2 GiB/120 s supervisor; do not activate Field unless peak is below 1.5 GiB"]
fn c320_one_adapter_resource_preflight() -> Result<(), String> {
    let directory = std::path::PathBuf::from(std::env::var_os("C319_EXTRACT_DIR")
        .ok_or("C319_EXTRACT_DIR required")?);
    let admitted = admit(&directory)?;
    let root = decode_hex::<32>(&admitted.receipt.parent.root)?;
    let total = decode_hex::<28>(&admitted.receipt.parent.total_be28)?;
    let parent = crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(N, 21, root, total)?;
    let a = &admitted.receipt.controls[0];
    let b = &admitted.receipt.controls[1];
    let floor_a = decode_hex::<28>(&a.floor_be28)?;
    let floor_b = decode_hex::<28>(&b.floor_be28)?;
    let audit_a = audit_be28(a)?;
    let audit_b = audit_be28(b)?;
    let adapter_a = crate::checkpoint_role4_internal::CheckpointRole4Adapter::new(
        &parent, a.h as u64, public(a, RAW_A, floor_a, audit_a))?;
    let relation_a = adapter_a.admit_query((a.h as u64, a.f as u64))?;
    let binding_a = relation_a.descriptor();
    let binding_b = {
        let lane_b = crate::checkpoint_output_layout::CheckpointRole4Lane::new(
            &parent, b.h as u64, public(b, RAW_B, floor_b, audit_b))?;
        crate::checkpoint_role4_internal::CheckpointRole4Binding {
            tag: binding_a.tag,
            parent_object: binding_a.parent_object,
            checkpoint: lane_b.descriptor(),
        }
    };
    if binding_a.parent_object != binding_b.parent_object
        || binding_a.checkpoint.root != binding_b.checkpoint.root
        || binding_a.checkpoint.total != binding_b.checkpoint.total
    { return Err("C320 preflight A/B binding parent mismatch".into()); }
    let baseline = crate::work_tree_layout::shared_baseline()?;
    if baseline.header_alias_wires.len() != 4_112 + 10 + 64
        || baseline.endpoints.upper.len() != 224
    { return Err("C320 preflight shared baseline widths".into()); }
    println!("C320_ONE_ADAPTER_PREFLIGHT_READY parent_n={N} A_h={} A_f={} B_h={} B_f={} header_wires={} floor_wires={}",
        a.h, a.f, b.h, b.f, baseline.header_alias_wires.len(), baseline.endpoints.upper.len());
    Ok(())
}

#[test]
#[ignore = "requires C320 Field PASS and independent C321 static review before activation"]
fn c321_carry_template_selection_preflight() -> Result<(), String> {
    let directory = std::path::PathBuf::from(std::env::var_os("C319_EXTRACT_DIR")
        .ok_or("C319_EXTRACT_DIR required")?);
    let admitted = admit(&directory)?;
    let receipt = &admitted.receipt;
    let root = decode_hex::<32>(&receipt.parent.root)?;
    let total = decode_hex::<28>(&receipt.parent.total_be28)?;
    let parent = crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        N, receipt.parent.slot_log, root, total,
    )?;
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(&parent)?;

    const OWNERS: [usize; 4] = [1_810_840, 1_810_841, 1_810_902, 1_810_903];
    const OWNER_ROWS: usize = 1 << 19;
    const OWNER_WIDTH: usize = 1 << 20;
    const FACTOR_POINT: [u64; 21] = [
        2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
    ];
    let point: Vec<Fr> = FACTOR_POINT.into_iter().map(Fr::from).collect();
    let mut reference: Option<Vec<crate::sparse::Term>> = None;
    let mut records = Vec::with_capacity(OWNERS.len());

    for owner in OWNERS {
        if roster.owner_class(owner as u64)? != crate::daa_history_roster::OwnerClass::Carry {
            return Err(format!("owner {owner} is not Carry in the admitted H21 roster"));
        }
        let row_base = owner.checked_mul(OWNER_ROWS)
            .ok_or_else(|| format!("owner {owner} row base overflow"))?;
        let wire_base = owner.checked_mul(OWNER_WIDTH)
            .ok_or_else(|| format!("owner {owner} wire base overflow"))?;
        let mut terms = Vec::new();
        let counts = roster.visit_header_terms(owner as u64, |mut term| {
            term.row = term.row.checked_sub(row_base)
                .ok_or_else(|| format!("owner {owner} row precedes checked base"))?;
            term.gate.left = term.gate.left.checked_sub(wire_base)
                .ok_or_else(|| format!("owner {owner} left wire precedes checked base"))?;
            term.gate.right = term.gate.right.checked_sub(wire_base)
                .ok_or_else(|| format!("owner {owner} right wire precedes checked base"))?;
            terms.push(term);
            Ok(())
        })?;
        if counts.emitted != terms.len() || terms.is_empty() {
            return Err(format!("owner {owner} emitted count/template mismatch"));
        }
        if let Some(first) = &reference {
            if first != &terms {
                return Err(format!("normalized Carry header template differs at owner {owner}"));
            }
        } else {
            reference = Some(terms.clone());
        }

        // Hash the complete ordered vector, including duplicate terms and all four coefficients.
        let mut encoded = Vec::with_capacity(terms.len() * 152);
        for term in &terms {
            encoded.extend_from_slice(&u64::try_from(term.row)
                .map_err(|_| "normalized row does not fit u64")?.to_le_bytes());
            encoded.extend_from_slice(&u64::try_from(term.gate.left)
                .map_err(|_| "normalized left wire does not fit u64")?.to_le_bytes());
            encoded.extend_from_slice(&u64::try_from(term.gate.right)
                .map_err(|_| "normalized right wire does not fit u64")?.to_le_bytes());
            for coefficient in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
                ark_serialize::CanonicalSerialize::serialize_compressed(&coefficient, &mut encoded)
                    .map_err(|error| format!("coefficient encoding failed: {error}"))?;
            }
        }
        let template_digest = digest(&encoded)?;

        // Keep the owner bits LSB-first. Check the factor against a separate direct product.
        let lsb_factor = point.iter().enumerate().fold(Fr::one(), |product, (bit, x)| {
            product * if ((owner >> bit) & 1) == 1 { *x } else { Fr::one() - x }
        });
        let mut direct_product = Fr::one();
        for bit in 0..21usize {
            let coordinate = point[bit];
            let owner_bit = (owner / (1usize << bit)) % 2;
            direct_product *= if owner_bit == 1 { coordinate } else { Fr::one() - coordinate };
        }
        if lsb_factor != direct_product {
            return Err(format!("21-bit LSB-first owner factor mismatch at owner {owner}"));
        }
        if lsb_factor == Fr::zero() || lsb_factor == Fr::one() {
            return Err(format!("owner {owner} factor is Boolean at the selected field point"));
        }
        let mut factor_bytes = Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(&lsb_factor, &mut factor_bytes)
            .map_err(|error| format!("owner factor encoding failed: {error}"))?;
        records.push(format!(
            "owner={owner},class=Carry,terms={},template_sha256={},factor={}",
            terms.len(), template_digest, hex(&factor_bytes),
        ));
    }

    // `visit_header_terms` selects only the header-family relation. This does not
    // establish the separate full DAA-plus-header relation.
    println!("C321_CARRY_TEMPLATE_PREFLIGHT_PASS surface=header_only full_daa_checked=false source=C319_receipt={} owners={}",
        C319_RECEIPT_SHA256, records.join(";"));
    Ok(())
}

#[test]
#[ignore = "bounded C322 diagnostic; run only after current C319/C321 source review"]
fn c322_h21_u0_literal_vs_shared_template_differential() -> Result<(), String> {
    let directory = std::path::PathBuf::from(std::env::var_os("C319_EXTRACT_DIR")
        .ok_or("C319_EXTRACT_DIR required")?);
    let admitted = admit(&directory)?;
    let root = decode_hex::<32>(&admitted.receipt.parent.root)?;
    let total = decode_hex::<28>(&admitted.receipt.parent.total_be28)?;
    let parent = crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        N, admitted.receipt.parent.slot_log, root, total,
    )?;
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(&parent)?;
    const OWNER_ROWS: usize = 1 << 19;
    const OWNER_WIDTH: usize = 1 << 20;
    let mut captured = Vec::with_capacity(OWNERS.len());
    for owner in OWNERS {
        if roster.owner_class(owner as u64)? != crate::daa_history_roster::OwnerClass::Carry {
            return Err(format!("owner {owner} is not Carry in the admitted H21 roster"));
        }
        let row_base = owner.checked_mul(OWNER_ROWS)
            .ok_or_else(|| format!("owner {owner} row base overflow"))?;
        let wire_base = owner.checked_mul(OWNER_WIDTH)
            .ok_or_else(|| format!("owner {owner} wire base overflow"))?;
        let mut terms = Vec::new();
        let counts = roster.visit_header_terms(owner as u64, |mut term| {
            term.row = term.row.checked_sub(row_base)
                .ok_or_else(|| format!("owner {owner} row precedes checked base"))?;
            term.gate.left = term.gate.left.checked_sub(wire_base)
                .ok_or_else(|| format!("owner {owner} left wire precedes checked base"))?;
            term.gate.right = term.gate.right.checked_sub(wire_base)
                .ok_or_else(|| format!("owner {owner} right wire precedes checked base"))?;
            terms.push(term);
            Ok(())
        })?;
        if counts.emitted != terms.len() || terms.is_empty() {
            return Err(format!("owner {owner} emitted count/template mismatch"));
        }
        captured.push(terms);
    }
    // Require complete ordered term equality (row, endpoints, all coefficients)
    // before reading owner inputs or invoking either U-message construction.
    if captured.iter().skip(1).any(|template|template!=&captured[0]) {
        return Err("C322 normalized Carry header templates differ".into());
    }
    const C321_CARRY_TEMPLATE_SHA256:&str=
        "afd297fef8a856b273c15cf0d5bb6c859ec2e1886ffa5eb4f3aa2f0811c1ed4d";
    let template_digest=|terms:&[crate::sparse::Term]|->Result<String,String>{
        let mut encoded=Vec::with_capacity(terms.len()*152);
        for term in terms{
            encoded.extend_from_slice(&u64::try_from(term.row)
                .map_err(|_|"C322 normalized row does not fit u64")?.to_le_bytes());
            encoded.extend_from_slice(&u64::try_from(term.gate.left)
                .map_err(|_|"C322 normalized left wire does not fit u64")?.to_le_bytes());
            encoded.extend_from_slice(&u64::try_from(term.gate.right)
                .map_err(|_|"C322 normalized right wire does not fit u64")?.to_le_bytes());
            for coefficient in [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]{
                ark_serialize::CanonicalSerialize::serialize_compressed(&coefficient,&mut encoded)
                    .map_err(|error|format!("C322 coefficient encoding failed: {error}"))?;
            }
        }
        digest(&encoded)
    };
    if captured[0].len()!=396_561||template_digest(&captured[0])?!=C321_CARRY_TEMPLATE_SHA256{
        return Err("C322 four-owner template does not match the pinned C321 digest".into());
    }

    // Check the last Carry immediately before the retarget boundary against
    // the same full C321 template. Keep the next owner as a class-only probe.
    const BOUNDARY_CARRY:usize=1_810_815;
    const BOUNDARY_NEXT:usize=1_810_816;
    if roster.owner_class(BOUNDARY_CARRY as u64)?!=crate::daa_history_roster::OwnerClass::Carry{
        return Err("C322 boundary predecessor is not Carry".into());
    }
    let row_base=BOUNDARY_CARRY.checked_mul(OWNER_ROWS)
        .ok_or("C322 boundary Carry row base overflow")?;
    let wire_base=BOUNDARY_CARRY.checked_mul(OWNER_WIDTH)
        .ok_or("C322 boundary Carry wire base overflow")?;
    let mut boundary_terms=Vec::new();
    let boundary_count=roster.visit_header_terms(BOUNDARY_CARRY as u64,|mut term|{
        term.row=term.row.checked_sub(row_base).ok_or("C322 boundary row underflow")?;
        term.gate.left=term.gate.left.checked_sub(wire_base).ok_or("C322 boundary left underflow")?;
        term.gate.right=term.gate.right.checked_sub(wire_base).ok_or("C322 boundary right underflow")?;
        boundary_terms.push(term);Ok(())
    })?;
    if boundary_count.emitted!=boundary_terms.len()||boundary_terms!=captured[0]
        ||template_digest(&boundary_terms)?!=C321_CARRY_TEMPLATE_SHA256{
        return Err("C322 last-Carry boundary template differs from C321".into());
    }
    drop(boundary_terms);
    let next_class=roster.owner_class(BOUNDARY_NEXT as u64)?;
    if next_class==crate::daa_history_roster::OwnerClass::Carry{
        return Err("C322 expected retarget boundary owner to leave Carry class".into());
    }
    let templates:[Vec<crate::sparse::Term>;4]=captured.try_into()
        .map_err(|_|"C322 Carry template count")?;
    for term in &templates[0]{
        if term.row>=OWNER_ROWS||term.gate.left>=OWNER_WIDTH||term.gate.right>=OWNER_WIDTH{
            return Err("C322 Carry template contains an anchor or out-of-range endpoint".into());
        }
    }

    let row_point=(23u64..=41).map(Fr::from);
    let owner_point=(2u64..=22).map(Fr::from).collect::<Vec<_>>();
    let point=row_point.chain(owner_point.iter().copied()).collect::<Vec<_>>();
    if point.len()!=40 { return Err("C322 row/owner point width".into()); }
    // Keep the C321 owner-factor pins local to this test and independently
    // recompute them from the 21 LSB-first owner coordinates.
    const OWNER_FACTOR_PINS:[&str;4]=[
        "01aa49fb353c46ff8970b97948e833285d588181b64550b829a031e1724e6430",
        "00ac6ce9bb7237890e0000000000000000000000000000000000000000000000",
        "018053fd9ea2a0f98370b97948e833285d588181b64550b829a031e1724e6430",
        "000059e5e9a582941a0000000000000000000000000000000000000000000000",
    ];
    let owner_factors:[Fr;4]=std::array::from_fn(|index|{
        let owner=OWNERS[index];
        owner_point.iter().enumerate().fold(Fr::one(),|product,(bit,coordinate)|{
            if ((owner>>bit)&1)==1{product * *coordinate}else{product*(Fr::one()-*coordinate)}
        })
    });
    for index in 0..OWNERS.len(){
        let factor=owner_factors[index];
        if factor.is_zero()||factor.is_one(){return Err("C322 owner factor is Boolean".into());}
        let mut encoded=Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(&factor,&mut encoded)
            .map_err(|error|format!("C322 owner factor encoding failed: {error}"))?;
        if hex(&encoded)!=OWNER_FACTOR_PINS[index]{
            return Err(format!("C322 owner {} independent factor differs from C321 pin",OWNERS[index]));
        }
    }
    let (literal_visits,shared_build_visits,owner_selection_visits,bank_capacity_bytes,selector_states)=
        crate::sparse_stream_roster::c322_u0_literal_template_differential(
            &templates,OWNERS,&point,&owner_factors,
            |index|{
                let owner=OWNERS[index];
                let mut input=Vec::with_capacity(OWNER_WIDTH);
                for wire in 0..OWNER_WIDTH {
                    input.push(Fr::from(fragment_bit(&admitted.fixture,owner,wire)? as u64));
                }
                Ok(input)
            },
            |index,sink|{
                let owner=OWNERS[index];
                let row_base=owner.checked_mul(OWNER_ROWS).ok_or("C322 direct row base overflow")?;
                let wire_base=owner.checked_mul(OWNER_WIDTH).ok_or("C322 direct wire base overflow")?;
                let mut term_index=0usize;
                let counts=roster.visit_header_terms(owner as u64,|mut term|{
                    term.row=term.row.checked_sub(row_base).ok_or("C322 direct row underflow")?;
                    term.gate.left=term.gate.left.checked_sub(wire_base).ok_or("C322 direct left underflow")?;
                    term.gate.right=term.gate.right.checked_sub(wire_base).ok_or("C322 direct right underflow")?;
                    if templates[index].get(term_index)!=Some(&term){
                        return Err(format!("C322 direct owner {owner} ordered term differs at {term_index}"));
                    }
                    term_index=term_index.checked_add(1).ok_or("C322 direct term index overflow")?;
                    sink(term)
                })?;
                if counts.emitted!=term_index||term_index!=templates[index].len(){
                    return Err(format!("C322 direct owner {owner} visit count differs from template"));
                }
                Ok(())
            },
        )?;
    let differential_path_term_visits=literal_visits.checked_add(shared_build_visits)
        .and_then(|visits|visits.checked_add(owner_selection_visits))
        .ok_or("C322 total visit counter overflow")?;
    println!("C322_U0_DIFFERENTIAL_PASS owner_count=4 template_count=1 template_terms=396561 template_sha256={C321_CARRY_TEMPLATE_SHA256} per_owner_coefficient_and_message_comparisons=4 aggregate_comparisons=1 negative_controls=3 wrong_owner_factor=true flipped_selector_bit=true row_index_bit=true point=row[23..41],owner[2..22] k=0 expanded_x_fields=4194304 boolean_checked_fields=4194304 direct_term_visits={literal_visits} shared_build_term_visits={shared_build_visits} owner_selection_visits={owner_selection_visits} differential_path_term_visits={differential_path_term_visits} selectors_zero={} selectors_one={} c2_terms={} c3_terms={} nonzero_right_terms={} bank_capacity_bytes={bank_capacity_bytes} boundary_predecessor=1810815:Carry:template_equal=true boundary_next=1810816:{next_class:?}:noncarry=true full_proof=false",
        selector_states[0],selector_states[1],selector_states[2],selector_states[3],selector_states[4]);
    Ok(())
}

#[test]
#[ignore = "bounded C323 timing diagnostic; C319 and C322 admission required"]
fn c323_h21_u0_shared_cost_split() -> Result<(), String> {
    let directory = std::path::PathBuf::from(std::env::var_os("C319_EXTRACT_DIR")
        .ok_or("C319_EXTRACT_DIR required")?);
    let admitted = admit(&directory)?;
    let root = decode_hex::<32>(&admitted.receipt.parent.root)?;
    let total = decode_hex::<28>(&admitted.receipt.parent.total_be28)?;
    let parent = crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        N, admitted.receipt.parent.slot_log, root, total,
    )?;
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(&parent)?;
    let carry_census = (0..(1u64 << 21)).try_fold(0u64, |count, owner| {
        let is_carry = roster.owner_class(owner)? == crate::daa_history_roster::OwnerClass::Carry;
        count.checked_add(u64::from(is_carry))
            .ok_or_else(|| "C323 Carry census overflow".to_owned())
    })?;
    if carry_census != 1_819_332 {
        return Err(format!("C323 H21 Carry census drift: {carry_census}"));
    }

    const OWNER_ROWS: usize = 1 << 19;
    const OWNER_WIDTH: usize = 1 << 20;
    const TEMPLATE_SHA256: &str =
        "afd297fef8a856b273c15cf0d5bb6c859ec2e1886ffa5eb4f3aa2f0811c1ed4d";
    let mut captured = Vec::with_capacity(OWNERS.len());
    for owner in OWNERS {
        if roster.owner_class(owner as u64)? != crate::daa_history_roster::OwnerClass::Carry {
            return Err(format!("C323 owner {owner} is not Carry"));
        }
        let row_base = owner.checked_mul(OWNER_ROWS).ok_or("C323 row base overflow")?;
        let wire_base = owner.checked_mul(OWNER_WIDTH).ok_or("C323 wire base overflow")?;
        let mut terms = Vec::new();
        let counts = roster.visit_header_terms(owner as u64, |mut term| {
            term.row = term.row.checked_sub(row_base).ok_or("C323 row underflow")?;
            term.gate.left = term.gate.left.checked_sub(wire_base).ok_or("C323 left underflow")?;
            term.gate.right = term.gate.right.checked_sub(wire_base).ok_or("C323 right underflow")?;
            terms.push(term);
            Ok(())
        })?;
        if counts.emitted != terms.len() || terms.len() != 396_561 {
            return Err(format!("C323 owner {owner} header template size drift"));
        }
        captured.push(terms);
    }
    if captured.iter().skip(1).any(|terms| terms != &captured[0]) {
        return Err("C323 four Carry templates differ".into());
    }
    let mut encoded = Vec::with_capacity(captured[0].len() * 152);
    for term in &captured[0] {
        encoded.extend_from_slice(&u64::try_from(term.row)
            .map_err(|_| "C323 row width")?.to_le_bytes());
        encoded.extend_from_slice(&u64::try_from(term.gate.left)
            .map_err(|_| "C323 left width")?.to_le_bytes());
        encoded.extend_from_slice(&u64::try_from(term.gate.right)
            .map_err(|_| "C323 right width")?.to_le_bytes());
        for coefficient in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
            ark_serialize::CanonicalSerialize::serialize_compressed(&coefficient, &mut encoded)
                .map_err(|error| format!("C323 coefficient encoding failed: {error}"))?;
        }
    }
    if digest(&encoded)? != TEMPLATE_SHA256 {
        return Err("C323 common template digest differs from C321".into());
    }
    drop(encoded);
    let templates: [Vec<crate::sparse::Term>; 4] = captured.try_into()
        .map_err(|_| "C323 Carry template count")?;
    if templates[0].iter().any(|term| {
        term.row >= OWNER_ROWS || term.gate.left >= OWNER_WIDTH || term.gate.right >= OWNER_WIDTH
    }) {
        return Err("C323 Carry template has out-of-range local term".into());
    }

    let row_point = (23u64..=41).map(Fr::from);
    let owner_point = (2u64..=22).map(Fr::from).collect::<Vec<_>>();
    let point = row_point.chain(owner_point.iter().copied()).collect::<Vec<_>>();
    if point.len() != 40 { return Err("C323 field-point width".into()); }
    const OWNER_FACTOR_PINS: [&str; 4] = [
        "01aa49fb353c46ff8970b97948e833285d588181b64550b829a031e1724e6430",
        "00ac6ce9bb7237890e0000000000000000000000000000000000000000000000",
        "018053fd9ea2a0f98370b97948e833285d588181b64550b829a031e1724e6430",
        "000059e5e9a582941a0000000000000000000000000000000000000000000000",
    ];
    let owner_factors: [Fr; 4] = std::array::from_fn(|index| {
        let owner = OWNERS[index];
        owner_point.iter().enumerate().fold(Fr::one(), |product, (bit, coordinate)| {
            if ((owner >> bit) & 1) == 1 { product * *coordinate }
            else { product * (Fr::one() - *coordinate) }
        })
    });
    for (index, factor) in owner_factors.iter().enumerate() {
        let mut bytes = Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(factor, &mut bytes)
            .map_err(|error| format!("C323 factor encoding failed: {error}"))?;
        if factor.is_zero() || factor.is_one() || hex(&bytes) != OWNER_FACTOR_PINS[index] {
            return Err(format!("C323 owner {} factor differs from C321 pin", OWNERS[index]));
        }
    }
    let result = crate::sparse_stream_roster::c323_u0_shared_cost_split(
        &templates, OWNERS, &point, &owner_factors,
        |index| {
            let owner = OWNERS[index];
            let mut input = Vec::with_capacity(OWNER_WIDTH);
            for wire in 0..OWNER_WIDTH {
                input.push(Fr::from(fragment_bit(&admitted.fixture, owner, wire)? as u64));
            }
            Ok(input)
        },
        |index, sink| {
            let owner = OWNERS[index];
            let row_base = owner.checked_mul(OWNER_ROWS).ok_or("C323 direct row base overflow")?;
            let wire_base = owner.checked_mul(OWNER_WIDTH).ok_or("C323 direct wire base overflow")?;
            let mut term_index = 0usize;
            let counts = roster.visit_header_terms(owner as u64, |mut term| {
                term.row = term.row.checked_sub(row_base).ok_or("C323 direct row underflow")?;
                term.gate.left = term.gate.left.checked_sub(wire_base).ok_or("C323 direct left underflow")?;
                term.gate.right = term.gate.right.checked_sub(wire_base).ok_or("C323 direct right underflow")?;
                if templates[index].get(term_index) != Some(&term) {
                    return Err(format!("C323 owner {owner} direct term drift at {term_index}"));
                }
                term_index = term_index.checked_add(1).ok_or("C323 direct index overflow")?;
                sink(term)
            })?;
            if counts.emitted != term_index || term_index != templates[index].len() {
                return Err(format!("C323 owner {owner} direct term count drift"));
            }
            Ok(())
        },
    )?;
    if result.bank_build_ns == 0 || result.bank_capacity_bytes != 57_104_848
        || result.direct_term_visits != 1_586_244
        || result.bank_build_term_visits != 396_561
        || result.owner_selection_visits != 6_344_976 {
        return Err("C323 bank capacity, visit count or clock measurement drift".into());
    }
    let cycle_times = result.measured.iter().map(|cycle| serde_json::json!({
        "load_check_ns": cycle.map(|cost| cost.load_check_ns),
        "select_ns": cycle.map(|cost| cost.select_ns),
        "message_ns": cycle.map(|cost| cost.message_ns),
    })).collect::<Vec<_>>();
    println!("C323_U0_COST_PASS {}", serde_json::json!({
        "schema": 1,
        "scope": "header_only_k0_four_c319_carry",
        "full_proof": false,
        "owners": OWNERS,
        "carry_census": carry_census,
        "template_terms": templates[0].len(),
        "template_sha256": TEMPLATE_SHA256,
        "bank_build_ns": result.bank_build_ns,
        "bank_capacity_bytes": result.bank_capacity_bytes,
        "baseline_direct_visits": result.direct_term_visits,
        "bank_build_term_visits": result.bank_build_term_visits,
        "owner_selection_visits": result.owner_selection_visits,
        "warmup_cycles": 1,
        "measured_cycles": result.measured.len(),
        "cycle_times": cycle_times,
        "baseline_coefficients_equal": true,
        "all_messages_equal": true,
    }));
    Ok(())
}

#[test]
#[ignore = "bounded C324 fused first-U diagnostic; C319 and pinned C323 source required"]
fn c324_h21_u0_fused_cost_split() -> Result<(), String> {
    let directory=std::path::PathBuf::from(std::env::var_os("C319_EXTRACT_DIR")
        .ok_or("C319_EXTRACT_DIR required")?);
    let admitted=admit(&directory)?;
    let root=decode_hex::<32>(&admitted.receipt.parent.root)?;
    let total=decode_hex::<28>(&admitted.receipt.parent.total_be28)?;
    let parent=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        N,admitted.receipt.parent.slot_log,root,total,
    )?;
    let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&parent)?;
    let carry_census=(0..(1u64<<21)).try_fold(0u64,|count,owner|{
        count.checked_add(u64::from(roster.owner_class(owner)?==crate::daa_history_roster::OwnerClass::Carry))
            .ok_or_else(||"C324 Carry census overflow".to_owned())
    })?;
    if carry_census!=1_819_332{return Err(format!("C324 H21 Carry census drift: {carry_census}"));}

    const OWNER_ROWS:usize=1<<19;
    const OWNER_WIDTH:usize=1<<20;
    const TEMPLATE_SHA256:&str="afd297fef8a856b273c15cf0d5bb6c859ec2e1886ffa5eb4f3aa2f0811c1ed4d";
    let mut captured=Vec::with_capacity(OWNERS.len());
    for owner in OWNERS{
        if roster.owner_class(owner as u64)?!=crate::daa_history_roster::OwnerClass::Carry{
            return Err(format!("C324 owner {owner} is not Carry"));
        }
        let row_base=owner.checked_mul(OWNER_ROWS).ok_or("C324 row base overflow")?;
        let wire_base=owner.checked_mul(OWNER_WIDTH).ok_or("C324 wire base overflow")?;
        let mut terms=Vec::new();
        let counts=roster.visit_header_terms(owner as u64,|mut term|{
            term.row=term.row.checked_sub(row_base).ok_or("C324 row underflow")?;
            term.gate.left=term.gate.left.checked_sub(wire_base).ok_or("C324 left underflow")?;
            term.gate.right=term.gate.right.checked_sub(wire_base).ok_or("C324 right underflow")?;
            terms.push(term);Ok(())
        })?;
        if counts.emitted!=terms.len()||terms.len()!=396_561{
            return Err(format!("C324 owner {owner} header template size drift"));
        }
        captured.push(terms);
    }
    if captured.iter().skip(1).any(|terms|terms!=&captured[0]){
        return Err("C324 four Carry templates differ".into());
    }
    let mut encoded=Vec::with_capacity(captured[0].len()*152);
    for term in &captured[0]{
        encoded.extend_from_slice(&u64::try_from(term.row).map_err(|_|"C324 row width")?.to_le_bytes());
        encoded.extend_from_slice(&u64::try_from(term.gate.left).map_err(|_|"C324 left width")?.to_le_bytes());
        encoded.extend_from_slice(&u64::try_from(term.gate.right).map_err(|_|"C324 right width")?.to_le_bytes());
        for coefficient in [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]{
            ark_serialize::CanonicalSerialize::serialize_compressed(&coefficient,&mut encoded)
                .map_err(|error|format!("C324 coefficient encoding failed: {error}"))?;
        }
    }
    if digest(&encoded)?!=TEMPLATE_SHA256{return Err("C324 template digest differs from pinned C323/C321 value".into());}
    drop(encoded);
    let templates:[Vec<crate::sparse::Term>;4]=captured.try_into().map_err(|_|"C324 Carry template count")?;
    if templates[0].iter().any(|term|term.row>=OWNER_ROWS||term.gate.left>=OWNER_WIDTH||term.gate.right>=OWNER_WIDTH){
        return Err("C324 Carry template has out-of-range local term".into());
    }

    let row_point=(23u64..=41).map(Fr::from);
    let owner_point=(2u64..=22).map(Fr::from).collect::<Vec<_>>();
    let point=row_point.chain(owner_point.iter().copied()).collect::<Vec<_>>();
    if point.len()!=40{return Err("C324 field-point width".into());}
    const OWNER_FACTOR_PINS:[&str;4]=[
        "01aa49fb353c46ff8970b97948e833285d588181b64550b829a031e1724e6430",
        "00ac6ce9bb7237890e0000000000000000000000000000000000000000000000",
        "018053fd9ea2a0f98370b97948e833285d588181b64550b829a031e1724e6430",
        "000059e5e9a582941a0000000000000000000000000000000000000000000000",
    ];
    let owner_factors:[Fr;4]=std::array::from_fn(|index|{
        let owner=OWNERS[index];
        owner_point.iter().enumerate().fold(Fr::one(),|product,(bit,coordinate)|{
            if ((owner>>bit)&1)==1{product * *coordinate}else{product*(Fr::one()-*coordinate)}
        })
    });
    for (index,factor) in owner_factors.iter().enumerate(){
        let mut bytes=Vec::new();ark_serialize::CanonicalSerialize::serialize_compressed(factor,&mut bytes)
            .map_err(|error|format!("C324 factor encoding failed: {error}"))?;
        if factor.is_zero()||factor.is_one()||hex(&bytes)!=OWNER_FACTOR_PINS[index]{
            return Err(format!("C324 owner {} factor differs from pinned C323/C321 value",OWNERS[index]));
        }
    }
    let result=crate::sparse_stream_roster::c324_u0_fused_cost_split(
        &templates,OWNERS,&point,&owner_factors,
        |index|{
            let owner=OWNERS[index];let mut input=Vec::with_capacity(OWNER_WIDTH);
            for wire in 0..OWNER_WIDTH{input.push(Fr::from(fragment_bit(&admitted.fixture,owner,wire)? as u64));}
            Ok(input)
        },
        |index,sink|{
            let owner=OWNERS[index];
            let row_base=owner.checked_mul(OWNER_ROWS).ok_or("C324 direct row base overflow")?;
            let wire_base=owner.checked_mul(OWNER_WIDTH).ok_or("C324 direct wire base overflow")?;
            let mut term_index=0usize;
            let counts=roster.visit_header_terms(owner as u64,|mut term|{
                term.row=term.row.checked_sub(row_base).ok_or("C324 direct row underflow")?;
                term.gate.left=term.gate.left.checked_sub(wire_base).ok_or("C324 direct left underflow")?;
                term.gate.right=term.gate.right.checked_sub(wire_base).ok_or("C324 direct right underflow")?;
                if templates[index].get(term_index)!=Some(&term){
                    return Err(format!("C324 owner {owner} direct term drift at {term_index}"));
                }
                term_index=term_index.checked_add(1).ok_or("C324 direct index overflow")?;sink(term)
            })?;
            if counts.emitted!=term_index||term_index!=templates[index].len(){
                return Err(format!("C324 owner {owner} direct term count drift"));
            }
            Ok(())
        },
    )?;
    if result.bank_build_ns==0||result.bank_capacity_bytes!=57_104_848
        ||result.direct_term_visits!=1_586_244||result.bank_build_term_visits!=396_561
        ||result.fused_entry_visits!=4_758_732{
        return Err("C324 bank capacity or direct/build/fused visit count drift".into());
    }
    let cycle_times=result.measured.iter().map(|cycle|serde_json::json!({
        "load_check_ns":cycle.map(|cost|cost.load_check_ns),
        "fused_select_message_ns":cycle.map(|cost|cost.fused_select_message_ns),
    })).collect::<Vec<_>>();
    println!("C324_U0_FUSED_PASS {}",serde_json::json!({
        "schema":1,"scope":"header_only_k0_four_c319_carry","full_proof":false,
        "owners":OWNERS,"carry_census":carry_census,"template_terms":templates[0].len(),
        "template_sha256":TEMPLATE_SHA256,"bank_build_ns":result.bank_build_ns,
        "bank_capacity_bytes":result.bank_capacity_bytes,"baseline_direct_visits":result.direct_term_visits,
        "bank_build_term_visits":result.bank_build_term_visits,"fused_entry_visits":result.fused_entry_visits,
        "warmup_cycles":1,"measured_cycles":result.measured.len(),"cycle_times":cycle_times,
        "direct_dense_shared_fused_messages_equal":true,"full_x_boolean_check_retained":true,
        "owner_factor_applied_after_fused_message":true,
    }));
    Ok(())
}

#[test]
#[ignore = "bounded C325 first-prefix U1 differential; requires pinned C319 extraction"]
fn c325_h21_u1_four_carry_differential() -> Result<(), String> {
    let directory=std::path::PathBuf::from(std::env::var_os("C319_EXTRACT_DIR")
        .ok_or("C319_EXTRACT_DIR required")?);
    let admitted=admit(&directory)?;
    let root=decode_hex::<32>(&admitted.receipt.parent.root)?;
    let total=decode_hex::<28>(&admitted.receipt.parent.total_be28)?;
    let parent=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        N,admitted.receipt.parent.slot_log,root,total,
    )?;
    let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&parent)?;
    let carry_census=(0..(1u64<<21)).try_fold(0u64,|count,owner|{
        count.checked_add(u64::from(roster.owner_class(owner)?==crate::daa_history_roster::OwnerClass::Carry))
            .ok_or_else(||"C325 Carry census overflow".to_owned())
    })?;
    if carry_census!=1_819_332{return Err(format!("C325 H21 Carry census drift: {carry_census}"));}

    const OWNER_ROWS:usize=1<<19;
    const OWNER_WIDTH:usize=1<<20;
    const TEMPLATE_SHA256:&str="afd297fef8a856b273c15cf0d5bb6c859ec2e1886ffa5eb4f3aa2f0811c1ed4d";
    let mut captured=Vec::with_capacity(OWNERS.len());
    for owner in OWNERS{
        if roster.owner_class(owner as u64)?!=crate::daa_history_roster::OwnerClass::Carry{
            return Err(format!("C325 owner {owner} is not Carry"));
        }
        let row_base=owner.checked_mul(OWNER_ROWS).ok_or("C325 row base overflow")?;
        let wire_base=owner.checked_mul(OWNER_WIDTH).ok_or("C325 wire base overflow")?;
        let mut terms=Vec::new();
        let counts=roster.visit_header_terms(owner as u64,|mut term|{
            term.row=term.row.checked_sub(row_base).ok_or("C325 row underflow")?;
            term.gate.left=term.gate.left.checked_sub(wire_base).ok_or("C325 left underflow")?;
            term.gate.right=term.gate.right.checked_sub(wire_base).ok_or("C325 right underflow")?;
            terms.push(term);Ok(())
        })?;
        if counts.emitted!=terms.len()||terms.len()!=396_561{
            return Err(format!("C325 owner {owner} header template size drift"));
        }
        captured.push(terms);
    }
    if captured.iter().skip(1).any(|terms|terms!=&captured[0]){
        return Err("C325 four Carry templates differ".into());
    }
    let mut encoded=Vec::with_capacity(captured[0].len()*152);
    for term in &captured[0]{
        encoded.extend_from_slice(&u64::try_from(term.row).map_err(|_|"C325 row width")?.to_le_bytes());
        encoded.extend_from_slice(&u64::try_from(term.gate.left).map_err(|_|"C325 left width")?.to_le_bytes());
        encoded.extend_from_slice(&u64::try_from(term.gate.right).map_err(|_|"C325 right width")?.to_le_bytes());
        for coefficient in [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]{
            ark_serialize::CanonicalSerialize::serialize_compressed(&coefficient,&mut encoded)
                .map_err(|error|format!("C325 coefficient encoding failed: {error}"))?;
        }
    }
    if digest(&encoded)?!=TEMPLATE_SHA256{return Err("C325 template digest differs from pinned C323/C321 value".into());}
    drop(encoded);
    let templates:[Vec<crate::sparse::Term>;4]=captured.try_into().map_err(|_|"C325 Carry template count")?;
    if templates[0].iter().any(|term|term.row>=OWNER_ROWS||term.gate.left>=OWNER_WIDTH||term.gate.right>=OWNER_WIDTH){
        return Err("C325 Carry template has out-of-range local term".into());
    }

    let row_point=(23u64..=41).map(Fr::from).collect::<Vec<_>>();
    if row_point.len()!=19{return Err("C325 local row point width".into());}
    let local_row_weights=crate::gkr::eq_weights(&row_point);
    if local_row_weights.len()!=OWNER_ROWS{return Err("C325 local row weight length".into());}
    let q=Fr::from(2u64);
    let prefix=[q];
    let prefix_weights=crate::gkr::eq_weights(&prefix);
    if prefix_weights.len()!=2||prefix_weights[0]!=Fr::one()-q||prefix_weights[1]!=q{
        return Err("C325 U1 prefix equality weights drift".into());
    }
    const OWNER_FACTOR_PINS:[&str;4]=[
        "01aa49fb353c46ff8970b97948e833285d588181b64550b829a031e1724e6430",
        "00ac6ce9bb7237890e0000000000000000000000000000000000000000000000",
        "018053fd9ea2a0f98370b97948e833285d588181b64550b829a031e1724e6430",
        "000059e5e9a582941a0000000000000000000000000000000000000000000000",
    ];
    let owner_point=(2u64..=22).map(Fr::from).collect::<Vec<_>>();
    let owner_factors:[Fr;4]=std::array::from_fn(|index|{
        let owner=OWNERS[index];
        owner_point.iter().enumerate().fold(Fr::one(),|product,(bit,coordinate)|{
            if ((owner>>bit)&1)==1{product * *coordinate}else{product*(Fr::one()-*coordinate)}
        })
    });
    for (index,factor) in owner_factors.iter().enumerate(){
        let mut bytes=Vec::new();ark_serialize::CanonicalSerialize::serialize_compressed(factor,&mut bytes)
            .map_err(|error|format!("C325 factor encoding failed: {error}"))?;
        if factor.is_zero()||factor.is_one()||hex(&bytes)!=OWNER_FACTOR_PINS[index]{
            return Err(format!("C325 owner {} factor differs from pinned C323/C321 value",OWNERS[index]));
        }
    }

    let mut comparisons=Vec::with_capacity(OWNERS.len());
    let mut literal_term_visits=0u64;
    let mut fused_term_visits=0u64;
    let mut boolean_checked_fields=0usize;
    let mut folded_nonboolean_fields=0usize;
    for index in 0..OWNERS.len(){
        let owner=OWNERS[index];
        let mut original_x=Vec::with_capacity(OWNER_WIDTH);
        for wire in 0..OWNER_WIDTH{
            original_x.push(Fr::from(fragment_bit(&admitted.fixture,owner,wire)? as u64));
        }
        if original_x.len()!=OWNER_WIDTH||original_x.iter().any(|value|!value.is_zero()&&!value.is_one()){
            return Err(format!("C325 owner {owner} full X is not Boolean"));
        }
        boolean_checked_fields=boolean_checked_fields.checked_add(original_x.len())
            .ok_or("C325 Boolean field count overflow")?;
        let mut folded_x=original_x.clone();
        crate::gkr::fold(&mut folded_x,q);
        if folded_x.len()!=OWNER_WIDTH/2{return Err("C325 folded X width drift".into());}
        folded_nonboolean_fields=folded_nonboolean_fields.checked_add(
            folded_x.iter().filter(|value|!value.is_zero()&&!value.is_one()).count(),
        ).ok_or("C325 folded non-Boolean count overflow")?;

        // Independent literal construction of A/B from every captured term.
        // Build full-width A/B with row equality only; folding by q applies the
        // first-prefix equality on the input wire bit exactly once.
        let mut dense_a=vec![Fr::zero();OWNER_WIDTH];
        let mut dense_b=vec![Fr::zero();OWNER_WIDTH];
        for term in &templates[index]{
            let row_weight=local_row_weights[term.row];
            let selected_right=original_x[term.gate.right];
            dense_a[term.gate.left]+=row_weight*(term.gate.c1+term.gate.c3*selected_right);
            dense_b[term.gate.left]+=row_weight*(term.gate.c0+term.gate.c2*selected_right);
            literal_term_visits=literal_term_visits.checked_add(1).ok_or("C325 literal visit overflow")?;
        }
        crate::gkr::fold(&mut dense_a,q);
        crate::gkr::fold(&mut dense_b,q);
        let dense_message:[Fr;3]=crate::gkr::quadratic_message(&dense_a,&dense_b,&folded_x)
            .try_into().map_err(|_|"C325 dense message width")?;
        let fused=crate::sparse_stream_roster::c325_fused_prefix_u_message_for_test(
            &templates[index],&prefix,&local_row_weights,&original_x,&folded_x,
        )?;
        fused_term_visits=fused_term_visits.checked_add(templates[index].len() as u64)
            .ok_or("C325 fused visit overflow")?;
        let scaled_fused=fused.map(|coefficient|coefficient*owner_factors[index]);
        let scaled_dense=dense_message.map(|coefficient|coefficient*owner_factors[index]);
        if scaled_fused!=scaled_dense{
            return Err(format!("C325 owner {owner} fused U1 message differs from literal dense reference"));
        }
        comparisons.push(serde_json::json!({"owner":owner,"equal":true}));
    }
    if boolean_checked_fields!=4*OWNER_WIDTH||folded_nonboolean_fields==0
        ||literal_term_visits!=1_586_244||fused_term_visits!=1_586_244{
        return Err("C325 Boolean/folded field or exact term visit counts drift".into());
    }
    println!("C325_U1_PASS {}",serde_json::json!({
        "schema":1,"scope":"header_only_k1_four_c319_carry","full_proof":false,
        "owners":OWNERS,"carry_census":carry_census,"template_terms":templates[0].len(),
        "template_sha256":TEMPLATE_SHA256,"c319_receipt_sha256":C319_RECEIPT_SHA256,
        "c319_runner_receipt_sha256":C319_RUNNER_RECEIPT_SHA256,
        "c319_source_closure_sha256":C319_SOURCE_CLOSURE_SHA256,
        "c319_fixture_sha256":C319_FIXTURE_SHA256,"owner_messages_equal":comparisons,
        "all_four_owner_messages_equal":true,"q":2,"prefix_len":1,
        "local_row_weight_count":local_row_weights.len(),"full_x_width":OWNER_WIDTH,
        "folded_x_width":OWNER_WIDTH/2,"boolean_checked_fields":boolean_checked_fields,
        "folded_nonboolean_fields":folded_nonboolean_fields,
        "literal_term_visits":literal_term_visits,"fused_term_visits":fused_term_visits,
        "owner_factor_applied_after_message":true
    }));
    Ok(())
}

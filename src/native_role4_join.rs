//! Test-only, witness-free receiver for the diagnostic whole-S12 GKR→PCS32 join.
//!
//! The verifier accepts only a code-owned statement policy and verifier-key
//! digest. It derives the role-4 endpoint relation from the retained native
//! plan, derives the PCS claim from a fresh GKR verification, then verifies Dory
//! at that claim. This does not authenticate the RAW preimage or all history.

use dory_pcs::backends::arkworks::ArkGT;
use serde_json::{json, Value};
use std::collections::BTreeMap;

use crate::{
    daa_history_roster::DaaHistoryRoster,
    gkr::{GkrProof, InputClaim},
    historical_prefix_height_work::HeightWork,
    native_prefix_auth_plan::{Role4EndpointAdapter, Role4EndpointScope},
    pcs,
    transcript::Transcript,
    verifier_key::AdmittedVerifierKey,
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const STATEMENT_SCHEMA: &str = "native-role4-gkr-pcs32-statement-v1";
const MANIFEST_SCHEMA: &str = "native-role4-gkr-pcs32-manifest-v1";
const TRANSCRIPT_DOMAIN: &[u8] = b"native-role4-gkr-pcs32-diagnostic-v1";
const SOURCE_REVISION: &str = "8995ff243b140e7fe716bd3204423dd35690c2e4";
const NATIVE_PROFILE: &str = "role4-whole-s12";
const RAW_BYTES: u64 = 869_449;
const RAW_SHA256: &str = "ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const WITNESS_BYTES: u64 = 536_870_912;
const WITNESS_SHA256: &str = "C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
const ROOT_HEX: &str = "DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913";
const TOTAL_WORK_HEX: &str = "000000000000000000000000000000000000000000564F0B9B000000";
const EXPECTED_VK_SHA256: &str = "D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2";
const SETUP_ID_HEX: &str = "1ae7badc1e529c7a5cda709ad1b418af6ae2efb6b7b4d909816d091c3260a51b";
const SETUP_ID_JSON: &str = "1AE7BADC1E529C7A5CDA709AD1B418AF6AE2EFB6B7B4D909816D091C3260A51B";
const PCS_VENDOR_TEXT: &str = "5246DA503C3E2C6BAA40EC00D714987C73A3E6EB";
const PCS_MODE: &str = "Transparent-dory-v1";
const LOG_N: usize = 32;
const KEY_BYTES: usize = 33_264;
const COMMITMENT_BYTES: usize = 384;
const GKR_BYTES: usize = 7_264;
const DORY_BYTES: usize = 42_381;
const STATEMENT_CAP: usize = 8_192;
const MANIFEST_CAP: usize = 8_192;
const PACKAGE_CAP: usize = 100_000;

/// A checked, immutable preamble. The producer receives only a clone of the
/// initial transcript; verification starts from the same bytes independently.
pub(crate) struct BoundRole4Transcript {
    statement: Vec<u8>,
    commitment: ArkGT,
    key: AdmittedVerifierKey,
    context_sha256: [u8; 32],
    transcript: Transcript,
}

impl BoundRole4Transcript {
    pub(crate) fn statement_bytes(&self) -> &[u8] {
        &self.statement
    }

    /// Clone the already-bound prefix for the private live producer.
    pub(crate) fn producer_transcript(&self) -> Transcript {
        self.transcript.clone()
    }

    pub(crate) fn verify_gkr(&self, proof_bytes: &[u8]) -> Result<VerifiedInputClaim, String> {
        if proof_bytes.len() != GKR_BYTES {
            return Err("GKR proof extent mismatch".into());
        }
        let proof = crate::gkr::decode_dimensions(&[LOG_N], proof_bytes)?;
        if crate::gkr::encode_proof(&proof)? != proof_bytes {
            return Err("GKR proof canonical re-encoding mismatch".into());
        }

        let parent = compile_expected_parent()?;
        let height = HeightWork::compile_history(&parent)?;
        let daa = DaaHistoryRoster::compile(&parent)?;
        let adapter = Role4EndpointAdapter::new(&height, &daa, Role4EndpointScope::WholeS12)?;
        let mut transcript = self.transcript.clone();
        // The statement/preamble binds the fixed circuit descriptor already;
        // no caller-supplied bind closure may alter the verifier transcript.
        let requests = std::cell::Cell::new(0usize);
        let claim = crate::gkr::verify_with_wiring(
            &[LOG_N],
            1usize << LOG_N,
            &proof,
            &mut transcript,
            |_| {},
            |layer, r, u, v| {
                if layer != 0 || r.len() != LOG_N || u.len() != LOG_N || v.len() != LOG_N {
                    return Err(crate::gkr::GkrError::PointDimension);
                }
                requests.set(requests.get() + 1);
                adapter
                    .coefficients(r, u, v)
                    .map_err(|_| crate::gkr::GkrError::TerminalExpression)
            },
        )
        .map_err(|e| e.to_string())?;
        if requests.get() != 1 || claim.point.len() != LOG_N {
            return Err("GKR role-4 wiring closure mismatch".into());
        }
        Ok(VerifiedInputClaim {
            claim,
            transcript,
            context_sha256: self.context_sha256,
        })
    }

    /// Consume a claim token created by this context; callers cannot supply a
    /// PCS point or value independently of fresh GKR verification.
    pub(crate) fn verify_dory(
        &self,
        token: VerifiedInputClaim,
        proof_bytes: &[u8],
    ) -> Result<(), String> {
        if token.context_sha256 != self.context_sha256 {
            return Err("GKR claim belongs to another statement context".into());
        }
        if proof_bytes.len() != DORY_BYTES {
            return Err("Dory proof extent mismatch".into());
        }
        let proof = pcs::decode_proof(proof_bytes, LOG_N)?;
        let mut transcript = token.transcript;
        pcs::verify_admitted(
            self.commitment.clone(),
            token.claim.value,
            &token.claim.point,
            &proof,
            &self.key,
            &mut transcript,
        )
    }

    pub(crate) fn verify_gkr_and_dory(
        &self,
        gkr_bytes: &[u8],
        dory_bytes: &[u8],
    ) -> Result<InputClaim, String> {
        let token = self.verify_gkr(gkr_bytes)?;
        let claim = token.claim.clone();
        self.verify_dory(token, dory_bytes)?;
        Ok(claim)
    }
}

/// Opaque proof-derived claim plus the exact transcript continuation required
/// by PCS verification. Only read access to the derived claim is exposed.
pub(crate) struct VerifiedInputClaim {
    claim: InputClaim,
    transcript: Transcript,
    context_sha256: [u8; 32],
}

impl VerifiedInputClaim {
    pub(crate) fn claim(&self) -> &InputClaim {
        &self.claim
    }

    pub(crate) fn transcript(&self) -> &Transcript {
        &self.transcript
    }
}

/// Build the canonical statement from the code-owned expected policy and a
/// canonical encoded commitment. The verifier-key digest remains fail-closed
/// until ROOT binds the independently exported key SHA-256 in this source.
pub(crate) fn expected_statement_bytes(commitment_bytes: &[u8]) -> Result<Vec<u8>, String> {
    let key_sha = checked_expected_key_sha()?;
    let commitment = decode_commitment(commitment_bytes)?;
    let commitment_sha = sha256_hex(commitment_bytes)?;
    let value = expected_statement_value(&key_sha, &commitment_sha)?;
    let bytes = canonical_json(&value)?;
    if bytes.len() > STATEMENT_CAP {
        return Err("statement exceeds 8192 bytes".into());
    }
    let _ = commitment;
    Ok(bytes)
}

pub(crate) fn start_transcript(
    statement_bytes: &[u8],
    key_bytes: &[u8],
    commitment_bytes: &[u8],
) -> Result<BoundRole4Transcript, String> {
    if statement_bytes.len() > STATEMENT_CAP {
        return Err("statement exceeds 8192 bytes".into());
    }
    let expected_key_sha = checked_expected_key_sha()?;
    let expected_key_sha_bytes = decode_hex::<32>(&expected_key_sha)?;
    if key_bytes.len() != KEY_BYTES {
        return Err("PCS32 key extent mismatch".into());
    }
    let actual_key_sha = sha256(key_bytes)?;
    if actual_key_sha != expected_key_sha_bytes {
        return Err("code-owned PCS32 key SHA-256 mismatch".into());
    }

    let commitment = decode_commitment(commitment_bytes)?;
    let commitment_sha = sha256_hex(commitment_bytes)?;
    let expected_value = expected_statement_value(&expected_key_sha, &commitment_sha)?;
    validate_statement_bytes(statement_bytes, &expected_value)?;

    let setup_id = decode_hex::<32>(SETUP_ID_HEX)?;
    let key = crate::verifier_key::admit_generated_test_key(LOG_N, key_bytes, setup_id)?;
    if key.log_n() != LOG_N || key.id() != &setup_id {
        return Err("admitted key setup identity mismatch".into());
    }

    let mut transcript = Transcript::new(TRANSCRIPT_DOMAIN);
    bind_preamble(
        &mut transcript,
        statement_bytes,
        commitment_bytes,
        &expected_key_sha_bytes,
        &setup_id,
    );
    let mut context_input = Vec::with_capacity(statement_bytes.len() + commitment_bytes.len() + 32);
    context_input.extend_from_slice(statement_bytes);
    context_input.extend_from_slice(&expected_key_sha_bytes);
    context_input.extend_from_slice(commitment_bytes);
    let context_sha256 = sha256(&context_input)?;

    Ok(BoundRole4Transcript {
        statement: statement_bytes.to_vec(),
        commitment,
        key,
        context_sha256,
        transcript,
    })
}

fn bind_preamble(
    transcript: &mut Transcript,
    statement: &[u8],
    commitment: &[u8],
    key_sha: &[u8; 32],
    setup_id: &[u8; 32],
) {
    bind_common_pcs_preamble(transcript, statement, commitment, key_sha, setup_id, LOG_N);
    transcript.append_bytes(
        b"gkr-circuit",
        b"whole-s12-v20-high-v12-line33-input-claim-v1",
    );
    transcript.append_u64(b"gkr-input-log-n", LOG_N as u64);
    transcript.append_u64(b"gkr-output-width", 1u64 << LOG_N);
}

fn bind_common_pcs_preamble(
    transcript: &mut Transcript,
    statement: &[u8],
    commitment: &[u8],
    key_sha: &[u8; 32],
    setup_id: &[u8; 32],
    log_n: usize,
) {
    transcript.append_bytes(b"role4-statement-canonical-json", statement);
    transcript.append_bytes(b"pcs-vendor", pcs::VENDOR_PIN);
    transcript.append_bytes(b"pcs-mode", PCS_MODE.as_bytes());
    transcript.append_bytes(b"pcs-setup-id", setup_id);
    transcript.append_bytes(b"pcs-verifier-key-sha256", key_sha);
    transcript.append_u64(b"pcs-log-n", log_n as u64);
    transcript.append_bytes(b"pcs-commitment-canonical", commitment);
}

fn expected_statement_value(key_sha: &str, commitment_sha: &str) -> Result<Value, String> {
    let parent = compile_expected_parent()?;
    let height = HeightWork::compile_history(&parent)?;
    let daa = DaaHistoryRoster::compile(&parent)?;
    let adapter = Role4EndpointAdapter::new(&height, &daa, Role4EndpointScope::WholeS12)?;
    let binding = adapter.binding();
    let identities = binding
        .whole_alias_identities
        .ok_or("whole-S12 aliases absent")?;
    let aliases: Vec<String> = identities
        .iter()
        .flat_map(|pair| pair.iter())
        .map(|id| hex_upper(id))
        .collect();
    if aliases.len() != 4 {
        return Err("whole-S12 alias identity count".into());
    }
    Ok(json!({
        "schema": STATEMENT_SCHEMA,
        "version": 1,
        "official_source_revision": SOURCE_REVISION,
        "native_profile": NATIVE_PROFILE,
        "raw_sha256": RAW_SHA256,
        "raw_bytes": RAW_BYTES,
        "witness_sha256": WITNESS_SHA256,
        "witness_bytes": WITNESS_BYTES,
        "scalar_count": 4_294_967_296u64,
        "scalar_semantics": "2^32 Boolean scalars stored as bits, each Fr encoded in 32 bytes",
        "field_encoding": "BN254Fr-canonical-little-endian-32",
        "pcs_vendor": PCS_VENDOR_TEXT,
        "pcs_mode": PCS_MODE,
        "pcs_setup_id": SETUP_ID_JSON,
        "pcs_log_n": 32,
        "pcs_vk_sha256": key_sha,
        "commitment_sha256": commitment_sha,
        "headers": 3073,
        "slots": 4096,
        "slot_log": 12,
        "input_log": 32,
        "row_log": 32,
        "role_index": 4,
        "local_input_log": 20,
        "base_row_log": 19,
        "family_log": 1,
        "height_member_row_log": 19,
        "daa_member_row_log": 19,
        "parent_root": ROOT_HEX,
        "parent_total_work_be28": TOTAL_WORK_HEX,
        "aliases": aliases,
    }))
}

fn compile_expected_parent() -> Result<WorkTreeHistoryPlan, String> {
    let root = decode_hex::<32>(ROOT_HEX)?;
    let total = decode_hex::<28>(TOTAL_WORK_HEX)?;
    WorkTreeHistoryPlan::compile(3073, 12, root, total)
}

fn decode_commitment(bytes: &[u8]) -> Result<ArkGT, String> {
    if bytes.len() != COMMITMENT_BYTES {
        return Err("PCS32 commitment extent mismatch".into());
    }
    pcs::decode_commitment(bytes)
}

fn canonical_json(value: &Value) -> Result<Vec<u8>, String> {
    serde_json::to_vec(value).map_err(|e| e.to_string())
}

fn validate_statement_bytes(bytes: &[u8], expected: &Value) -> Result<(), String> {
    let parsed: Value = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    if canonical_json(&parsed)? != bytes {
        return Err("statement JSON is not canonical".into());
    }
    if &parsed != expected {
        return Err("statement is not the canonical code-owned policy".into());
    }
    Ok(())
}

fn checked_expected_key_sha() -> Result<String, String> {
    if EXPECTED_VK_SHA256.len() != 64
        || !EXPECTED_VK_SHA256
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_lowercase())
    {
        return Err("trusted PCS32 verifier-key SHA-256 pin is not bound".into());
    }
    Ok(EXPECTED_VK_SHA256.to_owned())
}

fn decode_hex<const N: usize>(text: &str) -> Result<[u8; N], String> {
    if text.len() != 2 * N || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("fixed hexadecimal extent".into());
    }
    let mut out = [0u8; N];
    for (index, pair) in text.as_bytes().chunks_exact(2).enumerate() {
        let digit = |b: u8| -> Result<u8, String> {
            match b {
                b'0'..=b'9' => Ok(b - b'0'),
                b'a'..=b'f' => Ok(b - b'a' + 10),
                b'A'..=b'F' => Ok(b - b'A' + 10),
                _ => Err("invalid hexadecimal digit".into()),
            }
        };
        out[index] = (digit(pair[0])? << 4) | digit(pair[1])?;
    }
    Ok(out)
}

fn hex_upper(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 15) as usize] as char);
    }
    out
}

fn sha256(bytes: &[u8]) -> Result<[u8; 32], String> {
    if bytes.len() > PACKAGE_CAP {
        return Err("SHA-256 input exceeds closed package cap".into());
    }
    use std::ffi::c_void;
    #[link(name = "crypt32")]
    extern "system" {
        fn CryptHashCertificate2(
            algorithm: *const u16,
            flags: u32,
            reserved: *mut c_void,
            data: *const u8,
            length: u32,
            output: *mut u8,
            output_length: *mut u32,
        ) -> i32;
    }
    let length = u32::try_from(bytes.len()).map_err(|e| e.to_string())?;
    let algorithm = [83u16, 72, 65, 50, 53, 54, 0];
    let mut out = [0u8; 32];
    let mut output_length = out.len() as u32;
    let ok = unsafe {
        CryptHashCertificate2(
            algorithm.as_ptr(),
            0,
            std::ptr::null_mut(),
            bytes.as_ptr(),
            length,
            out.as_mut_ptr(),
            &mut output_length,
        )
    };
    if ok == 0 || output_length != 32 {
        return Err("Windows SHA-256 provider failed".into());
    }
    Ok(out)
}

fn sha256_hex(bytes: &[u8]) -> Result<String, String> {
    Ok(hex_upper(&sha256(bytes)?))
}

/// Closed six-file proof-package validation; the manifest lists only the other
/// five files and is itself pinned by the outer settled controller receipt.
pub(crate) fn validate_package(
    members: &BTreeMap<String, Vec<u8>>,
) -> Result<ValidatedPackage, String> {
    let manifest_sha256 = validate_closed_members(members)?;
    let context = start_transcript(
        &members["statement.json"],
        &members["public-key.bin"],
        &members["commitment.bin"],
    )?;
    Ok(ValidatedPackage {
        context,
        gkr_proof: members["gkr-proof.bin"].clone(),
        dory_proof: members["dory-proof.bin"].clone(),
        manifest_sha256,
    })
}

fn validate_closed_members(members: &BTreeMap<String, Vec<u8>>) -> Result<String, String> {
    const NAMES: [&str; 6] = [
        "commitment.bin",
        "dory-proof.bin",
        "gkr-proof.bin",
        "manifest.json",
        "public-key.bin",
        "statement.json",
    ];
    if members.len() != NAMES.len() || NAMES.iter().any(|name| !members.contains_key(*name)) {
        return Err("proof package must contain exactly the six closed filenames".into());
    }
    let total = members.values().try_fold(0usize, |sum, bytes| {
        sum.checked_add(bytes.len())
            .ok_or("package extent overflow")
    })?;
    if total > PACKAGE_CAP {
        return Err("aggregate proof package exceeds 100000 bytes".into());
    }
    for (name, expected) in [
        ("public-key.bin", KEY_BYTES),
        ("commitment.bin", COMMITMENT_BYTES),
        ("gkr-proof.bin", GKR_BYTES),
        ("dory-proof.bin", DORY_BYTES),
    ] {
        if members[name].len() != expected {
            return Err(format!("{name} extent mismatch"));
        }
    }
    if members["statement.json"].len() > STATEMENT_CAP
        || members["manifest.json"].len() > MANIFEST_CAP
    {
        return Err("statement or manifest cap exceeded".into());
    }
    let mut expected_files = Vec::new();
    for name in NAMES
        .iter()
        .copied()
        .filter(|name| *name != "manifest.json")
    {
        let bytes = &members[name];
        expected_files
            .push(json!({"name": name, "bytes": bytes.len(), "sha256": sha256_hex(bytes)?}));
    }
    expected_files.sort_by(|a, b| a["name"].as_str().cmp(&b["name"].as_str()));
    let expected_manifest = json!({"schema": MANIFEST_SCHEMA, "files": expected_files});
    let manifest_bytes = &members["manifest.json"];
    let manifest: Value = serde_json::from_slice(manifest_bytes).map_err(|e| e.to_string())?;
    if canonical_json(&manifest)? != *manifest_bytes || manifest != expected_manifest {
        return Err("manifest is not the exact canonical five-member closure".into());
    }
    sha256_hex(manifest_bytes)
}

pub(crate) struct ValidatedPackage {
    pub(crate) context: BoundRole4Transcript,
    pub(crate) gkr_proof: Vec<u8>,
    pub(crate) dory_proof: Vec<u8>,
    /// The outer receipt must bind this digest; it is not self-listed.
    pub(crate) manifest_sha256: String,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sparse;
    use ark_bn254::Fr;
    use ark_ff::{One, Zero};

    #[test]
    fn trusted_key_pin_is_exact_uppercase_sha256() {
        let pin = checked_expected_key_sha().expect("ROOT must bind the reviewed export pin");
        assert_eq!(pin.len(), 64);
        assert!(pin
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'A'..=b'F').contains(&byte)));
        assert_eq!(hex_upper(&decode_hex::<32>(&pin).unwrap()), pin);
    }

    #[test]
    fn commitment_codec_rejects_wrong_extent_before_decode() {
        assert!(decode_commitment(&[0u8; COMMITMENT_BYTES - 1])
            .unwrap_err()
            .contains("extent"));
        assert!(pcs::decode_commitment(&[]).is_err());
    }

    #[test]
    fn package_inventory_and_fixed_extents_reject_single_faults() {
        let mut members = BTreeMap::new();
        for (name, len) in [
            ("commitment.bin", COMMITMENT_BYTES),
            ("dory-proof.bin", DORY_BYTES),
            ("gkr-proof.bin", GKR_BYTES),
            ("public-key.bin", KEY_BYTES),
            ("statement.json", 2),
        ] {
            members.insert(name.to_owned(), vec![0u8; len]);
        }
        let manifest = make_manifest(&members);
        members.insert("manifest.json".into(), manifest);
        let pristine = members.clone();
        let pinned = validate_closed_members(&pristine).unwrap();
        assert_eq!(pinned, sha256_hex(&pristine["manifest.json"]).unwrap());

        let mut changed_member = pristine.clone();
        changed_member.get_mut("gkr-proof.bin").unwrap()[0] ^= 1;
        assert!(validate_closed_members(&changed_member)
            .err()
            .unwrap()
            .contains("manifest"));

        let mut extra_member = pristine.clone();
        extra_member.insert("extra.bin".into(), Vec::new());
        assert!(validate_closed_members(&extra_member)
            .err()
            .unwrap()
            .contains("exactly the six"));

        for name in [
            "public-key.bin",
            "commitment.bin",
            "gkr-proof.bin",
            "dory-proof.bin",
        ] {
            for oversized in [false, true] {
                let mut wrong_extent = pristine.clone();
                let bytes = wrong_extent.get_mut(name).unwrap();
                if oversized {
                    bytes.push(0);
                } else {
                    bytes.pop();
                }
                assert!(validate_closed_members(&wrong_extent)
                    .unwrap_err()
                    .contains(&format!("{name} extent mismatch")));
            }
        }
        for name in ["statement.json", "manifest.json"] {
            let mut oversized = pristine.clone();
            oversized.insert(name.into(), vec![0u8; 8193]);
            assert!(validate_closed_members(&oversized)
                .unwrap_err()
                .contains("cap exceeded"));
        }
        let mut missing_member = pristine;
        missing_member.remove("commitment.bin");
        assert!(validate_closed_members(&missing_member)
            .err()
            .unwrap()
            .contains("exactly the six"));
    }

    #[test]
    fn statement_policy_requires_exact_sorted_canonical_bytes() {
        let expected = expected_statement_value(&"A".repeat(64), &"B".repeat(64)).unwrap();
        let canonical = canonical_json(&expected).unwrap();
        validate_statement_bytes(&canonical, &expected).unwrap();
        let spaced = serde_json::to_string_pretty(&expected).unwrap();
        assert!(validate_statement_bytes(spaced.as_bytes(), &expected)
            .unwrap_err()
            .contains("not canonical"));
        let mut changed = expected.clone();
        changed["native_profile"] = json!("other-role");
        assert!(
            validate_statement_bytes(&canonical_json(&changed).unwrap(), &expected)
                .unwrap_err()
                .contains("code-owned policy")
        );
        let duplicate = b"{\"a\":1,\"a\":1}";
        assert!(validate_statement_bytes(duplicate, &expected).is_err());
    }

    #[test]
    fn key_pin_is_checked_before_test_key_admission() {
        let error = start_transcript(b"{}", &[0u8; KEY_BYTES], &[0u8; COMMITMENT_BYTES])
            .err()
            .unwrap();
        assert!(error.contains("code-owned PCS32 key SHA-256 mismatch"));
    }

    #[test]
    fn proof_extents_are_closed() {
        let wrong = vec![0u8; GKR_BYTES - 1];
        assert!(crate::gkr::decode_dimensions(&[LOG_N], &wrong).is_err());
        assert!(pcs::decode_proof(&vec![0u8; DORY_BYTES - 1], LOG_N).is_err());
    }

    #[test]
    fn shared_preamble_composes_log18_gkr_claim_with_dory_opening() {
        let log_n = 18;
        let key_bytes = include_bytes!("../fixtures/verifier-keys-v1/log18.vk");
        let key = crate::verifier_key::admit(log_n, key_bytes).unwrap();
        let setup = pcs::generate_setup(log_n).unwrap();
        assert_eq!(&setup.id, key.id());

        let witness = (0..(1usize << log_n))
            .map(|index| {
                if index & 1 == 0 {
                    Fr::zero()
                } else {
                    Fr::one()
                }
            })
            .collect::<Vec<_>>();
        let circuit = sparse::Circuit {
            input_len: 1usize << log_n,
            row_count: 1,
            terms: vec![sparse::Term {
                row: 0,
                gate: crate::gkr::Gate {
                    left: 0,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: -Fr::one(),
                    c3: Fr::zero(),
                },
            }],
        };
        let committed = pcs::commit(&witness, &setup).unwrap();
        let commitment_bytes = pcs::encode(&committed.commitment).unwrap();
        let key_sha = sha256(key_bytes).unwrap();
        let statement = br#"{"schema":"role4-shared-preamble-test-v1"}"#;
        let domain = b"role4-private-log18-shared-preamble-test-v1";

        // Commitment and all public PCS identity fields enter before GKR output-point sampling.
        let mut producer = Transcript::new(domain);
        bind_common_pcs_preamble(
            &mut producer,
            statement,
            &commitment_bytes,
            &key_sha,
            &setup.id,
            log_n,
        );
        let (proof, producer_claim) = sparse::prove(&circuit, &witness, 0, &mut producer).unwrap();
        let gkr_bytes = crate::gkr::encode_proof(&proof).unwrap();
        let decoded_gkr = sparse::decode_proof(&circuit, 0, &gkr_bytes).unwrap();
        let rejects_gkr = |candidate: &crate::gkr::GkrProof,
                           statement: &[u8],
                           commitment: &[u8],
                           candidate_key_sha: &[u8; 32],
                           candidate_setup_id: &[u8; 32],
                           candidate_log_n: usize| {
            let mut verifier = Transcript::new(domain);
            bind_common_pcs_preamble(
                &mut verifier,
                statement,
                commitment,
                candidate_key_sha,
                candidate_setup_id,
                candidate_log_n,
            );
            sparse::verify(&circuit, 0, candidate, &mut verifier).is_err()
        };

        let mut consumer = Transcript::new(domain);
        bind_common_pcs_preamble(
            &mut consumer,
            statement,
            &commitment_bytes,
            &key_sha,
            &setup.id,
            log_n,
        );
        let verified_claim = sparse::verify(&circuit, 0, &decoded_gkr, &mut consumer).unwrap();
        assert_eq!(verified_claim, producer_claim);
        assert_eq!(
            verified_claim.value,
            crate::gkr::mle(&witness, &verified_claim.point).unwrap()
        );

        let pre_pcs_consumer = consumer.clone();
        let opening = pcs::open(&committed, &producer_claim.point, &setup, &mut producer).unwrap();
        let opening_bytes = pcs::encode_proof(&opening).unwrap();
        let decoded_opening = pcs::decode_proof(&opening_bytes, log_n).unwrap();
        pcs::verify_admitted(
            committed.commitment.clone(),
            verified_claim.value,
            &verified_claim.point,
            &decoded_opening,
            &key,
            &mut consumer,
        )
        .unwrap();
        assert_eq!(
            producer.clone().challenge_scalar(b"post-pcs"),
            consumer.clone().challenge_scalar(b"post-pcs")
        );

        // Every receiver mutant starts from the original proof and a fresh transcript.
        let mut wrong_commitment_bytes = commitment_bytes.clone();
        wrong_commitment_bytes[0] ^= 1;
        assert!(rejects_gkr(
            &decoded_gkr,
            statement,
            &wrong_commitment_bytes,
            &key_sha,
            &setup.id,
            log_n,
        ));

        let alternate_witness = witness
            .iter()
            .map(|value| Fr::one() - *value)
            .collect::<Vec<_>>();
        let alternate_commitment = pcs::commit(&alternate_witness, &setup).unwrap();
        let alternate_commitment_bytes = pcs::encode(&alternate_commitment.commitment).unwrap();
        assert_ne!(alternate_commitment_bytes, commitment_bytes);
        assert!(rejects_gkr(
            &decoded_gkr,
            statement,
            &alternate_commitment_bytes,
            &key_sha,
            &setup.id,
            log_n,
        ));

        let changed_statement = br#"{"schema":"role4-shared-preamble-test-mutant-v1"}"#;
        assert!(rejects_gkr(
            &decoded_gkr,
            changed_statement,
            &commitment_bytes,
            &key_sha,
            &setup.id,
            log_n,
        ));
        let mut changed_key_sha = key_sha;
        changed_key_sha[0] ^= 1;
        assert!(rejects_gkr(
            &decoded_gkr,
            statement,
            &commitment_bytes,
            &changed_key_sha,
            &setup.id,
            log_n,
        ));
        let mut changed_setup_id = setup.id;
        changed_setup_id[0] ^= 1;
        assert!(rejects_gkr(
            &decoded_gkr,
            statement,
            &commitment_bytes,
            &key_sha,
            &changed_setup_id,
            log_n,
        ));
        assert!(rejects_gkr(
            &decoded_gkr,
            statement,
            &commitment_bytes,
            &key_sha,
            &setup.id,
            log_n - 1,
        ));

        let mut omitted_commitment = Transcript::new(domain);
        bind_common_preamble_without_commitment(
            &mut omitted_commitment,
            statement,
            &key_sha,
            &setup.id,
            log_n,
        );
        assert!(sparse::verify(&circuit, 0, &decoded_gkr, &mut omitted_commitment).is_err());
        let mut reordered_commitment = Transcript::new(domain);
        bind_common_preamble_commitment_first(
            &mut reordered_commitment,
            statement,
            &commitment_bytes,
            &key_sha,
            &setup.id,
            log_n,
        );
        assert!(sparse::verify(&circuit, 0, &decoded_gkr, &mut reordered_commitment).is_err());

        // First and second sumcheck polynomials are the U and V phases respectively.
        for round_index in [0, log_n] {
            let mut changed_phase_polynomial = decoded_gkr.clone();
            changed_phase_polynomial.layers[0].rounds[round_index][0] += Fr::one();
            assert!(rejects_gkr(
                &changed_phase_polynomial,
                statement,
                &commitment_bytes,
                &key_sha,
                &setup.id,
                log_n,
            ));
        }

        let mut wrong_gkr = decoded_gkr.clone();
        wrong_gkr.layers[0].line_coefficients[0] += Fr::one();
        assert!(rejects_gkr(
            &wrong_gkr,
            statement,
            &commitment_bytes,
            &key_sha,
            &setup.id,
            log_n,
        ));

        assert!(pcs::verify_admitted(
            committed.commitment.clone(),
            verified_claim.value + Fr::one(),
            &verified_claim.point,
            &decoded_opening,
            &key,
            &mut pre_pcs_consumer.clone(),
        )
        .is_err());
        let mut wrong_point = verified_claim.point.clone();
        wrong_point[0] += Fr::one();
        assert!(pcs::verify_admitted(
            committed.commitment.clone(),
            verified_claim.value,
            &wrong_point,
            &decoded_opening,
            &key,
            &mut pre_pcs_consumer.clone(),
        )
        .is_err());
        let mut corrupt_opening = opening_bytes;
        corrupt_opening[0] ^= 1;
        let corrupted = pcs::decode_proof(&corrupt_opening, log_n);
        assert!(
            corrupted.is_err()
                || pcs::verify_admitted(
                    committed.commitment.clone(),
                    verified_claim.value,
                    &verified_claim.point,
                    &corrupted.unwrap(),
                    &key,
                    &mut pre_pcs_consumer.clone(),
                )
                .is_err()
        );
    }

    fn make_manifest(members: &BTreeMap<String, Vec<u8>>) -> Vec<u8> {
        let files = members
            .iter()
            .map(|(name, bytes)| {
                json!({"name": name, "bytes": bytes.len(), "sha256": sha256_hex(bytes).unwrap()})
            })
            .collect::<Vec<_>>();
        canonical_json(&json!({"schema": MANIFEST_SCHEMA, "files": files})).unwrap()
    }

    fn bind_common_preamble_without_commitment(
        transcript: &mut Transcript,
        statement: &[u8],
        key_sha: &[u8; 32],
        setup_id: &[u8; 32],
        log_n: usize,
    ) {
        transcript.append_bytes(b"role4-statement-canonical-json", statement);
        transcript.append_bytes(b"pcs-vendor", pcs::VENDOR_PIN);
        transcript.append_bytes(b"pcs-mode", PCS_MODE.as_bytes());
        transcript.append_bytes(b"pcs-setup-id", setup_id);
        transcript.append_bytes(b"pcs-verifier-key-sha256", key_sha);
        transcript.append_u64(b"pcs-log-n", log_n as u64);
    }

    fn bind_common_preamble_commitment_first(
        transcript: &mut Transcript,
        statement: &[u8],
        commitment: &[u8],
        key_sha: &[u8; 32],
        setup_id: &[u8; 32],
        log_n: usize,
    ) {
        transcript.append_bytes(b"role4-statement-canonical-json", statement);
        transcript.append_bytes(b"pcs-vendor", pcs::VENDOR_PIN);
        transcript.append_bytes(b"pcs-mode", PCS_MODE.as_bytes());
        transcript.append_bytes(b"pcs-commitment-canonical", commitment);
        transcript.append_bytes(b"pcs-setup-id", setup_id);
        transcript.append_bytes(b"pcs-verifier-key-sha256", key_sha);
        transcript.append_u64(b"pcs-log-n", log_n as u64);
    }
}

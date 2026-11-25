//! Bounded diagnostic for projecting one fixed compression bank from a native
//! packed window. This is test-only evidence; it does not define a proof profile.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::{ArkGT, ArkworksVerifierSetup};
use serde_json::json;
use std::{
    fs::{self, OpenOptions},
    io::Write,
    time::Instant,
};

use crate::{
    circuit::{self, CompressionLayout},
    gkr::{self, GkrError, GkrProof, InputClaim},
    packed::{PackedFile, PackedIoSnapshot},
    sparse::{self, Circuit as SparseCircuit, Shape, Term},
    sparse_stream_roster,
    transcript::Transcript,
    work_tree_layout,
};

const SOURCE_SHA256: &str = "5771F251321B9A1EB5B7B8438F822DC54DC79668EBD1D66443B2983C3CC9F2FF";
const SOURCE_BITS: usize = 1 << 24;
const SOURCE_BYTES: u64 = 1 << 21;
const CORE_INPUT_BITS: usize = 16;
const CORE_ROW_BITS: usize = 17;
const SLOT_BITS: usize = 4;
const OWNER_COUNT: usize = 1 << SLOT_BITS;
const BANK_INDEX: usize = 0;
const BANK_START: usize = 0;
const BANK_WIDTH: usize = 1 << CORE_INPUT_BITS;
const CORE_ROWS: usize = 1 << CORE_ROW_BITS;
const CORE_TERMS: usize = 172_480;
const PARENT_LOG_N: usize = 24;
const PARENT_OWNER_BITS: usize = 20;
const BANK_COPY_FACTOR: usize = 16;
const RESULT_FILE: &str = "core-bank-projection-result.json";
const PROOF_FILE: &str = "core-bank-projection-gkr-proof.bin";
const TRANSCRIPT_DOMAIN: &[u8] = b"nipopow-v2-native-core-bank-projection-v1";
const COMMON_PCS_TRANSCRIPT_DOMAIN: &[u8] = b"nipopow-v2-native-bank0-parent-pcs-join-v1";
const COMMON_PCS_ARTIFACT_DIR_ENV: &str = "NIPOPOW_CORE_PCS_ARTIFACT_DIR";
const COMMON_PCS_COMMITMENT_FILE: &str = "common-pcs-parent-commitment.bin";
const COMMON_PCS_GKR_FILE: &str = "common-pcs-projected-gkr-proof.bin";
const COMMON_PCS_DORY_FILE: &str = "common-pcs-parent-opening.bin";
const COMMON_PCS_KEY_FILE: &str = "common-pcs-test-verifier-key.bin";
const COMMON_PCS_RESULT_FILE: &str = "common-pcs-result.json";

#[derive(Clone, Copy)]
struct ProjectionSpec {
    bank_index: usize,
    bank_start: usize,
    bank_width: usize,
    input_bits: usize,
    row_bits: usize,
    slot_bits: usize,
}

const BANK0_SPEC: ProjectionSpec = ProjectionSpec {
    bank_index: BANK_INDEX,
    bank_start: BANK_START,
    bank_width: BANK_WIDTH,
    input_bits: CORE_INPUT_BITS,
    row_bits: CORE_ROW_BITS,
    slot_bits: SLOT_BITS,
};

fn canonical_core() -> (SparseCircuit, CompressionLayout, String) {
    let baseline = work_tree_layout::shared_baseline().expect("canonical layout baseline");
    let built = circuit::build_compression(None).expect("canonical compression core");
    let layout = built.layout;
    let core = built.compiled.circuit;
    let digest = work_tree_layout::hash_terms(&core.terms);

    assert_eq!(layout, baseline.compression, "canonical compression layout pin");
    assert_eq!(core.input_len, BANK_WIDTH, "canonical core input width");
    assert_eq!(core.row_count, CORE_ROWS, "canonical core row width");
    assert_eq!(core.terms.len(), CORE_TERMS, "canonical core term count");
    assert_eq!(digest, baseline.inventory.core.terms_blake2b256, "canonical core term digest");

    (core, layout, digest)
}

fn validate_projection(core: &SparseCircuit, spec: ProjectionSpec) -> Result<Shape, String> {
    if spec.bank_index != BANK_INDEX
        || spec.bank_start != BANK_START
        || spec.bank_width != BANK_WIDTH
        || spec.input_bits != CORE_INPUT_BITS
        || spec.row_bits != CORE_ROW_BITS
        || spec.slot_bits != SLOT_BITS
    {
        return Err("fixed bank projection mapping mismatch".into());
    }
    if spec.bank_start.checked_add(spec.bank_width).is_none_or(|end| end > work_tree_layout::WIDTH)
        || spec.bank_width != 1usize.checked_shl(spec.input_bits as u32).ok_or("bank width overflow")?
        || work_tree_layout::WIDTH / spec.bank_width != BANK_COPY_FACTOR
        || spec.row_bits + spec.slot_bits > 24
        || spec.input_bits + spec.slot_bits > 24
    {
        return Err("fixed bank projection dimensions invalid".into());
    }
    if core.input_len != BANK_WIDTH
        || core.row_count != CORE_ROWS
        || core.terms.len() != CORE_TERMS
        || core.terms.iter().any(|term| {
            term.row >= CORE_ROWS
                || term.gate.left >= BANK_WIDTH
                || term.gate.right >= BANK_WIDTH
        })
    {
        return Err("canonical core geometry invalid".into());
    }
    sparse::validate(core, 0).map_err(|error| error.to_string())
}

fn bind_projection(transcript: &mut Transcript, core_digest: &str, spec: ProjectionSpec) {
    transcript.append_bytes(b"projection-relation", b"fixed-compression-bank0-v1");
    transcript.append_bytes(b"parent-source-sha256", SOURCE_SHA256.as_bytes());
    gkr::append_usize(transcript, b"projection-bank-index", spec.bank_index);
    gkr::append_usize(transcript, b"projection-bank-start", spec.bank_start);
    gkr::append_usize(transcript, b"projection-bank-width", spec.bank_width);
    gkr::append_usize(transcript, b"projection-core-input-bits", spec.input_bits);
    gkr::append_usize(transcript, b"projection-core-row-bits", spec.row_bits);
    gkr::append_usize(transcript, b"projection-slot-bits", spec.slot_bits);
    gkr::append_usize(transcript, b"projection-total-input-bits", spec.input_bits + spec.slot_bits);
    gkr::append_usize(transcript, b"projection-total-row-bits", spec.row_bits + spec.slot_bits);
    gkr::append_usize(transcript, b"parent-packed-input-bits", PARENT_LOG_N);
    gkr::append_usize(transcript, b"parent-owner-row-bits", PARENT_OWNER_BITS);
    gkr::append_usize(transcript, b"projected-claim-point-bits", spec.input_bits + spec.slot_bits);
    gkr::append_usize(transcript, b"projection-owner-count", 1usize << spec.slot_bits);
    transcript.append_bytes(b"projection-core-terms-blake2b256", core_digest.as_bytes());
    transcript.append_bytes(
        b"projection-coordinate-recipe",
        b"local-z16, fixed-bank-b4, source-slot-s4; owner-copy=owner*16+bank0",
    );
}

fn projected_wiring(
    core: &SparseCircuit,
    local_shape: &Shape,
    row_point: &[Fr],
    left_point: &[Fr],
    right_point: &[Fr],
) -> Result<[Fr; 4], String> {
    if row_point.len() != CORE_ROW_BITS + SLOT_BITS
        || left_point.len() != CORE_INPUT_BITS + SLOT_BITS
        || right_point.len() != CORE_INPUT_BITS + SLOT_BITS
    {
        return Err("projected wiring point dimensions".into());
    }
    let mut coefficients = sparse::wiring(
        core,
        local_shape,
        &row_point[..CORE_ROW_BITS],
        &left_point[..CORE_INPUT_BITS],
        &right_point[..CORE_INPUT_BITS],
    )
    .map_err(|error| error.to_string())?;

    let same_slot_factor = projection_slot_factor(row_point, left_point, right_point);
    for coefficient in &mut coefficients {
        *coefficient *= same_slot_factor;
    }
    Ok(coefficients)
}

fn projection_slot_factor(row_point: &[Fr], left_point: &[Fr], right_point: &[Fr]) -> Fr {
    let row_slots = gkr::eq_weights(&row_point[CORE_ROW_BITS..]);
    let left_slots = gkr::eq_weights(&left_point[CORE_INPUT_BITS..]);
    let right_slots = gkr::eq_weights(&right_point[CORE_INPUT_BITS..]);
    row_slots
        .iter()
        .zip(left_slots)
        .zip(right_slots)
        .fold(Fr::zero(), |sum, ((row, left), right)| sum + *row * left * right)
}

fn prove_projection(
    core: &SparseCircuit,
    core_digest: &str,
    spec: ProjectionSpec,
    load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    visit_terms: impl FnMut(usize, &mut dyn FnMut(Term) -> Result<(), String>) -> Result<(), String>,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), String> {
    let _ = validate_projection(core, spec)?;
    let local_shape = sparse::validate(core, 0).map_err(|error| error.to_string())?;
    sparse_stream_roster::prove(
        spec.input_bits,
        spec.slot_bits,
        spec.row_bits,
        0,
        &[spec.row_bits],
        load_copy,
        transcript,
        |transcript| bind_projection(transcript, core_digest, spec),
        visit_terms,
        |row, left, right| projected_wiring(core, &local_shape, row, left, right),
    )
}

fn checked_parent_claim(
    claim: &InputClaim,
    supplied_parent_point: &[Fr],
    evaluate: impl FnOnce(&[Fr]) -> Result<Fr, String>,
) -> Result<Fr, String> {
    if claim.point.len() != CORE_INPUT_BITS + SLOT_BITS {
        return Err("projected claim point dimension mismatch".into());
    }
    let expected_parent_point = work_tree_layout::embed_bank(
        BANK_START,
        BANK_WIDTH,
        SLOT_BITS,
        &claim.point,
    )?;
    if supplied_parent_point != expected_parent_point.as_slice() {
        return Err("parent point embedding mismatch".into());
    }
    if supplied_parent_point.len() != PARENT_LOG_N {
        return Err("parent point dimension mismatch".into());
    }
    let parent_value = evaluate(supplied_parent_point)?;
    if parent_value != claim.value {
        return Err("parent MLE claim mismatch".into());
    }
    Ok(parent_value)
}

fn resident_expanded_wiring(
    core: &SparseCircuit,
    row_point: &[Fr],
    left_point: &[Fr],
    right_point: &[Fr],
) -> [Fr; 4] {
    let row_weights = gkr::eq_weights(row_point);
    let left_weights = gkr::eq_weights(left_point);
    let right_weights = gkr::eq_weights(right_point);
    let mut coefficients = [Fr::zero(); 4];
    for owner in 0..OWNER_COUNT {
        let row_offset = owner * CORE_ROWS;
        let input_offset = owner * BANK_WIDTH;
        for term in &core.terms {
            let gate = &term.gate;
            let weight = row_weights[row_offset + term.row]
                * left_weights[input_offset + gate.left]
                * right_weights[input_offset + gate.right];
            coefficients[0] += weight * gate.c0;
            coefficients[1] += weight * gate.c1;
            coefficients[2] += weight * gate.c2;
            coefficients[3] += weight * gate.c3;
        }
    }
    coefficients
}

fn bool_point(width: usize, index: usize) -> Vec<Fr> {
    (0..width)
        .map(|bit| Fr::from(((index >> bit) & 1) as u64))
        .collect()
}

fn assert_embeds_index(point: &[Fr], local: usize, owner: usize) {
    let embedded = work_tree_layout::embed_bank(BANK_START, BANK_WIDTH, SLOT_BITS, point).unwrap();
    let index = owner * work_tree_layout::WIDTH + BANK_START + local;
    let expected = bool_point(PARENT_LOG_N, index);
    assert_eq!(embedded, expected, "parent point for owner {owner}, local {local}");
}

#[test]
fn fixed_bank_embedding_and_wiring_reject_invalid_mappings() {
    let (core, _, core_digest) = canonical_core();
    let shape = validate_projection(&core, BANK0_SPEC).unwrap();
    assert_eq!(shape.input_bits, CORE_INPUT_BITS);
    assert_eq!(shape.row_bits, CORE_ROW_BITS);
    assert_eq!(shape.copies, 1);

    for owner in [0, 1, OWNER_COUNT - 1] {
        for local in [0, 1, BANK_WIDTH / 2, BANK_WIDTH - 1] {
            let point = bool_point(CORE_INPUT_BITS + SLOT_BITS, local | (owner << CORE_INPUT_BITS));
            assert_embeds_index(&point, local, owner);
        }
    }

    let asymmetric: Vec<_> = (0..CORE_INPUT_BITS + SLOT_BITS)
        .map(|index| Fr::from((index + 2) as u64))
        .collect();
    let embedded = work_tree_layout::embed_bank(BANK_START, BANK_WIDTH, SLOT_BITS, &asymmetric).unwrap();
    assert_eq!(&embedded[..CORE_INPUT_BITS], &asymmetric[..CORE_INPUT_BITS]);
    assert_eq!(&embedded[CORE_INPUT_BITS..CORE_INPUT_BITS + 4], &[Fr::zero(); 4]);
    assert_eq!(&embedded[CORE_INPUT_BITS + 4..], &asymmetric[CORE_INPUT_BITS..]);

    let wrong_bank = work_tree_layout::embed_bank(BANK_WIDTH, BANK_WIDTH, SLOT_BITS, &asymmetric).unwrap();
    assert_ne!(wrong_bank, embedded, "wrong-bank mapping changes the public embedding");

    let mut malformed_claim = InputClaim { point: asymmetric.clone(), value: Fr::one() };
    malformed_claim.point.pop();
    let mut malformed_claim_evaluator_calls = 0usize;
    let malformed_claim_error = checked_parent_claim(&malformed_claim, &embedded, |_| {
        malformed_claim_evaluator_calls += 1;
        Ok(Fr::one())
    }).unwrap_err();
    assert_eq!(malformed_claim_error, "projected claim point dimension mismatch");
    assert_eq!(malformed_claim_evaluator_calls, 0);

    let row_point: Vec<_> = (0..CORE_ROW_BITS + SLOT_BITS)
        .map(|index| Fr::from((index + 3) as u64))
        .collect();
    let left_point: Vec<_> = (0..CORE_INPUT_BITS + SLOT_BITS)
        .map(|index| Fr::from((index + 29) as u64))
        .collect();
    let right_point: Vec<_> = (0..CORE_INPUT_BITS + SLOT_BITS)
        .map(|index| Fr::from((index + 71) as u64))
        .collect();
    let projected = projected_wiring(&core, &shape, &row_point, &left_point, &right_point).unwrap();
    let expanded = resident_expanded_wiring(&core, &row_point, &left_point, &right_point);
    assert_eq!(projected, expanded, "all four coefficients match 16-copy resident expansion");
    drop(expanded);

    let mut load_calls = 0usize;
    let invalid_specs = [
        ProjectionSpec { bank_index: 1, ..BANK0_SPEC },
        ProjectionSpec { bank_start: 1, ..BANK0_SPEC },
        ProjectionSpec { bank_width: BANK_WIDTH / 2, ..BANK0_SPEC },
        ProjectionSpec { input_bits: CORE_INPUT_BITS - 1, ..BANK0_SPEC },
        ProjectionSpec { row_bits: CORE_ROW_BITS - 1, ..BANK0_SPEC },
        ProjectionSpec { slot_bits: SLOT_BITS - 1, ..BANK0_SPEC },
    ];
    for invalid in invalid_specs {
        let mut transcript = Transcript::new(TRANSCRIPT_DOMAIN);
        let rejected = prove_projection(
            &core,
            &core_digest,
            invalid,
            |_| {
                load_calls += 1;
                Err("loader must not run for invalid projection".into())
            },
            |_, _| Ok(()),
            &mut transcript,
        );
        assert!(rejected.is_err(), "one-field mapping mutant must fail closed");
    }
    assert_eq!(load_calls, 0, "each mapping field is guarded before callbacks");

    let full_row: Vec<_> = (0..CORE_ROW_BITS + SLOT_BITS)
        .map(|index| Fr::from((index + 3) as u64))
        .collect();
    let full_left: Vec<_> = (0..CORE_INPUT_BITS + SLOT_BITS)
        .map(|index| Fr::from((index + 29) as u64))
        .collect();
    let full_right: Vec<_> = (0..CORE_INPUT_BITS + SLOT_BITS)
        .map(|index| Fr::from((index + 71) as u64))
        .collect();
    assert!(projected_wiring(&core, &shape, &full_row[..full_row.len() - 1], &full_left, &full_right).is_err());
    assert!(projected_wiring(&core, &shape, &full_row, &full_left[..full_left.len() - 1], &full_right).is_err());
    assert!(projected_wiring(&core, &shape, &full_row, &full_left, &full_right[..full_right.len() - 1]).is_err());

    let mixed_row: Vec<_> = (0..CORE_ROW_BITS)
        .map(|index| Fr::from((index + 103) as u64))
        .chain([0u64, 1, 2, 5].into_iter().map(Fr::from))
        .collect();
    let mixed_left: Vec<_> = (0..CORE_INPUT_BITS)
        .map(|index| Fr::from((index + 211) as u64))
        .chain([2u64, 1, 5, 0].into_iter().map(Fr::from))
        .collect();
    let mixed_right: Vec<_> = (0..CORE_INPUT_BITS)
        .map(|index| Fr::from((index + 307) as u64))
        .chain([0u64, 3, 7, 9].into_iter().map(Fr::from))
        .collect();
    let mixed_projected = projected_wiring(&core, &shape, &mixed_row, &mixed_left, &mixed_right).unwrap();
    let mixed_expanded = resident_expanded_wiring(&core, &mixed_row, &mixed_left, &mixed_right);
    assert!(!projection_slot_factor(&mixed_row, &mixed_left, &mixed_right).is_zero());
    assert_eq!(mixed_projected, mixed_expanded, "mixed Boolean/non-Boolean nonzero slot factor");
}

fn packed_io_json(snapshot: PackedIoSnapshot) -> serde_json::Value {
    json!({
        "read_calls": snapshot.read_calls,
        "read_bytes": snapshot.read_bytes,
        "read_ns": snapshot.read_ns,
    })
}

fn bind_projection_parent_pcs(
    transcript: &mut Transcript,
    core_digest: &str,
    spec: ProjectionSpec,
    setup_id: &[u8; 32],
    parent_commitment: &[u8],
) {
    bind_projection(transcript, core_digest, spec);
    transcript.append_bytes(b"common-parent-setup-id", setup_id);
    transcript.append_bytes(b"common-parent-commitment", parent_commitment);
}

fn prove_projection_parent_pcs(
    core: &SparseCircuit,
    core_digest: &str,
    spec: ProjectionSpec,
    setup_id: &[u8; 32],
    parent_commitment: &[u8],
    load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    visit_terms: impl FnMut(usize, &mut dyn FnMut(Term) -> Result<(), String>) -> Result<(), String>,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), String> {
    let _ = validate_projection(core, spec)?;
    let local_shape = sparse::validate(core, 0).map_err(|error| error.to_string())?;
    sparse_stream_roster::prove(
        spec.input_bits,
        spec.slot_bits,
        spec.row_bits,
        0,
        &[spec.row_bits],
        load_copy,
        transcript,
        |transcript| {
            bind_projection_parent_pcs(
                transcript,
                core_digest,
                spec,
                setup_id,
                parent_commitment,
            )
        },
        visit_terms,
        |row, left, right| projected_wiring(core, &local_shape, row, left, right),
    )
}

fn verify_projection_parent_pcs(
    core: &SparseCircuit,
    core_digest: &str,
    spec: ProjectionSpec,
    setup_id: &[u8; 32],
    parent_commitment: &[u8],
    proof: &GkrProof,
    transcript: &mut Transcript,
) -> Result<InputClaim, GkrError> {
    let local_shape = sparse::validate(core, 0).map_err(|_| GkrError::PointDimension)?;
    gkr::verify_with_wiring(
        &[spec.input_bits + spec.slot_bits],
        1usize << (spec.row_bits + spec.slot_bits),
        proof,
        transcript,
        |transcript| {
            bind_projection_parent_pcs(
                transcript,
                core_digest,
                spec,
                setup_id,
                parent_commitment,
            )
        },
        |layer, row, left, right| {
            if layer != 0 {
                return Err(GkrError::PointDimension);
            }
            projected_wiring(core, &local_shape, row, left, right)
                .map_err(|_| GkrError::PointDimension)
        },
    )
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        text.push(HEX[(byte >> 4) as usize] as char);
        text.push(HEX[(byte & 0x0f) as usize] as char);
    }
    text
}

fn write_new_pcs_artifact(directory: &str, name: &str, bytes: &[u8]) {
    let path = std::path::Path::new(directory).join(name);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .unwrap_or_else(|error| panic!("create new {name} artifact: {error}"));
    file.write_all(bytes)
        .unwrap_or_else(|error| panic!("write {name} artifact: {error}"));
}

struct PrefixMutantEvidence {
    gkr_rejected: bool,
    gkr_error: String,
    pcs_dispatch_calls: usize,
    pcs_error: String,
}

fn verify_prefix_mutant(
    core: &SparseCircuit,
    core_digest: &str,
    spec: ProjectionSpec,
    setup_id: &[u8; 32],
    bound_commitment: &[u8],
    proof: &GkrProof,
    actual_commitment: &ArkGT,
    opening: &dory_pcs::backends::arkworks::ArkDoryProof,
    key: &crate::verifier_key::AdmittedVerifierKey,
) -> PrefixMutantEvidence {
    let mut transcript = Transcript::new(COMMON_PCS_TRANSCRIPT_DOMAIN);
    match verify_projection_parent_pcs(
        core,
        core_digest,
        spec,
        setup_id,
        bound_commitment,
        proof,
        &mut transcript,
    ) {
        Err(error) => PrefixMutantEvidence {
            gkr_rejected: true,
            gkr_error: error.to_string(),
            pcs_dispatch_calls: 0,
            pcs_error: String::new(),
        },
        Ok(claim) => {
            let embedded_point = work_tree_layout::embed_bank(
                BANK_START,
                BANK_WIDTH,
                SLOT_BITS,
                &claim.point,
            )
            .expect("accepted GKR claim has embeddable point");
            let pcs_result = crate::pcs::verify_admitted(
                actual_commitment.clone(),
                claim.value,
                &embedded_point,
                opening,
                key,
                &mut transcript,
            );
            let pcs_error = pcs_result.err().unwrap_or_default();
            PrefixMutantEvidence {
                gkr_rejected: false,
                gkr_error: String::new(),
                pcs_dispatch_calls: 1,
                pcs_error,
            }
        }
    }
}

fn prefix_mutant_json(evidence: PrefixMutantEvidence) -> serde_json::Value {
    json!({
        "gkr_rejected": evidence.gkr_rejected,
        "gkr_error": evidence.gkr_error,
        "pcs_dispatch_calls": evidence.pcs_dispatch_calls,
        "pcs_error": evidence.pcs_error,
    })
}

#[test]
fn native_window16_bank0_gkr_claim_authenticates_original_parent_commitment_pcs24() {
    let whole_started = Instant::now();
    let (core, _core_layout, core_digest) = canonical_core();
    let _ = validate_projection(&core, BANK0_SPEC).unwrap();

    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE")
        .expect("runner pins NIPOPOW_CORE_PROJECTION_WINDOW_FILE");
    assert_eq!(fs::metadata(&source_path).unwrap().len(), SOURCE_BYTES);
    let parent = PackedFile::open(&source_path, PARENT_LOG_N)
        .expect("open locked native Window16 for common commitment");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    let source_open_io = parent.io_metrics_snapshot();
    assert_eq!(source_open_io.read_calls, 0);
    assert_eq!(source_open_io.read_bytes, 0);

    let setup_started = Instant::now();
    let setup = crate::pcs::generate_setup(PARENT_LOG_N).expect("generate diagnostic setup24");
    let setup_ms = setup_started.elapsed().as_millis();
    assert_eq!(setup.log_n, PARENT_LOG_N);
    let setup_id = setup.id;

    let key_encode_started = Instant::now();
    let verifier_key_bytes = crate::pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))
        .expect("serialize generated public verifier key");
    let key_encode_ms = key_encode_started.elapsed().as_millis();
    assert_eq!(verifier_key_bytes.len(), 25_584);
    let public_admit_started = Instant::now();
    let public_admit_24_error = match crate::verifier_key::admit(PARENT_LOG_N, &verifier_key_bytes) {
        Err(error) => error,
        Ok(_) => panic!("public verifier-key admission unexpectedly accepted dimension 24"),
    };
    let public_admit_24_ms = public_admit_started.elapsed().as_millis();
    assert_eq!(public_admit_24_error, "unsupported verifier-key dimension");

    let key_admit_started = Instant::now();
    let verifier_key = crate::verifier_key::admit_generated_test_key(
        PARENT_LOG_N,
        &verifier_key_bytes,
        setup_id,
    )
    .expect("admit generated diagnostic public key");
    let key_admit_ms = key_admit_started.elapsed().as_millis();
    assert_eq!(verifier_key.log_n(), PARENT_LOG_N);
    assert_eq!(verifier_key.id(), &setup_id);

    parent.reset_io_metrics();
    let commit_started = Instant::now();
    let committed = crate::packed::commit(&parent, &setup)
        .expect("commit original native Window16");
    let commit_ms = commit_started.elapsed().as_millis();
    let commit_io = parent.io_metrics_snapshot();
    let commitment_bytes = crate::pcs::encode_commitment(&committed.commitment)
        .expect("encode original parent commitment");
    assert_eq!(commitment_bytes.len(), 384);
    let parent_commitment = crate::pcs::decode_commitment(&commitment_bytes)
        .expect("decode canonical original parent commitment");
    assert_eq!(parent_commitment, committed.commitment, "original commitment canonical roundtrip");

    let alternate_commitment = ArkGT(
        committed.commitment.0.clone() + setup.prover.ht.0.clone(),
    );
    assert_ne!(alternate_commitment, parent_commitment);
    let alternate_commitment_bytes = crate::pcs::encode_commitment(&alternate_commitment)
        .expect("encode alternate valid GT commitment");
    assert_eq!(
        crate::pcs::decode_commitment(&alternate_commitment_bytes).unwrap(),
        alternate_commitment,
        "alternate commitment canonical roundtrip",
    );

    let mut prover_transcript = Transcript::new(COMMON_PCS_TRANSCRIPT_DOMAIN);
    parent.reset_io_metrics();
    let gkr_started = Instant::now();
    let (proof, claim) = prove_projection_parent_pcs(
        &core,
        &core_digest,
        BANK0_SPEC,
        &setup_id,
        &commitment_bytes,
        |owner| {
            let copy = owner
                .checked_mul(BANK_COPY_FACTOR)
                .and_then(|offset| offset.checked_add(BANK_INDEX))
                .ok_or("owner copy index overflow")?;
            parent.read_copy(BANK_WIDTH, copy)
        },
        |_, sink| {
            for term in &core.terms {
                sink(term.clone())?;
            }
            Ok(())
        },
        &mut prover_transcript,
    )
    .expect("stream native bank0 GKR proof with original commitment prefix");
    let gkr_ms = gkr_started.elapsed().as_millis();
    let projected_gkr_io = parent.io_metrics_snapshot();
    assert_eq!(projected_gkr_io.read_calls, 64);
    assert_eq!(projected_gkr_io.read_bytes, 524_288);

    let encoded_gkr = gkr::encode_proof(&proof).expect("encode projected GKR proof");
    assert_eq!(encoded_gkr.len(), 4_576);
    let gkr_decode_started = Instant::now();
    let decoded_gkr = gkr::decode_dimensions(&[CORE_INPUT_BITS + SLOT_BITS], &encoded_gkr)
        .expect("decode exact projected GKR dimensions");
    let gkr_decode_ms = gkr_decode_started.elapsed().as_millis();
    assert_eq!(decoded_gkr, proof);

    parent.reset_io_metrics();
    let mut verifier_transcript = Transcript::new(COMMON_PCS_TRANSCRIPT_DOMAIN);
    let verify_gkr_started = Instant::now();
    let verified_claim = verify_projection_parent_pcs(
        &core,
        &core_digest,
        BANK0_SPEC,
        &setup_id,
        &commitment_bytes,
        &decoded_gkr,
        &mut verifier_transcript,
    )
    .expect("fresh bound GKR verifier");
    let verify_gkr_ms = verify_gkr_started.elapsed().as_millis();
    let verify_gkr_io = parent.io_metrics_snapshot();
    assert_eq!(claim, verified_claim);
    assert_eq!(verify_gkr_io.read_calls, 0);
    assert_eq!(verify_gkr_io.read_bytes, 0);
    assert_eq!(prover_transcript.challenges(), verifier_transcript.challenges());
    assert_eq!(prover_transcript.raw_queries(), verifier_transcript.raw_queries());
    assert_eq!(prover_transcript.bytes_absorbed(), verifier_transcript.bytes_absorbed());
    let mut gkr_prover_continuation = prover_transcript.clone();
    let mut gkr_verifier_continuation = verifier_transcript.clone();
    assert_eq!(
        gkr_prover_continuation.challenge_scalar(b"common-pcs-post-gkr"),
        gkr_verifier_continuation.challenge_scalar(b"common-pcs-post-gkr"),
        "fresh GKR verifier transcript continuation",
    );

    let parent_point = work_tree_layout::embed_bank(
        BANK_START,
        BANK_WIDTH,
        SLOT_BITS,
        &verified_claim.point,
    )
    .expect("embed fixed bank0 claim into parent coordinates");
    assert_eq!(verified_claim.point.len(), CORE_INPUT_BITS + SLOT_BITS);
    assert_eq!(parent_point.len(), PARENT_LOG_N);
    parent.reset_io_metrics();
    let parent_reference_started = Instant::now();
    let parent_value = parent.evaluate(&parent_point).expect("evaluate original parent MLE");
    let parent_reference_ms = parent_reference_started.elapsed().as_millis();
    let parent_reference_io = parent.io_metrics_snapshot();
    assert_eq!(parent_value, verified_claim.value);
    assert_eq!(parent_reference_io.read_calls, 1);
    assert_eq!(parent_reference_io.read_bytes, SOURCE_BYTES);

    let post_gkr_verifier = verifier_transcript.clone();
    parent.reset_io_metrics();
    let opening_started = Instant::now();
    let opening = crate::packed::open(
        &committed,
        &parent,
        &parent_point,
        &setup,
        &mut prover_transcript,
    )
    .expect("open projected claim against original parent commitment");
    let opening_ms = opening_started.elapsed().as_millis();
    let opening_io = parent.io_metrics_snapshot();
    assert_eq!(opening_io.read_calls, 2);
    assert_eq!(opening_io.read_bytes, SOURCE_BYTES * 2);

    let encoded_dory = crate::pcs::encode_proof(&opening).expect("encode parent Dory opening");
    assert_eq!(encoded_dory.len(), 32_013);
    let dory_decode_started = Instant::now();
    let decoded_dory = crate::pcs::decode_proof(&encoded_dory, PARENT_LOG_N)
        .expect("decode canonical Dory opening at dimension 24");
    let dory_decode_ms = dory_decode_started.elapsed().as_millis();
    assert_eq!(crate::pcs::encode_proof(&decoded_dory).unwrap(), encoded_dory);

    let mut appended_dory = encoded_dory.clone();
    appended_dory.push(0);
    let appended_dory_error = match crate::pcs::decode_proof(&appended_dory, PARENT_LOG_N) {
        Err(error) => error,
        Ok(_) => panic!("Dory decoder accepted an appended proof byte"),
    };

    let mut prefix_setup_id = setup_id;
    prefix_setup_id[0] ^= 1;
    parent.reset_io_metrics();
    let setup_prefix = verify_prefix_mutant(
        &core,
        &core_digest,
        BANK0_SPEC,
        &prefix_setup_id,
        &commitment_bytes,
        &decoded_gkr,
        &parent_commitment,
        &decoded_dory,
        &verifier_key,
    );
    let commitment_prefix = verify_prefix_mutant(
        &core,
        &core_digest,
        BANK0_SPEC,
        &setup_id,
        &alternate_commitment_bytes,
        &decoded_gkr,
        &parent_commitment,
        &decoded_dory,
        &verifier_key,
    );
    let prefix_mutant_io = parent.io_metrics_snapshot();
    assert!(setup_prefix.gkr_rejected);
    assert_eq!(setup_prefix.pcs_dispatch_calls, 0);
    assert!(commitment_prefix.gkr_rejected);
    assert_eq!(commitment_prefix.pcs_dispatch_calls, 0);
    assert_eq!(prefix_mutant_io.read_calls, 0);
    assert_eq!(prefix_mutant_io.read_bytes, 0);

    let original_parent_commitment = parent_commitment.clone();
    drop(committed);
    drop(setup);

    parent.reset_io_metrics();
    let verify_pcs_started = Instant::now();
    let mut consumer_transcript = post_gkr_verifier.clone();
    crate::pcs::verify_admitted(
        original_parent_commitment.clone(),
        verified_claim.value,
        &parent_point,
        &decoded_dory,
        &verifier_key,
        &mut consumer_transcript,
    )
    .expect("fresh PCS verification with generated public-key object");
    let verify_pcs_ms = verify_pcs_started.elapsed().as_millis();
    let verify_pcs_io = parent.io_metrics_snapshot();
    assert_eq!(verify_pcs_io.read_calls, 0);
    assert_eq!(verify_pcs_io.read_bytes, 0);
    let mut prover_next = prover_transcript.clone();
    let mut verifier_next = consumer_transcript.clone();
    assert_eq!(
        prover_next.challenge_scalar(b"common-pcs-post-opening"),
        verifier_next.challenge_scalar(b"common-pcs-post-opening"),
        "prover and public-key-only verifier transcript continuation",
    );
    assert_eq!(prover_transcript.challenges(), consumer_transcript.challenges());
    assert_eq!(prover_transcript.raw_queries(), consumer_transcript.raw_queries());
    assert_eq!(prover_transcript.bytes_absorbed(), consumer_transcript.bytes_absorbed());

    parent.reset_io_metrics();
    let mut wrong_value_context = post_gkr_verifier.clone();
    let wrong_value_result = crate::pcs::verify_admitted(
        original_parent_commitment.clone(),
        verified_claim.value + Fr::one(),
        &parent_point,
        &decoded_dory,
        &verifier_key,
        &mut wrong_value_context,
    );
    let wrong_value_error = wrong_value_result
        .err()
        .expect("PCS accepted a changed value");
    let mut wrong_point = parent_point.clone();
    wrong_point[0] += Fr::one();
    let mut wrong_point_context = post_gkr_verifier.clone();
    let wrong_point_result = crate::pcs::verify_admitted(
        original_parent_commitment.clone(),
        verified_claim.value,
        &wrong_point,
        &decoded_dory,
        &verifier_key,
        &mut wrong_point_context,
    );
    let wrong_point_error = wrong_point_result
        .err()
        .expect("PCS accepted a changed point coordinate");
    let mut wrong_commitment_context = post_gkr_verifier.clone();
    let wrong_commitment_result = crate::pcs::verify_admitted(
        alternate_commitment,
        verified_claim.value,
        &parent_point,
        &decoded_dory,
        &verifier_key,
        &mut wrong_commitment_context,
    );
    let wrong_commitment_error = wrong_commitment_result
        .err()
        .expect("PCS accepted a different valid commitment");
    let pcs_mutant_io = parent.io_metrics_snapshot();
    assert_eq!(pcs_mutant_io.read_calls, 0);
    assert_eq!(pcs_mutant_io.read_bytes, 0);

    let artifact_directory = std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV)
        .expect("runner provides fresh common-PCS artifact directory");
    fs::create_dir_all(&artifact_directory).expect("create common-PCS artifact directory");
    write_new_pcs_artifact(
        &artifact_directory,
        COMMON_PCS_COMMITMENT_FILE,
        &commitment_bytes,
    );
    write_new_pcs_artifact(&artifact_directory, COMMON_PCS_GKR_FILE, &encoded_gkr);
    write_new_pcs_artifact(&artifact_directory, COMMON_PCS_DORY_FILE, &encoded_dory);
    write_new_pcs_artifact(&artifact_directory, COMMON_PCS_KEY_FILE, &verifier_key_bytes);

    let result = json!({
        "schema": "native-core-bank-projection-pcs-v1",
        "test": "native_window16_bank0_gkr_claim_authenticates_original_parent_commitment_pcs24",
        "source": {
            "sha256": SOURCE_SHA256,
            "bits": SOURCE_BITS,
            "bytes": SOURCE_BYTES,
            "reader_log_n": PARENT_LOG_N,
            "owners": OWNER_COUNT,
            "bank": BANK_INDEX,
            "bank_copy_factor": BANK_COPY_FACTOR,
        },
        "projection": {
            "bank_index": BANK_INDEX,
            "bank_start": BANK_START,
            "bank_width": BANK_WIDTH,
            "core_input_bits": CORE_INPUT_BITS,
            "core_row_bits": CORE_ROW_BITS,
            "slot_bits": SLOT_BITS,
            "projected_point_bits": verified_claim.point.len(),
            "parent_point_bits": parent_point.len(),
            "claim_value_hex": hex_bytes(&crate::pcs::encode(&verified_claim.value).unwrap()),
            "claim_point_hex": verified_claim.point.iter()
                .map(|coordinate| hex_bytes(&crate::pcs::encode(coordinate).unwrap()))
                .collect::<Vec<_>>(),
            "embedded_parent_point_hex": parent_point.iter()
                .map(|coordinate| hex_bytes(&crate::pcs::encode(coordinate).unwrap()))
                .collect::<Vec<_>>(),
        },
        "setup": {
            "log_n": PARENT_LOG_N,
            "id_hex": hex_bytes(&setup_id),
            "generated_test_key_id_hex": hex_bytes(verifier_key.id()),
            "key_file": COMMON_PCS_KEY_FILE,
            "verifier_key_bytes": verifier_key_bytes.len(),
            "verifier_key_blake2b256": work_tree_layout::hash_bytes(&verifier_key_bytes),
            "public_admit_24_rejected": true,
            "public_admit_24_error": public_admit_24_error,
        },
        "commitment": {
            "file": COMMON_PCS_COMMITMENT_FILE,
            "bytes": commitment_bytes.len(),
            "blake2b256": work_tree_layout::hash_bytes(&commitment_bytes),
            "canonical_roundtrip": true,
            "valid_mutant_bytes": alternate_commitment_bytes.len(),
            "valid_mutant_blake2b256": work_tree_layout::hash_bytes(&alternate_commitment_bytes),
            "valid_mutant_canonical_roundtrip": true,
        },
        "gkr": {
            "file": COMMON_PCS_GKR_FILE,
            "bytes": encoded_gkr.len(),
            "blake2b256": work_tree_layout::hash_bytes(&encoded_gkr),
            "decoded_exact_dimensions": true,
            "fresh_claim_matches": claim == verified_claim,
            "transcript_continuation_matches": true,
            "projected_claim_point_bits": verified_claim.point.len(),
            "embedded_parent_point_bits": parent_point.len(),
            "claim_matches_parent_mle": verified_claim.value == parent_value,
        },
        "dory": {
            "file": COMMON_PCS_DORY_FILE,
            "bytes": encoded_dory.len(),
            "blake2b256": work_tree_layout::hash_bytes(&encoded_dory),
            "decoded_roundtrip": true,
            "verified_with_generated_test_key": true,
            "post_pcs_continuation_matches": true,
        },
        "timing_ms": {
            "setup": setup_ms,
            "verifier_key_encode": key_encode_ms,
            "public_key_admit_24_reject": public_admit_24_ms,
            "generated_test_key_admit": key_admit_ms,
            "commit": commit_ms,
            "gkr": gkr_ms,
            "gkr_decode": gkr_decode_ms,
            "verify_gkr_fresh": verify_gkr_ms,
            "parent_mle_reference": parent_reference_ms,
            "open_dory": opening_ms,
            "dory_decode": dory_decode_ms,
            "verify_pcs_fresh": verify_pcs_ms,
            "whole_test_before_artifact_write": whole_started.elapsed().as_millis(),
        },
        "io": {
            "source_open": packed_io_json(source_open_io),
            "commit": packed_io_json(commit_io),
            "projected_gkr": packed_io_json(projected_gkr_io),
            "verify_gkr": packed_io_json(verify_gkr_io),
            "parent_mle_reference": packed_io_json(parent_reference_io),
            "open_dory": packed_io_json(opening_io),
            "verify_pcs": packed_io_json(verify_pcs_io),
            "gkr_prefix_mutants": packed_io_json(prefix_mutant_io),
            "pcs_mutants": packed_io_json(pcs_mutant_io),
        },
        "mutants": {
            "setup_id_prefix": prefix_mutant_json(setup_prefix),
            "commitment_prefix": prefix_mutant_json(commitment_prefix),
            "wrong_value": {
                "pcs_rejected": true,
                "pcs_error": wrong_value_error,
                "pcs_dispatch_calls": 1,
            },
            "wrong_point": {
                "pcs_rejected": true,
                "pcs_error": wrong_point_error,
                "pcs_dispatch_calls": 1,
            },
            "valid_commitment": {
                "pcs_rejected": true,
                "pcs_error": wrong_commitment_error,
                "pcs_dispatch_calls": 1,
                "encoding_roundtrip": true,
                "encoded_commitment_blake2b256": work_tree_layout::hash_bytes(&alternate_commitment_bytes),
            },
            "appended_dory_byte": {
                "codec_rejected": true,
                "codec_error": appended_dory_error,
                "pcs_dispatch_calls": 0,
            },
        },
        "scope": "one fixed bank0 claim authenticated against the original Window16 commitment with a generated test-only public key; not global PCS or an admitted production profile",
        "global_proof": false,
        "pcs_scope": "bounded diagnostic only",
    });
    let result_bytes = serde_json::to_vec_pretty(&result).expect("serialize common-PCS result");
    write_new_pcs_artifact(&artifact_directory, COMMON_PCS_RESULT_FILE, &result_bytes);
    println!(
        "common_pcs_projection_result={}",
        serde_json::to_string(&result).unwrap(),
    );
}

#[test]
fn native_window16_bank0_streamed_proof_matches_resident_and_parent_mle() {
    let (core, core_layout, core_digest) = canonical_core();
    let _ = validate_projection(&core, BANK0_SPEC).unwrap();
    assert!(core.terms.iter().filter(|term| {
        term.gate.left == core_layout.output[0][0] || term.gate.right == core_layout.output[0][0]
    }).count() > 0, "selected output wire is constrained by the canonical relation");

    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE")
        .expect("runner pins NIPOPOW_CORE_PROJECTION_WINDOW_FILE");
    assert_eq!(fs::metadata(&source_path).unwrap().len(), SOURCE_BYTES);
    let parent = PackedFile::open(&source_path, PARENT_LOG_N).expect("open locked native Window16");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    let source_open_io = parent.io_metrics_snapshot();
    assert_eq!(source_open_io.read_calls, 0);
    assert_eq!(source_open_io.read_bytes, 0);
    parent.reset_io_metrics();

    let started = Instant::now();
    let mut load_copy_calls = 0usize;
    let mut term_visit_passes = vec![0usize; OWNER_COUNT];
    let mut term_sink_calls = 0usize;
    let mut prover_transcript = Transcript::new(TRANSCRIPT_DOMAIN);
    let (proof, claim) = prove_projection(
        &core,
        &core_digest,
        BANK0_SPEC,
        |owner| {
            load_copy_calls += 1;
            let copy = owner
                .checked_mul(BANK_COPY_FACTOR)
                .and_then(|offset| offset.checked_add(BANK_INDEX))
                .ok_or("owner copy index overflow")?;
            parent.read_copy(BANK_WIDTH, copy)
        },
        |owner, sink| {
            term_visit_passes[owner] += 1;
            for term in &core.terms {
                term_sink_calls += 1;
                sink(term.clone())?;
            }
            Ok(())
        },
        &mut prover_transcript,
    )
    .expect("streamed native projected GKR proof");
    let proof_elapsed_ms = started.elapsed().as_millis();
    let projection_io = parent.io_metrics_snapshot();

    assert_eq!(load_copy_calls, OWNER_COUNT * 4, "four bounded reads per owner");
    assert_eq!(term_visit_passes, vec![3; OWNER_COUNT], "three canonical term passes per owner");
    assert_eq!(term_sink_calls, OWNER_COUNT * 3 * CORE_TERMS);
    assert_eq!(projection_io.read_calls, load_copy_calls as u64);
    assert_eq!(projection_io.read_bytes, (load_copy_calls * (BANK_WIDTH / 8)) as u64);

    let encoded_proof = gkr::encode_proof(&proof).expect("encode projected GKR proof");
    let decoded_proof = gkr::decode_dimensions(
        &[CORE_INPUT_BITS + SLOT_BITS],
        &encoded_proof,
    )
    .expect("decode exact projected proof dimensions");
    assert_eq!(decoded_proof, proof, "encoded proof round-trips through fresh dimensions");
    assert_eq!(proof.layers.len(), 1);
    assert_eq!(proof.layers[0].rounds.len(), 2 * (CORE_INPUT_BITS + SLOT_BITS));
    assert_eq!(claim.point.len(), CORE_INPUT_BITS + SLOT_BITS);

    let mut verifier_transcript = Transcript::new(TRANSCRIPT_DOMAIN);
    let verifier_shape = [CORE_INPUT_BITS + SLOT_BITS];
    let verifier = gkr::verify_with_wiring(
        &verifier_shape,
        1usize << (CORE_ROW_BITS + SLOT_BITS),
        &decoded_proof,
        &mut verifier_transcript,
        |transcript| bind_projection(transcript, &core_digest, BANK0_SPEC),
        |layer, row, left, right| {
            if layer != 0 {
                return Err(GkrError::PointDimension);
            }
            let local_shape = sparse::validate(&core, 0).map_err(|_| GkrError::PointDimension)?;
            projected_wiring(&core, &local_shape, row, left, right)
                .map_err(|_| GkrError::PointDimension)
        },
    )
    .expect("fresh analytic GKR verification");
    assert_eq!(claim, verifier, "fresh verifier returns the producer input claim");
    assert_eq!(prover_transcript.challenges(), verifier_transcript.challenges());
    assert_eq!(prover_transcript.raw_queries(), verifier_transcript.raw_queries());
    assert_eq!(prover_transcript.bytes_absorbed(), verifier_transcript.bytes_absorbed());
    assert_eq!(
        prover_transcript.challenge_scalar(b"projection-post-proof-continuation"),
        verifier_transcript.challenge_scalar(b"projection-post-proof-continuation"),
        "fresh verifier transcript continuation matches",
    );

    let embedded_point = work_tree_layout::embed_bank(BANK_START, BANK_WIDTH, SLOT_BITS, &claim.point)
        .expect("fixed bank parent point");
    assert_eq!(embedded_point.len(), PARENT_LOG_N);
    parent.reset_io_metrics();
    let mut parent_evaluator_calls = 0usize;
    let parent_value = checked_parent_claim(&claim, &embedded_point, |point| {
        parent_evaluator_calls += 1;
        parent.evaluate(point)
    })
    .expect("checked parent-point/value consumer join");
    let parent_mle_io = parent.io_metrics_snapshot();
    assert_eq!(parent_evaluator_calls, 1);
    assert_eq!(parent_mle_io.read_bytes, SOURCE_BYTES);
    assert!(parent_mle_io.read_calls > 0);

    let mut wrong_value_claim = claim.clone();
    wrong_value_claim.value += Fr::one();
    let mut wrong_value_evaluator_calls = 0usize;
    let wrong_value_error = checked_parent_claim(&wrong_value_claim, &embedded_point, |_| {
        wrong_value_evaluator_calls += 1;
        Ok(parent_value)
    })
    .expect_err("changed projected value must be rejected by the parent consumer");
    let wrong_projected_value_rejected = wrong_value_error == "parent MLE claim mismatch";
    assert!(wrong_projected_value_rejected);
    assert_eq!(wrong_value_evaluator_calls, 1);
    let wrong_bank_point = work_tree_layout::embed_bank(BANK_WIDTH, BANK_WIDTH, SLOT_BITS, &claim.point)
        .expect("alternate bank point for mapping mutant");
    let mut wrong_bank_evaluator_calls = 0usize;
    let wrong_bank_error = checked_parent_claim(&claim, &wrong_bank_point, |_| {
        wrong_bank_evaluator_calls += 1;
        Ok(claim.value)
    })
    .expect_err("wrong parent embedding must be rejected before evaluation");
    let wrong_bank_embedding_rejected = wrong_bank_error == "parent point embedding mismatch";
    assert!(wrong_bank_embedding_rejected);
    assert_eq!(wrong_bank_evaluator_calls, 0);

    let output_wire = core_layout.output[0][0];
    assert!(output_wire < BANK_WIDTH);
    parent.reset_io_metrics();
    let mut mutant_load_copy_calls = 0usize;
    let mut mutant_transcript = Transcript::new(TRANSCRIPT_DOMAIN);
    let mutant = prove_projection(
        &core,
        &core_digest,
        BANK0_SPEC,
        |owner| {
            mutant_load_copy_calls += 1;
            let copy = owner * BANK_COPY_FACTOR + BANK_INDEX;
            let mut values = parent.read_copy(BANK_WIDTH, copy)?;
            if owner == 0 {
                assert!(values[output_wire] == Fr::zero() || values[output_wire] == Fr::one());
                values[output_wire] = if values[output_wire].is_zero() { Fr::one() } else { Fr::zero() };
            }
            Ok(values)
        },
        |_, sink| {
            for term in &core.terms {
                sink(term.clone())?;
            }
            Ok(())
        },
        &mut mutant_transcript,
    );
    let mutant_io = parent.io_metrics_snapshot();
    let output_bitflip_error = mutant.as_ref().err().cloned().unwrap_or_default();
    let output_bitflip_rejected = output_bitflip_error == GkrError::NonzeroOutput.to_string();
    assert!(output_bitflip_rejected, "output bitflip must fail at the residual check");
    assert_eq!(mutant_load_copy_calls, 1, "first owner's changed output is rejected immediately");
    assert_eq!(mutant_io.read_calls, 1);
    assert_eq!(mutant_io.read_bytes, (BANK_WIDTH / 8) as u64);

    let artifact_directory = std::env::var("NIPOPOW_CORE_PROJECTION_ARTIFACT_DIR")
        .expect("runner provides a fresh projection artifact directory");
    fs::create_dir_all(&artifact_directory).expect("create artifact directory");
    let proof_path = std::path::Path::new(&artifact_directory).join(PROOF_FILE);
    let mut proof_output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&proof_path)
        .expect("create new GKR proof artifact");
    proof_output.write_all(&encoded_proof).expect("write GKR proof artifact");

    let result = json!({
        "schema": "native-core-bank-projection-v1",
        "test": "native_window16_bank0_streamed_proof_matches_resident_and_parent_mle",
        "source": {
            "sha256": SOURCE_SHA256,
            "bits": SOURCE_BITS,
            "bytes": SOURCE_BYTES,
            "reader_log_n": PARENT_LOG_N,
            "owners": OWNER_COUNT,
            "bank": BANK_INDEX,
            "bank_copy_factor": BANK_COPY_FACTOR,
        },
        "projection": {
            "core_terms": CORE_TERMS,
            "core_term_digest_blake2b256": core_digest,
            "core_input_bits": CORE_INPUT_BITS,
            "core_row_bits": CORE_ROW_BITS,
            "slot_bits": SLOT_BITS,
            "total_input_bits": CORE_INPUT_BITS + SLOT_BITS,
            "total_row_bits": CORE_ROW_BITS + SLOT_BITS,
            "bank_start": BANK_START,
            "bank_width": BANK_WIDTH,
        },
        "stream": {
            "load_copy_calls": load_copy_calls,
            "term_visit_passes": term_visit_passes.iter().sum::<usize>(),
            "term_sink_calls": term_sink_calls,
            "elapsed_ms": proof_elapsed_ms,
        },
        "source_open_io": packed_io_json(source_open_io),
        "proof_reader_io": packed_io_json(projection_io),
        "parent_mle_io": packed_io_json(parent_mle_io),
        "mutant_io": packed_io_json(mutant_io),
        "mutant_load_copy_calls": mutant_load_copy_calls,
        "proof": {
            "file": PROOF_FILE,
            "gkr_bytes": encoded_proof.len(),
            "proof_blake2b256": work_tree_layout::hash_bytes(&encoded_proof),
            "decoded_from_exact_dimensions": true,
            "layers": proof.layers.len(),
            "sumcheck_rounds": proof.layers[0].rounds.len(),
            "projected_claim_point_bits": claim.point.len(),
            "parent_mle_point_bits": embedded_point.len(),
            "embedded_point_bits": embedded_point.len(),
            "claim_matches_fresh_verifier": claim == verifier,
            "transcript_continuation_matches": true,
            "claim_matches_parent_mle": claim.value == parent_value,
        },
        "mutants": {
            "output_bitflip_rejected": output_bitflip_rejected,
            "output_bitflip_error": output_bitflip_error,
            "wrong_projected_value_rejected": wrong_projected_value_rejected,
            "wrong_projected_value_error": wrong_value_error,
            "wrong_projected_value_evaluator_calls": wrong_value_evaluator_calls,
            "wrong_bank_embedding_rejected": wrong_bank_embedding_rejected,
            "wrong_bank_embedding_error": wrong_bank_error,
            "wrong_bank_evaluator_calls": wrong_bank_evaluator_calls,
        },
        "reference_scope": "all four wiring coefficients match an explicit 16-copy resident expansion in the mapping test; no resident proof parity was run",
        "global_proof": false,
        "pcs": false,
    });
    let result_path = std::path::Path::new(&artifact_directory).join(RESULT_FILE);
    let mut result_output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&result_path)
        .expect("create new structured result artifact");
    let result_bytes = serde_json::to_vec_pretty(&result).expect("serialize structured result");
    result_output.write_all(&result_bytes).expect("write structured result artifact");
    println!("core_bank_projection_result={}", serde_json::to_string(&result).unwrap());
}

const CACHE_REFERENCE_INPUTS_SHA256: &str =
    "0C79E1960864FB33F220D811CBCE924BDC89623153FC1361D6A4CF8DFA859479";
const CACHE_REFERENCE_SETUP_ID_HEX: &str =
    "b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe";
const CACHE_REFERENCE_COMMITMENT_SHA256: &str =
    "E87D71503ED0117D3D234293DCF72CBED2758DA652610B846119EA1C92E5D6DD";
const CACHE_REFERENCE_GKR_SHA256: &str =
    "CAF6EDD302C54D363C61BD734CF768CB10E1CD31FCBC9962AAC50A6D5E2CD075";
const CACHE_REFERENCE_DORY_SHA256: &str =
    "5E4A28249E19FD63C52B5DEB5B35F34E88CCAC9030C73F971728A2E1A8B8693D";
const CACHE_REFERENCE_KEY_SHA256: &str =
    "3D77BC139351C2832EA098B9E683961C171D918708300121145F0DABFBB48740";
const CACHE_REFERENCE_RESULT_SHA256: &str =
    "97A82215802D40D8B273065BC66CECCFAE9570733CEB80197F59EAEB92C52A14";
const CACHE_REFERENCE_DIR_ENV: &str = "NIPOPOW_CORE_PCS_REFERENCE_DIR";
const NATIVE_BANK_CACHE_ARTIFACT_DIR_ENV: &str = "NIPOPOW_NATIVE_BANK_CACHE_ARTIFACT_DIR";
const NATIVE_BANK_CACHE_PROOF_FILE: &str = "uncached-native-bank-gkr-proof.bin";
const NATIVE_BANK_CACHE_RESULT_FILE: &str = "native-bank-cache-fallback-result.json";

fn prove_projection_parent_pcs_uncached(
    core: &SparseCircuit,
    core_digest: &str,
    spec: ProjectionSpec,
    setup_id: &[u8; 32],
    parent_commitment: &[u8],
    load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    visit_terms: impl FnMut(usize, &mut dyn FnMut(Term) -> Result<(), String>) -> Result<(), String>,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), String> {
    let _ = validate_projection(core, spec)?;
    let local_shape = sparse::validate(core, 0).map_err(|error| error.to_string())?;
    sparse_stream_roster::prove_with_cache_budget_for_test(
        spec.input_bits,
        spec.slot_bits,
        spec.row_bits,
        0,
        &[spec.row_bits],
        Some(0),
        load_copy,
        transcript,
        |transcript| {
            bind_projection_parent_pcs(
                transcript,
                core_digest,
                spec,
                setup_id,
                parent_commitment,
            )
        },
        visit_terms,
        |row, left, right| projected_wiring(core, &local_shape, row, left, right),
    )
}

fn decode_setup_id_hex(text: &str) -> [u8; 32] {
    assert_eq!(text.len(), 64, "setup ID must be 32 encoded bytes");
    let mut id = [0u8; 32];
    for (index, byte) in id.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[index * 2..index * 2 + 2], 16)
            .expect("reference setup ID is hexadecimal");
    }
    id
}

#[test]
fn native_window16_bank0_uncached_proof_reuses_common_pcs_opening() {
    let whole_started = Instant::now();
    let (core, _core_layout, core_digest) = canonical_core();
    let _ = validate_projection(&core, BANK0_SPEC).unwrap();

    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE")
        .expect("runner pins NIPOPOW_CORE_PROJECTION_WINDOW_FILE");
    assert_eq!(fs::metadata(&source_path).unwrap().len(), SOURCE_BYTES);
    let parent = PackedFile::open(&source_path, PARENT_LOG_N)
        .expect("open the pinned native Window16 for cache fallback");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    let source_open_io = parent.io_metrics_snapshot();
    assert_eq!(source_open_io.read_calls, 0);
    assert_eq!(source_open_io.read_bytes, 0);

    let reference_directory = std::env::var(CACHE_REFERENCE_DIR_ENV)
        .expect("runner pins the previous common-PCS artifact directory");
    let reference_path = |name: &str| std::path::Path::new(&reference_directory).join(name);
    let reference_commitment_bytes = fs::read(reference_path(COMMON_PCS_COMMITMENT_FILE))
        .expect("read pinned original parent commitment");
    let reference_gkr_bytes = fs::read(reference_path(COMMON_PCS_GKR_FILE))
        .expect("read pinned cached common-PCS GKR proof");
    let reference_dory_bytes = fs::read(reference_path(COMMON_PCS_DORY_FILE))
        .expect("read pinned common-PCS Dory opening");
    let reference_key_bytes = fs::read(reference_path(COMMON_PCS_KEY_FILE))
        .expect("read pinned TEST24 verifier key");
    let reference_result_bytes = fs::read(reference_path(COMMON_PCS_RESULT_FILE))
        .expect("read pinned common-PCS structured result");
    let reference_result: serde_json::Value = serde_json::from_slice(&reference_result_bytes)
        .expect("decode pinned common-PCS structured result");
    assert_eq!(
        reference_result["schema"].as_str(),
        Some("native-core-bank-projection-pcs-v1")
    );
    assert_eq!(
        reference_result["test"].as_str(),
        Some("native_window16_bank0_gkr_claim_authenticates_original_parent_commitment_pcs24")
    );
    assert_eq!(reference_result["source"]["sha256"].as_str(), Some(SOURCE_SHA256));
    assert_eq!(reference_result["source"]["bits"].as_u64(), Some(SOURCE_BITS as u64));
    assert_eq!(reference_result["source"]["bytes"].as_u64(), Some(SOURCE_BYTES));
    assert_eq!(reference_result["source"]["owners"].as_u64(), Some(OWNER_COUNT as u64));
    assert_eq!(reference_result["source"]["bank"].as_u64(), Some(BANK_INDEX as u64));
    assert_eq!(reference_result["projection"]["bank_index"].as_u64(), Some(BANK_INDEX as u64));
    assert_eq!(reference_result["projection"]["bank_start"].as_u64(), Some(BANK_START as u64));
    assert_eq!(reference_result["projection"]["bank_width"].as_u64(), Some(BANK_WIDTH as u64));
    assert_eq!(reference_result["projection"]["core_input_bits"].as_u64(), Some(CORE_INPUT_BITS as u64));
    assert_eq!(reference_result["projection"]["core_row_bits"].as_u64(), Some(CORE_ROW_BITS as u64));
    assert_eq!(reference_result["projection"]["slot_bits"].as_u64(), Some(SLOT_BITS as u64));
    assert_eq!(reference_result["projection"]["projected_point_bits"].as_u64(), Some((CORE_INPUT_BITS + SLOT_BITS) as u64));
    assert_eq!(reference_result["projection"]["parent_point_bits"].as_u64(), Some(PARENT_LOG_N as u64));
    assert_eq!(reference_result["gkr"]["file"].as_str(), Some(COMMON_PCS_GKR_FILE));
    assert_eq!(reference_result["gkr"]["bytes"].as_u64(), Some(4_576));
    assert_eq!(reference_result["commitment"]["file"].as_str(), Some(COMMON_PCS_COMMITMENT_FILE));
    assert_eq!(reference_result["dory"]["file"].as_str(), Some(COMMON_PCS_DORY_FILE));
    assert_eq!(reference_result["setup"]["key_file"].as_str(), Some(COMMON_PCS_KEY_FILE));
    assert_eq!(reference_gkr_bytes.len(), 4_576);
    assert_eq!(reference_commitment_bytes.len(), 384);
    assert_eq!(reference_dory_bytes.len(), 32_013);
    assert_eq!(reference_key_bytes.len(), 25_584);
    assert_eq!(
        work_tree_layout::hash_bytes(&reference_gkr_bytes),
        reference_result["gkr"]["blake2b256"].as_str().unwrap()
    );
    assert_eq!(
        work_tree_layout::hash_bytes(&reference_commitment_bytes),
        reference_result["commitment"]["blake2b256"].as_str().unwrap()
    );
    assert_eq!(
        work_tree_layout::hash_bytes(&reference_dory_bytes),
        reference_result["dory"]["blake2b256"].as_str().unwrap()
    );
    assert_eq!(
        work_tree_layout::hash_bytes(&reference_key_bytes),
        reference_result["setup"]["verifier_key_blake2b256"].as_str().unwrap()
    );
    let setup_id_hex = reference_result["setup"]["id_hex"]
        .as_str()
        .expect("reference setup ID");
    assert_eq!(setup_id_hex, CACHE_REFERENCE_SETUP_ID_HEX);
    let setup_id = decode_setup_id_hex(setup_id_hex);
    assert_eq!(
        reference_result["setup"]["generated_test_key_id_hex"].as_str(),
        Some(setup_id_hex)
    );
    assert_eq!(reference_result["setup"]["log_n"].as_u64(), Some(PARENT_LOG_N as u64));
    assert_eq!(reference_result["gkr"]["fresh_claim_matches"].as_bool(), Some(true));
    assert_eq!(reference_result["gkr"]["transcript_continuation_matches"].as_bool(), Some(true));
    assert_eq!(reference_result["dory"]["verified_with_generated_test_key"].as_bool(), Some(true));
    let reference_commitment = crate::pcs::decode_commitment(&reference_commitment_bytes)
        .expect("decode pinned original parent commitment");
    assert_eq!(
        crate::pcs::encode_commitment(&reference_commitment).unwrap(),
        reference_commitment_bytes
    );
    let reference_dory = crate::pcs::decode_proof(&reference_dory_bytes, PARENT_LOG_N)
        .expect("decode pinned original Dory opening");
    assert_eq!(crate::pcs::encode_proof(&reference_dory).unwrap(), reference_dory_bytes);

    let public_admit_started = Instant::now();
    let public_admit_24_error = match crate::verifier_key::admit(PARENT_LOG_N, &reference_key_bytes) {
        Err(error) => error,
        Ok(_) => panic!("public verifier-key admission unexpectedly accepted dimension 24"),
    };
    let public_admit_24_reject_ms = public_admit_started.elapsed().as_millis();
    assert_eq!(public_admit_24_error, "unsupported verifier-key dimension");
    let key_admit_started = Instant::now();
    let verifier_key = crate::verifier_key::admit_generated_test_key(
        PARENT_LOG_N,
        &reference_key_bytes,
        setup_id,
    )
    .expect("admit the pinned generated TEST24 verifier key");
    let key_admit_ms = key_admit_started.elapsed().as_millis();
    assert_eq!(verifier_key.log_n(), PARENT_LOG_N);
    assert_eq!(verifier_key.id(), &setup_id);

    parent.reset_io_metrics();
    let mut producer_transcript = Transcript::new(COMMON_PCS_TRANSCRIPT_DOMAIN);
    let mut load_calls = 0usize;
    let mut term_visit_passes_by_owner = vec![0usize; OWNER_COUNT];
    let mut term_sink_calls = 0usize;
    let proof_started = Instant::now();
    let (proof, claim) = prove_projection_parent_pcs_uncached(
        &core,
        &core_digest,
        BANK0_SPEC,
        &setup_id,
        &reference_commitment_bytes,
        |owner| {
            load_calls += 1;
            let copy = owner
                .checked_mul(BANK_COPY_FACTOR)
                .and_then(|offset| offset.checked_add(BANK_INDEX))
                .ok_or("owner copy index overflow")?;
            parent.read_copy(BANK_WIDTH, copy)
        },
        |owner, sink| {
            if owner >= OWNER_COUNT {
                return Err("cache fallback owner index out of range".into());
            }
            term_visit_passes_by_owner[owner] += 1;
            for term in &core.terms {
                term_sink_calls += 1;
                sink(term.clone())?;
            }
            Ok(())
        },
        &mut producer_transcript,
    )
    .expect("produce native bank0 GKR proof with the cache budget forced to zero");
    let proof_ms = proof_started.elapsed().as_millis();
    assert_eq!(load_calls, 592);
    assert_eq!(term_visit_passes_by_owner, vec![37; OWNER_COUNT]);
    let term_visit_passes: usize = term_visit_passes_by_owner.iter().sum();
    assert_eq!(term_visit_passes, 592);
    assert_eq!(term_sink_calls, 102_108_160);
    let uncached_producer_io = parent.io_metrics_snapshot();
    assert_eq!(uncached_producer_io.read_calls, 592);
    assert_eq!(uncached_producer_io.read_bytes, 4_849_664);

    let encoded_proof = gkr::encode_proof(&proof).expect("encode cache-fallback GKR proof");
    assert_eq!(encoded_proof.len(), 4_576);
    assert_eq!(encoded_proof, reference_gkr_bytes, "cache-fallback GKR bytes match the frozen common-PCS proof");
    let proof_decode_started = Instant::now();
    let decoded_proof = gkr::decode_dimensions(&[CORE_INPUT_BITS + SLOT_BITS], &encoded_proof)
        .expect("decode cache-fallback proof at the exact projected dimension");
    let proof_decode_ms = proof_decode_started.elapsed().as_millis();
    assert_eq!(decoded_proof, proof);

    let reference_claim_value_hex = reference_result["projection"]["claim_value_hex"]
        .as_str()
        .expect("reference claim value");
    let reference_claim_point = reference_result["projection"]["claim_point_hex"]
        .as_array()
        .expect("reference projected claim point");
    let claim_value_hex = hex_bytes(&crate::pcs::encode(&claim.value).unwrap());
    let claim_point_hex: Vec<_> = claim
        .point
        .iter()
        .map(|coordinate| hex_bytes(&crate::pcs::encode(coordinate).unwrap()))
        .collect();
    assert_eq!(claim_value_hex, reference_claim_value_hex);
    assert_eq!(claim_point_hex.len(), reference_claim_point.len());
    for (actual, expected) in claim_point_hex.iter().zip(reference_claim_point) {
        assert_eq!(actual, expected.as_str().expect("reference point coordinate"));
    }

    parent.reset_io_metrics();
    let mut verifier_transcript = Transcript::new(COMMON_PCS_TRANSCRIPT_DOMAIN);
    let fresh_gkr_verify_started = Instant::now();
    let verified_claim = verify_projection_parent_pcs(
        &core,
        &core_digest,
        BANK0_SPEC,
        &setup_id,
        &reference_commitment_bytes,
        &decoded_proof,
        &mut verifier_transcript,
    )
    .expect("fresh verify the decoded cache-fallback GKR proof");
    let fresh_gkr_verify_ms = fresh_gkr_verify_started.elapsed().as_millis();
    let fresh_gkr_io = parent.io_metrics_snapshot();
    assert_eq!(fresh_gkr_io.read_calls, 0);
    assert_eq!(fresh_gkr_io.read_bytes, 0);
    assert_eq!(claim, verified_claim);
    let claim_matches_reference = claim_value_hex == reference_claim_value_hex
        && claim_point_hex.len() == reference_claim_point.len()
        && claim_point_hex
            .iter()
            .zip(reference_claim_point)
            .all(|(actual, expected)| expected.as_str() == Some(actual.as_str()));
    assert!(claim_matches_reference);
    assert_eq!(producer_transcript.challenges(), verifier_transcript.challenges());
    assert_eq!(producer_transcript.raw_queries(), verifier_transcript.raw_queries());
    assert_eq!(producer_transcript.bytes_absorbed(), verifier_transcript.bytes_absorbed());
    let mut producer_continuation = producer_transcript.clone();
    let mut verifier_continuation = verifier_transcript.clone();
    let producer_next = producer_continuation.challenge_scalar(b"common-pcs-post-gkr");
    let verifier_next = verifier_continuation.challenge_scalar(b"common-pcs-post-gkr");
    let gkr_prover_verifier_continuation_matches = producer_next == verifier_next
        && producer_continuation.challenges() == verifier_continuation.challenges()
        && producer_continuation.raw_queries() == verifier_continuation.raw_queries()
        && producer_continuation.bytes_absorbed() == verifier_continuation.bytes_absorbed();
    assert!(gkr_prover_verifier_continuation_matches);

    let parent_point = work_tree_layout::embed_bank(
        BANK_START,
        BANK_WIDTH,
        SLOT_BITS,
        &verified_claim.point,
    )
    .expect("embed fresh verified bank0 claim into parent W24 coordinates");
    assert_eq!(parent_point.len(), PARENT_LOG_N);
    let reference_parent_point = reference_result["projection"]["embedded_parent_point_hex"]
        .as_array()
        .expect("reference embedded parent point");
    assert_eq!(parent_point.len(), reference_parent_point.len());
    for (actual, expected) in parent_point.iter().zip(reference_parent_point) {
        assert_eq!(
            hex_bytes(&crate::pcs::encode(actual).unwrap()),
            expected.as_str().expect("reference parent point coordinate")
        );
    }

    parent.reset_io_metrics();
    let mut consumer_transcript = verifier_transcript.clone();
    let fresh_pcs_verify_started = Instant::now();
    crate::pcs::verify_admitted(
        reference_commitment,
        verified_claim.value,
        &parent_point,
        &reference_dory,
        &verifier_key,
        &mut consumer_transcript,
    )
    .expect("verify the reused Dory opening with the pinned TEST24 public key");
    let fresh_pcs_verify_ms = fresh_pcs_verify_started.elapsed().as_millis();
    let fresh_pcs_io = parent.io_metrics_snapshot();
    assert_eq!(fresh_pcs_io.read_calls, 0);
    assert_eq!(fresh_pcs_io.read_bytes, 0);

    let artifact_directory = std::env::var(NATIVE_BANK_CACHE_ARTIFACT_DIR_ENV)
        .expect("runner provides a fresh native bank cache-fallback artifact directory");
    assert_eq!(
        fs::read_dir(&artifact_directory).unwrap().count(),
        0,
        "cache-fallback artifact directory must start empty"
    );
    write_new_pcs_artifact(
        &artifact_directory,
        NATIVE_BANK_CACHE_PROOF_FILE,
        &encoded_proof,
    );
    let result = json!({
        "schema": "native-bank-cache-fallback-v1",
        "test": "native_window16_bank0_uncached_proof_reuses_common_pcs_opening",
        "scope": "one native Window16 bank0 cache-budget-zero GKR proof byte-matched to the frozen common-PCS reference and verified with its reused TEST24 opening; bounded diagnostic only",
        "source": {
            "sha256": SOURCE_SHA256,
            "bits": SOURCE_BITS,
            "bytes": SOURCE_BYTES,
            "reader_log_n": PARENT_LOG_N,
            "owners": OWNER_COUNT,
            "bank": BANK_INDEX,
            "bank_copy_factor": BANK_COPY_FACTOR,
        },
        "projection": {
            "bank_index": BANK_INDEX,
            "bank_start": BANK_START,
            "bank_width": BANK_WIDTH,
            "core_input_bits": CORE_INPUT_BITS,
            "core_row_bits": CORE_ROW_BITS,
            "slot_bits": SLOT_BITS,
            "projected_point_bits": CORE_INPUT_BITS + SLOT_BITS,
            "parent_point_bits": PARENT_LOG_N,
        },
        "reference": {
            "input_receipt_sha256": CACHE_REFERENCE_INPUTS_SHA256,
            "setup_id_hex": setup_id_hex,
            "commitment_sha256": CACHE_REFERENCE_COMMITMENT_SHA256,
            "gkr_proof_sha256": CACHE_REFERENCE_GKR_SHA256,
            "dory_opening_sha256": CACHE_REFERENCE_DORY_SHA256,
            "test_verifier_key_sha256": CACHE_REFERENCE_KEY_SHA256,
            "result_json_sha256": CACHE_REFERENCE_RESULT_SHA256,
        },
        "producer": {
            "cache_budget_bytes": 0,
            "load_calls": load_calls,
            "term_visit_passes": term_visit_passes,
            "term_sink_calls": term_sink_calls,
            "proof_file": NATIVE_BANK_CACHE_PROOF_FILE,
            "proof_bytes": encoded_proof.len(),
            "proof_blake2b256": work_tree_layout::hash_bytes(&encoded_proof),
            "proof_bytes_match_reference": encoded_proof == reference_gkr_bytes,
            "claim_matches_reference": claim_matches_reference,
            "claim_value_hex": claim_value_hex,
            "claim_point_hex": claim_point_hex,
            "gkr_prover_verifier_continuation_matches": gkr_prover_verifier_continuation_matches,
        },
        "verifier": {
            "decoded_exact_dimensions": decoded_proof == proof,
            "fresh_claim_matches_reference": verified_claim == claim,
            "pcs_verified_with_reused_opening": true,
            "public_admit_24_rejected": true,
            "public_admit_24_error": public_admit_24_error,
        },
        "timing_ms": {
            "proof": proof_ms,
            "proof_decode": proof_decode_ms,
            "fresh_gkr_verify": fresh_gkr_verify_ms,
            "test_key_decode_and_admit": key_admit_ms,
            "public_admit_24_reject": public_admit_24_reject_ms,
            "fresh_pcs_verify": fresh_pcs_verify_ms,
            "whole_test_before_artifact_write": whole_started.elapsed().as_millis(),
        },
        "io": {
            "source_open": packed_io_json(source_open_io),
            "uncached_producer": packed_io_json(uncached_producer_io),
            "fresh_gkr_verify": packed_io_json(fresh_gkr_io),
            "fresh_pcs_verify": packed_io_json(fresh_pcs_io),
        },
        "global_proof": false,
        "pcs_scope": "bounded diagnostic only",
    });
    let result_bytes = serde_json::to_vec_pretty(&result).expect("serialize cache-fallback result");
    write_new_pcs_artifact(
        &artifact_directory,
        NATIVE_BANK_CACHE_RESULT_FILE,
        &result_bytes,
    );
    println!(
        "native_bank_cache_fallback_result={}",
        serde_json::to_string(&result).unwrap()
    );
}

// Two adjacent compression banks are represented with disjoint input and row
// namespaces. This remains a test-only diagnostic over the pinned Window16.
const TWO_BANK_TRANSCRIPT_DOMAIN: &[u8] = b"nipopow-v2-native-two-bank-common-pcs-v1";
const TWO_BANK_BANKS: [usize; 2] = [0, 1];
const TWO_BANK_INPUT_OFFSETS: [usize; 2] = [0, BANK_WIDTH];
const TWO_BANK_ROW_OFFSETS: [usize; 2] = [0, CORE_ROWS];
const TWO_BANK_INPUT_BITS: usize = CORE_INPUT_BITS + 1;
const TWO_BANK_ROW_BITS: usize = CORE_ROW_BITS + 1;
const TWO_BANK_PROJECTED_INPUT_BITS: usize = TWO_BANK_INPUT_BITS + SLOT_BITS;
const TWO_BANK_PROJECTED_ROW_BITS: usize = TWO_BANK_ROW_BITS + SLOT_BITS;
const TWO_BANK_TERMS: usize = CORE_TERMS * 2;
const TWO_BANK_SPEC: TwoBankSpec = TwoBankSpec {
    bank_indices: TWO_BANK_BANKS,
    bank_input_offsets: TWO_BANK_INPUT_OFFSETS,
    bank_row_offsets: TWO_BANK_ROW_OFFSETS,
    input_bits: TWO_BANK_INPUT_BITS,
    row_bits: TWO_BANK_ROW_BITS,
    slot_bits: SLOT_BITS,
};
const TWO_BANK_MAPPING_TEST_NAME: &str =
    "two_bank_mapping_and_wiring_reject_invalid_mappings";
const TWO_BANK_NATIVE_TEST_NAME: &str =
    "native_window16_banks0_1_gkr_claim_authenticates_original_parent_commitment_pcs24";
const TWO_BANK_ARTIFACT_DIR_ENV: &str = "NIPOPOW_TWO_BANK_ARTIFACT_DIR";
const TWO_BANK_GKR_FILE: &str = "two-bank-gkr-proof.bin";
const TWO_BANK_OPENING_FILE: &str = "two-bank-parent-opening.bin";
const TWO_BANK_RESULT_FILE: &str = "two-bank-result.json";
const TWO_BANK_CORE_DIGEST: &str =
    "5210e3be7975701b4e97647b724c8340e443c622debbda0c0ea44f5bc995577c";

#[derive(Clone, Copy)]
struct TwoBankSpec {
    bank_indices: [usize; 2],
    bank_input_offsets: [usize; 2],
    bank_row_offsets: [usize; 2],
    input_bits: usize,
    row_bits: usize,
    slot_bits: usize,
}

fn build_two_bank_core(core: &SparseCircuit, spec: TwoBankSpec) -> Result<SparseCircuit, String> {
    let input_width = 1usize
        .checked_shl(spec.input_bits as u32)
        .ok_or("two-bank input width overflow")?;
    let row_count = 1usize
        .checked_shl(spec.row_bits as u32)
        .ok_or("two-bank row count overflow")?;
    let mut terms = Vec::with_capacity(core.terms.len().saturating_mul(2));
    for bank in 0..spec.bank_indices.len() {
        let input_offset = spec.bank_input_offsets[bank];
        let row_offset = spec.bank_row_offsets[bank];
        for term in &core.terms {
            let mut shifted = term.clone();
            shifted.row = shifted.row.checked_add(row_offset).ok_or("two-bank row overflow")?;
            shifted.gate.left = shifted.gate.left.checked_add(input_offset)
                .ok_or("two-bank left-wire overflow")?;
            shifted.gate.right = shifted.gate.right.checked_add(input_offset)
                .ok_or("two-bank right-wire overflow")?;
            terms.push(shifted);
        }
    }
    Ok(SparseCircuit { input_len: input_width, row_count, terms })
}

fn validate_two_bank(
    core: &SparseCircuit,
    paired: &SparseCircuit,
    core_digest: &str,
    spec: TwoBankSpec,
) -> Result<Shape, String> {
    if spec.bank_indices != TWO_BANK_BANKS
        || spec.bank_input_offsets != TWO_BANK_INPUT_OFFSETS
        || spec.bank_row_offsets != TWO_BANK_ROW_OFFSETS
        || spec.input_bits != TWO_BANK_INPUT_BITS
        || spec.row_bits != TWO_BANK_ROW_BITS
        || spec.slot_bits != SLOT_BITS
    {
        return Err("two-bank projection mapping mismatch".into());
    }
    if core.input_len != BANK_WIDTH
        || core.row_count != CORE_ROWS
        || core.terms.len() != CORE_TERMS
        || core_digest != TWO_BANK_CORE_DIGEST
        || work_tree_layout::hash_terms(&core.terms) != core_digest
    {
        return Err("two-bank canonical core identity mismatch".into());
    }
    let input_width = 1usize.checked_shl(spec.input_bits as u32)
        .ok_or("two-bank input width overflow")?;
    let row_count = 1usize.checked_shl(spec.row_bits as u32)
        .ok_or("two-bank row count overflow")?;
    if input_width != BANK_WIDTH.checked_mul(2).ok_or("two-bank input overflow")?
        || row_count != CORE_ROWS.checked_mul(2).ok_or("two-bank row overflow")?
        || paired.input_len != input_width
        || paired.row_count != row_count
        || paired.terms.len() != TWO_BANK_TERMS
    {
        return Err("two-bank expanded circuit geometry mismatch".into());
    }
    for bank in 0..2 {
        let start = bank * CORE_TERMS;
        let end = start + CORE_TERMS;
        let input_offset = spec.bank_input_offsets[bank];
        let row_offset = spec.bank_row_offsets[bank];
        for (actual, source) in paired.terms[start..end].iter().zip(&core.terms) {
            if actual.row != source.row.checked_add(row_offset).ok_or("two-bank row overflow")?
                || actual.gate.left != source.gate.left.checked_add(input_offset)
                    .ok_or("two-bank left-wire overflow")?
                || actual.gate.right != source.gate.right.checked_add(input_offset)
                    .ok_or("two-bank right-wire overflow")?
                || actual.gate.c0 != source.gate.c0
                || actual.gate.c1 != source.gate.c1
                || actual.gate.c2 != source.gate.c2
                || actual.gate.c3 != source.gate.c3
            {
                return Err("two-bank row or input namespaces overlap or changed".into());
            }
        }
    }
    sparse::validate(paired, 0).map_err(|error| error.to_string())
}

fn bind_two_bank_parent_pcs(
    transcript: &mut Transcript,
    core_digest: &str,
    spec: TwoBankSpec,
    setup_id: &[u8; 32],
    parent_commitment: &[u8],
) {
    transcript.append_bytes(b"two-bank-projection-relation", b"compression-banks-0-and-1-v1");
    transcript.append_bytes(b"parent-source-sha256", SOURCE_SHA256.as_bytes());
    transcript.append_bytes(b"two-bank-core-term-digest-blake2b256", core_digest.as_bytes());
    for bank in 0..2 {
        gkr::append_usize(transcript, b"two-bank-index", spec.bank_indices[bank]);
        gkr::append_usize(transcript, b"two-bank-input-offset", spec.bank_input_offsets[bank]);
        gkr::append_usize(transcript, b"two-bank-row-offset", spec.bank_row_offsets[bank]);
    }
    gkr::append_usize(transcript, b"two-bank-core-input-bits", CORE_INPUT_BITS);
    gkr::append_usize(transcript, b"two-bank-core-row-bits", CORE_ROW_BITS);
    gkr::append_usize(transcript, b"two-bank-combined-input-bits", spec.input_bits);
    gkr::append_usize(transcript, b"two-bank-combined-row-bits", spec.row_bits);
    gkr::append_usize(transcript, b"two-bank-slot-bits", spec.slot_bits);
    gkr::append_usize(transcript, b"two-bank-projected-input-bits", TWO_BANK_PROJECTED_INPUT_BITS);
    gkr::append_usize(transcript, b"two-bank-projected-row-bits", TWO_BANK_PROJECTED_ROW_BITS);
    gkr::append_usize(transcript, b"parent-packed-input-bits", PARENT_LOG_N);
    gkr::append_usize(transcript, b"parent-owner-row-bits", PARENT_OWNER_BITS);
    transcript.append_bytes(
        b"two-bank-coordinate-recipe",
        b"local-z16, bank-b1, fixed-parent-bits-17-19-zero, source-slot-s4; owner-copy=owner*8",
    );
    transcript.append_bytes(b"common-parent-setup-id", setup_id);
    transcript.append_bytes(b"common-parent-commitment", parent_commitment);
}

fn two_bank_slot_factor(row_point: &[Fr], left_point: &[Fr], right_point: &[Fr]) -> Fr {
    let row_slots = gkr::eq_weights(&row_point[TWO_BANK_ROW_BITS..]);
    let left_slots = gkr::eq_weights(&left_point[TWO_BANK_INPUT_BITS..]);
    let right_slots = gkr::eq_weights(&right_point[TWO_BANK_INPUT_BITS..]);
    row_slots
        .iter()
        .zip(left_slots)
        .zip(right_slots)
        .fold(Fr::zero(), |sum, ((row, left), right)| sum + *row * left * right)
}

fn two_bank_triple_eq(a: Fr, b: Fr, c: Fr) -> Fr {
    (Fr::one() - a) * (Fr::one() - b) * (Fr::one() - c) + a * b * c
}

fn two_bank_wiring(
    core: &SparseCircuit,
    core_shape: &Shape,
    row_point: &[Fr],
    left_point: &[Fr],
    right_point: &[Fr],
) -> Result<[Fr; 4], String> {
    if row_point.len() != TWO_BANK_PROJECTED_ROW_BITS
        || left_point.len() != TWO_BANK_PROJECTED_INPUT_BITS
        || right_point.len() != TWO_BANK_PROJECTED_INPUT_BITS
    {
        return Err("two-bank projected wiring point dimensions".into());
    }
    let mut coefficients = sparse::wiring(
        core,
        core_shape,
        &row_point[..CORE_ROW_BITS],
        &left_point[..CORE_INPUT_BITS],
        &right_point[..CORE_INPUT_BITS],
    ).map_err(|error| error.to_string())?;
    let bank_factor = two_bank_triple_eq(
        row_point[CORE_ROW_BITS],
        left_point[CORE_INPUT_BITS],
        right_point[CORE_INPUT_BITS],
    );
    let slot_factor = two_bank_slot_factor(row_point, left_point, right_point);
    for coefficient in &mut coefficients {
        *coefficient *= bank_factor * slot_factor;
    }
    Ok(coefficients)
}

// Independent streamed reference: index directly into the two physical bank
// offsets rather than calling the paired-circuit wiring implementation.
fn two_bank_streamed_global_oracle(
    core: &SparseCircuit,
    row_point: &[Fr],
    left_point: &[Fr],
    right_point: &[Fr],
) -> [Fr; 4] {
    let row_weights = gkr::eq_weights(row_point);
    let left_weights = gkr::eq_weights(left_point);
    let right_weights = gkr::eq_weights(right_point);
    let mut coefficients = [Fr::zero(); 4];
    for owner in 0..OWNER_COUNT {
        let owner_row_offset = owner << TWO_BANK_ROW_BITS;
        let owner_input_offset = owner << TWO_BANK_INPUT_BITS;
        for bank in 0..2 {
            for term in &core.terms {
                let row = owner_row_offset + TWO_BANK_ROW_OFFSETS[bank] + term.row;
                let left = owner_input_offset + TWO_BANK_INPUT_OFFSETS[bank] + term.gate.left;
                let right = owner_input_offset + TWO_BANK_INPUT_OFFSETS[bank] + term.gate.right;
                let weight = row_weights[row] * left_weights[left] * right_weights[right];
                coefficients[0] += weight * term.gate.c0;
                coefficients[1] += weight * term.gate.c1;
                coefficients[2] += weight * term.gate.c2;
                coefficients[3] += weight * term.gate.c3;
            }
        }
    }
    coefficients
}

fn prove_two_bank_projection(
    core: &SparseCircuit,
    paired: &SparseCircuit,
    core_digest: &str,
    spec: TwoBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    cache_budget_bytes: Option<usize>,
    load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    visit_terms: impl FnMut(usize, &mut dyn FnMut(Term) -> Result<(), String>) -> Result<(), String>,
    transcript: &mut Transcript,
    bind_calls: &mut usize,
) -> Result<(GkrProof, InputClaim), String> {
    let _ = validate_two_bank(core, paired, core_digest, spec)?;
    let core_shape = sparse::validate(core, 0).map_err(|error| error.to_string())?;
    sparse_stream_roster::prove_with_cache_budget_for_test(
        spec.input_bits,
        spec.slot_bits,
        spec.row_bits,
        0,
        &[spec.row_bits],
        cache_budget_bytes,
        load_copy,
        transcript,
        |transcript| {
            *bind_calls += 1;
            bind_two_bank_parent_pcs(transcript, core_digest, spec, setup_id, commitment_bytes);
        },
        visit_terms,
        |row, left, right| two_bank_wiring(core, &core_shape, row, left, right),
    )
}

fn verify_two_bank_projection(
    core: &SparseCircuit,
    paired: &SparseCircuit,
    core_digest: &str,
    spec: TwoBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    proof: &GkrProof,
    transcript: &mut Transcript,
    bind_calls: &mut usize,
) -> Result<InputClaim, GkrError> {
    if validate_two_bank(core, paired, core_digest, spec).is_err() {
        return Err(GkrError::PointDimension);
    }
    let core_shape = sparse::validate(core, 0).map_err(|_| GkrError::PointDimension)?;
    gkr::verify_with_wiring(
        &[TWO_BANK_PROJECTED_INPUT_BITS],
        1usize << TWO_BANK_PROJECTED_ROW_BITS,
        proof,
        transcript,
        |transcript| {
            *bind_calls += 1;
            bind_two_bank_parent_pcs(transcript, core_digest, spec, setup_id, commitment_bytes);
        },
        |layer, row, left, right| {
            if layer != 0 {
                return Err(GkrError::PointDimension);
            }
            two_bank_wiring(core, &core_shape, row, left, right)
                .map_err(|_| GkrError::PointDimension)
        },
    )
}

fn two_bank_hex_point(point: &[Fr]) -> Vec<String> {
    point.iter().map(|value| {
        hex_bytes(&crate::pcs::encode(value).expect("encode field coordinate"))
    }).collect()
}

fn load_two_bank_owner(parent: &PackedFile, owner: usize) -> Result<Vec<Fr>, String> {
    if owner >= OWNER_COUNT {
        return Err("two-bank owner index out of range".into());
    }
    let first_copy = owner.checked_mul(16).ok_or("two-bank owner copy overflow")?;
    let second_copy = first_copy.checked_add(1).ok_or("two-bank owner copy overflow")?;
    let mut values = parent.read_copy(BANK_WIDTH, first_copy)?;
    let second_bank = parent.read_copy(BANK_WIDTH, second_copy)?;
    if values.len() != BANK_WIDTH || second_bank.len() != BANK_WIDTH {
        return Err("two-bank physical bank width mismatch".into());
    }
    values.extend(second_bank);
    if values.len() != BANK_WIDTH * 2 {
        return Err("two-bank logical owner width mismatch".into());
    }
    Ok(values)
}

struct TwoBankNegative {
    rejected_by: &'static str,
    error: String,
    gkr_verify_calls: usize,
    pcs_verify_calls: usize,
    bind_calls: usize,
    challenge_count: u64,
}

fn two_bank_negative_json(evidence: &TwoBankNegative) -> serde_json::Value {
    json!({
        "rejected_by": evidence.rejected_by,
        "error": evidence.error,
        "gkr_verify_calls": evidence.gkr_verify_calls,
        "pcs_verify_calls": evidence.pcs_verify_calls,
        "bind_calls": evidence.bind_calls,
        "challenge_count": evidence.challenge_count,
    })
}

fn assert_two_bank_rejects_before_callbacks(
    core: &SparseCircuit,
    paired: &SparseCircuit,
    core_digest: &str,
    spec: TwoBankSpec,
) {
    let mut loader_calls = 0usize;
    let mut visitor_calls = 0usize;
    let mut bind_calls = 0usize;
    let mut transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
    let result = prove_two_bank_projection(
        core, paired, core_digest, spec, &[0u8; 32], b"mapping-fixture-commitment",
        None,
        |_| { loader_calls += 1; Err("loader must not run for invalid mapping".into()) },
        |_, _| { visitor_calls += 1; Ok(()) },
        &mut transcript, &mut bind_calls,
    );
    assert!(result.is_err());
    assert_eq!((loader_calls, visitor_calls, bind_calls, transcript.challenges()), (0, 0, 0, 0));
}

fn two_bank_prefix_negative(
    core: &SparseCircuit,
    paired: &SparseCircuit,
    core_digest: &str,
    spec: TwoBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    proof: &GkrProof,
) -> TwoBankNegative {
    let mut transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
    let mut bind_calls = 0usize;
    let mut gkr_verify_calls = 0usize;
    gkr_verify_calls += 1;
    let result = verify_two_bank_projection(
        core, paired, core_digest, spec, setup_id, commitment_bytes, proof,
        &mut transcript, &mut bind_calls,
    );
    let error = match result {
        Err(error) => error.to_string(),
        Ok(_) => "prefix mutant unexpectedly verified".into(),
    };
    TwoBankNegative {
        rejected_by: "fresh_gkr_verifier",
        error,
        gkr_verify_calls,
        pcs_verify_calls: 0,
        bind_calls,
        challenge_count: transcript.challenges(),
    }
}

fn two_bank_pcs_negative(
    core: &SparseCircuit,
    paired: &SparseCircuit,
    core_digest: &str,
    spec: TwoBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    proof: &GkrProof,
    commitment: &ArkGT,
    opening: &dory_pcs::backends::arkworks::ArkDoryProof,
    key: &crate::verifier_key::AdmittedVerifierKey,
    wrong_point: bool,
) -> TwoBankNegative {
    let mut transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
    let mut bind_calls = 0usize;
    let mut gkr_verify_calls = 0usize;
    let mut pcs_verify_calls = 0usize;
    gkr_verify_calls += 1;
    let claim = match verify_two_bank_projection(
        core, paired, core_digest, spec, setup_id, commitment_bytes, proof,
        &mut transcript, &mut bind_calls,
    ) {
        Ok(claim) => claim,
        Err(error) => return TwoBankNegative {
            rejected_by: "fresh_gkr_verifier",
            error: error.to_string(),
            gkr_verify_calls,
            pcs_verify_calls,
            bind_calls,
            challenge_count: transcript.challenges(),
        },
    };
    let mut parent_point = work_tree_layout::embed_bank(
        BANK_START,
        BANK_WIDTH * 2,
        SLOT_BITS,
        &claim.point,
    ).expect("fresh claim embeds into original W24 coordinates");
    let value = if wrong_point {
        parent_point[17] += Fr::one();
        claim.value
    } else {
        claim.value + Fr::one()
    };
    pcs_verify_calls += 1;
    let result = crate::pcs::verify_admitted(
        commitment.clone(), value, &parent_point, opening, key, &mut transcript,
    );
    let error = result.err().unwrap_or_else(|| "PCS accepted the isolated mutant".into());
    TwoBankNegative {
        rejected_by: "pcs_consumer",
        error,
        gkr_verify_calls,
        pcs_verify_calls,
        bind_calls,
        challenge_count: transcript.challenges(),
    }
}

#[test]
fn two_bank_mapping_and_wiring_reject_invalid_mappings() {
    let (core, _, core_digest) = canonical_core();
    let paired = build_two_bank_core(&core, TWO_BANK_SPEC).unwrap();
    let paired_shape = validate_two_bank(&core, &paired, &core_digest, TWO_BANK_SPEC).unwrap();
    let core_shape = sparse::validate(&core, 0).unwrap();
    assert_eq!(paired_shape.input_bits, TWO_BANK_INPUT_BITS);
    assert_eq!(paired_shape.row_bits, TWO_BANK_ROW_BITS);
    assert_eq!(paired_shape.copies, 1);
    assert_eq!(paired.input_len, 1 << 17);
    assert_eq!(paired.row_count, 1 << 18);
    assert_eq!(paired.terms.len(), TWO_BANK_TERMS);
    assert_eq!(core_digest, TWO_BANK_CORE_DIGEST);

    let bad_specs = [
        TwoBankSpec { bank_indices: [1, 0], ..TWO_BANK_SPEC },
        TwoBankSpec { bank_indices: [0, 2], ..TWO_BANK_SPEC },
        TwoBankSpec { bank_input_offsets: [0, 65_535], ..TWO_BANK_SPEC },
        TwoBankSpec { bank_row_offsets: [0, 131_071], ..TWO_BANK_SPEC },
        TwoBankSpec { input_bits: TWO_BANK_INPUT_BITS - 1, ..TWO_BANK_SPEC },
        TwoBankSpec { row_bits: TWO_BANK_ROW_BITS - 1, ..TWO_BANK_SPEC },
        TwoBankSpec { slot_bits: SLOT_BITS - 1, ..TWO_BANK_SPEC },
    ];
    for invalid in bad_specs {
        let mut loader_calls = 0usize;
        let mut visitor_calls = 0usize;
        let mut bind_calls = 0usize;
        let mut transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
        let result = prove_two_bank_projection(
            &core, &paired, &core_digest, invalid, &[0u8; 32], b"commitment",
            None,
            |_| { loader_calls += 1; Err("loader must not run".into()) },
            |_, _| { visitor_calls += 1; Ok(()) },
            &mut transcript, &mut bind_calls,
        );
        assert!(result.is_err(), "each isolated mapping mutant is rejected");
        assert_eq!((loader_calls, visitor_calls, bind_calls, transcript.challenges()), (0, 0, 0, 0));
    }
    for owner in [0usize, 1, OWNER_COUNT - 1] {
        for local in [0usize, 1, BANK_WIDTH, BANK_WIDTH * 2 - 1] {
            let point = bool_point(TWO_BANK_PROJECTED_INPUT_BITS, local | (owner << TWO_BANK_INPUT_BITS));
            let embedded = work_tree_layout::embed_bank(0, BANK_WIDTH * 2, SLOT_BITS, &point).unwrap();
            let expected_index = owner * SOURCE_BITS / OWNER_COUNT + local;
            assert_eq!(embedded, bool_point(PARENT_LOG_N, expected_index));
        }
    }
    let valid_bank_point = bool_point(TWO_BANK_PROJECTED_INPUT_BITS, BANK_WIDTH);
    assert!(work_tree_layout::embed_bank(BANK_WIDTH, BANK_WIDTH * 2, SLOT_BITS, &valid_bank_point).is_err());
    assert!(work_tree_layout::embed_bank(0, BANK_WIDTH * 2, SLOT_BITS, &valid_bank_point[..20]).is_err());
    let mut truncated_pair = paired.clone();
    truncated_pair.terms.pop();
    assert!(validate_two_bank(&core, &truncated_pair, &core_digest, TWO_BANK_SPEC).is_err());
    let mut truncated_loader_calls = 0usize;
    let mut truncated_visitor_calls = 0usize;
    let mut truncated_bind_calls = 0usize;
    let mut truncated_transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
    assert!(prove_two_bank_projection(
        &core, &truncated_pair, &core_digest, TWO_BANK_SPEC, &[0u8; 32], b"commitment",
        None,
        |_| { truncated_loader_calls += 1; Err("loader must not run".into()) },
        |_, _| { truncated_visitor_calls += 1; Ok(()) },
        &mut truncated_transcript, &mut truncated_bind_calls,
    ).is_err());
    assert_eq!(
        (truncated_loader_calls, truncated_visitor_calls, truncated_bind_calls, truncated_transcript.challenges()),
        (0, 0, 0, 0),
        "malformed combined term length is rejected before callbacks",
    );
    let original_first_term = paired.terms[0].clone();
    let mut mutated_pair = paired.clone();
    for mutation in 0..7 {
        let term = &mut mutated_pair.terms[0];
        match mutation {
            0 => term.row += 1,
            1 => term.gate.left += 1,
            2 => term.gate.right += 1,
            3 => term.gate.c0 += Fr::one(),
            4 => term.gate.c1 += Fr::one(),
            5 => term.gate.c2 += Fr::one(),
            6 => term.gate.c3 += Fr::one(),
            _ => unreachable!(),
        }
        assert_two_bank_rejects_before_callbacks(&core, &mutated_pair, &core_digest, TWO_BANK_SPEC);
        mutated_pair.terms[0] = original_first_term.clone();
    }
    let mut bad_input_dimensions = paired.clone();
    bad_input_dimensions.input_len += 1;
    assert_two_bank_rejects_before_callbacks(&core, &bad_input_dimensions, &core_digest, TWO_BANK_SPEC);
    let mut bad_row_dimensions = paired.clone();
    bad_row_dimensions.row_count += 1;
    assert_two_bank_rejects_before_callbacks(&core, &bad_row_dimensions, &core_digest, TWO_BANK_SPEC);

    let row_point: Vec<_> = (0..TWO_BANK_PROJECTED_ROW_BITS)
        .map(|index| Fr::from((index + 3) as u64)).collect();
    let left_point: Vec<_> = (0..TWO_BANK_PROJECTED_INPUT_BITS)
        .map(|index| Fr::from((index + 29) as u64)).collect();
    let right_point: Vec<_> = (0..TWO_BANK_PROJECTED_INPUT_BITS)
        .map(|index| Fr::from((index + 71) as u64)).collect();
    let projected = two_bank_wiring(&core, &core_shape, &row_point, &left_point, &right_point).unwrap();
    let streamed = two_bank_streamed_global_oracle(&core, &row_point, &left_point, &right_point);
    assert_eq!(projected, streamed, "all four coefficients match the independent streamed bank oracle");

    let mixed_row: Vec<_> = (0..TWO_BANK_ROW_BITS)
        .map(|index| Fr::from((index + 103) as u64))
        .chain([0u64, 1, 2, 5].into_iter().map(Fr::from)).collect();
    let mixed_left: Vec<_> = (0..TWO_BANK_INPUT_BITS)
        .map(|index| Fr::from((index + 211) as u64))
        .chain([2u64, 1, 5, 0].into_iter().map(Fr::from)).collect();
    let mixed_right: Vec<_> = (0..TWO_BANK_INPUT_BITS)
        .map(|index| Fr::from((index + 307) as u64))
        .chain([0u64, 3, 7, 9].into_iter().map(Fr::from)).collect();
    assert!(!two_bank_slot_factor(&mixed_row, &mixed_left, &mixed_right).is_zero());
    assert_eq!(
        two_bank_wiring(&core, &core_shape, &mixed_row, &mixed_left, &mixed_right).unwrap(),
        two_bank_streamed_global_oracle(&core, &mixed_row, &mixed_left, &mixed_right),
        "mixed Boolean/non-Boolean points retain a nonzero selector factor",
    );
    assert!(two_bank_wiring(&core, &core_shape, &row_point[..row_point.len()-1], &left_point, &right_point).is_err());
    assert!(two_bank_wiring(&core, &core_shape, &row_point, &left_point[..left_point.len()-1], &right_point).is_err());
    assert!(two_bank_wiring(&core, &core_shape, &row_point, &left_point, &right_point[..right_point.len()-1]).is_err());

    // Exercise the actual roster residual gate: distinct nonzero rows must
    // reject before the relation binder can sample a challenge.
    let cancellation = SparseCircuit {
        input_len: 1,
        row_count: 2,
        terms: vec![
            Term { row: 0, gate: gkr::Gate { left: 0, right: 0, c0: Fr::one(), c1: Fr::zero(), c2: Fr::zero(), c3: Fr::zero() } },
            Term { row: 1, gate: gkr::Gate { left: 0, right: 0, c0: -Fr::one(), c1: Fr::zero(), c2: Fr::zero(), c3: Fr::zero() } },
        ],
    };
    let mut cancellation_loader_calls = 0usize;
    let mut cancellation_term_visits = 0usize;
    let mut cancellation_bind_calls = 0usize;
    let mut cancellation_transcript = Transcript::new(b"two-bank-row-cancellation-fixture");
    let cancellation_result = sparse_stream_roster::prove(
        0, 0, 1, 0, &[1],
        |_| { cancellation_loader_calls += 1; Ok(vec![Fr::zero()]) },
        &mut cancellation_transcript,
        |_| { cancellation_bind_calls += 1; },
        |_, sink| {
            cancellation_term_visits += 1;
            for term in &cancellation.terms { sink(term.clone())?; }
            Ok(())
        },
        |_, _, _| Ok([Fr::zero(); 4]),
    );
    assert_eq!(cancellation_result.unwrap_err(), "GKR error: NonzeroOutput");
    assert_eq!(cancellation_loader_calls, 1);
    assert_eq!(cancellation_term_visits, 1);
    assert_eq!(cancellation_bind_calls, 0);
    assert_eq!(cancellation_transcript.challenges(), 0);
}

#[test]
fn native_window16_banks0_1_gkr_claim_authenticates_original_parent_commitment_pcs24() {
    let whole_started = Instant::now();
    let (core, core_layout, core_digest) = canonical_core();
    let paired = build_two_bank_core(&core, TWO_BANK_SPEC).expect("build shifted two-bank relation");
    let shape = validate_two_bank(&core, &paired, &core_digest, TWO_BANK_SPEC).unwrap();
    assert_eq!(shape.input_bits + SLOT_BITS, 21);
    assert_eq!(shape.row_bits + SLOT_BITS, 22);
    assert_eq!(paired.terms.len(), TWO_BANK_TERMS);

    let artifact_directory = std::env::var(TWO_BANK_ARTIFACT_DIR_ENV)
        .expect("runner pins NIPOPOW_TWO_BANK_ARTIFACT_DIR");
    assert_eq!(fs::read_dir(&artifact_directory).unwrap().count(), 0, "fresh output dir");
    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE")
        .expect("runner pins Window16 source");
    assert_eq!(fs::metadata(&source_path).unwrap().len(), SOURCE_BYTES);
    let parent = PackedFile::open(&source_path, PARENT_LOG_N).expect("open pinned Window16 source");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    let source_open_io = parent.io_metrics_snapshot();
    assert_eq!((source_open_io.read_calls, source_open_io.read_bytes), (0, 0));

    let reference_directory = std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV)
        .expect("runner pins original common-PCS artifacts");
    let reference_path = |name: &str| std::path::Path::new(&reference_directory).join(name);
    let reference_commitment_bytes = fs::read(reference_path(COMMON_PCS_COMMITMENT_FILE))
        .expect("read original parent commitment bytes");
    let reference_key_bytes = fs::read(reference_path(COMMON_PCS_KEY_FILE))
        .expect("read original TEST24 public verifier key bytes");
    let reference_result_bytes = fs::read(reference_path(COMMON_PCS_RESULT_FILE))
        .expect("read original common-PCS structured result");
    let reference_result: serde_json::Value = serde_json::from_slice(&reference_result_bytes)
        .expect("decode original common-PCS result");
    assert_eq!(reference_result["schema"].as_str(), Some("native-core-bank-projection-pcs-v1"));
    assert_eq!(reference_result["test"].as_str(), Some("native_window16_bank0_gkr_claim_authenticates_original_parent_commitment_pcs24"));
    assert_eq!(reference_result["source"]["sha256"].as_str(), Some(SOURCE_SHA256));
    assert_eq!(reference_result["source"]["bytes"].as_u64(), Some(SOURCE_BYTES));
    assert_eq!(reference_result["setup"]["log_n"].as_u64(), Some(PARENT_LOG_N as u64));
    assert_eq!(reference_result["dory"]["verified_with_generated_test_key"].as_bool(), Some(true));

    let setup_started = Instant::now();
    let setup = crate::pcs::generate_setup(PARENT_LOG_N).expect("reconstruct original diagnostic setup24");
    let setup_reconstruction_ms = setup_started.elapsed().as_millis();
    let setup_id = setup.id;
    let setup_id_hex = hex_bytes(&setup_id);
    assert_eq!(setup_id_hex, reference_result["setup"]["id_hex"].as_str().unwrap());
    assert_eq!(setup_id_hex, "b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe");

    let key_encode_started = Instant::now();
    let verifier_key_bytes = crate::pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))
        .expect("serialize original diagnostic verifier key");
    let verifier_key_encode_ms = key_encode_started.elapsed().as_millis();
    assert_eq!(verifier_key_bytes.len(), reference_key_bytes.len());
    assert_eq!(verifier_key_bytes, reference_key_bytes, "reconstructed key byte identity");
    let verifier_key_hash = work_tree_layout::hash_bytes(&verifier_key_bytes);
    assert_eq!(verifier_key_hash, reference_result["setup"]["verifier_key_blake2b256"].as_str().unwrap());

    let public_admit_started = Instant::now();
    let public_admit_24_error = match crate::verifier_key::admit(PARENT_LOG_N, &verifier_key_bytes) {
        Err(error) => error,
        Ok(_) => panic!("public verifier-key admission unexpectedly accepted dimension 24"),
    };
    let public_admit_24_reject_ms = public_admit_started.elapsed().as_millis();
    assert_eq!(public_admit_24_error, "unsupported verifier-key dimension");
    parent.reset_io_metrics();
    let commitment_started = Instant::now();
    let committed = crate::packed::commit(&parent, &setup).expect("reconstruct original parent commitment");
    let commitment_reconstruction_ms = commitment_started.elapsed().as_millis();
    let commitment_io = parent.io_metrics_snapshot();
    assert_eq!(commitment_io.read_calls, 1);
    assert_eq!(commitment_io.read_bytes, SOURCE_BYTES);
    let commitment_bytes = crate::pcs::encode_commitment(&committed.commitment)
        .expect("encode reconstructed original commitment");
    assert_eq!(commitment_bytes.len(), 384);
    assert_eq!(commitment_bytes, reference_commitment_bytes, "reconstructed original commitment bytes");
    assert_eq!(
        work_tree_layout::hash_bytes(&commitment_bytes),
        reference_result["commitment"]["blake2b256"].as_str().unwrap(),
    );
    let parent_commitment = crate::pcs::decode_commitment(&commitment_bytes)
        .expect("decode reconstructed commitment for consumers");
    assert_eq!(crate::pcs::encode_commitment(&parent_commitment).unwrap(), commitment_bytes);
    let alternate_commitment = ArkGT(parent_commitment.0.clone() + setup.prover.ht.0.clone());
    assert_ne!(alternate_commitment, parent_commitment);
    let alternate_commitment_bytes = crate::pcs::encode_commitment(&alternate_commitment)
        .expect("encode different valid GT commitment prefix mutant");
    assert_eq!(
        crate::pcs::decode_commitment(&alternate_commitment_bytes).unwrap(),
        alternate_commitment,
        "alternate prefix is a canonical valid GT commitment",
    );

    // A one-bit corruption in bank1 must fail the real residual pass before
    // relation binding or any transcript challenge.
    let mutation_wire = core_layout.output[0][0];
    assert!(mutation_wire < BANK_WIDTH);
    let mut mutation_transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
    let mut mutation_bind_calls = 0usize;
    let mut mutation_loader_calls = 0usize;
    let mut mutation_visitor_calls = 0usize;
    let mutation_result = prove_two_bank_projection(
        &core, &paired, &core_digest, TWO_BANK_SPEC, &setup_id, &commitment_bytes,
        None,
        |owner| {
            mutation_loader_calls += 1;
            let mut values = load_two_bank_owner(&parent, owner)?;
            if owner == 0 {
                let cell = &mut values[BANK_WIDTH + mutation_wire];
                assert!(*cell == Fr::zero() || *cell == Fr::one());
                *cell = Fr::one() - *cell;
            }
            Ok(values)
        },
        |_, sink| {
            mutation_visitor_calls += 1;
            for term in &paired.terms { sink(term.clone())?; }
            Ok(())
        },
        &mut mutation_transcript, &mut mutation_bind_calls,
    );
    let mutation_error = mutation_result.err().expect("bank1 mutated witness must fail residuals");
    assert_eq!(mutation_error, "GKR error: NonzeroOutput");
    assert!(mutation_loader_calls > 0);
    assert!(mutation_visitor_calls > 0, "mutated bank1 reaches the actual residual visitor");
    assert_eq!((mutation_bind_calls, mutation_transcript.challenges()), (0, 0));

    parent.reset_io_metrics();
    let mut prover_transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
    let mut load_calls = 0usize;
    let mut term_visit_passes_by_owner = vec![0usize; OWNER_COUNT];
    let mut term_sink_calls = 0usize;
    let mut producer_bind_calls = 0usize;
    let producer_started = Instant::now();
    let (proof, claim) = prove_two_bank_projection(
        &core, &paired, &core_digest, TWO_BANK_SPEC, &setup_id, &commitment_bytes,
        None,
        |owner| {
            load_calls += 1;
            load_two_bank_owner(&parent, owner)
        },
        |owner, sink| {
            if owner >= OWNER_COUNT { return Err("two-bank owner index out of range".into()); }
            term_visit_passes_by_owner[owner] += 1;
            for term in &paired.terms {
                term_sink_calls += 1;
                sink(term.clone())?;
            }
            Ok(())
        },
        &mut prover_transcript, &mut producer_bind_calls,
    ).expect("prove paired native bank relation using the unchanged default cache budget");
    let producer_gkr_ms = producer_started.elapsed().as_millis();
    assert_eq!(producer_bind_calls, 1);
    let term_visit_passes: usize = term_visit_passes_by_owner.iter().sum();
    assert_eq!(term_visit_passes_by_owner.len(), OWNER_COUNT);
    let producer_io = parent.io_metrics_snapshot();
    assert_eq!(producer_io.read_calls, (load_calls * 2) as u64);
    assert_eq!(producer_io.read_bytes, (load_calls * (1 << TWO_BANK_INPUT_BITS) / 8) as u64);
    let encoded_proof = gkr::encode_proof(&proof).expect("encode paired GKR proof");
    assert_eq!(encoded_proof.len(), 4_800);
    let prover_post_gkr = prover_transcript.clone();

    let parent_point = work_tree_layout::embed_bank(
        BANK_START, BANK_WIDTH * 2, SLOT_BITS, &claim.point,
    ).expect("embed the producer claim into the original W24 parent coordinates");
    assert_eq!(claim.point.len(), TWO_BANK_PROJECTED_INPUT_BITS);
    assert_eq!(parent_point.len(), PARENT_LOG_N);
    assert_eq!(&parent_point[17..20], &[Fr::zero(); 3]);

    parent.reset_io_metrics();
    let parent_mle_started = Instant::now();
    let parent_mle_value = parent.evaluate(&parent_point).expect("evaluate original parent MLE at paired claim");
    let parent_mle_ms = parent_mle_started.elapsed().as_millis();
    let parent_mle_io = parent.io_metrics_snapshot();
    assert_eq!(parent_mle_io.read_calls, 1);
    assert_eq!(parent_mle_io.read_bytes, SOURCE_BYTES);
    assert_eq!(parent_mle_value, claim.value);

    parent.reset_io_metrics();
    let opening_started = Instant::now();
    let opening = crate::packed::open(
        &committed, &parent, &parent_point, &setup, &mut prover_transcript,
    ).expect("create a new Dory opening at the paired parent point");
    let open_dory_ms = opening_started.elapsed().as_millis();
    let opening_io = parent.io_metrics_snapshot();
    assert_eq!(opening_io.read_calls, 2);
    assert_eq!(opening_io.read_bytes, SOURCE_BYTES * 2);
    let encoded_opening = crate::pcs::encode_proof(&opening).expect("encode new Dory opening");
    assert_eq!(encoded_opening.len(), 32_013);

    // All prover-side setup and row commitments are dropped before verification.
    drop(committed);
    drop(setup);

    let decoded_opening = crate::pcs::decode_proof(&encoded_opening, PARENT_LOG_N)
        .expect("fresh decode new Dory opening after dropping prover setup");
    assert_eq!(crate::pcs::encode_proof(&decoded_opening).unwrap(), encoded_opening);

    let key_admit_started = Instant::now();
    let verifier_key = crate::verifier_key::admit_generated_test_key(
        PARENT_LOG_N, &reference_key_bytes, setup_id,
    ).expect("freshly decode the original stored TEST24 public key after dropping setup");
    let verifier_key_decode_admit_ms = key_admit_started.elapsed().as_millis();
    assert_eq!(verifier_key.id(), &setup_id);

    let proof_decode_started = Instant::now();
    let decoded_proof = gkr::decode_dimensions(&[TWO_BANK_PROJECTED_INPUT_BITS], &encoded_proof)
        .expect("fresh decode exact 21-dimensional proof after dropping setup");
    let proof_decode_ms = proof_decode_started.elapsed().as_millis();
    assert_eq!(decoded_proof, proof);
    let mut verifier_transcript = Transcript::new(TWO_BANK_TRANSCRIPT_DOMAIN);
    let mut verifier_bind_calls = 0usize;
    let mut gkr_verify_calls = 0usize;
    gkr_verify_calls += 1;
    parent.reset_io_metrics();
    let fresh_gkr_started = Instant::now();
    let verified_claim = verify_two_bank_projection(
        &core, &paired, &core_digest, TWO_BANK_SPEC, &setup_id, &commitment_bytes,
        &decoded_proof, &mut verifier_transcript, &mut verifier_bind_calls,
    ).expect("fresh verify paired proof after dropping prover setup");
    let fresh_gkr_verify_ms = fresh_gkr_started.elapsed().as_millis();
    let fresh_gkr_io = parent.io_metrics_snapshot();
    assert_eq!(fresh_gkr_io.read_calls, 0);
    assert_eq!(fresh_gkr_io.read_bytes, 0);
    assert_eq!(gkr_verify_calls, 1);
    assert_eq!(verifier_bind_calls, 1);
    assert_eq!(claim, verified_claim);
    assert_eq!(prover_post_gkr.challenges(), verifier_transcript.challenges());
    assert_eq!(prover_post_gkr.raw_queries(), verifier_transcript.raw_queries());
    assert_eq!(prover_post_gkr.bytes_absorbed(), verifier_transcript.bytes_absorbed());
    assert_eq!(
        work_tree_layout::embed_bank(BANK_START, BANK_WIDTH * 2, SLOT_BITS, &verified_claim.point).unwrap(),
        parent_point,
    );
    let mut prover_continuation = prover_post_gkr.clone();
    let mut verifier_continuation = verifier_transcript.clone();
    let prover_next = prover_continuation.challenge_scalar(b"two-bank-post-gkr");
    let verifier_next = verifier_continuation.challenge_scalar(b"two-bank-post-gkr");
    let transcript_continuation_matches = prover_next == verifier_next
        && prover_continuation.challenges() == verifier_continuation.challenges()
        && prover_continuation.raw_queries() == verifier_continuation.raw_queries()
        && prover_continuation.bytes_absorbed() == verifier_continuation.bytes_absorbed();
    assert!(transcript_continuation_matches);
    let mut trailing_proof = encoded_proof.clone();
    trailing_proof.push(0);
    let trailing_error = gkr::decode_dimensions(&[TWO_BANK_PROJECTED_INPUT_BITS], &trailing_proof)
        .expect_err("GKR codec must reject the isolated trailing byte");
    assert_eq!(trailing_error, "GKR proof length: expected 4800, received 4801");

    parent.reset_io_metrics();
    let fresh_pcs_started = Instant::now();
    let mut pcs_verify_calls = 0usize;
    pcs_verify_calls += 1;
    let mut consumer_transcript = verifier_transcript.clone();
    crate::pcs::verify_admitted(
        parent_commitment.clone(), verified_claim.value, &parent_point, &decoded_opening,
        &verifier_key, &mut consumer_transcript,
    ).expect("verify new opening using original TEST24 public-key object");
    let fresh_pcs_verify_ms = fresh_pcs_started.elapsed().as_millis();
    let fresh_pcs_io = parent.io_metrics_snapshot();
    assert_eq!(fresh_pcs_io.read_calls, 0);
    assert_eq!(fresh_pcs_io.read_bytes, 0);
    assert_eq!(pcs_verify_calls, 1);

    let mut setup_prefix = setup_id;
    setup_prefix[0] ^= 1;
    let setup_negative = two_bank_prefix_negative(
        &core, &paired, &core_digest, TWO_BANK_SPEC, &setup_prefix,
        &commitment_bytes, &decoded_proof,
    );
    let commitment_negative = two_bank_prefix_negative(
        &core, &paired, &core_digest, TWO_BANK_SPEC, &setup_id,
        &alternate_commitment_bytes, &decoded_proof,
    );
    let wrong_point_negative = two_bank_pcs_negative(
        &core, &paired, &core_digest, TWO_BANK_SPEC, &setup_id, &commitment_bytes,
        &decoded_proof, &parent_commitment, &decoded_opening, &verifier_key, true,
    );
    let wrong_value_negative = two_bank_pcs_negative(
        &core, &paired, &core_digest, TWO_BANK_SPEC, &setup_id, &commitment_bytes,
        &decoded_proof, &parent_commitment, &decoded_opening, &verifier_key, false,
    );
    assert_eq!(setup_negative.rejected_by, "fresh_gkr_verifier");
    assert_eq!(setup_negative.pcs_verify_calls, 0);
    assert_eq!(commitment_negative.rejected_by, "fresh_gkr_verifier");
    assert_eq!(commitment_negative.pcs_verify_calls, 0);
    assert_eq!(wrong_point_negative.rejected_by, "pcs_consumer");
    assert_eq!(wrong_point_negative.error, "Invalid proof");
    assert_eq!(wrong_value_negative.rejected_by, "pcs_consumer");
    assert_eq!(wrong_value_negative.error, "Invalid proof");
    assert_eq!((wrong_point_negative.gkr_verify_calls, wrong_point_negative.pcs_verify_calls), (1, 1));
    assert_eq!((wrong_value_negative.gkr_verify_calls, wrong_value_negative.pcs_verify_calls), (1, 1));
    assert_eq!((setup_negative.bind_calls, setup_negative.pcs_verify_calls), (1, 0));
    assert_eq!((commitment_negative.bind_calls, commitment_negative.pcs_verify_calls), (1, 0));
    assert_eq!(setup_negative.error, "GKR error: SumcheckIdentity");
    assert_eq!(commitment_negative.error, "GKR error: SumcheckIdentity");
    assert!(setup_negative.challenge_count > 0);
    assert!(commitment_negative.challenge_count > 0);

    let output_bit_negative = TwoBankNegative {
        rejected_by: "residual_guard",
        error: mutation_error,
        gkr_verify_calls: 0,
        pcs_verify_calls: 0,
        bind_calls: mutation_bind_calls,
        challenge_count: mutation_transcript.challenges(),
    };
    let trailing_negative = TwoBankNegative {
        rejected_by: "gkr_codec",
        error: trailing_error,
        gkr_verify_calls: 0,
        pcs_verify_calls: 0,
        bind_calls: 0,
        challenge_count: 0,
    };

    let gkr_point_hex = two_bank_hex_point(&verified_claim.point);
    let embedded_parent_point_hex = two_bank_hex_point(&parent_point);
    let claim_value_hex = hex_bytes(&crate::pcs::encode(&verified_claim.value).unwrap());
    let parent_mle_value_hex = hex_bytes(&crate::pcs::encode(&parent_mle_value).unwrap());
    let proof_blake2b256 = work_tree_layout::hash_bytes(&encoded_proof);
    let opening_blake2b256 = work_tree_layout::hash_bytes(&encoded_opening);
    let commitment_blake2b256 = work_tree_layout::hash_bytes(&commitment_bytes);
    let total_before_result_write_ms = whole_started.elapsed().as_millis();
    assert!(term_visit_passes_by_owner.iter().all(|passes| *passes == term_visit_passes_by_owner[0]));
    let term_passes_per_owner = term_visit_passes_by_owner[0];

    write_new_pcs_artifact(&artifact_directory, TWO_BANK_GKR_FILE, &encoded_proof);
    write_new_pcs_artifact(&artifact_directory, TWO_BANK_OPENING_FILE, &encoded_opening);
    let result = json!({
        "schema": "native-two-bank-common-pcs-v1",
        "test": TWO_BANK_NATIVE_TEST_NAME,
        "scope": "one native Window16 two-bank GKR claim authenticated to the original parent commitment with a reconstructed diagnostic setup and original TEST24 verifier key; bounded diagnostic only",
        "source": {
            "sha256": SOURCE_SHA256,
            "bytes": SOURCE_BYTES,
            "bits": SOURCE_BITS,
            "parent_log_n": PARENT_LOG_N,
            "owner_count": OWNER_COUNT,
            "parent_owner_bits": PARENT_OWNER_BITS,
        },
        "relation": {
            "bank_indices": TWO_BANK_BANKS,
            "bank_input_offsets": TWO_BANK_INPUT_OFFSETS,
            "bank_row_offsets": TWO_BANK_ROW_OFFSETS,
            "bank_width": BANK_WIDTH,
            "core_input_bits": CORE_INPUT_BITS,
            "core_row_bits": CORE_ROW_BITS,
            "core_terms": CORE_TERMS,
            "core_term_digest_blake2b256": core_digest,
            "combined_input_bits": TWO_BANK_INPUT_BITS,
            "combined_row_bits": TWO_BANK_ROW_BITS,
            "combined_terms": paired.terms.len(),
            "member_row_bits": [TWO_BANK_ROW_BITS],
            "slot_bits": SLOT_BITS,
            "projected_input_bits": TWO_BANK_PROJECTED_INPUT_BITS,
            "projected_row_bits": TWO_BANK_PROJECTED_ROW_BITS,
            "parent_point_bits": PARENT_LOG_N,
            "parent_fixed_zero_coordinates": [17, 18, 19],
            "source_read_width": 1usize << TWO_BANK_INPUT_BITS,
            "copies_per_owner": 8,
            "wiring_recipe": "core_wiring(r[..17],u[..16],v[..16])*triple_eq(r[17],u[16],v[16])*product(j=0..3,triple_eq(r[18+j],u[17+j],v[17+j])); triple_eq(a,b,c)=(1-a)*(1-b)*(1-c)+a*b*c",
        },
        "identity": {
            "input_receipt_sha256": CACHE_REFERENCE_INPUTS_SHA256,
            "setup_id_hex": setup_id_hex,
            "setup_id_matches_reference": true,
            "verifier_key_file": COMMON_PCS_KEY_FILE,
            "verifier_key_bytes": verifier_key_bytes.len(),
            "verifier_key_blake2b256": verifier_key_hash,
            "verifier_key_matches_reference": verifier_key_bytes == reference_key_bytes,
            "commitment_file": COMMON_PCS_COMMITMENT_FILE,
            "commitment_bytes": commitment_bytes.len(),
            "commitment_blake2b256": commitment_blake2b256,
            "commitment_matches_reference": commitment_bytes == reference_commitment_bytes,
            "public_admit_24_rejected": true,
            "public_admit_24_error": public_admit_24_error,
        },
        "producer": {
            "cache_budget_bytes": sparse_stream_roster::MAX_INCREMENTAL_CACHE_STATE_BYTES,
            "load_calls": load_calls,
            "term_visit_passes": term_visit_passes,
            "term_passes_per_owner": term_passes_per_owner,
            "term_sink_calls": term_sink_calls,
            "proof_file": TWO_BANK_GKR_FILE,
            "proof_bytes": encoded_proof.len(),
            "proof_blake2b256": proof_blake2b256,
            "decoded_exact_dimensions": decoded_proof == proof,
            "proof_point_hex": gkr_point_hex,
            "embedded_parent_point_hex": embedded_parent_point_hex,
            "claim_value_hex": claim_value_hex,
            "parent_mle_value_hex": parent_mle_value_hex,
            "claim_matches_fresh_verifier": claim == verified_claim,
            "claim_matches_parent_mle": verified_claim.value == parent_mle_value,
            "transcript_continuation_matches": transcript_continuation_matches,
        },
        "opening": {
            "file": TWO_BANK_OPENING_FILE,
            "bytes": encoded_opening.len(),
            "blake2b256": opening_blake2b256,
            "verified_with_original_test_key": true,
        },
        "negative": {
            "bank1_output_mutation": two_bank_negative_json(&output_bit_negative),
            "wrong_setup_prefix": two_bank_negative_json(&setup_negative),
            "wrong_commitment_prefix": two_bank_negative_json(&commitment_negative),
            "wrong_embedded_bank_coordinate": two_bank_negative_json(&wrong_point_negative),
            "wrong_valid_claim_value": two_bank_negative_json(&wrong_value_negative),
            "trailing_gkr_byte": two_bank_negative_json(&trailing_negative),
        },
        "timing_ms": {
            "setup_reconstruction": setup_reconstruction_ms,
            "verifier_key_encode": verifier_key_encode_ms,
            "public_admit_24_reject": public_admit_24_reject_ms,
            "commitment_reconstruction": commitment_reconstruction_ms,
            "producer_gkr": producer_gkr_ms,
            "proof_decode": proof_decode_ms,
            "fresh_gkr_verify": fresh_gkr_verify_ms,
            "parent_mle": parent_mle_ms,
            "open_dory": open_dory_ms,
            "verifier_key_decode_admit": verifier_key_decode_admit_ms,
            "fresh_pcs_verify": fresh_pcs_verify_ms,
            "whole_test_before_result_write": total_before_result_write_ms,
        },
        "io": {
            "source_open": packed_io_json(source_open_io),
            "commitment_reconstruction": packed_io_json(commitment_io),
            "producer": packed_io_json(producer_io),
            "parent_mle": packed_io_json(parent_mle_io),
            "open_dory": packed_io_json(opening_io),
            "fresh_gkr_verify": packed_io_json(fresh_gkr_io),
            "fresh_pcs_verify": packed_io_json(fresh_pcs_io),
        },
        "global_proof": false,
        "pcs_scope": "bounded diagnostic only",
    });
    let result_bytes = serde_json::to_vec_pretty(&result).expect("serialize two-bank result");
    write_new_pcs_artifact(&artifact_directory, TWO_BANK_RESULT_FILE, &result_bytes);
    println!("two_bank_common_pcs_result={}", serde_json::to_string(&result).unwrap());
}

// Far-bank diagnostic: keep the native compression circuit local and select
// one fixed physical source bank through the transcript and parent embedding.
const FAR_BANK_ARTIFACT_DIR_ENV: &str = "NIPOPOW_FAR_BANK_ARTIFACT_DIR";
const FAR_BANK_GKR_FILE: &str = "far-bank-gkr-proof.bin";
const FAR_BANK_OPENING_FILE: &str = "far-bank-parent-opening.bin";
const FAR_BANK_RESULT_FILE: &str = "far-bank-result.json";
const FAR_BANK_TRANSCRIPT_DOMAIN: &[u8] = b"nipopow-v2-native-far-bank-parent-pcs-join-v1";
const FAR_BANK_PROJECTED_INPUT_BITS: usize = CORE_INPUT_BITS + SLOT_BITS;
const FAR_BANK_PROJECTED_ROW_BITS: usize = CORE_ROW_BITS + SLOT_BITS;
const FAR_BANK_PROOF_BYTES: usize = 4_576;
const FAR_BANK_OPENING_BYTES: usize = 32_013;
const FAR_BANK_CORE_DIGEST: &str =
    "5210e3be7975701b4e97647b724c8340e443c622debbda0c0ea44f5bc995577c";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FarBankAddress {
    core_ordinal: usize,
    physical_index: usize,
    start: usize,
}

const FAR_BANK_MAPPING: [FarBankAddress; 11] = [
    FarBankAddress { core_ordinal: 0, physical_index: 0, start: 0 },
    FarBankAddress { core_ordinal: 1, physical_index: 1, start: 65_536 },
    FarBankAddress { core_ordinal: 2, physical_index: 2, start: 131_072 },
    FarBankAddress { core_ordinal: 3, physical_index: 3, start: 196_608 },
    FarBankAddress { core_ordinal: 4, physical_index: 4, start: 262_144 },
    FarBankAddress { core_ordinal: 5, physical_index: 5, start: 327_680 },
    FarBankAddress { core_ordinal: 6, physical_index: 6, start: 393_216 },
    FarBankAddress { core_ordinal: 7, physical_index: 7, start: 458_752 },
    FarBankAddress { core_ordinal: 8, physical_index: 11, start: 720_896 },
    FarBankAddress { core_ordinal: 9, physical_index: 13, start: 851_968 },
    FarBankAddress { core_ordinal: 10, physical_index: 14, start: 917_504 },
];

#[derive(Clone, Copy)]
struct FarBankSpec {
    bank_mapping: [FarBankAddress; 11],
    selected_bank: FarBankAddress,
    input_bits: usize,
    row_bits: usize,
    slot_bits: usize,
}

const FAR_BANK_SPEC: FarBankSpec = FarBankSpec {
    bank_mapping: FAR_BANK_MAPPING,
    selected_bank: FAR_BANK_MAPPING[10],
    input_bits: CORE_INPUT_BITS,
    row_bits: CORE_ROW_BITS,
    slot_bits: SLOT_BITS,
};

fn validate_far_bank_spec(spec: FarBankSpec) -> Result<(), String> {
    if spec.bank_mapping != FAR_BANK_MAPPING {
        return Err("far-bank fixed mapping mismatch".into());
    }
    for (ordinal, bank) in spec.bank_mapping.iter().enumerate() {
        if bank.core_ordinal != ordinal || bank.start != work_tree_layout::CORE_OFFSETS[ordinal] {
            return Err("far-bank mapping differs from canonical core offsets".into());
        }
    }
    if spec.input_bits != CORE_INPUT_BITS
        || spec.row_bits != CORE_ROW_BITS
        || spec.slot_bits != SLOT_BITS
    {
        return Err("far-bank dimensions mismatch".into());
    }
    let selected = spec.selected_bank;
    if selected.core_ordinal >= spec.bank_mapping.len()
        || spec.bank_mapping[selected.core_ordinal] != selected
        || selected.physical_index >= BANK_COPY_FACTOR
        || selected.physical_index.checked_mul(BANK_WIDTH) != Some(selected.start)
        || selected.start.checked_add(BANK_WIDTH).is_none_or(|end| end > (1usize << PARENT_OWNER_BITS))
    {
        return Err("far-bank selected address mismatch".into());
    }
    Ok(())
}

fn validate_far_bank(
    core: &SparseCircuit,
    core_digest: &str,
    spec: FarBankSpec,
) -> Result<Shape, String> {
    validate_far_bank_spec(spec)?;
    if core.input_len != BANK_WIDTH
        || core.row_count != CORE_ROWS
        || core.terms.len() != CORE_TERMS
        || core_digest != FAR_BANK_CORE_DIGEST
        || work_tree_layout::hash_terms(&core.terms) != core_digest
        || core.terms.iter().any(|term| {
            term.row >= CORE_ROWS || term.gate.left >= BANK_WIDTH || term.gate.right >= BANK_WIDTH
        })
    {
        return Err("far-bank canonical core identity mismatch".into());
    }
    sparse::validate(core, 0).map_err(|error| error.to_string())
}

fn bind_far_bank_parent_pcs(
    transcript: &mut Transcript,
    core_digest: &str,
    spec: FarBankSpec,
    setup_id: &[u8; 32],
    parent_commitment: &[u8],
) {
    transcript.append_bytes(b"far-bank-projection-relation", b"compression-fixed-bank-selection-v1");
    transcript.append_bytes(b"parent-source-sha256", SOURCE_SHA256.as_bytes());
    transcript.append_bytes(b"far-bank-core-term-digest-blake2b256", core_digest.as_bytes());
    for bank in spec.bank_mapping {
        gkr::append_usize(transcript, b"far-bank-core-ordinal", bank.core_ordinal);
        gkr::append_usize(transcript, b"far-bank-physical-index", bank.physical_index);
        gkr::append_usize(transcript, b"far-bank-source-start", bank.start);
    }
    gkr::append_usize(transcript, b"far-bank-selected-ordinal", spec.selected_bank.core_ordinal);
    gkr::append_usize(transcript, b"far-bank-selected-index", spec.selected_bank.physical_index);
    gkr::append_usize(transcript, b"far-bank-selected-start", spec.selected_bank.start);
    gkr::append_usize(transcript, b"far-bank-width", BANK_WIDTH);
    gkr::append_usize(transcript, b"far-bank-core-input-bits", spec.input_bits);
    gkr::append_usize(transcript, b"far-bank-core-row-bits", spec.row_bits);
    gkr::append_usize(transcript, b"far-bank-owner-bits", spec.slot_bits);
    gkr::append_usize(transcript, b"far-bank-projected-input-bits", FAR_BANK_PROJECTED_INPUT_BITS);
    gkr::append_usize(transcript, b"far-bank-projected-row-bits", FAR_BANK_PROJECTED_ROW_BITS);
    gkr::append_usize(transcript, b"parent-packed-input-bits", PARENT_LOG_N);
    gkr::append_usize(transcript, b"parent-owner-bits", PARENT_OWNER_BITS);
    gkr::append_usize(transcript, b"far-bank-owner-count", OWNER_COUNT);
    transcript.append_bytes(
        b"far-bank-coordinate-recipe",
        b"local-z16, fixed-bank-b4, source-slot-s4; owner-copy=owner*16+physical-index",
    );
    transcript.append_bytes(b"common-parent-setup-id", setup_id);
    transcript.append_bytes(b"common-parent-commitment", parent_commitment);
}

fn far_bank_slot_factor(row_point: &[Fr], left_point: &[Fr], right_point: &[Fr]) -> Fr {
    let row_slots = gkr::eq_weights(&row_point[CORE_ROW_BITS..]);
    let left_slots = gkr::eq_weights(&left_point[CORE_INPUT_BITS..]);
    let right_slots = gkr::eq_weights(&right_point[CORE_INPUT_BITS..]);
    row_slots.iter().zip(left_slots).zip(right_slots)
        .fold(Fr::zero(), |sum, ((row, left), right)| sum + *row * left * right)
}

fn far_bank_wiring(
    core: &SparseCircuit,
    core_shape: &Shape,
    row_point: &[Fr],
    left_point: &[Fr],
    right_point: &[Fr],
) -> Result<[Fr; 4], String> {
    if row_point.len() != FAR_BANK_PROJECTED_ROW_BITS
        || left_point.len() != FAR_BANK_PROJECTED_INPUT_BITS
        || right_point.len() != FAR_BANK_PROJECTED_INPUT_BITS
    {
        return Err("far-bank projected wiring point dimensions".into());
    }
    let mut coefficients = sparse::wiring(
        core,
        core_shape,
        &row_point[..CORE_ROW_BITS],
        &left_point[..CORE_INPUT_BITS],
        &right_point[..CORE_INPUT_BITS],
    ).map_err(|error| error.to_string())?;
    let owner_factor = far_bank_slot_factor(row_point, left_point, right_point);
    for coefficient in &mut coefficients {
        *coefficient *= owner_factor;
    }
    Ok(coefficients)
}

// Independent coefficient oracle expands owner coordinates in the global
// 20/21-bit namespaces and scans the canonical terms directly.
fn far_bank_streamed_global_oracle(
    core: &SparseCircuit,
    row_point: &[Fr],
    left_point: &[Fr],
    right_point: &[Fr],
) -> [Fr; 4] {
    let row_weights = gkr::eq_weights(row_point);
    let left_weights = gkr::eq_weights(left_point);
    let right_weights = gkr::eq_weights(right_point);
    let mut coefficients = [Fr::zero(); 4];
    for owner in 0..OWNER_COUNT {
        let row_offset = owner << CORE_ROW_BITS;
        let input_offset = owner << CORE_INPUT_BITS;
        for term in &core.terms {
            let weight = row_weights[row_offset + term.row]
                * left_weights[input_offset + term.gate.left]
                * right_weights[input_offset + term.gate.right];
            coefficients[0] += weight * term.gate.c0;
            coefficients[1] += weight * term.gate.c1;
            coefficients[2] += weight * term.gate.c2;
            coefficients[3] += weight * term.gate.c3;
        }
    }
    coefficients
}

fn far_bank_parent_point(spec: FarBankSpec, projected: &[Fr]) -> Result<Vec<Fr>, String> {
    validate_far_bank_spec(spec)?;
    if projected.len() != FAR_BANK_PROJECTED_INPUT_BITS {
        return Err("far-bank projected claim point dimension mismatch".into());
    }
    work_tree_layout::embed_bank(spec.selected_bank.start, BANK_WIDTH, SLOT_BITS, projected)
}

fn prove_far_bank_projection(
    core: &SparseCircuit,
    core_digest: &str,
    spec: FarBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    visit_terms: impl FnMut(usize, &mut dyn FnMut(Term) -> Result<(), String>) -> Result<(), String>,
    transcript: &mut Transcript,
    bind_calls: &mut usize,
) -> Result<(GkrProof, InputClaim), String> {
    validate_far_bank(core, core_digest, spec)?;
    let core_shape = sparse::validate(core, 0).map_err(|error| error.to_string())?;
    sparse_stream_roster::prove(
        spec.input_bits,
        spec.slot_bits,
        spec.row_bits,
        0,
        &[spec.row_bits],
        load_copy,
        transcript,
        |transcript| {
            *bind_calls += 1;
            bind_far_bank_parent_pcs(transcript, core_digest, spec, setup_id, commitment_bytes);
        },
        visit_terms,
        |row, left, right| far_bank_wiring(core, &core_shape, row, left, right),
    )
}

fn verify_far_bank_projection(
    core: &SparseCircuit,
    core_digest: &str,
    spec: FarBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    proof: &GkrProof,
    transcript: &mut Transcript,
    bind_calls: &mut usize,
) -> Result<InputClaim, GkrError> {
    if validate_far_bank(core, core_digest, spec).is_err() {
        return Err(GkrError::PointDimension);
    }
    let core_shape = sparse::validate(core, 0).map_err(|_| GkrError::PointDimension)?;
    gkr::verify_with_wiring(
        &[FAR_BANK_PROJECTED_INPUT_BITS],
        1usize << FAR_BANK_PROJECTED_ROW_BITS,
        proof,
        transcript,
        |transcript| {
            *bind_calls += 1;
            bind_far_bank_parent_pcs(transcript, core_digest, spec, setup_id, commitment_bytes);
        },
        |layer, row, left, right| {
            if layer != 0 { return Err(GkrError::PointDimension); }
            far_bank_wiring(core, &core_shape, row, left, right)
                .map_err(|_| GkrError::PointDimension)
        },
    )
}

fn load_far_bank_with(
    owner: usize,
    physical_index: usize,
    read_copy: impl FnOnce(usize) -> Result<Vec<Fr>, String>,
) -> Result<Vec<Fr>, String> {
    if owner >= OWNER_COUNT { return Err("far-bank owner index out of range".into()); }
    if physical_index >= BANK_COPY_FACTOR { return Err("far-bank physical index out of range".into()); }
    let copy = owner.checked_mul(BANK_COPY_FACTOR)
        .and_then(|base| base.checked_add(physical_index))
        .ok_or("far-bank physical copy overflow")?;
    let values = read_copy(copy)?;
    if values.len() != BANK_WIDTH { return Err("far-bank read width mismatch".into()); }
    Ok(values)
}

fn load_far_bank_owner(parent: &PackedFile, owner: usize, physical_index: usize) -> Result<Vec<Fr>, String> {
    load_far_bank_with(owner, physical_index, |copy| {
        parent.read_copy(BANK_WIDTH, copy).map_err(|error| error.to_string())
    })
}

struct FarBankNegative {
    rejected_by: &'static str,
    error: String,
    gkr_verify_calls: usize,
    pcs_verify_calls: usize,
    bind_calls: usize,
    challenge_count: u64,
}

fn far_bank_negative_json(evidence: &FarBankNegative) -> serde_json::Value {
    json!({
        "rejected_by": evidence.rejected_by,
        "error": evidence.error,
        "gkr_verify_calls": evidence.gkr_verify_calls,
        "pcs_verify_calls": evidence.pcs_verify_calls,
        "bind_calls": evidence.bind_calls,
        "challenge_count": evidence.challenge_count,
    })
}

fn far_bank_prefix_negative(
    core: &SparseCircuit,
    core_digest: &str,
    spec: FarBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    proof: &GkrProof,
) -> FarBankNegative {
    let mut transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
    let mut bind_calls = 0usize;
    let mut gkr_verify_calls = 1usize;
    let result = verify_far_bank_projection(
        core, core_digest, spec, setup_id, commitment_bytes, proof, &mut transcript, &mut bind_calls,
    );
    let error = match result {
        Err(error) => error.to_string(),
        Ok(_) => "far-bank GKR verifier unexpectedly accepted mutant".into(),
    };
    FarBankNegative {
        rejected_by: "fresh_gkr_verifier",
        error,
        gkr_verify_calls,
        pcs_verify_calls: 0,
        bind_calls,
        challenge_count: transcript.challenges(),
    }
}

fn far_bank_pcs_negative(
    core: &SparseCircuit,
    core_digest: &str,
    spec: FarBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    proof: &GkrProof,
    commitment: &ArkGT,
    opening: &dory_pcs::backends::arkworks::ArkDoryProof,
    key: &crate::verifier_key::AdmittedVerifierKey,
    wrong_point: bool,
) -> FarBankNegative {
    let mut transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
    let mut bind_calls = 0usize;
    let claim = match verify_far_bank_projection(
        core, core_digest, spec, setup_id, commitment_bytes, proof, &mut transcript, &mut bind_calls,
    ) {
        Ok(claim) => claim,
        Err(error) => return FarBankNegative {
            rejected_by: "fresh_gkr_verifier",
            error: error.to_string(),
            gkr_verify_calls: 1,
            pcs_verify_calls: 0,
            bind_calls,
            challenge_count: transcript.challenges(),
        },
    };
    let mut parent_point = far_bank_parent_point(spec, &claim.point)
        .expect("fresh far-bank claim embeds into W24 parent coordinates");
    let value = if wrong_point {
        parent_point[CORE_INPUT_BITS + 1] += Fr::one();
        claim.value
    } else {
        claim.value + Fr::one()
    };
    let result = crate::pcs::verify_admitted(
        commitment.clone(), value, &parent_point, opening, key, &mut transcript,
    );
    FarBankNegative {
        rejected_by: "pcs_consumer",
        error: result.err().unwrap_or_else(|| "PCS accepted the isolated mutant".into()),
        gkr_verify_calls: 1,
        pcs_verify_calls: 1,
        bind_calls,
        challenge_count: transcript.challenges(),
    }
}

fn assert_far_bank_rejects_before_callbacks(
    core: &SparseCircuit,
    core_digest: &str,
    spec: FarBankSpec,
) {
    let mut loader_calls = 0usize;
    let mut visitor_calls = 0usize;
    let mut bind_calls = 0usize;
    let mut transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
    let result = prove_far_bank_projection(
        core, core_digest, spec, &[0u8; 32], b"mapping-fixture-commitment",
        |_| { loader_calls += 1; Err("loader must not run for invalid mapping".into()) },
        |_, _| { visitor_calls += 1; Ok(()) },
        &mut transcript, &mut bind_calls,
    );
    assert!(result.is_err());
    assert_eq!((loader_calls, visitor_calls, bind_calls, transcript.challenges()), (0, 0, 0, 0));
}

#[test]
fn all_11_fixed_core_bank_mappings_and_far_wiring_reject_invalid_mappings() {
    let (core, _, core_digest) = canonical_core();
    assert_eq!(core_digest, FAR_BANK_CORE_DIGEST);
    let shape = validate_far_bank(&core, &core_digest, FAR_BANK_SPEC).unwrap();
    assert_eq!((shape.input_bits, shape.row_bits, shape.copies), (CORE_INPUT_BITS, CORE_ROW_BITS, 1));
    assert_eq!(FAR_BANK_MAPPING.map(|entry| entry.core_ordinal), [0,1,2,3,4,5,6,7,8,9,10]);
    assert_eq!(FAR_BANK_MAPPING.map(|entry| entry.physical_index), [0,1,2,3,4,5,6,7,11,13,14]);
    assert_eq!(FAR_BANK_MAPPING.map(|entry| entry.start), [0,65_536,131_072,196_608,262_144,327_680,393_216,458_752,720_896,851_968,917_504]);
    assert_eq!(FAR_BANK_MAPPING.map(|entry| entry.start), work_tree_layout::CORE_OFFSETS);
    assert_eq!(FAR_BANK_SPEC.selected_bank, FAR_BANK_MAPPING[10]);

    for address in FAR_BANK_MAPPING {
        for owner in [0usize, OWNER_COUNT - 1] {
            for local in [0usize, BANK_WIDTH - 1] {
                let projected = bool_point(FAR_BANK_PROJECTED_INPUT_BITS, local | (owner << CORE_INPUT_BITS));
                let parent_point = far_bank_parent_point(
                    FarBankSpec { selected_bank: address, ..FAR_BANK_SPEC }, &projected,
                ).unwrap();
                let expected_index = (owner << PARENT_OWNER_BITS) + address.start + local;
                assert_eq!(parent_point, bool_point(PARENT_LOG_N, expected_index));
            }
        }
    }
    for hole in [8usize, 9, 10, 12, 15] {
        assert!(validate_far_bank(
            &core, &core_digest,
            FarBankSpec { selected_bank: FarBankAddress { core_ordinal: 0, physical_index: hole, start: hole * BANK_WIDTH }, ..FAR_BANK_SPEC },
        ).is_err());
    }
    assert!(far_bank_parent_point(FAR_BANK_SPEC, &vec![Fr::zero(); FAR_BANK_PROJECTED_INPUT_BITS - 1]).is_err());
    let all_zero_point = vec![Fr::zero(); FAR_BANK_PROJECTED_INPUT_BITS];
    let mut bad_embedding_mapping = FAR_BANK_SPEC;
    bad_embedding_mapping.bank_mapping[10].physical_index = 15;
    assert!(far_bank_parent_point(bad_embedding_mapping, &all_zero_point).is_err());
    let mut bad_embedding_dimensions = FAR_BANK_SPEC;
    bad_embedding_dimensions.slot_bits += 1;
    assert!(far_bank_parent_point(bad_embedding_dimensions, &all_zero_point).is_err());
    let bad_embedding_address = FarBankSpec {
        selected_bank: FarBankAddress { core_ordinal: 10, physical_index: usize::MAX, start: usize::MAX },
        ..FAR_BANK_SPEC
    };
    assert!(far_bank_parent_point(bad_embedding_address, &all_zero_point).is_err());

    let bad_specs = [
        FarBankSpec { selected_bank: FarBankAddress { core_ordinal: 11, physical_index: 15, start: 983_040 }, ..FAR_BANK_SPEC },
        FarBankSpec { selected_bank: FarBankAddress { start: 917_505, ..FAR_BANK_SPEC.selected_bank }, ..FAR_BANK_SPEC },
        FarBankSpec { selected_bank: FarBankAddress { physical_index: 13, ..FAR_BANK_SPEC.selected_bank }, ..FAR_BANK_SPEC },
        FarBankSpec { input_bits: CORE_INPUT_BITS - 1, ..FAR_BANK_SPEC },
        FarBankSpec { row_bits: CORE_ROW_BITS - 1, ..FAR_BANK_SPEC },
        FarBankSpec { slot_bits: SLOT_BITS - 1, ..FAR_BANK_SPEC },
        FarBankSpec { bank_mapping: { let mut map = FAR_BANK_MAPPING; map[10].start += 1; map }, ..FAR_BANK_SPEC },
    ];
    for spec in bad_specs { assert_far_bank_rejects_before_callbacks(&core, &core_digest, spec); }
    for hole in [8usize, 9, 10, 12, 15] {
        assert_far_bank_rejects_before_callbacks(
            &core, &core_digest,
            FarBankSpec { selected_bank: FarBankAddress { core_ordinal: 0, physical_index: hole, start: hole * BANK_WIDTH }, ..FAR_BANK_SPEC },
        );
    }
    assert_far_bank_rejects_before_callbacks(&core, "wrong-core-digest", FAR_BANK_SPEC);

    let mut read_calls = 0usize;
    let owner_error = load_far_bank_with(OWNER_COUNT, 14, |_| {
        read_calls += 1;
        Ok(vec![Fr::zero(); BANK_WIDTH])
    }).unwrap_err();
    assert_eq!(owner_error, "far-bank owner index out of range");
    assert_eq!(read_calls, 0, "owner16 fails before physical read callback");
    let physical_error = load_far_bank_with(0, BANK_COPY_FACTOR, |_| {
        read_calls += 1;
        Ok(vec![Fr::zero(); BANK_WIDTH])
    }).unwrap_err();
    assert_eq!(physical_error, "far-bank physical index out of range");
    assert_eq!(read_calls, 0, "invalid physical bank fails before read callback");
    let wrong_width = load_far_bank_with(0, 14, |_| {
        read_calls += 1;
        Ok(vec![Fr::zero(); BANK_WIDTH - 1])
    }).unwrap_err();
    assert_eq!(wrong_width, "far-bank read width mismatch");
    assert_eq!(read_calls, 1);
    for (owner, expected_copy) in [(0usize, 14usize), (OWNER_COUNT - 1, 254usize)] {
        let mut observed_copy = None;
        let values = load_far_bank_with(owner, 14, |copy| {
            observed_copy = Some(copy);
            Ok(vec![Fr::zero(); BANK_WIDTH])
        }).unwrap();
        assert_eq!(observed_copy, Some(expected_copy));
        assert_eq!(values.len(), BANK_WIDTH);
    }

    let row_point: Vec<_> = (0..FAR_BANK_PROJECTED_ROW_BITS).map(|i| Fr::from((i + 3) as u64)).collect();
    let left_point: Vec<_> = (0..FAR_BANK_PROJECTED_INPUT_BITS).map(|i| Fr::from((i + 29) as u64)).collect();
    let right_point: Vec<_> = (0..FAR_BANK_PROJECTED_INPUT_BITS).map(|i| Fr::from((i + 71) as u64)).collect();
    let projected = far_bank_wiring(&core, &shape, &row_point, &left_point, &right_point).unwrap();
    let streamed = far_bank_streamed_global_oracle(&core, &row_point, &left_point, &right_point);
    assert_eq!(projected, streamed, "all four coefficients match the independent 16-owner streamed oracle");
    let mixed_row: Vec<_> = (0..CORE_ROW_BITS).map(|i| Fr::from((i + 103) as u64))
        .chain([0u64, 1, 2, 5].into_iter().map(Fr::from)).collect();
    let mixed_left: Vec<_> = (0..CORE_INPUT_BITS).map(|i| Fr::from((i + 211) as u64))
        .chain([2u64, 1, 5, 0].into_iter().map(Fr::from)).collect();
    let mixed_right: Vec<_> = (0..CORE_INPUT_BITS).map(|i| Fr::from((i + 307) as u64))
        .chain([0u64, 3, 7, 9].into_iter().map(Fr::from)).collect();
    assert!(!far_bank_slot_factor(&mixed_row, &mixed_left, &mixed_right).is_zero());
    assert_eq!(
        far_bank_wiring(&core, &shape, &mixed_row, &mixed_left, &mixed_right).unwrap(),
        far_bank_streamed_global_oracle(&core, &mixed_row, &mixed_left, &mixed_right),
        "mixed Boolean/non-Boolean owner point retains a nonzero factor",
    );
    assert!(far_bank_wiring(&core, &shape, &row_point[..row_point.len()-1], &left_point, &right_point).is_err());
    assert!(far_bank_wiring(&core, &shape, &row_point, &left_point[..left_point.len()-1], &right_point).is_err());
    assert!(far_bank_wiring(&core, &shape, &row_point, &left_point, &right_point[..right_point.len()-1]).is_err());

    let mut mutated_core = core.clone();
    let saved = mutated_core.terms[0].clone();
    for mutation in 0..7 {
        let term = &mut mutated_core.terms[0];
        match mutation {
            0 => term.row += 1,
            1 => term.gate.left += 1,
            2 => term.gate.right += 1,
            3 => term.gate.c0 += Fr::one(),
            4 => term.gate.c1 += Fr::one(),
            5 => term.gate.c2 += Fr::one(),
            6 => term.gate.c3 += Fr::one(),
            _ => unreachable!(),
        }
        assert_far_bank_rejects_before_callbacks(&mutated_core, &core_digest, FAR_BANK_SPEC);
        mutated_core.terms[0] = saved.clone();
    }
    let last_term = mutated_core.terms.pop().unwrap();
    assert_far_bank_rejects_before_callbacks(&mutated_core, &core_digest, FAR_BANK_SPEC);
    mutated_core.terms.push(last_term);
    mutated_core.input_len += 1;
    assert_far_bank_rejects_before_callbacks(&mutated_core, &core_digest, FAR_BANK_SPEC);
    mutated_core.input_len -= 1;
    mutated_core.row_count += 1;
    assert_far_bank_rejects_before_callbacks(&mutated_core, &core_digest, FAR_BANK_SPEC);
}

#[test]
fn native_window16_far_bank14_gkr_claim_authenticates_original_parent_commitment_pcs24() {
    let whole_started = Instant::now();
    let (core, core_layout, core_digest) = canonical_core();
    validate_far_bank(&core, &core_digest, FAR_BANK_SPEC).unwrap();
    let artifact_directory = std::env::var(FAR_BANK_ARTIFACT_DIR_ENV)
        .expect("runner pins NIPOPOW_FAR_BANK_ARTIFACT_DIR");
    assert_eq!(fs::read_dir(&artifact_directory).unwrap().count(), 0, "fresh output directory");
    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE")
        .expect("runner pins original Window16 source");
    assert_eq!(fs::metadata(&source_path).unwrap().len(), SOURCE_BYTES);
    let parent = PackedFile::open(&source_path, PARENT_LOG_N).expect("open pinned Window16");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    let source_open_io = parent.io_metrics_snapshot();
    assert_eq!((source_open_io.read_calls, source_open_io.read_bytes, source_open_io.read_ns), (0, 0, 0));

    let reference_directory = std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV)
        .expect("runner pins original common-PCS identity artifacts");
    let reference_path = |name: &str| std::path::Path::new(&reference_directory).join(name);
    let reference_commitment_bytes = fs::read(reference_path(COMMON_PCS_COMMITMENT_FILE))
        .expect("read frozen C1 parent commitment");
    let reference_key_bytes = fs::read(reference_path(COMMON_PCS_KEY_FILE))
        .expect("read frozen C1 TEST24 key");
    let reference_result_bytes = fs::read(reference_path(COMMON_PCS_RESULT_FILE))
        .expect("read frozen C1 structured result");
    let reference_result: serde_json::Value = serde_json::from_slice(&reference_result_bytes)
        .expect("decode frozen C1 result");
    assert_eq!(reference_result["schema"].as_str(), Some("native-core-bank-projection-pcs-v1"));
    assert_eq!(reference_result["test"].as_str(), Some("native_window16_bank0_gkr_claim_authenticates_original_parent_commitment_pcs24"));
    assert_eq!(reference_result["source"]["sha256"].as_str(), Some(SOURCE_SHA256));
    assert_eq!(reference_result["source"]["bytes"].as_u64(), Some(SOURCE_BYTES));
    assert_eq!(reference_result["setup"]["log_n"].as_u64(), Some(PARENT_LOG_N as u64));
    assert_eq!(reference_result["dory"]["verified_with_generated_test_key"].as_bool(), Some(true));

    let setup_started = Instant::now();
    let setup = crate::pcs::generate_setup(PARENT_LOG_N).expect("reconstruct original diagnostic setup24");
    let setup_reconstruction_ms = setup_started.elapsed().as_millis();
    let setup_id = setup.id;
    let setup_id_hex = hex_bytes(&setup_id);
    assert_eq!(setup_id_hex, reference_result["setup"]["id_hex"].as_str().unwrap());
    assert_eq!(setup_id_hex, "b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe");
    let key_encode_started = Instant::now();
    let verifier_key_bytes = crate::pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))
        .expect("serialize original diagnostic verifier key");
    let verifier_key_encode_ms = key_encode_started.elapsed().as_millis();
    assert_eq!(verifier_key_bytes, reference_key_bytes, "original verifier key byte identity");
    let verifier_key_hash = work_tree_layout::hash_bytes(&verifier_key_bytes);
    assert_eq!(verifier_key_hash, reference_result["setup"]["verifier_key_blake2b256"].as_str().unwrap());
    let public_admit_started = Instant::now();
    let public_admit_24_error = match crate::verifier_key::admit(PARENT_LOG_N, &verifier_key_bytes) {
        Err(error) => error,
        Ok(_) => panic!("public TEST24 admission unexpectedly accepted"),
    };
    let public_admit_24_reject_ms = public_admit_started.elapsed().as_millis();
    assert_eq!(public_admit_24_error, "unsupported verifier-key dimension");

    parent.reset_io_metrics();
    let commitment_started = Instant::now();
    let committed = crate::packed::commit(&parent, &setup).expect("reconstruct original parent commitment");
    let commitment_reconstruction_ms = commitment_started.elapsed().as_millis();
    let commitment_io = parent.io_metrics_snapshot();
    assert_eq!((commitment_io.read_calls, commitment_io.read_bytes), (1, SOURCE_BYTES));
    let commitment_bytes = crate::pcs::encode_commitment(&committed.commitment)
        .expect("encode reconstructed parent commitment");
    assert_eq!(commitment_bytes.len(), 384);
    assert_eq!(commitment_bytes, reference_commitment_bytes);
    let commitment_blake2b256 = work_tree_layout::hash_bytes(&commitment_bytes);
    assert_eq!(commitment_blake2b256, reference_result["commitment"]["blake2b256"].as_str().unwrap());
    let parent_commitment = crate::pcs::decode_commitment(&commitment_bytes)
        .expect("decode original parent commitment");
    assert_eq!(crate::pcs::encode_commitment(&parent_commitment).unwrap(), commitment_bytes);
    let alternate_commitment = ArkGT(parent_commitment.0.clone() + setup.prover.ht.0.clone());
    assert_ne!(alternate_commitment, parent_commitment);
    let alternate_commitment_bytes = crate::pcs::encode_commitment(&alternate_commitment)
        .expect("encode alternate valid GT commitment");
    assert_eq!(crate::pcs::decode_commitment(&alternate_commitment_bytes).unwrap(), alternate_commitment);

    let mutation_wire = core_layout.output[0][0];
    assert!(mutation_wire < BANK_WIDTH);
    let mut mutation_transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
    let mut mutation_bind_calls = 0usize;
    let mut mutation_loader_calls = 0usize;
    let mut mutation_visitor_calls = 0usize;
    let mutation_result = prove_far_bank_projection(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        |owner| {
            mutation_loader_calls += 1;
            let mut values = load_far_bank_owner(&parent, owner, FAR_BANK_SPEC.selected_bank.physical_index)?;
            if owner == 0 {
                let cell = &mut values[mutation_wire];
                assert!(*cell == Fr::zero() || *cell == Fr::one());
                *cell = Fr::one() - *cell;
            }
            Ok(values)
        },
        |_, sink| { mutation_visitor_calls += 1; for term in &core.terms { sink(term.clone())?; } Ok(()) },
        &mut mutation_transcript, &mut mutation_bind_calls,
    );
    let mutation_error = mutation_result.err().expect("mutated selected output rejects before GKR binding");
    assert_eq!(mutation_error, "GKR error: NonzeroOutput");
    assert!(mutation_loader_calls > 0 && mutation_visitor_calls > 0);
    assert_eq!((mutation_bind_calls, mutation_transcript.challenges()), (0, 0));

    parent.reset_io_metrics();
    let mut prover_transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
    let mut load_calls = 0usize;
    let mut term_visit_passes_by_owner = vec![0usize; OWNER_COUNT];
    let mut term_sink_calls = 0usize;
    let mut producer_bind_calls = 0usize;
    let producer_started = Instant::now();
    let (proof, claim) = prove_far_bank_projection(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        |owner| { load_calls += 1; load_far_bank_owner(&parent, owner, FAR_BANK_SPEC.selected_bank.physical_index) },
        |owner, sink| {
            if owner >= OWNER_COUNT { return Err("far-bank owner index out of range".into()); }
            term_visit_passes_by_owner[owner] += 1;
            for term in &core.terms { term_sink_calls += 1; sink(term.clone())?; }
            Ok(())
        },
        &mut prover_transcript, &mut producer_bind_calls,
    ).expect("prove selected bank14 relation with unchanged default cache");
    let producer_gkr_ms = producer_started.elapsed().as_millis();
    assert_eq!(producer_bind_calls, 1);
    let term_visit_passes: usize = term_visit_passes_by_owner.iter().sum();
    let term_passes_per_owner = term_visit_passes_by_owner[0];
    assert!(term_passes_per_owner > 0);
    assert!(term_visit_passes_by_owner.iter().all(|passes| *passes == term_passes_per_owner));
    assert_eq!(term_sink_calls, CORE_TERMS * term_visit_passes);
    let producer_io = parent.io_metrics_snapshot();
    assert_eq!(producer_io.read_calls, load_calls as u64);
    assert_eq!(producer_io.read_bytes, (load_calls * (BANK_WIDTH / 8)) as u64);
    assert_eq!(producer_io.read_bytes, load_calls as u64 * 8_192);
    let encoded_proof = gkr::encode_proof(&proof).expect("encode selected-bank GKR proof");
    assert_eq!(encoded_proof.len(), FAR_BANK_PROOF_BYTES);
    let prover_post_gkr = prover_transcript.clone();
    let parent_point = far_bank_parent_point(FAR_BANK_SPEC, &claim.point)
        .expect("embed producer claim in original W24 coordinates");
    assert_eq!(claim.point.len(), FAR_BANK_PROJECTED_INPUT_BITS);
    assert_eq!(parent_point.len(), PARENT_LOG_N);
    assert_eq!(&parent_point[16..20], &[Fr::zero(), Fr::one(), Fr::one(), Fr::one()]);

    parent.reset_io_metrics();
    let parent_mle_started = Instant::now();
    let parent_mle_value = parent.evaluate(&parent_point).expect("evaluate original parent MLE");
    let parent_mle_ms = parent_mle_started.elapsed().as_millis();
    let parent_mle_io = parent.io_metrics_snapshot();
    assert_eq!((parent_mle_io.read_calls, parent_mle_io.read_bytes), (1, SOURCE_BYTES));
    assert_eq!(parent_mle_value, claim.value);
    parent.reset_io_metrics();
    let opening_started = Instant::now();
    let opening = crate::packed::open(&committed, &parent, &parent_point, &setup, &mut prover_transcript)
        .expect("create new Dory opening at selected far-bank parent point");
    let open_dory_ms = opening_started.elapsed().as_millis();
    let opening_io = parent.io_metrics_snapshot();
    assert_eq!((opening_io.read_calls, opening_io.read_bytes), (2, SOURCE_BYTES * 2));
    let encoded_opening = crate::pcs::encode_proof(&opening).expect("encode Dory opening");
    assert_eq!(encoded_opening.len(), FAR_BANK_OPENING_BYTES);
    drop(committed);
    drop(setup);

    let decoded_opening = crate::pcs::decode_proof(&encoded_opening, PARENT_LOG_N)
        .expect("freshly decode Dory opening after dropping prover setup");
    assert_eq!(crate::pcs::encode_proof(&decoded_opening).unwrap(), encoded_opening);
    let key_admit_started = Instant::now();
    let verifier_key = crate::verifier_key::admit_generated_test_key(
        PARENT_LOG_N, &reference_key_bytes, setup_id,
    ).expect("decode original stored TEST24 key after dropping setup");
    let verifier_key_decode_admit_ms = key_admit_started.elapsed().as_millis();
    assert_eq!(verifier_key.id(), &setup_id);
    let proof_decode_started = Instant::now();
    let decoded_proof = gkr::decode_dimensions(&[FAR_BANK_PROJECTED_INPUT_BITS], &encoded_proof)
        .expect("freshly decode exact 20-dimensional GKR proof");
    let proof_decode_ms = proof_decode_started.elapsed().as_millis();
    assert_eq!(decoded_proof, proof);
    let mut verifier_transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
    let mut verifier_bind_calls = 0usize;
    parent.reset_io_metrics();
    let fresh_gkr_started = Instant::now();
    let verified_claim = verify_far_bank_projection(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        &decoded_proof, &mut verifier_transcript, &mut verifier_bind_calls,
    ).expect("fresh GKR verification after dropping setup");
    let fresh_gkr_verify_ms = fresh_gkr_started.elapsed().as_millis();
    let fresh_gkr_io = parent.io_metrics_snapshot();
    assert_eq!((fresh_gkr_io.read_calls, fresh_gkr_io.read_bytes, fresh_gkr_io.read_ns), (0, 0, 0));
    assert_eq!(verifier_bind_calls, 1);
    assert_eq!(claim, verified_claim);
    assert_eq!(prover_post_gkr.challenges(), verifier_transcript.challenges());
    assert_eq!(prover_post_gkr.raw_queries(), verifier_transcript.raw_queries());
    assert_eq!(prover_post_gkr.bytes_absorbed(), verifier_transcript.bytes_absorbed());
    assert_eq!(far_bank_parent_point(FAR_BANK_SPEC, &verified_claim.point).unwrap(), parent_point);
    let mut prover_continuation = prover_post_gkr.clone();
    let mut verifier_continuation = verifier_transcript.clone();
    let transcript_continuation_matches = prover_continuation.challenge_scalar(b"far-bank-post-gkr")
        == verifier_continuation.challenge_scalar(b"far-bank-post-gkr")
        && prover_continuation.challenges() == verifier_continuation.challenges()
        && prover_continuation.raw_queries() == verifier_continuation.raw_queries()
        && prover_continuation.bytes_absorbed() == verifier_continuation.bytes_absorbed();
    assert!(transcript_continuation_matches);
    let mut trailing_proof = encoded_proof.clone();
    trailing_proof.push(0);
    let trailing_error = gkr::decode_dimensions(&[FAR_BANK_PROJECTED_INPUT_BITS], &trailing_proof)
        .expect_err("GKR codec rejects isolated trailing byte");
    assert_eq!(trailing_error, "GKR proof length: expected 4576, received 4577");

    parent.reset_io_metrics();
    let fresh_pcs_started = Instant::now();
    crate::pcs::verify_admitted(
        parent_commitment.clone(), verified_claim.value, &parent_point, &decoded_opening,
        &verifier_key, &mut verifier_transcript.clone(),
    ).expect("fresh original TEST24 key verifies selected-bank parent opening");
    let fresh_pcs_verify_ms = fresh_pcs_started.elapsed().as_millis();
    let fresh_pcs_io = parent.io_metrics_snapshot();
    assert_eq!((fresh_pcs_io.read_calls, fresh_pcs_io.read_bytes, fresh_pcs_io.read_ns), (0, 0, 0));

    let mut wrong_setup = setup_id;
    wrong_setup[0] ^= 1;
    let setup_negative = far_bank_prefix_negative(&core, &core_digest, FAR_BANK_SPEC, &wrong_setup, &commitment_bytes, &decoded_proof);
    let commitment_negative = far_bank_prefix_negative(&core, &core_digest, FAR_BANK_SPEC, &setup_id, &alternate_commitment_bytes, &decoded_proof);
    let wrong_bank = FarBankSpec { selected_bank: FAR_BANK_MAPPING[9], ..FAR_BANK_SPEC };
    let wrong_selection_negative = far_bank_prefix_negative(&core, &core_digest, wrong_bank, &setup_id, &commitment_bytes, &decoded_proof);
    let wrong_point_negative = far_bank_pcs_negative(&core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        &decoded_proof, &parent_commitment, &decoded_opening, &verifier_key, true);
    let wrong_value_negative = far_bank_pcs_negative(&core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        &decoded_proof, &parent_commitment, &decoded_opening, &verifier_key, false);
    for negative in [&setup_negative, &commitment_negative, &wrong_selection_negative] {
        assert_eq!(negative.rejected_by, "fresh_gkr_verifier");
        assert_eq!(negative.error, "GKR error: SumcheckIdentity");
        assert_eq!((negative.gkr_verify_calls, negative.pcs_verify_calls, negative.bind_calls), (1, 0, 1));
        assert!(negative.challenge_count > 0);
    }
    for negative in [&wrong_point_negative, &wrong_value_negative] {
        assert_eq!(negative.rejected_by, "pcs_consumer");
        assert_eq!(negative.error, "Invalid proof");
        assert_eq!((negative.gkr_verify_calls, negative.pcs_verify_calls, negative.bind_calls), (1, 1, 1));
        assert!(negative.challenge_count > 0);
    }
    let selected_output_negative = FarBankNegative {
        rejected_by: "residual_guard",
        error: mutation_error,
        gkr_verify_calls: 0,
        pcs_verify_calls: 0,
        bind_calls: mutation_bind_calls,
        challenge_count: mutation_transcript.challenges(),
    };
    assert_eq!(selected_output_negative.error, "GKR error: NonzeroOutput");
    assert_eq!((selected_output_negative.bind_calls, selected_output_negative.challenge_count), (0, 0));
    let trailing_negative = FarBankNegative {
        rejected_by: "gkr_codec",
        error: trailing_error,
        gkr_verify_calls: 0,
        pcs_verify_calls: 0,
        bind_calls: 0,
        challenge_count: 0,
    };

    let proof_point_hex = two_bank_hex_point(&verified_claim.point);
    let embedded_parent_point_hex = two_bank_hex_point(&parent_point);
    let claim_value_hex = hex_bytes(&crate::pcs::encode(&verified_claim.value).unwrap());
    let parent_mle_value_hex = hex_bytes(&crate::pcs::encode(&parent_mle_value).unwrap());
    let proof_blake2b256 = work_tree_layout::hash_bytes(&encoded_proof);
    let opening_blake2b256 = work_tree_layout::hash_bytes(&encoded_opening);
    let total_before_result_write_ms = whole_started.elapsed().as_millis();
    let bank_mapping: Vec<_> = FAR_BANK_MAPPING.iter().map(|entry| json!({
        "core_ordinal": entry.core_ordinal,
        "start": entry.start,
        "physical_index": entry.physical_index,
    })).collect();
    write_new_pcs_artifact(&artifact_directory, FAR_BANK_GKR_FILE, &encoded_proof);
    write_new_pcs_artifact(&artifact_directory, FAR_BANK_OPENING_FILE, &encoded_opening);
    let result = json!({
        "schema": "native-far-bank-common-pcs-v1",
        "test": "native_window16_far_bank14_gkr_claim_authenticates_original_parent_commitment_pcs24",
        "scope": "one native Window16 far-bank14 GKR claim authenticated to the original parent commitment with a reconstructed diagnostic setup and original TEST24 verifier key; bounded diagnostic only",
        "source": {
            "sha256": SOURCE_SHA256,
            "bytes": SOURCE_BYTES,
            "bits": SOURCE_BITS,
            "parent_log_n": PARENT_LOG_N,
            "owner_count": OWNER_COUNT,
            "parent_owner_bits": PARENT_OWNER_BITS,
        },
        "relation": {
            "bank_width": BANK_WIDTH,
            "core_input_bits": CORE_INPUT_BITS,
            "core_row_bits": CORE_ROW_BITS,
            "core_terms": CORE_TERMS,
            "core_term_digest_blake2b256": core_digest,
            "slot_bits": SLOT_BITS,
            "projected_input_bits": FAR_BANK_PROJECTED_INPUT_BITS,
            "projected_row_bits": FAR_BANK_PROJECTED_ROW_BITS,
            "parent_point_bits": PARENT_LOG_N,
            "source_read_width": BANK_WIDTH,
            "copies_per_owner": BANK_COPY_FACTOR,
            "wiring_recipe": "core_wiring(r[..17],u[..16],v[..16])*product(j=0..3,triple_eq(r[17+j],u[16+j],v[16+j])); triple_eq(a,b,c)=(1-a)*(1-b)*(1-c)+a*b*c",
            "bank_mapping": bank_mapping,
            "selected_bank": {
                "core_ordinal": FAR_BANK_SPEC.selected_bank.core_ordinal,
                "start": FAR_BANK_SPEC.selected_bank.start,
                "physical_index": FAR_BANK_SPEC.selected_bank.physical_index,
            },
            "owner_bits": SLOT_BITS,
            "parent_fixed_coordinates": [16,17,18,19],
            "parent_fixed_coordinate_bits": [0,1,1,1],
        },
        "identity": {
            "input_receipt_sha256": CACHE_REFERENCE_INPUTS_SHA256,
            "setup_id_hex": setup_id_hex,
            "setup_id_matches_reference": true,
            "verifier_key_file": COMMON_PCS_KEY_FILE,
            "verifier_key_bytes": verifier_key_bytes.len(),
            "verifier_key_blake2b256": verifier_key_hash,
            "verifier_key_matches_reference": verifier_key_bytes == reference_key_bytes,
            "commitment_file": COMMON_PCS_COMMITMENT_FILE,
            "commitment_bytes": commitment_bytes.len(),
            "commitment_blake2b256": commitment_blake2b256,
            "commitment_matches_reference": commitment_bytes == reference_commitment_bytes,
            "public_admit_24_rejected": true,
            "public_admit_24_error": public_admit_24_error,
        },
        "producer": {
            "cache_budget_bytes": sparse_stream_roster::MAX_INCREMENTAL_CACHE_STATE_BYTES,
            "load_calls": load_calls,
            "term_visit_passes": term_visit_passes,
            "term_passes_per_owner": term_passes_per_owner,
            "term_sink_calls": term_sink_calls,
            "proof_file": FAR_BANK_GKR_FILE,
            "proof_bytes": encoded_proof.len(),
            "proof_blake2b256": proof_blake2b256,
            "decoded_exact_dimensions": decoded_proof == proof,
            "proof_point_hex": proof_point_hex,
            "embedded_parent_point_hex": embedded_parent_point_hex,
            "claim_value_hex": claim_value_hex,
            "parent_mle_value_hex": parent_mle_value_hex,
            "claim_matches_fresh_verifier": claim == verified_claim,
            "claim_matches_parent_mle": verified_claim.value == parent_mle_value,
            "transcript_continuation_matches": transcript_continuation_matches,
        },
        "opening": {
            "file": FAR_BANK_OPENING_FILE,
            "bytes": encoded_opening.len(),
            "blake2b256": opening_blake2b256,
            "verified_with_original_test_key": true,
        },
        "negative": {
            "wrong_setup_prefix": far_bank_negative_json(&setup_negative),
            "wrong_commitment_prefix": far_bank_negative_json(&commitment_negative),
            "wrong_embedded_bank_coordinate": far_bank_negative_json(&wrong_point_negative),
            "wrong_valid_claim_value": far_bank_negative_json(&wrong_value_negative),
            "trailing_gkr_byte": far_bank_negative_json(&trailing_negative),
            "selected_bank_output_mutation": far_bank_negative_json(&selected_output_negative),
            "wrong_valid_bank_selection": far_bank_negative_json(&wrong_selection_negative),
        },
        "timing_ms": {
            "setup_reconstruction": setup_reconstruction_ms,
            "verifier_key_encode": verifier_key_encode_ms,
            "public_admit_24_reject": public_admit_24_reject_ms,
            "commitment_reconstruction": commitment_reconstruction_ms,
            "producer_gkr": producer_gkr_ms,
            "proof_decode": proof_decode_ms,
            "fresh_gkr_verify": fresh_gkr_verify_ms,
            "parent_mle": parent_mle_ms,
            "open_dory": open_dory_ms,
            "verifier_key_decode_admit": verifier_key_decode_admit_ms,
            "fresh_pcs_verify": fresh_pcs_verify_ms,
            "whole_test_before_result_write": total_before_result_write_ms,
        },
        "io": {
            "source_open": packed_io_json(source_open_io),
            "commitment_reconstruction": packed_io_json(commitment_io),
            "producer": packed_io_json(producer_io),
            "parent_mle": packed_io_json(parent_mle_io),
            "open_dory": packed_io_json(opening_io),
            "fresh_gkr_verify": packed_io_json(fresh_gkr_io),
            "fresh_pcs_verify": packed_io_json(fresh_pcs_io),
        },
        "global_proof": false,
        "pcs_scope": "bounded diagnostic only",
    });
    let result_bytes = serde_json::to_vec_pretty(&result).expect("serialize far-bank result");
    write_new_pcs_artifact(&artifact_directory, FAR_BANK_RESULT_FILE, &result_bytes);
    println!("far_bank_common_pcs_result={}", serde_json::to_string(&result).unwrap());
}

const FIXED_V_ARTIFACT_DIR_ENV:&str="NIPOPOW_FIXED_V_ARTIFACT_DIR";
const FIXED_V_REFERENCE_DIR_ENV:&str="NIPOPOW_FIXED_V_REFERENCE_DIR";
const FIXED_V_PAIR_ORDER_ENV:&str="NIPOPOW_FIXED_V_PAIR_ORDER";
const FIXED_V_GKR_FILE:&str="fixed-v-gkr-proof.bin";
const FIXED_V_RESULT_FILE:&str="fixed-v-result.json";
const FIXED_V_TRANSCRIPT_DOMAIN:&[u8]=b"nipopow-v2-native-far-bank-parent-pcs-join-v1";
const FIXED_V_PROOF_BYTES:usize=4_576;

fn prove_far_bank_cache_zero(
    core:&SparseCircuit,core_digest:&str,spec:FarBankSpec,setup_id:&[u8;32],commitment_bytes:&[u8],
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    transcript:&mut Transcript,bind_calls:&mut usize,
)->Result<(GkrProof,InputClaim),String>{
    validate_far_bank(core,core_digest,spec)?;
    let shape=sparse::validate(core,0).map_err(|error|error.to_string())?;
    sparse_stream_roster::prove_with_cache_budget_for_test(
        spec.input_bits,spec.slot_bits,spec.row_bits,0,&[spec.row_bits],Some(0),load_copy,transcript,
        |transcript|{*bind_calls+=1;bind_far_bank_parent_pcs(transcript,core_digest,spec,setup_id,commitment_bytes);},
        visit_terms,|r,u,v|far_bank_wiring(core,&shape,r,u,v),
    )
}

fn prove_far_bank_fixed_v(
    core:&SparseCircuit,core_digest:&str,spec:FarBankSpec,setup_id:&[u8;32],commitment_bytes:&[u8],
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,bind_calls:&mut usize,
)->Result<(GkrProof,InputClaim,sparse_stream_roster::FixedCoreVProofStats),String>{
    validate_far_bank(core,core_digest,spec)?;
    let shape=sparse::validate(core,0).map_err(|error|error.to_string())?;
    let template=sparse_stream_roster::FixedCoreVTemplate::try_new(core,spec.input_bits,spec.slot_bits,spec.row_bits)?;
    sparse_stream_roster::prove_fixed_core_v_with_cache_budget_for_test(&template,Some(0),load_copy,transcript,
        |transcript|{*bind_calls+=1;bind_far_bank_parent_pcs(transcript,core_digest,spec,setup_id,commitment_bytes);},
        |r,u,v|far_bank_wiring(core,&shape,r,u,v),
    )
}

#[test]
fn native_window16_far_bank14_fixed_core_v_aggregation_authenticates_original_parent_commitment_pcs24(){
    let whole_started=Instant::now();let (core,core_layout,core_digest)=canonical_core();
    validate_far_bank(&core,&core_digest,FAR_BANK_SPEC).unwrap();
    let artifact_directory=std::env::var(FIXED_V_ARTIFACT_DIR_ENV).expect("runner pins fresh fixed-V output");
    assert_eq!(fs::read_dir(&artifact_directory).unwrap().count(),0,"fresh fixed-V artifact directory");
    let pair_order=std::env::var(FIXED_V_PAIR_ORDER_ENV).expect("runner pins producer pair order");
    assert!(pair_order=="reference_then_candidate"||pair_order=="candidate_then_reference");
    let source_path=std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE").expect("runner pins original Window16 source");
    assert_eq!(fs::metadata(&source_path).unwrap().len(),SOURCE_BYTES);
    let parent=PackedFile::open(&source_path,PARENT_LOG_N).expect("open pinned Window16 source");
    assert_eq!(parent.input_len(),SOURCE_BITS);
    let source_open_io=parent.io_metrics_snapshot();
    assert_eq!((source_open_io.read_calls,source_open_io.read_bytes,source_open_io.read_ns),(0,0,0));

    let original_directory=std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV).expect("runner pins original C1 PCS artifacts");
    let original_path=|name:&str|std::path::Path::new(&original_directory).join(name);
    let commitment_bytes=fs::read(original_path(COMMON_PCS_COMMITMENT_FILE)).expect("read original parent commitment");
    let key_bytes=fs::read(original_path(COMMON_PCS_KEY_FILE)).expect("read original TEST24 verifier key");
    let original_result_bytes=fs::read(original_path(COMMON_PCS_RESULT_FILE)).expect("read original PCS result");
    let original_result:serde_json::Value=serde_json::from_slice(&original_result_bytes).expect("decode original PCS result");
    assert_eq!(original_result["schema"].as_str(),Some("native-core-bank-projection-pcs-v1"));
    assert_eq!(commitment_bytes.len(),384);assert_eq!(key_bytes.len(),25_584);
    assert_eq!(work_tree_layout::hash_bytes(&commitment_bytes),original_result["commitment"]["blake2b256"].as_str().unwrap());
    assert_eq!(work_tree_layout::hash_bytes(&key_bytes),original_result["setup"]["verifier_key_blake2b256"].as_str().unwrap());
    let commitment=crate::pcs::decode_commitment(&commitment_bytes).expect("decode original parent commitment");
    assert_eq!(crate::pcs::encode_commitment(&commitment).unwrap(),commitment_bytes);
    let public_admit_24_error=match crate::verifier_key::admit(PARENT_LOG_N,&key_bytes){
        Err(error)=>error,Ok(_)=>panic!("public TEST24 admission unexpectedly accepted"),
    };
    assert_eq!(public_admit_24_error,"unsupported verifier-key dimension");

    let reference_directory=std::env::var(FIXED_V_REFERENCE_DIR_ENV).expect("runner pins frozen far-bank reference");
    let reference_path=|name:&str|std::path::Path::new(&reference_directory).join(name);
    let frozen_proof_bytes=fs::read(reference_path("far-bank-gkr-proof.bin")).expect("read frozen far proof");
    let frozen_opening_bytes=fs::read(reference_path("far-bank-parent-opening.bin")).expect("read frozen parent opening");
    let frozen_result_bytes=fs::read(reference_path("far-bank-result.json")).expect("read frozen far result");
    let frozen_result:serde_json::Value=serde_json::from_slice(&frozen_result_bytes).expect("decode frozen far result");
    assert_eq!(frozen_result["schema"].as_str(),Some("native-far-bank-common-pcs-v1"));
    assert_eq!(frozen_result["test"].as_str(),Some("native_window16_far_bank14_gkr_claim_authenticates_original_parent_commitment_pcs24"));
    assert_eq!(frozen_result["source"]["sha256"].as_str(),Some(SOURCE_SHA256));
    assert_eq!(frozen_result["identity"]["input_receipt_sha256"].as_str(),Some(CACHE_REFERENCE_INPUTS_SHA256));
    assert_eq!(frozen_result["producer"]["proof_bytes"].as_u64(),Some(FIXED_V_PROOF_BYTES as u64));
    assert_eq!(frozen_proof_bytes.len(),FIXED_V_PROOF_BYTES);
    assert_eq!(work_tree_layout::hash_bytes(&frozen_proof_bytes),"db0b5d40ec093d39b19390bd99984b82d0d9907d81c49b8cbfd9c7fe72982b06");
    assert_eq!(frozen_opening_bytes.len(),FAR_BANK_OPENING_BYTES);
    assert_eq!(work_tree_layout::hash_bytes(&frozen_opening_bytes),frozen_result["opening"]["blake2b256"].as_str().unwrap());
    let frozen_proof=gkr::decode_dimensions(&[FAR_BANK_PROJECTED_INPUT_BITS],&frozen_proof_bytes).expect("decode frozen 20-bit proof");
    let frozen_claim_value=&frozen_result["producer"]["claim_value_hex"];
    assert!(frozen_claim_value.is_string());

    let setup_id_hex=frozen_result["identity"]["setup_id_hex"].as_str().expect("frozen setup identifier");
    let setup_id_vec=(0..32).map(|index|u8::from_str_radix(&setup_id_hex[index*2..index*2+2],16).unwrap()).collect::<Vec<_>>();
    let setup_id:[u8;32]=setup_id_vec.try_into().expect("32-byte setup identifier");
    assert_eq!(setup_id_hex,"b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe");
    let mutation_wire=core_layout.output[0][0];assert!(mutation_wire<BANK_WIDTH);
    parent.reset_io_metrics();
    let mut mutation_transcript=Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);let mut mutation_bind_calls=0usize;let mut mutation_load_calls=0usize;
    let template=sparse_stream_roster::FixedCoreVTemplate::try_new(&core,CORE_INPUT_BITS,SLOT_BITS,CORE_ROW_BITS).unwrap();
    let mutation= sparse_stream_roster::prove_fixed_core_v_with_cache_budget_for_test(&template,Some(0),
        |owner|{mutation_load_calls+=1;let mut values=load_far_bank_owner(&parent,owner,FAR_BANK_SPEC.selected_bank.physical_index)?;
            if owner==0{let value=&mut values[mutation_wire];assert!(*value==Fr::zero()||*value==Fr::one());*value=Fr::one()-*value;}Ok(values)},
        &mut mutation_transcript,|_|mutation_bind_calls+=1,
        |r,u,v|far_bank_wiring(&core,&sparse::validate(&core,0).unwrap(),r,u,v));
    let mutation_error=mutation.err().expect("selected output mutation fails residual guard");
    assert_eq!(mutation_error,"GKR error: NonzeroOutput");assert!(mutation_load_calls>0);
    assert_eq!((mutation_bind_calls,mutation_transcript.challenges(),mutation_transcript.raw_queries()),(0,0,0));

    let mut reference_outcome=None;let mut candidate_outcome=None;
    for candidate_first in [pair_order=="candidate_then_reference",pair_order=="reference_then_candidate"]{
        if candidate_first{
            parent.reset_io_metrics();let started=Instant::now();let mut bind_calls=0usize;let mut load_calls=0usize;
            let (proof,claim,stats,transcript)={
                let mut transcript=Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);
                let (proof,claim,stats)=prove_far_bank_fixed_v(&core,&core_digest,FAR_BANK_SPEC,&setup_id,&commitment_bytes,
                    |owner|{load_calls+=1;load_far_bank_owner(&parent,owner,FAR_BANK_SPEC.selected_bank.physical_index)},
                    &mut transcript,&mut bind_calls).expect("fixed V cache-zero proof");
                (proof,claim,stats,transcript)
            };
            let elapsed=started.elapsed().as_millis();let io=parent.io_metrics_snapshot();
            assert_eq!(bind_calls,1);assert_eq!(io.read_calls,load_calls as u64);assert_eq!(io.read_bytes,load_calls as u64*8_192);
            candidate_outcome=Some((proof,claim,stats,transcript,load_calls,io,elapsed));
        }else{
            parent.reset_io_metrics();let started=Instant::now();let mut bind_calls=0usize;let mut load_calls=0usize;
            let mut passes=vec![0usize;OWNER_COUNT];let mut callbacks=0usize;
            let (proof,claim,transcript)={
                let mut transcript=Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);
                let (proof,claim)=prove_far_bank_cache_zero(&core,&core_digest,FAR_BANK_SPEC,&setup_id,&commitment_bytes,
                    |owner|{load_calls+=1;load_far_bank_owner(&parent,owner,FAR_BANK_SPEC.selected_bank.physical_index)},
                    |owner,sink|{passes[owner]+=1;for term in &core.terms{callbacks+=1;sink(term.clone())?;}Ok(())},
                    &mut transcript,&mut bind_calls).expect("legacy cache-zero reference proof");
                (proof,claim,transcript)
            };
            let elapsed=started.elapsed().as_millis();let io=parent.io_metrics_snapshot();
            assert_eq!(bind_calls,1);assert!(passes.iter().all(|count|*count==passes[0]));
            assert_eq!(callbacks,CORE_TERMS*passes.iter().sum::<usize>());
            assert_eq!(io.read_calls,load_calls as u64);assert_eq!(io.read_bytes,load_calls as u64*8_192);
            reference_outcome=Some((proof,claim,transcript,load_calls,passes,callbacks,io,elapsed));
        }
    }
    let (legacy_proof,legacy_claim,legacy_transcript,legacy_load_calls,legacy_passes,legacy_callbacks,legacy_io,legacy_ms)=reference_outcome.unwrap();
    let (proof,claim,stats,prover_transcript,load_calls,producer_io,producer_gkr_ms)=candidate_outcome.unwrap();
    let encoded_proof=gkr::encode_proof(&proof).expect("encode fixed V proof");
    assert_eq!(encoded_proof.len(),FIXED_V_PROOF_BYTES);
    assert_eq!(encoded_proof,gkr::encode_proof(&legacy_proof).unwrap());
    assert_eq!(encoded_proof,frozen_proof_bytes);
    assert_eq!(claim,legacy_claim);
    assert_eq!(stats.common_v_template_callbacks,CORE_TERMS);
    assert!(stats.common_state_peak_capacity_bytes>0&&stats.common_state_peak_capacity_bytes<=sparse_stream_roster::MAX_FIXED_V_COMMON_STATE_BYTES);
    assert!(load_calls>0&&producer_io.read_calls==load_calls as u64);
    let legacy_claim_point_hex=two_bank_hex_point(&legacy_claim.point);
    assert_eq!(serde_json::to_value(&legacy_claim_point_hex).unwrap(),frozen_result["producer"]["proof_point_hex"]);
    assert_eq!(serde_json::to_value(two_bank_hex_point(&far_bank_parent_point(FAR_BANK_SPEC,&legacy_claim.point).unwrap())).unwrap(),
        frozen_result["producer"]["embedded_parent_point_hex"]);
    let claim_value_hex=hex_bytes(&crate::pcs::encode(&claim.value).unwrap());
    assert_eq!(claim_value_hex,frozen_claim_value.as_str().unwrap());
    let proof_blake2b256=work_tree_layout::hash_bytes(&encoded_proof);
    assert_eq!(proof_blake2b256,"db0b5d40ec093d39b19390bd99984b82d0d9907d81c49b8cbfd9c7fe72982b06");
    let mut legacy_continuation=legacy_transcript.clone();let mut candidate_continuation=prover_transcript.clone();
    let transcript_continuation_matches=legacy_continuation.challenge_scalar(b"fixed-v-post-gkr")==candidate_continuation.challenge_scalar(b"fixed-v-post-gkr")
        &&legacy_continuation.challenges()==candidate_continuation.challenges()
        &&legacy_continuation.raw_queries()==candidate_continuation.raw_queries()
        &&legacy_continuation.bytes_absorbed()==candidate_continuation.bytes_absorbed();
    assert!(transcript_continuation_matches);

    let parent_point=far_bank_parent_point(FAR_BANK_SPEC,&claim.point).expect("embed fixed V claim into original W24 coordinates");
    assert_eq!(parent_point.len(),PARENT_LOG_N);assert_eq!(&parent_point[16..20],&[Fr::zero(),Fr::one(),Fr::one(),Fr::one()]);
    let parent_mle_started=Instant::now();parent.reset_io_metrics();
    let parent_mle_value=parent.evaluate(&parent_point).expect("evaluate original parent MLE");
    let parent_mle_ms=parent_mle_started.elapsed().as_millis();let parent_mle_io=parent.io_metrics_snapshot();
    assert_eq!((parent_mle_io.read_calls,parent_mle_io.read_bytes),(1,SOURCE_BYTES));assert_eq!(parent_mle_value,claim.value);

    let decoded_proof=gkr::decode_dimensions(&[FAR_BANK_PROJECTED_INPUT_BITS],&encoded_proof).expect("freshly decode fixed proof");
    assert_eq!(decoded_proof,proof);assert_eq!(gkr::encode_proof(&decoded_proof).unwrap(),encoded_proof);
    let decoded_opening=crate::pcs::decode_proof(&frozen_opening_bytes,PARENT_LOG_N).expect("decode original Dory opening");
    assert_eq!(crate::pcs::encode_proof(&decoded_opening).unwrap(),frozen_opening_bytes);
    let mut verifier_transcript=Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);let mut verifier_bind_calls=0usize;
    parent.reset_io_metrics();let fresh_gkr_started=Instant::now();
    let verified_claim=verify_far_bank_projection(&core,&core_digest,FAR_BANK_SPEC,&setup_id,&commitment_bytes,
        &decoded_proof,&mut verifier_transcript,&mut verifier_bind_calls).expect("fresh fixed-V GKR verifier");
    let fresh_gkr_verify_ms=fresh_gkr_started.elapsed().as_millis();let fresh_gkr_io=parent.io_metrics_snapshot();
    assert_eq!((fresh_gkr_io.read_calls,fresh_gkr_io.read_bytes,fresh_gkr_io.read_ns),(0,0,0));
    assert_eq!(verifier_bind_calls,1);assert_eq!(verified_claim,claim);
    assert_eq!(claim,legacy_claim);assert_eq!(claim,verified_claim);
    assert_eq!(far_bank_parent_point(FAR_BANK_SPEC,&verified_claim.point).unwrap(),parent_point);
    assert_eq!(verified_claim.value,parent_mle_value);
    let verifier_key=crate::verifier_key::admit_generated_test_key(PARENT_LOG_N,&key_bytes,setup_id)
        .expect("admit original stored TEST24 key through diagnostic-only adapter");
    assert_eq!(verifier_key.id(),&setup_id);
    parent.reset_io_metrics();let fresh_pcs_started=Instant::now();
    crate::pcs::verify_admitted(commitment.clone(),verified_claim.value,&parent_point,&decoded_opening,&verifier_key,&mut verifier_transcript.clone())
        .expect("fresh PCS verifier authenticates the unchanged original opening");
    let fresh_pcs_verify_ms=fresh_pcs_started.elapsed().as_millis();let fresh_pcs_io=parent.io_metrics_snapshot();
    assert_eq!((fresh_pcs_io.read_calls,fresh_pcs_io.read_bytes,fresh_pcs_io.read_ns),(0,0,0));

    let nonzero_output_mutation=json!({"rejected":true,"error":mutation_error,"bind_calls":mutation_bind_calls,
        "challenge_count":mutation_transcript.challenges()});
    let legacy_total_callbacks=legacy_callbacks;
    let total_callbacks=stats.streamed_term_callbacks.checked_add(stats.common_v_template_callbacks).expect("callback total overflow");
    write_new_pcs_artifact(&artifact_directory,FIXED_V_GKR_FILE,&encoded_proof);
    let result=json!({
        "schema":"native-fixed-core-v-aggregation-v1",
        "test":"native_window16_far_bank14_fixed_core_v_aggregation_authenticates_original_parent_commitment_pcs24",
        "pair_order":pair_order,
        "scope":"one Window16 far-bank14 proof parity and original parent-commitment consumer join; bounded diagnostic only",
        "source":{"file_sha256":SOURCE_SHA256,"bytes":SOURCE_BYTES,"owner_count":OWNER_COUNT,"parent_point_bits":PARENT_LOG_N},
        "relation":{"core_term_digest_blake2b256":core_digest,"core_terms":CORE_TERMS,"core_input_bits":CORE_INPUT_BITS,
            "core_row_bits":CORE_ROW_BITS,"owner_bits":SLOT_BITS,"family_bits":0,"selected_core_ordinal":10,
            "selected_physical_bank":14,"selected_bank_start":917_504,"bank_width":BANK_WIDTH,
            "template_requires_sorted_rows_and_active_endpoints":true},
        "identity":{"original_pcs_artifact_directory_env":COMMON_PCS_ARTIFACT_DIR_ENV,
            "input_receipt_sha256":CACHE_REFERENCE_INPUTS_SHA256,"setup_id_hex":setup_id_hex,
            "commitment_file":COMMON_PCS_COMMITMENT_FILE,"commitment_bytes":commitment_bytes.len(),
            "commitment_sha256":"E87D71503ED0117D3D234293DCF72CBED2758DA652610B846119EA1C92E5D6DD",
            "verifier_key_file":COMMON_PCS_KEY_FILE,"verifier_key_bytes":key_bytes.len(),
            "verifier_key_sha256":"3D77BC139351C2832EA098B9E683961C171D918708300121145F0DABFBB48740",
            "public_admit_24_still_rejected":true,"public_admit_24_error":public_admit_24_error},
        "reference":{"reference_input_receipt_sha256":"4000E347A7DC79E5C5C68BE385CCE1E5242E31F1A4317D015C3C110A8461FFC4",
            "reference_directory_env":FIXED_V_REFERENCE_DIR_ENV,
            "frozen_far_result_file":"far-bank-result.json","frozen_far_proof_file":"far-bank-gkr-proof.bin",
            "frozen_far_proof_bytes":frozen_proof_bytes.len(),"frozen_far_proof_sha256":"B3A4328E13A6586185A863A76A95DA6D914CCC1DB043703E169C1F5C77644193",
            "frozen_far_proof_blake2b256":proof_blake2b256,"legacy_cache_zero_load_calls":legacy_load_calls,
            "legacy_cache_zero_term_callbacks":legacy_total_callbacks,"legacy_cache_zero_matches_frozen_far":true,
            "original_opening_file":"far-bank-parent-opening.bin","original_opening_bytes":frozen_opening_bytes.len(),
            "original_opening_sha256":"E8299B1D9C8AB3B2928EEFDAB524A771A3310A9BA58C65F26BEB5AD2FDC021B6"},
        "producer":{"cache_budget_bytes":0,"fixed_v_common_state_cap_bytes":sparse_stream_roster::MAX_FIXED_V_COMMON_STATE_BYTES,
            "common_state_peak_capacity_bytes":stats.common_state_peak_capacity_bytes,"proof_file":FIXED_V_GKR_FILE,
            "proof_bytes":encoded_proof.len(),"proof_blake2b256":proof_blake2b256,"encoded_proof_matches_legacy_cache_zero":true,
            "encoded_proof_matches_frozen_far":true,"claim_point_bits":claim.point.len(),"claim_point_matches_legacy_and_frozen_far":true,
            "claim_value_hex":claim_value_hex,"claim_value_matches_legacy_and_frozen_far":true,
            "claim_matches_fresh_gkr_verifier":claim==verified_claim,"claim_matches_parent_mle":claim.value==parent_mle_value,
            "transcript_continuation_matches":transcript_continuation_matches,"load_calls":load_calls,
            "streamed_term_callbacks":stats.streamed_term_callbacks,"common_v_template_callbacks":stats.common_v_template_callbacks,
            "total_term_callbacks":total_callbacks,"counter_values_are_observed":true},
        "opening":{"verified_with_original_test_key":true,"setup_commitment_and_opening_regenerated":false},
        "negative":{"nonzero_output_mutation":nonzero_output_mutation},
        "timing_ms":{"legacy_cache_zero_gkr":legacy_ms,"fixed_v_candidate_gkr":producer_gkr_ms,
            "fresh_gkr_verify":fresh_gkr_verify_ms,"parent_mle":parent_mle_ms,"fresh_pcs_verify":fresh_pcs_verify_ms},
        "io":{"legacy_cache_zero":packed_io_json(legacy_io),"fixed_v_candidate":packed_io_json(producer_io),
            "fresh_gkr_verify":packed_io_json(fresh_gkr_io),"fresh_pcs_verify":packed_io_json(fresh_pcs_io)},
        "global_proof":false,"pcs_scope":"bounded diagnostic only"});
    let result_bytes=serde_json::to_vec_pretty(&result).expect("serialize fixed-V result");
    write_new_pcs_artifact(&artifact_directory,FIXED_V_RESULT_FILE,&result_bytes);
    println!("fixed_v_aggregation_result={}",serde_json::to_string(&result).unwrap());
}

const ALL_CORE_PARENT_PCS_ARTIFACT_DIR_ENV: &str = "NIPOPOW_ALL_CORE_PARENT_PCS_ARTIFACT_DIR";
const ALL_CORE_PARENT_PCS_RESULT_FILE: &str = "all-core-parent-pcs-result.json";
const ALL_CORE_PARENT_PCS_TEST_NAME: &str = "native_window16_all_core_banks_authenticate_original_parent_commitment_pcs24";
const ALL_CORE_PARENT_PCS_RESULT_PREFIX: &str = "all_core_parent_pcs_result=";
const ALL_CORE_PARENT_PCS_REFERENCE_INPUTS_SHA256: &str = "4000E347A7DC79E5C5C68BE385CCE1E5242E31F1A4317D015C3C110A8461FFC4";
const ALL_CORE_PARENT_PCS_IDENTITY_INPUTS_SHA256: &str = "0C79E1960864FB33F220D811CBCE924BDC89623153FC1361D6A4CF8DFA859479";
const ALL_CORE_PARENT_PCS_SETUP_ID_HEX: &str = "b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe";
const ALL_CORE_PARENT_PCS_COMMITMENT_SHA256: &str = "E87D71503ED0117D3D234293DCF72CBED2758DA652610B846119EA1C92E5D6DD";
const ALL_CORE_PARENT_PCS_KEY_SHA256: &str = "3D77BC139351C2832EA098B9E683961C171D918708300121145F0DABFBB48740";
const ALL_CORE_PARENT_PCS_FAR_PROOF_SHA256: &str = "B3A4328E13A6586185A863A76A95DA6D914CCC1DB043703E169C1F5C77644193";
const ALL_CORE_PARENT_PCS_FAR_OPENING_SHA256: &str = "E8299B1D9C8AB3B2928EEFDAB524A771A3310A9BA58C65F26BEB5AD2FDC021B6";

struct AllCoreParentBankRecord {
    address: FarBankAddress,
    claim: InputClaim,
    encoded_proof: Vec<u8>,
    parent_point: Vec<Fr>,
    encoded_opening: Vec<u8>,
    prover_post_gkr: Transcript,
    load_calls: usize,
    term_visit_passes: usize,
    term_callbacks: usize,
    producer_io: PackedIoSnapshot,
    parent_mle_io: PackedIoSnapshot,
    opening_io: PackedIoSnapshot,
    parent_mle_value: Fr,
    producer_ms: u128,
    parent_mle_ms: u128,
    opening_ms: u128,
    decoded_proof: Option<GkrProof>,
    decoded_opening: Option<dory_pcs::backends::arkworks::ArkDoryProof>,
    verified_claim: Option<InputClaim>,
    verifier_transcript: Option<Transcript>,
    transcript_continuation_matches: bool,
}

#[test]
fn native_window16_all_core_banks_authenticate_original_parent_commitment_pcs24() {
    let whole_started = Instant::now();
    let (core, core_layout, core_digest) = canonical_core();
    assert_eq!(FAR_BANK_MAPPING.map(|entry| entry.start), work_tree_layout::CORE_OFFSETS);
    assert_eq!(core_digest, FAR_BANK_CORE_DIGEST);
    for address in FAR_BANK_MAPPING {
        validate_far_bank(&core, &core_digest, FarBankSpec { selected_bank: address, ..FAR_BANK_SPEC })
            .expect("each frozen canonical bank spec validates");
    }

    let artifact_directory = std::env::var(ALL_CORE_PARENT_PCS_ARTIFACT_DIR_ENV)
        .expect("runner pins fresh all-core parent PCS artifact directory");
    assert_eq!(fs::read_dir(&artifact_directory).expect("read fresh artifact directory").count(), 0);
    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE")
        .expect("runner pins original Window16 source");
    assert_eq!(fs::metadata(&source_path).expect("source metadata").len(), SOURCE_BYTES);
    let parent = PackedFile::open(&source_path, PARENT_LOG_N).expect("open original Window16 source");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    let source_open_io = parent.io_metrics_snapshot();
    assert_eq!((source_open_io.read_calls, source_open_io.read_bytes, source_open_io.read_ns), (0, 0, 0));

    let original_directory = std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV)
        .expect("runner pins original common-PCS identity artifacts");
    let original_path = |name: &str| std::path::Path::new(&original_directory).join(name);
    let reference_commitment_bytes = fs::read(original_path(COMMON_PCS_COMMITMENT_FILE))
        .expect("read immutable original parent commitment");
    let reference_key_bytes = fs::read(original_path(COMMON_PCS_KEY_FILE))
        .expect("read immutable original TEST24 verifier key");
    assert_eq!(reference_commitment_bytes.len(), 384);
    assert_eq!(reference_key_bytes.len(), 25_584);

    let reference_directory = std::env::var(FIXED_V_REFERENCE_DIR_ENV)
        .expect("runner pins frozen bank14 far reference");
    let reference_path = |name: &str| std::path::Path::new(&reference_directory).join(name);
    let frozen_far_proof_bytes = fs::read(reference_path("far-bank-gkr-proof.bin"))
        .expect("read frozen bank14 far proof");
    let frozen_far_opening_bytes = fs::read(reference_path("far-bank-parent-opening.bin"))
        .expect("read frozen bank14 parent opening");
    let frozen_far_result_bytes = fs::read(reference_path("far-bank-result.json"))
        .expect("read frozen bank14 raw result");
    assert_eq!(frozen_far_proof_bytes.len(), FAR_BANK_PROOF_BYTES);
    assert_eq!(frozen_far_opening_bytes.len(), FAR_BANK_OPENING_BYTES);
    let frozen_far_result: serde_json::Value = serde_json::from_slice(&frozen_far_result_bytes)
        .expect("decode frozen bank14 raw result");
    assert_eq!(frozen_far_result["schema"].as_str(), Some("native-far-bank-common-pcs-v1"));
    assert_eq!(frozen_far_result["test"].as_str(), Some("native_window16_far_bank14_gkr_claim_authenticates_original_parent_commitment_pcs24"));
    assert_eq!(frozen_far_result["source"]["sha256"].as_str(), Some(SOURCE_SHA256));
    assert_eq!(frozen_far_result["identity"]["input_receipt_sha256"].as_str(), Some(CACHE_REFERENCE_INPUTS_SHA256));
    assert_eq!(frozen_far_result["identity"]["setup_id_hex"].as_str(), Some(ALL_CORE_PARENT_PCS_SETUP_ID_HEX));
    assert_eq!(frozen_far_result["identity"]["commitment_bytes"].as_u64(), Some(384));
    assert_eq!(frozen_far_result["identity"]["verifier_key_bytes"].as_u64(), Some(25_584));
    assert_eq!(frozen_far_result["producer"]["proof_bytes"].as_u64(), Some(FAR_BANK_PROOF_BYTES as u64));
    assert_eq!(frozen_far_result["opening"]["bytes"].as_u64(), Some(FAR_BANK_OPENING_BYTES as u64));
    assert_eq!(work_tree_layout::hash_bytes(&frozen_far_proof_bytes), frozen_far_result["producer"]["proof_blake2b256"].as_str().unwrap());
    assert_eq!(work_tree_layout::hash_bytes(&frozen_far_opening_bytes), frozen_far_result["opening"]["blake2b256"].as_str().unwrap());
    assert_eq!(frozen_far_result["producer"]["proof_blake2b256"].as_str(), Some("db0b5d40ec093d39b19390bd99984b82d0d9907d81c49b8cbfd9c7fe72982b06"));

    let setup_started = Instant::now();
    let setup = crate::pcs::generate_setup(PARENT_LOG_N).expect("reconstruct pinned diagnostic parent setup");
    let setup_reconstruction_ms = setup_started.elapsed().as_millis();
    let setup_id = setup.id;
    let setup_id_hex = hex_bytes(&setup_id);
    assert_eq!(setup_id_hex, ALL_CORE_PARENT_PCS_SETUP_ID_HEX);
    let key_encode_started = Instant::now();
    let verifier_key_bytes = crate::pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))
        .expect("encode reconstructed original TEST24 key");
    let verifier_key_encoding_ms = key_encode_started.elapsed().as_millis();
    assert_eq!(verifier_key_bytes, reference_key_bytes, "reconstructed TEST24 key exact byte identity");
    let public_admit_24_error = match crate::verifier_key::admit(PARENT_LOG_N, &reference_key_bytes) {
        Err(error) => error,
        Ok(_) => panic!("public TEST24 key admission unexpectedly accepted"),
    };
    assert_eq!(public_admit_24_error, "unsupported verifier-key dimension");

    parent.reset_io_metrics();
    let commitment_started = Instant::now();
    let committed = crate::packed::commit(&parent, &setup).expect("reconstruct original parent commitment");
    let commitment_ms = commitment_started.elapsed().as_millis();
    let commitment_io = parent.io_metrics_snapshot();
    assert_eq!((commitment_io.read_calls, commitment_io.read_bytes), (1, SOURCE_BYTES));
    let commitment_bytes = crate::pcs::encode_commitment(&committed.commitment)
        .expect("encode reconstructed parent commitment");
    assert_eq!(commitment_bytes.len(), 384);
    assert_eq!(commitment_bytes, reference_commitment_bytes, "original commitment exact byte identity");
    let parent_commitment = crate::pcs::decode_commitment(&commitment_bytes)
        .expect("decode original parent commitment");
    assert_eq!(crate::pcs::encode_commitment(&parent_commitment).unwrap(), commitment_bytes);
    let commitment_hash = work_tree_layout::hash_bytes(&commitment_bytes);
    assert_eq!(commitment_hash, frozen_far_result["identity"]["commitment_blake2b256"].as_str().unwrap());
    let key_hash = work_tree_layout::hash_bytes(&reference_key_bytes);
    assert_eq!(key_hash, frozen_far_result["identity"]["verifier_key_blake2b256"].as_str().unwrap());
    let alternate_commitment = ArkGT(parent_commitment.0.clone() + setup.prover.ht.0.clone());
    assert_ne!(alternate_commitment, parent_commitment);
    let alternate_commitment_bytes = crate::pcs::encode_commitment(&alternate_commitment)
        .expect("encode different valid parent commitment");
    assert_eq!(crate::pcs::decode_commitment(&alternate_commitment_bytes).unwrap(), alternate_commitment);

    let mutation_wire = core_layout.output[0][0];
    assert!(mutation_wire < BANK_WIDTH);
    let mut output_mutations = Vec::with_capacity(FAR_BANK_MAPPING.len());
    for address in FAR_BANK_MAPPING {
        let spec = FarBankSpec { selected_bank: address, ..FAR_BANK_SPEC };
        parent.reset_io_metrics();
        let mut mutation_transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
        let mut mutation_bind_calls = 0usize;
        let mut mutation_load_calls = 0usize;
        let mut mutation_visitor_calls = 0usize;
        let mutation_result = prove_far_bank_projection(
            &core, &core_digest, spec, &setup_id, &commitment_bytes,
            |owner| {
                mutation_load_calls += 1;
                let mut values = load_far_bank_owner(&parent, owner, address.physical_index)?;
                if owner == 0 {
                    let value = &mut values[mutation_wire];
                    assert!(*value == Fr::zero() || *value == Fr::one());
                    *value = Fr::one() - *value;
                }
                Ok(values)
            },
            |_, sink| {
                mutation_visitor_calls += 1;
                for term in &core.terms { sink(term.clone())?; }
                Ok(())
            },
            &mut mutation_transcript, &mut mutation_bind_calls,
        );
        let mutation_error = mutation_result.err().expect("changed selected output rejects at residual guard");
        assert_eq!(mutation_error, "GKR error: NonzeroOutput");
        assert!(mutation_load_calls > 0 && mutation_visitor_calls > 0);
        assert_eq!((mutation_bind_calls, mutation_transcript.challenges()), (0, 0));
        let evidence = FarBankNegative {
            rejected_by: "residual_guard",
            error: mutation_error,
            gkr_verify_calls: 0,
            pcs_verify_calls: 0,
            bind_calls: mutation_bind_calls,
            challenge_count: mutation_transcript.challenges(),
        };
        output_mutations.push(json!({
            "core_ordinal": address.core_ordinal,
            "physical_bank": address.physical_index,
            "bank_start": address.start,
            "output_wire_index": mutation_wire,
            "evidence": far_bank_negative_json(&evidence),
        }));
    }

    let mut records = Vec::with_capacity(FAR_BANK_MAPPING.len());
    let mut all_producer_reads = (0u64, 0u64, 0u128);
    let mut all_parent_mle_reads = (0u64, 0u64, 0u128);
    let mut all_opening_reads = (0u64, 0u64, 0u128);
    let mut all_producer_load_calls = 0usize;
    let mut all_term_visit_passes = 0usize;
    let mut all_term_callbacks = 0usize;
    let mut all_producer_ms = 0u128;
    let mut all_parent_mle_ms = 0u128;
    let mut all_opening_ms = 0u128;
    for address in FAR_BANK_MAPPING {
        let spec = FarBankSpec { selected_bank: address, ..FAR_BANK_SPEC };
        parent.reset_io_metrics();
        let mut prover_transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
        let mut load_calls = 0usize;
        let mut visits_by_owner = vec![0usize; OWNER_COUNT];
        let mut term_callbacks = 0usize;
        let mut bind_calls = 0usize;
        let producer_started = Instant::now();
        let (proof, claim) = prove_far_bank_projection(
            &core, &core_digest, spec, &setup_id, &commitment_bytes,
            |owner| {
                load_calls += 1;
                load_far_bank_owner(&parent, owner, address.physical_index)
            },
            |owner, sink| {
                if owner >= OWNER_COUNT { return Err("far-bank owner index out of range".into()); }
                visits_by_owner[owner] += 1;
                for term in &core.terms { term_callbacks += 1; sink(term.clone())?; }
                Ok(())
            },
            &mut prover_transcript, &mut bind_calls,
        ).expect("prove canonical selected bank with default cache");
        let producer_ms = producer_started.elapsed().as_millis();
        assert_eq!(bind_calls, 1);
        assert!(visits_by_owner[0] > 0 && visits_by_owner.iter().all(|count| *count == visits_by_owner[0]));
        let term_visit_passes: usize = visits_by_owner.iter().sum();
        assert_eq!(term_callbacks, CORE_TERMS * term_visit_passes);
        let producer_io = parent.io_metrics_snapshot();
        assert_eq!(producer_io.read_calls, load_calls as u64);
        assert_eq!(producer_io.read_bytes, load_calls as u64 * 8_192);
        let encoded_proof = gkr::encode_proof(&proof).expect("encode canonical bank GKR proof");
        assert_eq!(encoded_proof.len(), FAR_BANK_PROOF_BYTES);
        let decoded_proof = gkr::decode_dimensions(&[FAR_BANK_PROJECTED_INPUT_BITS], &encoded_proof)
            .expect("freshly decode exact 20-dimensional bank proof");
        assert_eq!(decoded_proof, proof);
        let prover_post_gkr = prover_transcript.clone();
        let parent_point = far_bank_parent_point(spec, &claim.point).expect("embed bank claim in original W24");
        assert_eq!(claim.point.len(), FAR_BANK_PROJECTED_INPUT_BITS);
        assert_eq!(parent_point.len(), PARENT_LOG_N);
        assert_eq!(&parent_point[..CORE_INPUT_BITS], &claim.point[..CORE_INPUT_BITS]);
        assert_eq!(&parent_point[CORE_INPUT_BITS + SLOT_BITS..], &claim.point[CORE_INPUT_BITS..]);
        let physical_bits: Vec<_> = (0..SLOT_BITS)
            .map(|bit| if address.physical_index & (1 << bit) == 0 { Fr::zero() } else { Fr::one() })
            .collect();
        assert_eq!(&parent_point[CORE_INPUT_BITS..CORE_INPUT_BITS + SLOT_BITS], physical_bits.as_slice());

        parent.reset_io_metrics();
        let parent_mle_started = Instant::now();
        let parent_mle_value = parent.evaluate(&parent_point).expect("evaluate original parent MLE");
        let parent_mle_ms = parent_mle_started.elapsed().as_millis();
        let parent_mle_io = parent.io_metrics_snapshot();
        assert_eq!((parent_mle_io.read_calls, parent_mle_io.read_bytes), (1, SOURCE_BYTES));
        assert_eq!(claim.value, parent_mle_value);

        parent.reset_io_metrics();
        let opening_started = Instant::now();
        let opening = crate::packed::open(&committed, &parent, &parent_point, &setup, &mut prover_transcript)
            .expect("open original commitment at this bank's parent point");
        let opening_ms = opening_started.elapsed().as_millis();
        let opening_io = parent.io_metrics_snapshot();
        assert_eq!((opening_io.read_calls, opening_io.read_bytes), (2, SOURCE_BYTES * 2));
        let encoded_opening = crate::pcs::encode_proof(&opening).expect("encode parent opening");
        assert_eq!(encoded_opening.len(), FAR_BANK_OPENING_BYTES);
        if address.core_ordinal == 10 {
            assert_eq!(encoded_proof, frozen_far_proof_bytes, "bank14 GKR exact historical bytes");
            assert_eq!(encoded_opening, frozen_far_opening_bytes, "bank14 opening exact historical bytes");
            assert_eq!(serde_json::to_value(two_bank_hex_point(&claim.point)).unwrap(), frozen_far_result["producer"]["proof_point_hex"]);
            assert_eq!(serde_json::to_value(two_bank_hex_point(&parent_point)).unwrap(), frozen_far_result["producer"]["embedded_parent_point_hex"]);
            assert_eq!(hex_bytes(&crate::pcs::encode(&claim.value).unwrap()), frozen_far_result["producer"]["claim_value_hex"].as_str().unwrap());
        }
        all_producer_reads.0 += producer_io.read_calls;
        all_producer_reads.1 += producer_io.read_bytes;
        all_producer_reads.2 += producer_io.read_ns;
        all_parent_mle_reads.0 += parent_mle_io.read_calls;
        all_parent_mle_reads.1 += parent_mle_io.read_bytes;
        all_parent_mle_reads.2 += parent_mle_io.read_ns;
        all_opening_reads.0 += opening_io.read_calls;
        all_opening_reads.1 += opening_io.read_bytes;
        all_opening_reads.2 += opening_io.read_ns;
        all_producer_load_calls += load_calls;
        all_term_visit_passes += term_visit_passes;
        all_term_callbacks += term_callbacks;
        all_producer_ms += producer_ms;
        all_parent_mle_ms += parent_mle_ms;
        all_opening_ms += opening_ms;
        records.push(AllCoreParentBankRecord {
            address, claim, encoded_proof, parent_point, encoded_opening, prover_post_gkr,
            load_calls, term_visit_passes, term_callbacks, producer_io, parent_mle_io, opening_io,
            parent_mle_value, producer_ms, parent_mle_ms, opening_ms,
            decoded_proof: Some(decoded_proof), decoded_opening: None,
            verified_claim: None, verifier_transcript: None, transcript_continuation_matches: false,
        });
    }

    drop(committed);
    drop(setup);
    let verifier_key = crate::verifier_key::admit_generated_test_key(
        PARENT_LOG_N, &reference_key_bytes, setup_id,
    ).expect("decode original stored TEST24 key after dropping prover setup and rows");
    assert_eq!(verifier_key.id(), &setup_id);

    let mut all_fresh_gkr_reads = (0u64, 0u64, 0u128);
    let mut all_fresh_pcs_reads = (0u64, 0u64, 0u128);
    let mut all_fresh_gkr_ms = 0u128;
    let mut all_fresh_pcs_ms = 0u128;
    let mut bank_results = Vec::with_capacity(records.len());
    for record in &mut records {
        let mut verifier_transcript = Transcript::new(FAR_BANK_TRANSCRIPT_DOMAIN);
        let mut verifier_bind_calls = 0usize;
        parent.reset_io_metrics();
        let fresh_gkr_started = Instant::now();
        let verified_claim = verify_far_bank_projection(
            &core, &core_digest,
            FarBankSpec { selected_bank: record.address, ..FAR_BANK_SPEC },
            &setup_id, &commitment_bytes, record.decoded_proof.as_ref().unwrap(),
            &mut verifier_transcript, &mut verifier_bind_calls,
        ).expect("fresh GKR verifier accepts exact bank proof after prover state drop");
        let fresh_gkr_ms = fresh_gkr_started.elapsed().as_millis();
        let fresh_gkr_io = parent.io_metrics_snapshot();
        assert_eq!((fresh_gkr_io.read_calls, fresh_gkr_io.read_bytes, fresh_gkr_io.read_ns), (0, 0, 0));
        assert_eq!(verifier_bind_calls, 1);
        assert_eq!(verified_claim, record.claim);
        assert_eq!(far_bank_parent_point(FarBankSpec { selected_bank: record.address, ..FAR_BANK_SPEC }, &verified_claim.point).unwrap(), record.parent_point);
        let mut producer_continuation = record.prover_post_gkr.clone();
        let mut verifier_continuation = verifier_transcript.clone();
        let continuation_matches = producer_continuation.challenge_scalar(b"far-bank-post-gkr")
            == verifier_continuation.challenge_scalar(b"far-bank-post-gkr")
            && producer_continuation.challenges() == verifier_continuation.challenges()
            && producer_continuation.raw_queries() == verifier_continuation.raw_queries()
            && producer_continuation.bytes_absorbed() == verifier_continuation.bytes_absorbed();
        assert!(continuation_matches);
        record.transcript_continuation_matches = continuation_matches;

        let decoded_opening = crate::pcs::decode_proof(&record.encoded_opening, PARENT_LOG_N)
            .expect("freshly decode Dory opening after dropping prover state");
        assert_eq!(crate::pcs::encode_proof(&decoded_opening).unwrap(), record.encoded_opening);
        parent.reset_io_metrics();
        let fresh_pcs_started = Instant::now();
        crate::pcs::verify_admitted(
            parent_commitment.clone(), verified_claim.value, &record.parent_point,
            &decoded_opening, &verifier_key, &mut verifier_transcript.clone(),
        ).expect("fresh original TEST24 consumer verifies this bank's parent opening");
        let fresh_pcs_ms = fresh_pcs_started.elapsed().as_millis();
        let fresh_pcs_io = parent.io_metrics_snapshot();
        assert_eq!((fresh_pcs_io.read_calls, fresh_pcs_io.read_bytes, fresh_pcs_io.read_ns), (0, 0, 0));
        if record.address.core_ordinal == 10 {
            assert!(continuation_matches);
            assert_eq!(serde_json::to_value(two_bank_hex_point(&verified_claim.point)).unwrap(), frozen_far_result["producer"]["proof_point_hex"]);
            assert_eq!(hex_bytes(&crate::pcs::encode(&verified_claim.value).unwrap()), frozen_far_result["producer"]["claim_value_hex"].as_str().unwrap());
        }
        all_fresh_gkr_reads.0 += fresh_gkr_io.read_calls;
        all_fresh_gkr_reads.1 += fresh_gkr_io.read_bytes;
        all_fresh_gkr_reads.2 += fresh_gkr_io.read_ns;
        all_fresh_pcs_reads.0 += fresh_pcs_io.read_calls;
        all_fresh_pcs_reads.1 += fresh_pcs_io.read_bytes;
        all_fresh_pcs_reads.2 += fresh_pcs_io.read_ns;
        all_fresh_gkr_ms += fresh_gkr_ms;
        all_fresh_pcs_ms += fresh_pcs_ms;
        record.decoded_opening = Some(decoded_opening);
        record.verified_claim = Some(verified_claim.clone());
        record.verifier_transcript = Some(verifier_transcript);
        bank_results.push(json!({
            "core_ordinal": record.address.core_ordinal,
            "physical_bank": record.address.physical_index,
            "bank_start": record.address.start,
            "projected_point_hex": two_bank_hex_point(&record.claim.point),
            "parent_point_hex": two_bank_hex_point(&record.parent_point),
            "claim_value_hex": hex_bytes(&crate::pcs::encode(&record.claim.value).unwrap()),
            "gkr_proof_file": format!("core-bank-ordinal-{:02}-gkr-proof.bin", record.address.core_ordinal),
            "gkr_proof_bytes": record.encoded_proof.len(),
            "gkr_proof_blake2b256": work_tree_layout::hash_bytes(&record.encoded_proof),
            "parent_opening_file": format!("core-bank-ordinal-{:02}-parent-opening.bin", record.address.core_ordinal),
            "parent_opening_bytes": record.encoded_opening.len(),
            "parent_opening_blake2b256": work_tree_layout::hash_bytes(&record.encoded_opening),
            "producer_load_calls": record.load_calls,
            "producer_term_visit_passes": record.term_visit_passes,
            "producer_term_callbacks": record.term_callbacks,
            "parent_mle_matches_claim": record.claim.value == record.parent_mle_value,
            "fresh_gkr_claim_matches_producer": verified_claim == record.claim,
            "gkr_transcript_continuation_matches": continuation_matches,
            "fresh_pcs_verified": true,
            "timing_ms": {
                "gkr_producer": record.producer_ms,
                "parent_mle": record.parent_mle_ms,
                "dory_opening": record.opening_ms,
                "fresh_gkr_verify": fresh_gkr_ms,
                "fresh_pcs_verify": fresh_pcs_ms
            },
            "io": {
                "producer": packed_io_json(record.producer_io),
                "parent_mle": packed_io_json(record.parent_mle_io),
                "dory_opening": packed_io_json(record.opening_io),
                "fresh_gkr_verify": packed_io_json(fresh_gkr_io),
                "fresh_pcs_verify": packed_io_json(fresh_pcs_io)
            }
        }));
    }

    let mut wrong_selections = Vec::with_capacity(records.len());
    let bank14_record_index = records.iter().position(|record| record.address.core_ordinal == 10).unwrap();
    parent.reset_io_metrics();
    let mut negative_gkr_calls = 0usize;
    let mut negative_pcs_calls = 0usize;
    let mut negative_bind_calls = 0usize;
    let mut negative_challenges = 0u64;
    for record in &records {
        let wrong_address = FAR_BANK_MAPPING[(record.address.core_ordinal + 1) % FAR_BANK_MAPPING.len()];
        let wrong_spec = FarBankSpec { selected_bank: wrong_address, ..FAR_BANK_SPEC };
        let evidence = far_bank_prefix_negative(
            &core, &core_digest, wrong_spec, &setup_id, &commitment_bytes,
            record.decoded_proof.as_ref().unwrap(),
        );
        assert_eq!(evidence.rejected_by, "fresh_gkr_verifier");
        assert_eq!(evidence.error, "GKR error: SumcheckIdentity");
        assert_eq!((evidence.gkr_verify_calls, evidence.pcs_verify_calls, evidence.bind_calls), (1, 0, 1));
        assert!(evidence.challenge_count > 0);
        negative_gkr_calls += evidence.gkr_verify_calls;
        negative_pcs_calls += evidence.pcs_verify_calls;
        negative_bind_calls += evidence.bind_calls;
        negative_challenges += evidence.challenge_count;
        wrong_selections.push(json!({
            "core_ordinal": record.address.core_ordinal,
            "physical_bank": record.address.physical_index,
            "bank_start": record.address.start,
            "wrong_selected_bank": {
                "core_ordinal": wrong_address.core_ordinal,
                "physical_bank": wrong_address.physical_index,
                "bank_start": wrong_address.start
            },
            "evidence": far_bank_negative_json(&evidence)
        }));
    }
    let bank14 = &records[bank14_record_index];
    let wrong_commitment = far_bank_prefix_negative(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &alternate_commitment_bytes,
        bank14.decoded_proof.as_ref().unwrap(),
    );
    assert_eq!(wrong_commitment.rejected_by, "fresh_gkr_verifier");
    assert_eq!(wrong_commitment.error, "GKR error: SumcheckIdentity");
    assert_eq!((wrong_commitment.gkr_verify_calls, wrong_commitment.pcs_verify_calls, wrong_commitment.bind_calls), (1, 0, 1));
    assert!(wrong_commitment.challenge_count > 0);
    negative_gkr_calls += wrong_commitment.gkr_verify_calls;
    negative_pcs_calls += wrong_commitment.pcs_verify_calls;
    negative_bind_calls += wrong_commitment.bind_calls;
    negative_challenges += wrong_commitment.challenge_count;

    let wrong_parent_point = far_bank_pcs_negative(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        bank14.decoded_proof.as_ref().unwrap(), &parent_commitment,
        bank14.decoded_opening.as_ref().unwrap(), &verifier_key, true,
    );
    let wrong_claim_value = far_bank_pcs_negative(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        bank14.decoded_proof.as_ref().unwrap(), &parent_commitment,
        bank14.decoded_opening.as_ref().unwrap(), &verifier_key, false,
    );
    for evidence in [&wrong_parent_point, &wrong_claim_value] {
        assert_eq!(evidence.rejected_by, "pcs_consumer");
        assert_eq!(evidence.error, "Invalid proof");
        assert_eq!((evidence.gkr_verify_calls, evidence.pcs_verify_calls, evidence.bind_calls), (1, 1, 1));
        assert!(evidence.challenge_count > 0);
        negative_gkr_calls += evidence.gkr_verify_calls;
        negative_pcs_calls += evidence.pcs_verify_calls;
        negative_bind_calls += evidence.bind_calls;
        negative_challenges += evidence.challenge_count;
    }
    let negative_consumers_io = parent.io_metrics_snapshot();
    assert_eq!((negative_consumers_io.read_calls, negative_consumers_io.read_bytes, negative_consumers_io.read_ns), (0, 0, 0));
    drop(parent);
    assert_eq!(negative_gkr_calls, FAR_BANK_MAPPING.len() + 3);
    assert_eq!(negative_pcs_calls, 2);
    assert_eq!(negative_bind_calls, FAR_BANK_MAPPING.len() + 3);
    assert!(negative_challenges > 0);

    let bank14_claim = bank14.verified_claim.as_ref().unwrap();
    let bank14_parent_point_hex = two_bank_hex_point(&bank14.parent_point);
    let bank14_claim_value_hex = hex_bytes(&crate::pcs::encode(&bank14_claim.value).unwrap());
    assert_eq!(bank14.encoded_proof, frozen_far_proof_bytes);
    assert_eq!(bank14.encoded_opening, frozen_far_opening_bytes);
    let bank14_anchor = json!({
        "core_ordinal": 10,
        "gkr_proof_matches_frozen_bytes": bank14.encoded_proof == frozen_far_proof_bytes,
        "parent_opening_matches_frozen_bytes": bank14.encoded_opening == frozen_far_opening_bytes,
        "claim_matches_frozen_point_and_value": serde_json::to_value(two_bank_hex_point(&bank14_claim.point)).unwrap() == frozen_far_result["producer"]["proof_point_hex"]
            && serde_json::to_value(&bank14_parent_point_hex).unwrap() == frozen_far_result["producer"]["embedded_parent_point_hex"]
            && bank14_claim_value_hex == frozen_far_result["producer"]["claim_value_hex"].as_str().unwrap(),
        "transcript_continuation_matches": bank14.transcript_continuation_matches
            && bank14.prover_post_gkr.challenges() == bank14.verifier_transcript.as_ref().unwrap().challenges()
            && bank14.prover_post_gkr.raw_queries() == bank14.verifier_transcript.as_ref().unwrap().raw_queries()
            && frozen_far_result["producer"]["transcript_continuation_matches"].as_bool() == Some(true)
    });

    let mut mutated_bank14_parent_point = bank14.parent_point.clone();
    mutated_bank14_parent_point[CORE_INPUT_BITS + 1] += Fr::one();
    let mutated_parent_point_hex = two_bank_hex_point(&mutated_bank14_parent_point);
    let mapping_json: Vec<_> = FAR_BANK_MAPPING.iter().map(|address| json!({
        "core_ordinal": address.core_ordinal,
        "physical_bank": address.physical_index,
        "bank_start": address.start,
    })).collect();
    let all_bank_fresh_gkr_io = json!({ "read_calls": all_fresh_gkr_reads.0, "read_bytes": all_fresh_gkr_reads.1, "read_ns": all_fresh_gkr_reads.2 });
    let all_bank_fresh_pcs_io = json!({ "read_calls": all_fresh_pcs_reads.0, "read_bytes": all_fresh_pcs_reads.1, "read_ns": all_fresh_pcs_reads.2 });
    let all_bank_producer_io = json!({ "read_calls": all_producer_reads.0, "read_bytes": all_producer_reads.1, "read_ns": all_producer_reads.2 });
    let all_bank_parent_mle_io = json!({ "read_calls": all_parent_mle_reads.0, "read_bytes": all_parent_mle_reads.1, "read_ns": all_parent_mle_reads.2 });
    let all_bank_dory_opening_io = json!({ "read_calls": all_opening_reads.0, "read_bytes": all_opening_reads.1, "read_ns": all_opening_reads.2 });
    let artifact_started = Instant::now();
    for record in &records {
        let proof_name = format!("core-bank-ordinal-{:02}-gkr-proof.bin", record.address.core_ordinal);
        let opening_name = format!("core-bank-ordinal-{:02}-parent-opening.bin", record.address.core_ordinal);
        write_new_pcs_artifact(&artifact_directory, &proof_name, &record.encoded_proof);
        write_new_pcs_artifact(&artifact_directory, &opening_name, &record.encoded_opening);
    }
    let artifact_writes_ms = artifact_started.elapsed().as_millis();
    assert_eq!(fs::read_dir(&artifact_directory).unwrap().count(), 22);
    let whole_test_ms = whole_started.elapsed().as_millis();
    let result = json!({
        "schema": "native-all-core-parent-pcs-v1",
        "test": ALL_CORE_PARENT_PCS_TEST_NAME,
        "scope": "all eleven canonical Window16 compression-bank statements and original parent-commitment consumers; bounded diagnostic only",
        "source": {
            "file_sha256": SOURCE_SHA256,
            "bytes": SOURCE_BYTES,
            "owner_count": OWNER_COUNT,
            "parent_point_bits": PARENT_LOG_N
        },
        "relation": {
            "core_term_digest_blake2b256": core_digest,
            "core_terms": CORE_TERMS,
            "core_input_bits": CORE_INPUT_BITS,
            "core_row_bits": CORE_ROW_BITS,
            "owner_bits": SLOT_BITS,
            "family_bits": 0,
            "bank_width": BANK_WIDTH,
            "producer_cache_policy": "existing-default-incremental-cache",
            "producer_cache_budget_bytes": sparse_stream_roster::MAX_INCREMENTAL_CACHE_STATE_BYTES,
            "bank_mapping": mapping_json
        },
        "identity": {
            "original_pcs_artifact_directory_env": COMMON_PCS_ARTIFACT_DIR_ENV,
            "input_receipt_sha256": ALL_CORE_PARENT_PCS_IDENTITY_INPUTS_SHA256,
            "setup_id_hex": setup_id_hex,
            "commitment_file": COMMON_PCS_COMMITMENT_FILE,
            "commitment_bytes": commitment_bytes.len(),
            "commitment_sha256": ALL_CORE_PARENT_PCS_COMMITMENT_SHA256,
            "verifier_key_file": COMMON_PCS_KEY_FILE,
            "verifier_key_bytes": reference_key_bytes.len(),
            "verifier_key_sha256": ALL_CORE_PARENT_PCS_KEY_SHA256,
            "public_admit_24_still_rejected": true,
            "public_admit_24_error": public_admit_24_error
        },
        "setup": {
            "setup_id_matches_original": setup_id_hex == ALL_CORE_PARENT_PCS_SETUP_ID_HEX,
            "verifier_key_bytes_match_original": verifier_key_bytes == reference_key_bytes,
            "commitment_bytes_match_original": commitment_bytes == reference_commitment_bytes,
            "setup_reconstruction_ms": setup_reconstruction_ms,
            "verifier_key_encoding_ms": verifier_key_encoding_ms,
            "commitment_ms": commitment_ms,
            "commitment_io": packed_io_json(commitment_io)
        },
        "reference": {
            "reference_input_receipt_sha256": ALL_CORE_PARENT_PCS_REFERENCE_INPUTS_SHA256,
            "reference_directory_env": FIXED_V_REFERENCE_DIR_ENV,
            "bank14_core_ordinal": 10,
            "bank14_physical_bank": 14,
            "bank14_start": 917_504,
            "bank14_gkr_proof_file": "far-bank-gkr-proof.bin",
            "bank14_gkr_proof_bytes": frozen_far_proof_bytes.len(),
            "bank14_gkr_proof_sha256": ALL_CORE_PARENT_PCS_FAR_PROOF_SHA256,
            "bank14_parent_opening_file": "far-bank-parent-opening.bin",
            "bank14_parent_opening_bytes": frozen_far_opening_bytes.len(),
            "bank14_parent_opening_sha256": ALL_CORE_PARENT_PCS_FAR_OPENING_SHA256
        },
        "banks": bank_results,
        "bank14_anchor": bank14_anchor,
        "aggregates": {
            "bank_count": records.len(),
            "producer_load_calls": all_producer_load_calls,
            "producer_term_visit_passes": all_term_visit_passes,
            "producer_term_callbacks": all_term_callbacks,
            "fresh_gkr_verifications": records.len(),
            "fresh_pcs_verifications": records.len()
        },
        "negative": {
            "per_bank_nonzero_output_mutation": output_mutations,
            "per_bank_wrong_valid_selection": wrong_selections,
            "wrong_valid_commitment": {
                "core_ordinal": 10,
                "valid_commitment_roundtrip": crate::pcs::decode_commitment(&alternate_commitment_bytes).unwrap() == alternate_commitment,
                "evidence": far_bank_negative_json(&wrong_commitment)
            },
            "wrong_parent_point": {
                "core_ordinal": 10,
                "mutated_parent_point_hex": mutated_parent_point_hex,
                "evidence": far_bank_negative_json(&wrong_parent_point)
            },
            "wrong_claim_value": {
                "core_ordinal": 10,
                "mutated_claim_value_hex": hex_bytes(&crate::pcs::encode(&(bank14_claim.value + Fr::one())).unwrap()),
                "evidence": far_bank_negative_json(&wrong_claim_value)
            }
        },
        "timing_ms": {
            "whole_test": whole_test_ms,
            "setup_reconstruction": setup_reconstruction_ms,
            "verifier_key_encoding": verifier_key_encoding_ms,
            "commitment": commitment_ms,
            "all_bank_gkr_producers": all_producer_ms,
            "all_bank_parent_mle": all_parent_mle_ms,
            "all_bank_dory_openings": all_opening_ms,
            "all_bank_fresh_gkr_verification": all_fresh_gkr_ms,
            "all_bank_fresh_pcs_verification": all_fresh_pcs_ms,
            "artifact_writes": artifact_writes_ms
        },
        "io": {
            "source_open": packed_io_json(source_open_io),
            "commitment": packed_io_json(commitment_io),
            "all_bank_producers": all_bank_producer_io,
            "all_bank_parent_mle": all_bank_parent_mle_io,
            "all_bank_dory_openings": all_bank_dory_opening_io,
            "all_bank_fresh_gkr_verify": all_bank_fresh_gkr_io,
            "all_bank_fresh_pcs_verify": all_bank_fresh_pcs_io,
            "negative_consumers": packed_io_json(negative_consumers_io)
        },
        "global_proof": false,
        "pcs_scope": "bounded diagnostic only"
    });
    let result_bytes = serde_json::to_vec_pretty(&result).expect("serialize exact all-core result schema");
    write_new_pcs_artifact(&artifact_directory, ALL_CORE_PARENT_PCS_RESULT_FILE, &result_bytes);
    assert_eq!(fs::read_dir(&artifact_directory).unwrap().count(), 23);
    println!("{}{}", ALL_CORE_PARENT_PCS_RESULT_PREFIX, serde_json::to_string(&result).unwrap());
}

const SELECTED_HEADER_TEST: &str = "native_window16_selected_header_owner7_authenticates_original_parent_commitment_pcs24";
const SELECTED_HEADER_DOMAIN: &[u8] = b"nipopow-v2-selected-header-owner7-parent-pcs-v1";
const SELECTED_HEADER_ARTIFACT_ENV: &str = "NIPOPOW_SELECTED_HEADER_PARENT_PCS_ARTIFACT_DIR";
const SELECTED_HEADER_PREFIX_ENV: &str = "NIPOPOW_SELECTED_HEADER_PREFIX_FILE";
const SELECTED_HEADER_INPUT_RECEIPT: &str = "7D06E75833DE5319F4532A6E8AAFFFA0703918A21CA4D3A0AD9E6B3AAD56D5B8";
const SELECTED_HEADER_SETUP_ID: &str = "b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe";
const SELECTED_HEADER_COMMITMENT_SHA256: &str = "E87D71503ED0117D3D234293DCF72CBED2758DA652610B846119EA1C92E5D6DD";
const SELECTED_HEADER_KEY_SHA256: &str = "3D77BC139351C2832EA098B9E683961C171D918708300121145F0DABFBB48740";
const SELECTED_HEADER_PREFIX_SHA256: &str = "ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const SELECTED_HEADER_RAW_ID: &str = "fce2c5727951945ac4d2bc7136d9c9292ee51c88e2bd8b7d169cc558dfcacac4";
const SELECTED_HEADER_ROW_ID: &str = "9cc2625d8eb53a2ef9b4c80bed0075d49a4dbbe470e427c97b37046c9aa09af5";
const SELECTED_HEADER_RETAINED_PROOF: &str = "selected-header-retained-gkr-proof.bin";
const SELECTED_HEADER_RETAINED_OPENING: &str = "selected-header-retained-parent-opening.bin";
const SELECTED_HEADER_POINTS_PROOF: &str = "selected-header-points-gkr-proof.bin";
const SELECTED_HEADER_POINTS_OPENING: &str = "selected-header-points-parent-opening.bin";
const SELECTED_HEADER_RESULT: &str = "selected-header-parent-pcs-result.json";
const SELECTED_OWNER: usize = 7;
const SELECTED_HEADERS: u64 = 3073;
const SELECTED_SLOT_LOG: usize = 12;
const SELECTED_INPUT_BITS: usize = 20;
const SELECTED_OWNER_COORDINATE_BITS: usize = PARENT_LOG_N - SELECTED_INPUT_BITS;
const SELECTED_ROW_BITS: usize = 19;
const SELECTED_POINT_BITS: usize = 13;
const SELECTED_POINT_OFFSET: usize = 786432;
const SELECTED_POINT_WIDTH: usize = 8192;
const SELECTED_RETAINED_TERMS: usize = 396561;
const SELECTED_ANCHOR_TERMS: usize = 256;
const SELECTED_RETAINED_PROOF_BYTES: usize = 4576;
const SELECTED_POINTS_PROOF_BYTES: usize = 3008;
const SELECTED_OPENING_BYTES: usize = 32013;

struct SelectedNativeHeader {
    raw: Vec<u8>,
    previous_raw: Vec<u8>,
}

fn selected_header_prefix_entry(prefix: &[u8], wanted: usize) -> Result<Vec<u8>, String> {
    let mut offset = 0usize;
    let mut found = None;
    for index in 0..SELECTED_HEADERS as usize {
        let len_end = offset.checked_add(4).ok_or("prefix length offset overflow")?;
        let len_bytes: [u8; 4] = prefix.get(offset..len_end).ok_or("prefix lacks u32 length")?
            .try_into().map_err(|_| "prefix length width")?;
        let len = u32::from_le_bytes(len_bytes) as usize;
        if !(1..=514).contains(&len) { return Err("prefix header length outside native bound".into()); }
        offset = len_end;
        let end = offset.checked_add(len).ok_or("prefix header offset overflow")?;
        let raw = prefix.get(offset..end).ok_or("prefix header truncated")?.to_vec();
        if index == wanted { found = Some(raw); }
        offset = end;
    }
    if offset != prefix.len() { return Err("prefix has trailing bytes".into()); }
    found.ok_or_else(|| "prefix requested header absent".into())
}

fn selected_header_plan(root: [u8; 32], total: [u8; 28]) -> crate::work_tree_history_plan::WorkTreeHistoryPlan {
    crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        SELECTED_HEADERS, SELECTED_SLOT_LOG, root, total,
    ).expect("compile canonical selected-header WorkTree plan")
}

fn selected_header_root_total() -> ([u8; 32], [u8; 28]) {
    let root = [0xdf,0x3c,0x1d,0x55,0x5f,0xcf,0x6d,0x2a,0x5b,0xa6,0x20,0x42,0x2d,0x10,0x07,0xa8,
        0x5c,0xa5,0xf8,0x96,0x8d,0x6f,0x60,0x8c,0x98,0x56,0xce,0x32,0x6c,0x44,0x89,0x13];
    let total = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x56,0x4f,0x0b,0x9b,0,0,0];
    (root, total)
}

fn selected_header_circuit(
    plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    id: [u8; 32],
) -> (SparseCircuit, String) {
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(plan)
        .expect("compile code-owned DAA header roster");
    assert_eq!(roster.owner_class(SELECTED_OWNER as u64).unwrap(), crate::daa_history_roster::OwnerClass::Carry);
    let mut terms = Vec::with_capacity(SELECTED_RETAINED_TERMS + SELECTED_ANCHOR_TERMS);
    let row_base = SELECTED_OWNER.checked_mul(1usize << SELECTED_ROW_BITS).unwrap();
    let input_base = SELECTED_OWNER.checked_mul(1usize << SELECTED_INPUT_BITS).unwrap();
    let counts = roster.visit_header_terms(SELECTED_OWNER as u64, |term| {
        let row = term.row.checked_sub(row_base).ok_or("selected header row precedes owner")?;
        let left = term.gate.left.checked_sub(input_base).ok_or("selected header left precedes owner")?;
        let right = term.gate.right.checked_sub(input_base).ok_or("selected header right precedes owner")?;
        terms.push(Term { row, gate: crate::gkr::Gate { left, right, ..term.gate } });
        Ok(())
    }).expect("emit complete retained owner header relation");
    assert_eq!(counts.emitted, SELECTED_RETAINED_TERMS);
    assert_eq!(counts.omitted_worktree, 78_194);
    assert_eq!(counts.omitted_mature_a4, 0);
    assert_eq!(counts.omitted_short_a4, 0, "Carry owner must not release A4");
    assert_eq!(counts.emitted + counts.omitted_worktree + counts.omitted_mature_a4, 474_755);
    let public_id_anchor_start = (1usize << SELECTED_ROW_BITS) - SELECTED_ANCHOR_TERMS;
    assert!(terms.iter().all(|term| term.row < public_id_anchor_start),
        "retained owner terms must leave the native-ID anchor tail unused");
    assert!(terms.windows(2).all(|pair| pair[0].row <= pair[1].row),
        "retained source endpoints must remain sorted by row");
    for bit in 0..SELECTED_ANCHOR_TERMS {
        let expected = (id[bit / 8] >> (bit % 8)) & 1;
        terms.push(Term {
            row: (1usize << SELECTED_ROW_BITS) - SELECTED_ANCHOR_TERMS + bit,
            gate: crate::gkr::Gate {
                left: crate::segment_relation::DIGEST_OFFSET + bit,
                right: 0,
                c0: -Fr::from(expected as u64),
                c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
            },
        });
    }
    assert_eq!(terms.len(), SELECTED_RETAINED_TERMS + SELECTED_ANCHOR_TERMS);
    assert!(terms.iter().all(|term| term.row < (1usize << SELECTED_ROW_BITS)
        && term.gate.left < (1usize << SELECTED_INPUT_BITS)
        && term.gate.right < (1usize << SELECTED_INPUT_BITS)),
        "retained source and native-ID endpoints must remain in local bounds");
    assert!(terms.windows(2).all(|pair| pair[0].row <= pair[1].row),
        "retained source and native-ID endpoints must remain sorted by row");
    let circuit = SparseCircuit { input_len: 1usize << SELECTED_INPUT_BITS,
        row_count: 1usize << SELECTED_ROW_BITS, terms };
    let shape = sparse::validate(&circuit, 0).expect("validate selected retained circuit");
    assert_eq!((shape.input_bits, shape.row_bits), (SELECTED_INPUT_BITS, SELECTED_ROW_BITS));
    let digest = work_tree_layout::hash_terms(&circuit.terms);
    (circuit, digest)
}

fn selected_header_bind(
    transcript: &mut Transcript,
    plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    role: &str,
    circuit_digest: &str,
    public_id: &[u8; 32],
    owner: usize,
    setup_id: &[u8; 32],
    commitment: &[u8],
) {
    transcript.append_bytes(b"selected-header-relation", b"retained-history-and-point-membership-v1");
    transcript.append_bytes(b"selected-header-family-role", role.as_bytes());
    transcript.append_bytes(b"selected-header-native-id-blake2b256", public_id);
    transcript.append_bytes(b"selected-header-circuit-terms-blake2b256", circuit_digest.as_bytes());
    gkr::append_usize(transcript, b"selected-header-owner", owner);
    gkr::append_usize(transcript, b"selected-header-local-input-bits", if role == "retained_header" { SELECTED_INPUT_BITS } else { SELECTED_POINT_BITS });
    gkr::append_usize(transcript, b"selected-header-parent-point-bits", PARENT_LOG_N);
    plan.bind(transcript);
    transcript.append_bytes(b"common-parent-setup-id", setup_id);
    transcript.append_bytes(b"common-parent-commitment", commitment);
}

fn selected_header_parent_point(point: &[Fr], role: &str) -> Result<Vec<Fr>, String> {
    let mut parent = Vec::with_capacity(PARENT_LOG_N);
    if role == "retained_header" {
        if point.len() != SELECTED_INPUT_BITS { return Err("retained point dimension mismatch".into()); }
        parent.extend_from_slice(point);
    } else if role == "points" {
        if point.len() != SELECTED_POINT_BITS { return Err("point-membership point dimension mismatch".into()); }
        parent.extend_from_slice(point);
        parent.extend((0..7).map(|bit| Fr::from(((96usize >> bit) & 1) as u64)));
    } else { return Err("unknown selected-header family role".into()); }
    parent.extend((0..SELECTED_OWNER_COORDINATE_BITS).map(|bit| Fr::from(((SELECTED_OWNER >> bit) & 1) as u64)));
    if parent.len() != PARENT_LOG_N { return Err("selected parent point width mismatch".into()); }
    Ok(parent)
}

fn selected_header_verify(
    circuit: &SparseCircuit,
    circuit_digest: &str,
    plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    role: &str,
    public_id: &[u8; 32],
    owner: usize,
    setup_id: &[u8; 32],
    commitment: &[u8],
    proof: &GkrProof,
    transcript: &mut Transcript,
) -> Result<InputClaim, GkrError> {
    let mut bind_calls = 0usize;
    selected_header_verify_counted(circuit, circuit_digest, plan, role, public_id, owner,
        setup_id, commitment, proof, transcript, &mut bind_calls)
}

fn selected_header_verify_counted(
    circuit: &SparseCircuit,
    circuit_digest: &str,
    plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    role: &str,
    public_id: &[u8;32],
    owner: usize,
    setup_id: &[u8;32],
    commitment: &[u8],
    proof: &GkrProof,
    transcript: &mut Transcript,
    bind_calls: &mut usize,
) -> Result<InputClaim, GkrError> {
    let shape = sparse::validate(circuit, 0)?;
    gkr::verify_with_wiring(
        &[shape.input_bits], shape.row_count, proof, transcript,
        |transcript| {
            *bind_calls += 1;
            selected_header_bind(transcript, plan, role, circuit_digest, public_id, owner, setup_id, commitment)
        },
        |layer, r, u, v| if layer == 0 { sparse::wiring(circuit, &shape, r, u, v) } else { Err(GkrError::PointDimension) },
    )
}

fn selected_header_residuals(circuit: &SparseCircuit, input: &[Fr]) -> Vec<Fr> {
    assert_eq!(input.len(), circuit.input_len);
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms { rows[term.row] += term.gate.evaluate(input); }
    rows
}

fn selected_header_hex_point(point: &[Fr]) -> Vec<String> {
    point.iter().map(|value| hex_bytes(&crate::pcs::encode(value).unwrap())).collect()
}

fn selected_header_counter_evidence(kind: &str, error: String, gkr_calls: usize, pcs_calls: usize, bind_calls: usize, challenges: u64) -> serde_json::Value {
    json!({"rejected_by":kind,"error":error,"gkr_verify_calls":gkr_calls,
        "pcs_verify_calls":pcs_calls,"bind_calls":bind_calls,"challenge_count":challenges})
}

fn selected_header_residual_negative(
    circuit: &SparseCircuit, input: &[Fr], plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    role: &str, digest: &str, id: &[u8;32], setup_id: &[u8;32], commitment: &[u8], owner: usize,
) -> serde_json::Value {
    assert!(selected_header_residuals(circuit,input).iter().any(|value| !value.is_zero()),
        "{role} negative witness must affect a constrained residual");
    let mut transcript=Transcript::new(SELECTED_HEADER_DOMAIN);
    let mut bind_calls=0usize;
    let result=sparse::prove_with_binding(circuit,input,0,&mut transcript,|t|{
        bind_calls+=1; selected_header_bind(t,plan,role,digest,id,owner,setup_id,commitment)
    });
    let error=match result {
        Ok(_) => panic!("{role} nonzero residual unexpectedly admitted"),
        Err(error) => error,
    };
    assert_eq!(error,GkrError::NonzeroOutput);
    assert_eq!((bind_calls,transcript.challenges()),(0,0));
    selected_header_counter_evidence("residual_guard",GkrError::NonzeroOutput.to_string(),0,0,bind_calls,transcript.challenges())
}

fn selected_header_fresh_verify(
    circuit: &SparseCircuit,
    digest: &str,
    plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    role: &str,
    id: &[u8;32],
    setup_id: &[u8;32],
    commitment_bytes: &[u8],
    decoded_proof: &GkrProof,
) -> (InputClaim, Vec<Fr>, Transcript, u128) {
    let mut transcript = Transcript::new(SELECTED_HEADER_DOMAIN);
    let gkr_started = Instant::now();
    let claim = selected_header_verify(circuit, digest, plan, role, id, SELECTED_OWNER, setup_id,
        commitment_bytes, decoded_proof, &mut transcript).expect("fresh selected-family GKR verify");
    let gkr_ms = gkr_started.elapsed().as_millis();
    let parent_point = selected_header_parent_point(&claim.point, role).unwrap();
    (claim,parent_point,transcript,gkr_ms)
}

#[test]
fn native_window16_selected_header_owner7_authenticates_original_parent_commitment_pcs24() {
    let whole_started = Instant::now();
    // PARENT_OWNER_BITS is the address width within a row, not its owner coordinates.
    assert_eq!(SELECTED_OWNER_COORDINATE_BITS, SLOT_BITS);
    let owner_coordinates = [Fr::one(), Fr::one(), Fr::one(), Fr::zero()];
    for (role, local_bits) in [("retained_header", SELECTED_INPUT_BITS), ("points", SELECTED_POINT_BITS)] {
        let local: Vec<Fr> = (0..local_bits).map(|bit| Fr::from((bit + 2) as u64)).collect();
        let embedded = selected_header_parent_point(&local, role).expect("preproof selected embedding");
        assert_eq!(embedded.len(), PARENT_LOG_N);
        assert_eq!(&embedded[..local_bits], local.as_slice());
        assert_eq!(&embedded[SELECTED_INPUT_BITS..], &owner_coordinates);
        if role == "points" {
            assert_eq!(&embedded[SELECTED_POINT_BITS..SELECTED_INPUT_BITS],
                &[Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::one(), Fr::one()]);
        }
        assert!(selected_header_parent_point(&local[..local_bits - 1], role).is_err());
        let mut oversized = local.clone(); oversized.push(Fr::zero());
        assert!(selected_header_parent_point(&oversized, role).is_err());
    }
    assert!(selected_header_parent_point(&[], "unknown").is_err());
    let artifact_dir = std::env::var(SELECTED_HEADER_ARTIFACT_ENV).expect("runner pins selected-header artifact dir");
    assert_eq!(fs::read_dir(&artifact_dir).unwrap().count(), 0);
    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE").expect("runner pins Window16");
    let prefix_path = std::env::var(SELECTED_HEADER_PREFIX_ENV).expect("runner pins native prefix");
    let pcs_dir = std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV).expect("runner pins original TEST24 key/commitment");
    let prefix = fs::read(prefix_path).expect("read pinned u32LE native prefix");
    assert_eq!(prefix.len(), 869449);
    let prefix_bytes=prefix.len();
    let raw = selected_header_prefix_entry(&prefix, SELECTED_OWNER).expect("extract native header8");
    let raw_header_bytes=raw.len();
    let previous_raw = selected_header_prefix_entry(&prefix, SELECTED_OWNER - 1).expect("extract native header7");
    let id = ergo_header_core::blake2b256(&raw);
    assert_eq!(hex_bytes(&id), SELECTED_HEADER_RAW_ID);
    let header = ergo_header_core::Header::decode(&raw, None).expect("decode selected native header");
    let previous_id = ergo_header_core::blake2b256(&previous_raw);
    let previous = ergo_header_core::Header::decode(&previous_raw, None).expect("decode predecessor");
    assert_eq!(header.height, 8);
    let fields = crate::serializer::Fields::from_header(&header).expect("selected native serializer fields");
    assert_eq!(header.encode().unwrap(), raw);
    let source_open_started = Instant::now();
    let parent = PackedFile::open(&source_path, PARENT_LOG_N).expect("open pinned Window16");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    let _source_open_ms = source_open_started.elapsed().as_millis();
    let source_open_io = parent.io_metrics_snapshot();
    assert_eq!((source_open_io.read_calls,source_open_io.read_bytes,source_open_io.read_ns),(0,0,0));
    let preproof_started = Instant::now();
    let mut owner_input = Vec::with_capacity(1usize << SELECTED_INPUT_BITS);
    for physical in 0..BANK_COPY_FACTOR {
        owner_input.extend(load_far_bank_owner(&parent, SELECTED_OWNER, physical).expect("read physical owner slice"));
    }
    assert_eq!(owner_input.len(), 1usize << SELECTED_INPUT_BITS);
    assert!(owner_input.iter().all(|x| x.is_zero() || x.is_one()));
    let owner_row_io = parent.io_metrics_snapshot();
    assert_eq!((owner_row_io.read_calls,owner_row_io.read_bytes),(16,131072));
    let packed_owner_bytes=owner_input.iter().enumerate().fold(vec![0u8; owner_input.len()/8], |mut b,(i,x)| {if x.is_one(){b[i/8]|=1<<(i%8);} b});
    assert_eq!(work_tree_layout::hash_bytes(&packed_owner_bytes), SELECTED_HEADER_ROW_ID);
    let mut point_input = owner_input[SELECTED_POINT_OFFSET..SELECTED_POINT_OFFSET+SELECTED_POINT_WIDTH].to_vec();
    let point_build_started=Instant::now();
    let point_compiled = crate::point_membership::build().expect("canonical point-membership circuit");
    let point_build_ms=point_build_started.elapsed().as_millis();
    assert_eq!((point_compiled.circuit.input_len,point_compiled.circuit.row_count,point_compiled.circuit.terms.len()),(8192,16384,288158));
    let point_digest=work_tree_layout::hash_terms(&point_compiled.circuit.terms);
    assert!(selected_header_residuals(&point_compiled.circuit,&point_input).iter().all(Zero::is_zero));
    let witness_bits = crate::point_membership::witness(fields.pk,fields.w).expect("native secp point witness");
    assert_eq!(point_input.iter().map(|x|x.is_one()).collect::<Vec<_>>(),witness_bits);
    let hash_template = crate::header_hash::build(None,id).expect("canonical native digest template");
    let hash_assignment = crate::header_hash::assign_from_template(&hash_template.compression_layout,&hash_template.serializer,&fields)
        .expect("assign canonical serializer/hash ports");
    assert_eq!(hash_assignment.len(), crate::header_hash::GLOBAL_WIDTH);
    assert_eq!(hash_assignment.len(), owner_input.len());
    assert_eq!(&owner_input[crate::header_hash::SERIALIZER_OFFSET..crate::header_hash::AUX_OFFSET],
        &hash_assignment[crate::header_hash::SERIALIZER_OFFSET..crate::header_hash::AUX_OFFSET],
        "native serializer ports must match the canonical header assignment");
    for bit in 0..256 {
        let expected=(id[bit/8]>>(bit%8))&1;
        assert_eq!(owner_input[crate::segment_relation::DIGEST_OFFSET+bit],Fr::from(expected as u64));
    }
    let serializer_assignment = hash_template.serializer.assign(&fields);
    assert_eq!(&owner_input[crate::header_hash::SERIALIZER_OFFSET..crate::header_hash::AUX_OFFSET],&serializer_assignment);
    let serialized_length = hash_template.serializer.layout.length.iter().enumerate().fold(0usize, |length,(bit,&index)| {
        length | ((serializer_assignment[index].is_one() as usize) << bit)
    });
    assert_eq!(serialized_length,raw.len(),"canonical serializer length port must match native bytes");
    let order_witness=crate::header_order::witness(fields.height,fields.timestamp,previous.height,previous.timestamp,false)
        .expect("native selected header order witness");
    assert_eq!(owner_input[crate::header_order::ORDER_OFFSET..crate::header_order::ORDER_OFFSET+crate::header_order::ORDER_WIDTH]
        .iter().map(|x|x.is_one()).collect::<Vec<_>>(),order_witness);
    let (root,total)=selected_header_root_total();
    let plan_compile_started=Instant::now();
    let plan=selected_header_plan(root,total);
    assert_eq!(plan.headers(),SELECTED_HEADERS);
    assert_eq!(plan.slot_log(),SELECTED_SLOT_LOG);
    assert_eq!(plan.retirement_counts().terms,78194);
    let (retained_circuit,retained_digest)=selected_header_circuit(&plan,id);
    assert_eq!(retained_circuit.terms.len(),396817);
    assert!(selected_header_residuals(&retained_circuit,&owner_input).iter().all(Zero::is_zero),"selected retained-header residual");
    let plan_compile_ms=point_build_ms.saturating_add(plan_compile_started.elapsed().as_millis());
    let preproof_checks_ms=preproof_started.elapsed().as_millis().saturating_sub(plan_compile_ms);
    let retained_term_count=retained_circuit.terms.len();
    let point_term_count=point_compiled.circuit.terms.len();
    let point_used_bits=point_compiled.stats.used_bits;
    let point_residual_rows=point_compiled.stats.residual_rows;

    let key_path=std::path::Path::new(&pcs_dir).join(COMMON_PCS_KEY_FILE);
    let commitment_path=std::path::Path::new(&pcs_dir).join(COMMON_PCS_COMMITMENT_FILE);
    let reference_key=fs::read(key_path).expect("read original TEST24 key");
    let reference_commitment=fs::read(commitment_path).expect("read original parent commitment");
    assert_eq!(reference_key.len(),25584);
    assert_eq!(reference_commitment.len(),384);
    let setup_started=Instant::now();
    let setup=crate::pcs::generate_setup(PARENT_LOG_N).expect("reconstruct diagnostic TEST24 setup");
    let setup_reconstruction_ms=setup_started.elapsed().as_millis();
    let setup_id=setup.id;
    assert_eq!(hex_bytes(&setup_id),SELECTED_HEADER_SETUP_ID);
    let key_started=Instant::now();
    let verifier_key_bytes=crate::pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let verifier_key_encode_ms=key_started.elapsed().as_millis();
    assert_eq!(verifier_key_bytes,reference_key);
    let public_admit_24_error=match crate::verifier_key::admit(PARENT_LOG_N,&verifier_key_bytes) {
        Ok(_) => panic!("public admission must reject TEST24 dimension"),
        Err(error) => error,
    };
    assert_eq!(public_admit_24_error,"unsupported verifier-key dimension");
    parent.reset_io_metrics();
    let commitment_started=Instant::now();
    let committed=crate::packed::commit(&parent,&setup).expect("reconstruct original parent commitment");
    let commitment_ms=commitment_started.elapsed().as_millis();
    let commitment_io=parent.io_metrics_snapshot();
    let commitment_bytes=crate::pcs::encode_commitment(&committed.commitment).unwrap();
    assert_eq!(commitment_bytes,reference_commitment);
    let parent_commitment=crate::pcs::decode_commitment(&commitment_bytes).unwrap();
    let alternate_commitment=ArkGT(parent_commitment.0.clone()+setup.prover.ht.0.clone());
    assert_ne!(alternate_commitment,parent_commitment);
    let alternate_commitment_bytes=crate::pcs::encode_commitment(&alternate_commitment).unwrap();
    assert_eq!(crate::pcs::decode_commitment(&alternate_commitment_bytes).unwrap(),alternate_commitment);

    let retained_nonzero_output = {
        let mut bad_owner_input=owner_input.clone();
        bad_owner_input[crate::segment_relation::DIGEST_OFFSET]+=Fr::one();
        selected_header_residual_negative(&retained_circuit,&bad_owner_input,&plan,
            "retained_header",&retained_digest,&id,&setup_id,&commitment_bytes,SELECTED_OWNER)
    };
    let point_nonzero_output = {
        let mut bad_point_input=point_input.clone(); bad_point_input[0]+=Fr::one();
        selected_header_residual_negative(&point_compiled.circuit,&bad_point_input,&plan,
            "points",&point_digest,&id,&setup_id,&commitment_bytes,SELECTED_OWNER)
    };
    let mut changed_anchor_id=id; changed_anchor_id[0]^=1;
    let (changed_anchor_circuit,changed_anchor_digest)=selected_header_circuit(&plan,changed_anchor_id);
    let changed_public_id=selected_header_residual_negative(&changed_anchor_circuit,&owner_input,&plan,
        "retained_header",&changed_anchor_digest,&changed_anchor_id,&setup_id,&commitment_bytes,SELECTED_OWNER);
    drop(changed_anchor_circuit);

    let mut family_data=Vec::new();
    let mut family_inputs=vec![owner_input.clone(),point_input.clone()];
    let families=[("retained_header",&retained_circuit,retained_digest.as_str(),0usize),
        ("points",&point_compiled.circuit,point_digest.as_str(),1usize)];
    let mut producer_timings=Vec::new();
    let mut producer_ios=Vec::new();
    let mut parent_mle_timings=Vec::new();
    let mut parent_mle_ios=Vec::new();
    let mut opening_timings=Vec::new();
    let mut opening_ios=Vec::new();
    let mut producer_decoded_exact=Vec::new();
    for (role,circuit,digest,index) in families {
        let input=&family_inputs[index];
        let mut prover_transcript=Transcript::new(SELECTED_HEADER_DOMAIN);
        parent.reset_io_metrics();
        let started=Instant::now();
        let (proof,claim)=sparse::prove_with_binding(circuit,input,0,&mut prover_transcript,|t|
            selected_header_bind(t,&plan,role,digest,&id,SELECTED_OWNER,&setup_id,&commitment_bytes))
            .unwrap_or_else(|error|panic!("selected {role} GKR proof: {error}"));
        let producer_ms=started.elapsed().as_millis();
        let producer_io=parent.io_metrics_snapshot();
        assert_eq!((producer_io.read_calls,producer_io.read_bytes,producer_io.read_ns),(0,0,0));
        let mut post_gkr=prover_transcript.clone();
        let parent_point=selected_header_parent_point(&claim.point,role).unwrap();
        parent.reset_io_metrics();
        let mle_started=Instant::now();
        let mle=parent.evaluate(&parent_point).expect("selected claim parent MLE");
        let parent_mle_ms=mle_started.elapsed().as_millis();
        let parent_mle_io=parent.io_metrics_snapshot();
        let claim_matches_parent_mle=mle==claim.value;
        assert!(claim_matches_parent_mle);
        parent.reset_io_metrics();
        let opening_started=Instant::now();
        let opening=crate::packed::open(&committed,&parent,&parent_point,&setup,&mut post_gkr)
            .expect("open selected family under original commitment");
        let opening_ms=opening_started.elapsed().as_millis();
        let opening_io=parent.io_metrics_snapshot();
        let proof_bytes=gkr::encode_proof(&proof).unwrap();
        let expected_len=if role=="retained_header" {SELECTED_RETAINED_PROOF_BYTES} else {SELECTED_POINTS_PROOF_BYTES};
        assert_eq!(proof_bytes.len(),expected_len);
        let opening_bytes=crate::pcs::encode_proof(&opening).unwrap();
        assert_eq!(opening_bytes.len(),SELECTED_OPENING_BYTES);
        producer_decoded_exact.push(gkr::decode_dimensions(&[circuit.input_len.trailing_zeros() as usize],&proof_bytes).unwrap()==proof);
        family_data.push((role.to_owned(),proof_bytes,opening_bytes,claim,parent_point,post_gkr,mle));
        producer_timings.push(producer_ms); producer_ios.push(producer_io);
        parent_mle_timings.push(parent_mle_ms); parent_mle_ios.push(parent_mle_io);
        opening_timings.push(opening_ms); opening_ios.push(opening_io);
    }
    drop(family_inputs);
    drop(owner_input);
    drop(point_input);
    drop(point_compiled);
    drop(retained_circuit);
    drop(plan);
    drop(committed);
    drop(setup);
    drop(prefix);
    drop(raw);
    drop(previous_raw);
    drop(header);
    drop(previous);
    drop(fields);
    drop(hash_assignment);
    drop(serializer_assignment);
    drop(hash_template);
    drop(witness_bits);

    let fresh_started=Instant::now();
    let fresh_plan=selected_header_plan(root,total);
    let (fresh_retained,fresh_retained_digest)=selected_header_circuit(&fresh_plan,id);
    let fresh_points=crate::point_membership::build().expect("rebuild public point circuit");
    let fresh_point_digest=work_tree_layout::hash_terms(&fresh_points.circuit.terms);
    let key_admit_started=Instant::now();
    let admitted_key=crate::verifier_key::admit_generated_test_key(PARENT_LOG_N,&verifier_key_bytes,
        setup_id_from_hex(SELECTED_HEADER_SETUP_ID)).expect("fresh admit original stored TEST key");
    let _key_admit_ms=key_admit_started.elapsed().as_millis();
    let fresh_parent_commitment=crate::pcs::decode_commitment(&commitment_bytes).expect("fresh decode original parent commitment");
    let decoded_data: Vec<(GkrProof,dory_pcs::backends::arkworks::ArkDoryProof)> = family_data.iter().map(|family| {
        let dimension=if family.0=="retained_header" {SELECTED_INPUT_BITS} else {SELECTED_POINT_BITS};
        (gkr::decode_dimensions(&[dimension],&family.1).expect("fresh exact-dimension GKR proof decode"),
         crate::pcs::decode_proof(&family.2,PARENT_LOG_N).expect("fresh original parent-opening decode"))
    }).collect();
    let fresh_context_preparation_ms=fresh_started.elapsed().as_millis();
    let mut fresh_claims=Vec::new();
    let mut fresh_timings=Vec::new();
    let mut fresh_ios=Vec::new();
    let mut fresh_matches=Vec::new();
    for (index,(role,proof_bytes,opening_bytes,claim,parent_point,producer_transcript,_parent_mle)) in family_data.iter().enumerate() {
        let circuit=if index==0 {&fresh_retained} else {&fresh_points.circuit};
        let digest=if index==0 {fresh_retained_digest.as_str()} else {fresh_point_digest.as_str()};
        parent.reset_io_metrics();
        let (verified,embedded,mut verifier_transcript,gkr_ms)=selected_header_fresh_verify(
            circuit,digest,&fresh_plan,role,&id,&setup_id,&commitment_bytes,&decoded_data[index].0);
        let gkr_io=parent.io_metrics_snapshot();
        assert_eq!((gkr_io.read_calls,gkr_io.read_bytes,gkr_io.read_ns),(0,0,0));
        assert_eq!(verified,*claim);
        assert_eq!(embedded,*parent_point);
        parent.reset_io_metrics();
        let pcs_started=Instant::now();
        crate::pcs::verify_admitted(fresh_parent_commitment.clone(),verified.value,
            &embedded,&decoded_data[index].1,&admitted_key,&mut verifier_transcript)
            .expect("fresh original TEST24 PCS consumer");
        let pcs_ms=pcs_started.elapsed().as_millis();
        let pcs_io=parent.io_metrics_snapshot();
        assert_eq!((pcs_io.read_calls,pcs_io.read_bytes,pcs_io.read_ns),(0,0,0));
        let mut p=producer_transcript.clone();let mut v=verifier_transcript.clone();
        let continuation=p.challenge_scalar(b"selected-header-post-gkr")==v.challenge_scalar(b"selected-header-post-gkr")
            && p.challenges()==v.challenges() && p.raw_queries()==v.raw_queries() && p.bytes_absorbed()==v.bytes_absorbed();
        assert!(continuation);
        fresh_matches.push((verified==*claim,continuation));
        assert_eq!(verified,*claim);
        assert_eq!(embedded,*parent_point);
        fresh_claims.push((verified,embedded,verifier_transcript));
        fresh_timings.push((gkr_ms,pcs_ms));fresh_ios.push((gkr_io,pcs_io));
    }
    assert_eq!(fresh_claims.len(),2);

    let mut family_values=Vec::new();
    for (index,(role,proof_bytes,opening_bytes,claim,parent_point,_,mle)) in family_data.iter().enumerate() {
        let input_bits=if index==0 {SELECTED_INPUT_BITS} else {SELECTED_POINT_BITS};
        let row_bits=if index==0 {SELECTED_ROW_BITS} else {14};
        let term_count=if index==0 {retained_term_count} else {point_term_count};
        let digest=if index==0 {retained_digest.as_str()} else {point_digest.as_str()};
        let proof_file=if index==0 {SELECTED_HEADER_RETAINED_PROOF} else {SELECTED_HEADER_POINTS_PROOF};
        let opening_file=if index==0 {SELECTED_HEADER_RETAINED_OPENING} else {SELECTED_HEADER_POINTS_OPENING};
        let opening_hash=work_tree_layout::hash_bytes(opening_bytes);
        family_values.push(json!({"role":role,"local_input_bits":input_bits,"local_row_bits":row_bits,"circuit_terms":term_count,
            "circuit_blake2b256":digest,"proof_file":proof_file,"proof_bytes":proof_bytes.len(),
            "proof_blake2b256":work_tree_layout::hash_bytes(proof_bytes),"decoded_exact_dimensions":producer_decoded_exact[index],
            "proof_point_hex":selected_header_hex_point(&claim.point),"parent_point_hex":selected_header_hex_point(parent_point),
            "claim_value_hex":hex_bytes(&crate::pcs::encode(&claim.value).unwrap()),"parent_mle_value_hex":hex_bytes(&crate::pcs::encode(mle).unwrap()),
            "claim_matches_parent_mle":claim.value==*mle,"claim_matches_fresh_gkr_verifier":fresh_matches[index].0,
            "transcript_continuation_matches":fresh_matches[index].1,"fresh_gkr_verified":fresh_matches[index].0,
            "parent_opening_file":opening_file,"parent_opening_bytes":opening_bytes.len(),"parent_opening_blake2b256":opening_hash,
            "fresh_pcs_verified_with_original_test_key":true,
            "timing_ms":{"gkr_producer":producer_timings[index],"parent_mle":parent_mle_timings[index],"dory_opening":opening_timings[index],
                "fresh_gkr_verify":fresh_timings[index].0,"fresh_pcs_verify":fresh_timings[index].1},
            "io":{"producer":packed_io_json(producer_ios[index]),"parent_mle":packed_io_json(parent_mle_ios[index]),
                "dory_opening":packed_io_json(opening_ios[index]),"fresh_gkr_verify":packed_io_json(fresh_ios[index].0),
                "fresh_pcs_verify":packed_io_json(fresh_ios[index].1)}}));
    }

    let mut negative_io_reads=0u64;
    let mut verify_gkr_negative = |role: &str, mutated_role: &str, owner: usize, changed_id: [u8;32], commitment: &[u8]| -> serde_json::Value {
        let (index,family)=if role=="retained_header" {(0usize,&family_data[0])} else {(1usize,&family_data[1])};
        let circuit=if index==0 {&fresh_retained} else {&fresh_points.circuit};
        let digest=if index==0 {fresh_retained_digest.as_str()} else {fresh_point_digest.as_str()};
        let proof=gkr::decode_dimensions(&[if index==0 {SELECTED_INPUT_BITS} else {SELECTED_POINT_BITS}],&family.1).unwrap();
        let mut transcript=Transcript::new(SELECTED_HEADER_DOMAIN); let mut binds=0usize;
        parent.reset_io_metrics();
        let result=selected_header_verify_counted(circuit,digest,&fresh_plan,mutated_role,&changed_id,owner,&setup_id,commitment,&proof,&mut transcript,&mut binds);
        let error=result.unwrap_err(); assert_eq!(error.to_string(),"GKR error: SumcheckIdentity");
        assert_eq!(binds,1); assert!(transcript.challenges()>0);
        let io=parent.io_metrics_snapshot(); assert_eq!((io.read_calls,io.read_bytes,io.read_ns),(0,0,0)); negative_io_reads+=io.read_calls;
        selected_header_counter_evidence("fresh_gkr_verifier",error.to_string(),1,0,binds,transcript.challenges())
    };
    let mut wrong_id=id; wrong_id[0]^=1;
    let wrong_retained_role=verify_gkr_negative("retained_header","points",SELECTED_OWNER,id, &commitment_bytes);
    let wrong_point_role=verify_gkr_negative("points","retained_header",SELECTED_OWNER,id, &commitment_bytes);
    let wrong_owner=verify_gkr_negative("retained_header","retained_header",SELECTED_OWNER+1,id,&commitment_bytes);
    let wrong_public_id=verify_gkr_negative("retained_header","retained_header",SELECTED_OWNER,wrong_id,&commitment_bytes);
    let wrong_commitment=verify_gkr_negative("retained_header","retained_header",SELECTED_OWNER,id,&alternate_commitment_bytes);
    drop(verify_gkr_negative);

    let mut pcs_negative = |index: usize, wrong_point: bool| -> serde_json::Value {
        let (role,proof_bytes,opening_bytes,expected_claim,expected_parent_point,_,_)=&family_data[index];
        let circuit=if index==0 {&fresh_retained} else {&fresh_points.circuit};
        let digest=if index==0 {fresh_retained_digest.as_str()} else {fresh_point_digest.as_str()};
        let dimension=if index==0 {SELECTED_INPUT_BITS} else {SELECTED_POINT_BITS};
        let proof=gkr::decode_dimensions(&[dimension],proof_bytes).unwrap();
        let opening=crate::pcs::decode_proof(opening_bytes,PARENT_LOG_N).unwrap();
        let mut transcript=Transcript::new(SELECTED_HEADER_DOMAIN); let mut binds=0usize;
        let claim=selected_header_verify_counted(circuit,digest,&fresh_plan,role,&id,SELECTED_OWNER,&setup_id,&commitment_bytes,&proof,&mut transcript,&mut binds).unwrap();
        assert_eq!(claim,*expected_claim); let mut point=selected_header_parent_point(&claim.point,role).unwrap(); assert_eq!(point,*expected_parent_point);
        let value=if wrong_point {
            assert_eq!(point.len(),PARENT_LOG_N);
            assert!(point[23].is_zero(),"selected owner7 top bit starts at zero");
            point[23]=Fr::one();
            claim.value
        } else { claim.value+Fr::one() };
        parent.reset_io_metrics();
        let result=crate::pcs::verify_admitted(fresh_parent_commitment.clone(),value,&point,&opening,&admitted_key,&mut transcript);
        let error=result.unwrap_err(); assert_eq!(error,"Invalid proof");
        let io=parent.io_metrics_snapshot(); assert_eq!((io.read_calls,io.read_bytes,io.read_ns),(0,0,0)); negative_io_reads+=io.read_calls;
        selected_header_counter_evidence("pcs_consumer",error,1,1,binds,transcript.challenges())
    };
    let wrong_retained_parent_point=pcs_negative(0,true);
    let wrong_retained_claim_value=pcs_negative(0,false);
    let wrong_point_parent_point=pcs_negative(1,true);
    let wrong_point_claim_value=pcs_negative(1,false);
    drop(pcs_negative);

    assert_eq!(negative_io_reads,0);
    let negative_consumers_io=parent.io_metrics_snapshot();
    assert_eq!((negative_consumers_io.read_calls,negative_consumers_io.read_bytes,negative_consumers_io.read_ns),(0,0,0));
    drop(parent);

    let mut fresh_family_results=family_values;
    for (i,result) in fresh_family_results.iter_mut().enumerate() {
        result["claim_matches_fresh_gkr_verifier"]=json!(fresh_matches[i].0);
        result["transcript_continuation_matches"]=json!(fresh_matches[i].1);
        result["fresh_gkr_verified"]=json!(fresh_matches[i].0);
        result["fresh_pcs_verified_with_original_test_key"]=json!(true);
        result["timing_ms"]["fresh_gkr_verify"]=json!(fresh_timings[i].0);
        result["timing_ms"]["fresh_pcs_verify"]=json!(fresh_timings[i].1);
        result["io"]["fresh_gkr_verify"]=packed_io_json(fresh_ios[i].0);
        result["io"]["fresh_pcs_verify"]=packed_io_json(fresh_ios[i].1);
    }
    let artifact_started=Instant::now();
    write_new_pcs_artifact(&artifact_dir,SELECTED_HEADER_RETAINED_PROOF,&family_data[0].1);
    write_new_pcs_artifact(&artifact_dir,SELECTED_HEADER_RETAINED_OPENING,&family_data[0].2);
    write_new_pcs_artifact(&artifact_dir,SELECTED_HEADER_POINTS_PROOF,&family_data[1].1);
    write_new_pcs_artifact(&artifact_dir,SELECTED_HEADER_POINTS_OPENING,&family_data[1].2);
    let artifact_writes_ms=artifact_started.elapsed().as_millis();
    let whole_test_before_result_write_ms=whole_started.elapsed().as_millis();
    let result=json!({
        "schema":"native-selected-header-parent-pcs-v1","test":SELECTED_HEADER_TEST,
        "scope":"selected owner7 retained-header and point-membership GKR claims authenticated with fresh consumers to the original Window16 parent commitment; bounded diagnostic only",
        "source":{"window_file_sha256":SOURCE_SHA256,"window_result_sha256":"FE4CAA50A98D9A22C9FBFD3F28FE9DF00DB13E7EC9C9498027CCD4DB2B38E805","window_bytes":SOURCE_BYTES,
            "parent_point_bits":PARENT_LOG_N,"parent_owner_count":OWNER_COUNT,"parent_owner_bits":SELECTED_OWNER_COORDINATE_BITS},
        "native_header":{"prefix_file":"mainnet-prefix-first-3073-u32le-v1.bin","prefix_bytes":prefix_bytes,
            "prefix_sha256":SELECTED_HEADER_PREFIX_SHA256,"headers":SELECTED_HEADERS,"selected_owner":SELECTED_OWNER,"selected_height":8,"owner_class":"Carry",
            "raw_header_bytes":raw_header_bytes,"header_id_blake2b256":SELECTED_HEADER_RAW_ID,"owner_row_bytes":131072,"owner_row_blake2b256":SELECTED_HEADER_ROW_ID,
            "owner_row_read_calls":owner_row_io.read_calls,"owner_row_read_bytes":owner_row_io.read_bytes,
            "native_decode_reencode_matches":true,"selected_digest_wire_matches_native_id":true,"retained_residuals_zero":true,
            "point_residuals_zero":true,"serializer_ports_match_native_raw":true},
        "identity":{"input_receipt_sha256":SELECTED_HEADER_INPUT_RECEIPT,"setup_id_hex":SELECTED_HEADER_SETUP_ID,
            "commitment_file":COMMON_PCS_COMMITMENT_FILE,"commitment_bytes":reference_commitment.len(),"commitment_sha256":SELECTED_HEADER_COMMITMENT_SHA256,
            "verifier_key_file":COMMON_PCS_KEY_FILE,"verifier_key_bytes":reference_key.len(),"verifier_key_sha256":SELECTED_HEADER_KEY_SHA256,
            "public_admit_24_still_rejected":true,"public_admit_24_error":"unsupported verifier-key dimension"},
        "plan":{"headers":SELECTED_HEADERS,"slot_log":SELECTED_SLOT_LOG,"root_hex":"DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913",
            "total_be28_hex":"000000000000000000000000000000000000000000564F0B9B000000","selected_owner":SELECTED_OWNER,"owner_class":"Carry",
            "source_boundary_terms":474755,"retired_terms":78194,"retained_terms_before_public_id_anchor":SELECTED_RETAINED_TERMS,
            "public_id_anchor_terms":SELECTED_ANCHOR_TERMS,"retained_terms_with_public_id_anchor":retained_term_count,
            "public_id_anchor_first_row":524032,"public_id_anchor_last_row":524287,"retained_circuit_blake2b256":retained_digest,
            "point_input_bits":SELECTED_POINT_BITS,"point_input_len":SELECTED_POINT_WIDTH,"point_row_bits":14,"point_row_count":16384,
            "point_terms":point_term_count,"point_used_bits":point_used_bits,"point_residual_rows":point_residual_rows,
            "point_circuit_blake2b256":point_digest,"point_offset":SELECTED_POINT_OFFSET,"point_width":SELECTED_POINT_WIDTH,"point_bank_index":96,
            "point_parent_fixed_bank_coordinates":[0,0,0,0,0,1,1],"parent_owner_coordinates":[1,1,1,0]},
        "setup":{"setup_id_matches_original":true,"verifier_key_bytes_match_original":true,"commitment_bytes_match_original":true,
            "setup_reconstruction_ms":setup_reconstruction_ms,"verifier_key_encoding_ms":verifier_key_encode_ms,"commitment_ms":commitment_ms,"commitment_io":packed_io_json(commitment_io)},
        "artifact_directory_env":SELECTED_HEADER_ARTIFACT_ENV,
        "artifact_names":{"result":SELECTED_HEADER_RESULT,"retained_header_gkr_proof":SELECTED_HEADER_RETAINED_PROOF,"retained_header_parent_opening":SELECTED_HEADER_RETAINED_OPENING,
            "points_gkr_proof":SELECTED_HEADER_POINTS_PROOF,"points_parent_opening":SELECTED_HEADER_POINTS_OPENING},
        "families":{"retained_header":fresh_family_results[0],"points":fresh_family_results[1]},
        "negative":{"retained_nonzero_output":retained_nonzero_output,
            "point_nonzero_output":point_nonzero_output,"changed_public_id":changed_public_id,
            "wrong_public_id_binding":wrong_public_id,"wrong_retained_family_role":wrong_retained_role,"wrong_point_family_role":wrong_point_role,
            "wrong_valid_owner_binding":wrong_owner,"wrong_valid_commitment":wrong_commitment,
            "wrong_retained_parent_point":wrong_retained_parent_point,"wrong_retained_claim_value":wrong_retained_claim_value,
            "wrong_point_parent_point":wrong_point_parent_point,"wrong_point_claim_value":wrong_point_claim_value},
        "timing_ms":{"plan_compile":plan_compile_ms,"preproof_checks":preproof_checks_ms,"fresh_context_preparation":fresh_context_preparation_ms,
            "whole_test_before_result_write":whole_test_before_result_write_ms,"setup_reconstruction":setup_reconstruction_ms,
            "verifier_key_encoding":verifier_key_encode_ms,"commitment":commitment_ms,
            "retained_header_gkr_producer":producer_timings[0],"point_membership_gkr_producer":producer_timings[1],
            "retained_header_parent_mle":parent_mle_timings[0],"point_membership_parent_mle":parent_mle_timings[1],
            "retained_header_dory_opening":opening_timings[0],"point_membership_dory_opening":opening_timings[1],"retained_header_fresh_gkr_verify":fresh_timings[0].0,
            "point_membership_fresh_gkr_verify":fresh_timings[1].0,"retained_header_fresh_pcs_verify":fresh_timings[0].1,
            "point_membership_fresh_pcs_verify":fresh_timings[1].1,"artifact_writes":artifact_writes_ms},
        "io":{"source_open":packed_io_json(source_open_io),"owner_row":packed_io_json(owner_row_io),"commitment":packed_io_json(commitment_io),
            "retained_header_producer":packed_io_json(producer_ios[0]),"point_membership_producer":packed_io_json(producer_ios[1]),
            "retained_header_parent_mle":packed_io_json(parent_mle_ios[0]),"point_membership_parent_mle":packed_io_json(parent_mle_ios[1]),
            "retained_header_dory_opening":packed_io_json(opening_ios[0]),"point_membership_dory_opening":packed_io_json(opening_ios[1]),
            "retained_header_fresh_gkr_verify":packed_io_json(fresh_ios[0].0),"point_membership_fresh_gkr_verify":packed_io_json(fresh_ios[1].0),
            "retained_header_fresh_pcs_verify":packed_io_json(fresh_ios[0].1),"point_membership_fresh_pcs_verify":packed_io_json(fresh_ios[1].1),
            "negative_consumers":packed_io_json(negative_consumers_io)},
        "global_proof":false,"pcs_scope":"bounded diagnostic only"});
    let result_bytes=serde_json::to_vec_pretty(&result).unwrap();
    write_new_pcs_artifact(&artifact_dir,SELECTED_HEADER_RESULT,&result_bytes);
    assert_eq!(fs::read_dir(&artifact_dir).unwrap().count(),5);
    println!("selected_header_parent_pcs_result={}",serde_json::to_string(&result).unwrap());
}

fn setup_id_from_hex(text: &str) -> [u8;32] {
    let mut out=[0u8;32];
    for i in 0..32 {out[i]=u8::from_str_radix(&text[i*2..i*2+2],16).unwrap();}
    out
}

const FIXED_UV_ARTIFACT_DIR_ENV: &str = "NIPOPOW_FIXED_UV_ARTIFACT_DIR";
const FIXED_UV_PAIR_ORDER_ENV: &str = "NIPOPOW_FIXED_UV_PAIR_ORDER";
const FIXED_UV_GKR_FILE: &str = "fixed-uv-gkr-proof.bin";
const FIXED_UV_RESULT_FILE: &str = "fixed-uv-result.json";
const FIXED_UV_RESULT_PREFIX: &str = "fixed_uv_common_pcs_result=";

fn prove_far_bank_fixed_uv(
    core: &SparseCircuit,
    core_digest: &str,
    spec: FarBankSpec,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
    load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    transcript: &mut Transcript,
    bind_calls: &mut usize,
) -> Result<(GkrProof, InputClaim, sparse_stream_roster::FixedCoreVProofStats), String> {
    validate_far_bank(core, core_digest, spec)?;
    let shape = sparse::validate(core, 0).map_err(|error| error.to_string())?;
    let template = sparse_stream_roster::FixedCoreVTemplate::try_new(
        core, spec.input_bits, spec.slot_bits, spec.row_bits,
    )?;
    sparse_stream_roster::prove_fixed_core_uv_with_cache_budget_for_test(
        &template,
        Some(0),
        load_copy,
        transcript,
        |transcript| {
            *bind_calls += 1;
            bind_far_bank_parent_pcs(transcript, core_digest, spec, setup_id, commitment_bytes);
        },
        |r, u, v| far_bank_wiring(core, &shape, r, u, v),
    )
}

#[test]
fn native_window16_far_bank14_fixed_core_uv_authenticates_original_parent_commitment_pcs24() {
    let whole_started = Instant::now();
    let (core, core_layout, core_digest) = canonical_core();
    validate_far_bank(&core, &core_digest, FAR_BANK_SPEC).unwrap();
    let artifact_directory = std::env::var(FIXED_UV_ARTIFACT_DIR_ENV)
        .expect("runner pins fresh UV output directory");
    assert_eq!(fs::read_dir(&artifact_directory).unwrap().count(), 0);
    let pair_order = std::env::var(FIXED_UV_PAIR_ORDER_ENV)
        .expect("runner pins UV/reference order");
    assert!(pair_order == "reference_then_candidate" || pair_order == "candidate_then_reference");

    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE")
        .expect("runner pins original Window16 source");
    assert_eq!(fs::metadata(&source_path).unwrap().len(), SOURCE_BYTES);
    assert_eq!(SOURCE_SHA256, "5771F251321B9A1EB5B7B8438F822DC54DC79668EBD1D66443B2983C3CC9F2FF");
    let parent = PackedFile::open(&source_path, PARENT_LOG_N).expect("open pinned Window16 source");
    assert_eq!(parent.input_len(), SOURCE_BITS);
    assert_eq!(
        (parent.io_metrics_snapshot().read_calls, parent.io_metrics_snapshot().read_bytes,
         parent.io_metrics_snapshot().read_ns),
        (0, 0, 0),
    );

    let pcs_directory = std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV)
        .expect("runner pins original TEST24 PCS artifacts");
    let pcs_path = |name: &str| std::path::Path::new(&pcs_directory).join(name);
    let commitment_bytes = fs::read(pcs_path(COMMON_PCS_COMMITMENT_FILE)).unwrap();
    let key_bytes = fs::read(pcs_path(COMMON_PCS_KEY_FILE)).unwrap();
    let original_pcs_result: serde_json::Value = serde_json::from_slice(
        &fs::read(pcs_path(COMMON_PCS_RESULT_FILE)).unwrap(),
    ).unwrap();
    assert_eq!(original_pcs_result["schema"].as_str(), Some("native-core-bank-projection-pcs-v1"));
    let commitment = crate::pcs::decode_commitment(&commitment_bytes).unwrap();
    assert_eq!(crate::pcs::encode_commitment(&commitment).unwrap(), commitment_bytes);
    assert_eq!(commitment_bytes.len(), 384);
    assert_eq!(key_bytes.len(), 25_584);
    let commitment_blake2b256 = work_tree_layout::hash_bytes(&commitment_bytes);
    let verifier_key_blake2b256 = work_tree_layout::hash_bytes(&key_bytes);
    assert_eq!(commitment_blake2b256,
        "929e7484df32f98c0a2be2155819887ce985ecfff61d7d3078ce7b0b7b14684f");
    assert_eq!(verifier_key_blake2b256,
        "4ac8cf1080d2ea989e0dfbde1c5b041bf9ecb82cb2261fc2df0ade6ad96a5050");
    assert_eq!(original_pcs_result["commitment"]["blake2b256"].as_str(),
        Some(commitment_blake2b256.as_str()));
    assert_eq!(original_pcs_result["setup"]["verifier_key_blake2b256"].as_str(),
        Some(verifier_key_blake2b256.as_str()));
    assert_eq!(original_pcs_result["commitment"]["bytes"].as_u64(), Some(commitment_bytes.len() as u64));
    assert_eq!(original_pcs_result["setup"]["verifier_key_bytes"].as_u64(), Some(key_bytes.len() as u64));
    assert_eq!(original_pcs_result["source"]["sha256"].as_str(), Some(SOURCE_SHA256));
    let public_admit_24_error = match crate::verifier_key::admit(PARENT_LOG_N, &key_bytes) {
        Err(error) => error,
        Ok(_) => panic!("public TEST24 admission unexpectedly accepted"),
    };
    assert_eq!(public_admit_24_error, "unsupported verifier-key dimension");

    let reference_directory = std::env::var(FIXED_V_REFERENCE_DIR_ENV)
        .expect("runner pins frozen far-bank proof/opening");
    let reference_path = |name: &str| std::path::Path::new(&reference_directory).join(name);
    let frozen_proof_bytes = fs::read(reference_path("far-bank-gkr-proof.bin")).unwrap();
    let opening_bytes = fs::read(reference_path("far-bank-parent-opening.bin")).unwrap();
    let frozen_result: serde_json::Value = serde_json::from_slice(
        &fs::read(reference_path("far-bank-result.json")).unwrap(),
    ).unwrap();
    assert_eq!(frozen_proof_bytes.len(), FIXED_V_PROOF_BYTES);
    assert_eq!(opening_bytes.len(), FAR_BANK_OPENING_BYTES);
    assert_eq!(frozen_result["schema"].as_str(), Some("native-far-bank-common-pcs-v1"));
    let opening_blake2b256 = work_tree_layout::hash_bytes(&opening_bytes);
    assert_eq!(opening_blake2b256,
        "15bc9b68561d38b70ab6721978dfbdc8ddb7e0a20f7d5e9d5748ec1955ba2b27");
    assert_eq!(frozen_result["opening"]["blake2b256"].as_str(), Some(opening_blake2b256.as_str()));
    let frozen_proof = gkr::decode_dimensions(&[FAR_BANK_PROJECTED_INPUT_BITS], &frozen_proof_bytes)
        .expect("decode original far-bank proof");
    let setup_id_hex = frozen_result["identity"]["setup_id_hex"].as_str().unwrap();
    assert_eq!(setup_id_hex, "b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe");
    assert_eq!(original_pcs_result["setup"]["id_hex"].as_str(), Some(setup_id_hex));
    assert_eq!(original_pcs_result["setup"]["generated_test_key_id_hex"].as_str(), Some(setup_id_hex));
    assert_eq!(frozen_result["identity"]["commitment_blake2b256"].as_str(),
        Some(commitment_blake2b256.as_str()));
    assert_eq!(frozen_result["identity"]["verifier_key_blake2b256"].as_str(),
        Some(verifier_key_blake2b256.as_str()));
    assert_eq!(frozen_result["identity"]["commitment_matches_reference"].as_bool(), Some(true));
    assert_eq!(frozen_result["identity"]["verifier_key_matches_reference"].as_bool(), Some(true));
    assert_eq!(frozen_result["identity"]["setup_id_matches_reference"].as_bool(), Some(true));
    assert!(frozen_result["source"]["sha256"].as_str().unwrap().eq_ignore_ascii_case(SOURCE_SHA256));
    assert_eq!(frozen_result["relation"]["core_term_digest_blake2b256"].as_str(),
        Some(core_digest.as_str()));
    assert_eq!(frozen_result["relation"]["core_terms"].as_u64(), Some(CORE_TERMS as u64));
    let setup_id: [u8; 32] = (0..32)
        .map(|index| u8::from_str_radix(&setup_id_hex[index * 2..index * 2 + 2], 16).unwrap())
        .collect::<Vec<_>>().try_into().unwrap();

    // One actual residual mutant: reject before binding/challenges on the UV path.
    let mutation_wire = core_layout.output[0][0];
    let mut mutation_transcript = Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);
    let mut mutation_bind_calls = 0usize;
    let mut mutation_load_calls = 0usize;
    let mutation = prove_far_bank_fixed_uv(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        |owner| {
            mutation_load_calls += 1;
            let mut values = load_far_bank_owner(&parent, owner, FAR_BANK_SPEC.selected_bank.physical_index)?;
            if owner == 0 {
                let value = &mut values[mutation_wire];
                assert!(*value == Fr::zero() || *value == Fr::one());
                *value = Fr::one() - *value;
            }
            Ok(values)
        },
        &mut mutation_transcript, &mut mutation_bind_calls,
    );
    let mutation_error = mutation.err().expect("UV output mutation fails residual guard");
    assert_eq!(mutation_error, "GKR error: NonzeroOutput");
    assert!(mutation_load_calls > 0);
    assert_eq!((mutation_bind_calls, mutation_transcript.challenges(), mutation_transcript.raw_queries()), (0, 0, 0));

    let mut fixed_v_outcome = None;
    let mut uv_outcome = None;
    let candidate_first = pair_order == "candidate_then_reference";
    for run_uv_first in [candidate_first, !candidate_first] {
        if run_uv_first {
            parent.reset_io_metrics();
            let started = Instant::now();
            let mut bind_calls = 0usize;
            let mut load_calls = 0usize;
            let (proof, claim, stats, transcript) = {
                let mut transcript = Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);
                let (proof, claim, stats) = prove_far_bank_fixed_uv(
                    &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
                    |owner| {
                        load_calls += 1;
                        load_far_bank_owner(&parent, owner, FAR_BANK_SPEC.selected_bank.physical_index)
                    },
                    &mut transcript, &mut bind_calls,
                ).expect("fixed U+V producer");
                (proof, claim, stats, transcript)
            };
            let elapsed_ns = started.elapsed().as_nanos() as u64;
            let io = parent.io_metrics_snapshot();
            assert_eq!(bind_calls, 1);
            assert_eq!(io.read_calls, load_calls as u64);
            assert_eq!(io.read_bytes, load_calls as u64 * 8_192);
            uv_outcome = Some((proof, claim, stats, transcript, load_calls, io, elapsed_ns));
        } else {
            parent.reset_io_metrics();
            let started = Instant::now();
            let mut bind_calls = 0usize;
            let mut load_calls = 0usize;
            let (proof, claim, stats, transcript) = {
                let mut transcript = Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);
                let (proof, claim, stats) = prove_far_bank_fixed_v(
                    &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
                    |owner| {
                        load_calls += 1;
                        load_far_bank_owner(&parent, owner, FAR_BANK_SPEC.selected_bank.physical_index)
                    },
                    &mut transcript, &mut bind_calls,
                ).expect("existing fixed-V reference producer");
                (proof, claim, stats, transcript)
            };
            let elapsed_ns = started.elapsed().as_nanos() as u64;
            let io = parent.io_metrics_snapshot();
            assert_eq!(bind_calls, 1);
            assert_eq!(io.read_calls, load_calls as u64);
            assert_eq!(io.read_bytes, load_calls as u64 * 8_192);
            fixed_v_outcome = Some((proof, claim, stats, transcript, load_calls, io, elapsed_ns));
        }
    }

    let (fixed_v_proof, fixed_v_claim, fixed_v_stats, fixed_v_transcript,
         fixed_v_loads, fixed_v_io, fixed_v_ns) = fixed_v_outcome.unwrap();
    let (uv_proof, uv_claim, uv_stats, uv_transcript, uv_loads, uv_io, uv_ns) = uv_outcome.unwrap();
    let encoded_uv = gkr::encode_proof(&uv_proof).unwrap();
    let encoded_fixed_v = gkr::encode_proof(&fixed_v_proof).unwrap();
    let encoded_frozen = gkr::encode_proof(&frozen_proof).unwrap();
    assert_eq!(encoded_uv.len(), FIXED_V_PROOF_BYTES);
    assert_eq!(encoded_uv, encoded_fixed_v);
    assert_eq!(encoded_uv, encoded_frozen);
    assert_eq!(encoded_uv, frozen_proof_bytes);
    let proof_blake2b256 = work_tree_layout::hash_bytes(&encoded_uv);
    assert_eq!(proof_blake2b256,
        "db0b5d40ec093d39b19390bd99984b82d0d9907d81c49b8cbfd9c7fe72982b06");
    assert_eq!(frozen_result["producer"]["proof_blake2b256"].as_str(), Some(proof_blake2b256.as_str()));
    assert_eq!(uv_claim, fixed_v_claim);
    let mut fixed_continuation = fixed_v_transcript.clone();
    let mut uv_continuation = uv_transcript.clone();
    let transcript_continuation_matches =
        fixed_continuation.challenge_scalar(b"fixed-uv-post-gkr")
            == uv_continuation.challenge_scalar(b"fixed-uv-post-gkr")
        && fixed_continuation.challenges() == uv_continuation.challenges()
        && fixed_continuation.raw_queries() == uv_continuation.raw_queries()
        && fixed_continuation.bytes_absorbed() == uv_continuation.bytes_absorbed();
    assert!(transcript_continuation_matches);

    let parent_point = far_bank_parent_point(FAR_BANK_SPEC, &uv_claim.point).unwrap();
    assert_eq!(parent_point.len(), PARENT_LOG_N);
    parent.reset_io_metrics();
    let parent_mle_value = parent.evaluate(&parent_point).unwrap();
    let parent_mle_io = parent.io_metrics_snapshot();
    assert_eq!(parent_mle_value, uv_claim.value);
    assert_eq!((parent_mle_io.read_calls, parent_mle_io.read_bytes), (1, SOURCE_BYTES));

    let decoded_uv = gkr::decode_dimensions(&[FAR_BANK_PROJECTED_INPUT_BITS], &encoded_uv).unwrap();
    let mut verifier_transcript = Transcript::new(FIXED_V_TRANSCRIPT_DOMAIN);
    let mut verifier_bind_calls = 0usize;
    parent.reset_io_metrics();
    let fresh_gkr_started = Instant::now();
    let verified_claim = verify_far_bank_projection(
        &core, &core_digest, FAR_BANK_SPEC, &setup_id, &commitment_bytes,
        &decoded_uv, &mut verifier_transcript, &mut verifier_bind_calls,
    ).expect("fresh UV GKR verification");
    let fresh_gkr_ns = fresh_gkr_started.elapsed().as_nanos() as u64;
    let fresh_gkr_io = parent.io_metrics_snapshot();
    assert_eq!(verified_claim, uv_claim);
    assert_eq!(verifier_bind_calls, 1);
    assert_eq!((fresh_gkr_io.read_calls, fresh_gkr_io.read_bytes, fresh_gkr_io.read_ns), (0, 0, 0));

    let verifier_key = crate::verifier_key::admit_generated_test_key(PARENT_LOG_N, &key_bytes, setup_id).unwrap();
    let opening = crate::pcs::decode_proof(&opening_bytes, PARENT_LOG_N).unwrap();
    parent.reset_io_metrics();
    let fresh_pcs_started = Instant::now();
    crate::pcs::verify_admitted(commitment, verified_claim.value, &parent_point, &opening,
        &verifier_key, &mut verifier_transcript.clone()).expect("original TEST24 PCS opening");
    let fresh_pcs_ns = fresh_pcs_started.elapsed().as_nanos() as u64;
    let fresh_pcs_io = parent.io_metrics_snapshot();
    assert_eq!((fresh_pcs_io.read_calls, fresh_pcs_io.read_bytes, fresh_pcs_io.read_ns), (0, 0, 0));

    assert_eq!(uv_stats.u.specialized_builders, 272);
    assert_eq!(uv_stats.u.generic_builders, 0);
    assert_eq!(uv_stats.u.descriptor_count, 145_665);
    assert_eq!(fixed_v_stats.u.specialized_builders, 0);
    assert_eq!(fixed_v_stats.u.generic_builders, 0);
    assert_eq!(fixed_v_stats.u.descriptor_count, 0);
    assert_eq!(fixed_v_stats.common_v_template_callbacks, CORE_TERMS);
    assert_eq!(uv_stats.common_v_template_callbacks, fixed_v_stats.common_v_template_callbacks);
    assert!(uv_stats.streamed_term_callbacks > 0);
    assert!(uv_stats.streamed_term_callbacks < fixed_v_stats.streamed_term_callbacks);
    assert!(uv_stats.common_state_peak_capacity_bytes > 0);
    assert!(uv_stats.u.common_u_capacity_bytes > 0);
    assert!(uv_stats.common_state_peak_capacity_bytes > 0
        && uv_stats.common_state_peak_capacity_bytes <= sparse_stream_roster::MAX_FIXED_V_COMMON_STATE_BYTES);
    let whole_test_ns = whole_started.elapsed().as_nanos() as u64;

    write_new_pcs_artifact(&artifact_directory, FIXED_UV_GKR_FILE, &encoded_uv);
    let result = json!({
        "schema":"native-fixed-core-uv-v1",
        "test":"native_window16_far_bank14_fixed_core_uv_authenticates_original_parent_commitment_pcs24",
        "pair_order":pair_order,
        "scope":"one Window16 far-bank14 U+V parity join against existing fixed-V and original parent PCS; bounded diagnostic only",
        "proof":{"file":FIXED_UV_GKR_FILE,"bytes":encoded_uv.len(),"blake2b256":proof_blake2b256,
            "matches_fixed_v":encoded_uv==encoded_fixed_v,"matches_frozen_far":encoded_uv==frozen_proof_bytes,
            "claim_matches_fixed_v":uv_claim==fixed_v_claim,"claim_matches_fresh_gkr":verified_claim==uv_claim,
            "claim_matches_parent_mle":uv_claim.value==parent_mle_value,
            "transcript_continuation_matches":transcript_continuation_matches},
        "identity":{"setup_id_hex":setup_id_hex,
            "setup_id_matches_original":true,
            "input_receipt_sha256":frozen_result["identity"]["input_receipt_sha256"],
            "commitment_blake2b256":commitment_blake2b256,
            "verifier_key_blake2b256":verifier_key_blake2b256,
            "commitment_bytes":commitment_bytes.len(),"verifier_key_bytes":key_bytes.len(),
            "public_admit_24_rejected":true,"public_admit_24_error":public_admit_24_error},
        "original_pcs":{"schema":original_pcs_result["schema"],
            "setup_id_hex":original_pcs_result["setup"]["id_hex"],
            "commitment_blake2b256":original_pcs_result["commitment"]["blake2b256"],
            "verifier_key_blake2b256":original_pcs_result["setup"]["verifier_key_blake2b256"],
            "source_sha256":original_pcs_result["source"]["sha256"]},
        "source":{"bytes":SOURCE_BYTES,"sha256":SOURCE_SHA256.to_ascii_lowercase()},
        "relation":{"core_terms":CORE_TERMS,"core_term_digest_blake2b256":core_digest},
        "fixed_v_stats":{"u_specialized_builders":fixed_v_stats.u.specialized_builders,
            "u_generic_builders":fixed_v_stats.u.generic_builders,
            "u_descriptor_count":fixed_v_stats.u.descriptor_count,
            "common_v_template_callbacks":fixed_v_stats.common_v_template_callbacks,
            "streamed_term_callbacks":fixed_v_stats.streamed_term_callbacks},
        "u_stats":{"specialized_builders":uv_stats.u.specialized_builders,
            "generic_builders":uv_stats.u.generic_builders,"descriptor_count":uv_stats.u.descriptor_count,
            "common_u_capacity_bytes":uv_stats.u.common_u_capacity_bytes},
        "v_stats":{"streamed_term_callbacks":uv_stats.streamed_term_callbacks,
            "common_v_template_callbacks":uv_stats.common_v_template_callbacks,
            "common_state_peak_capacity_bytes":uv_stats.common_state_peak_capacity_bytes},
        "producers":{"fixed_v":{"load_calls":fixed_v_loads,"io":packed_io_json(fixed_v_io),
                "elapsed_ns":fixed_v_ns,"proof_bytes":encoded_fixed_v.len()},
            "uv":{"load_calls":uv_loads,"io":packed_io_json(uv_io),"elapsed_ns":uv_ns,
                "proof_bytes":encoded_uv.len()}},
        "opening":{"file":"far-bank-parent-opening.bin","bytes":opening_bytes.len(),
            "blake2b256":opening_blake2b256,
            "verified_with_original_test_key":true,"setup_commitment_and_opening_regenerated":false},
        "negative":{"nonzero_output_mutation":{"rejected":true,"error":mutation_error,
            "bind_calls":mutation_bind_calls,"challenge_count":mutation_transcript.challenges()}},
        "timing_ns":{"fresh_gkr_verify":fresh_gkr_ns,"fresh_pcs_verify":fresh_pcs_ns,
            "whole_test_before_artifact_write":whole_test_ns},
        "io":{"parent_mle":packed_io_json(parent_mle_io),"fresh_gkr_verify":packed_io_json(fresh_gkr_io),
            "fresh_pcs_verify":packed_io_json(fresh_pcs_io)},
        "global_proof":false,"pcs_scope":"bounded diagnostic only"
    });
    let result_bytes = serde_json::to_vec_pretty(&result).unwrap();
    write_new_pcs_artifact(&artifact_directory, FIXED_UV_RESULT_FILE, &result_bytes);
    println!("{}{}", FIXED_UV_RESULT_PREFIX, serde_json::to_string(&result).unwrap());
}

const HEADER_ALIAS_TEST: &str = "native_window16_header_successor_aliases_authenticate_original_parent_pcs24";
const HEADER_ALIAS_UNIT_TEST: &str = "header_successor_alias_mapping_and_bounds_fail_closed";
const HEADER_ALIAS_DOMAIN: &[u8] = b"nipopow-v2-native-header-successor-alias-parent-pcs24-v1";
const HEADER_ALIAS_ARTIFACT_ENV: &str = "NIPOPOW_HEADER_ALIAS_ARTIFACT_DIR";
const HEADER_ALIAS_CENSUS_ENV: &str = "NIPOPOW_HEADER_ALIAS_CENSUS_REPORT";
const HEADER_ALIAS_CENSUS_SHA256: &str = "F324D27C80CB797D80540E0B0B949DE0C330A8E477E60BC2671EB7A4C4C4091A";
const HEADER_ALIAS_SOURCE_WIRES_BLAKE2B256: &str = "ebfe0893e769337e8a69f360b56fc520fee10d4e59e3087c17790ec61e1f9261";
const HEADER_ALIAS_DEST_WIRES_BLAKE2B256: &str = "075463f7605285039d8aab745182bfdc620e9676aaaba2ae0fb0b0a6c19217df";
const HEADER_ALIAS_RAW_ID: &str = "fce2c5727951945ac4d2bc7136d9c9292ee51c88e2bd8b7d169cc558dfcacac4";
const HEADER_ALIAS_HEIGHT: u32 = 8;
const HEADER_ALIAS_N_BITS: u32 = 100_734_821;
const HEADER_ALIAS_RECORD: usize = 7;
const HEADER_ALIAS_SOURCE_OWNER: usize = 7;
const HEADER_ALIAS_SOURCE_BANK: usize = 8;
const HEADER_ALIAS_SOURCE_COPY: usize = 120;
const HEADER_ALIAS_DEST_OWNER: usize = 6;
const HEADER_ALIAS_DEST_BANK: usize = 15;
const HEADER_ALIAS_DEST_COPY: usize = 111;
const HEADER_ALIAS_COUNT: usize = 4_186;
const HEADER_ALIAS_INPUT_BITS: usize = 17;
const HEADER_ALIAS_ROW_BITS: usize = 13;
const HEADER_ALIAS_PADDED_ROWS: usize = 1 << HEADER_ALIAS_ROW_BITS;
const HEADER_ALIAS_INPUTS: usize = 1 << HEADER_ALIAS_INPUT_BITS;
const HEADER_ALIAS_TERMS: usize = HEADER_ALIAS_COUNT * 2;
const HEADER_ALIAS_WITNESS_BYTES: usize = HEADER_ALIAS_INPUTS * 32;
const HEADER_ALIAS_OPENING_BYTES: usize = 32_013;
const HEADER_ALIAS_GKR_BYTES: usize = 3_904;
const HEADER_ALIAS_STATE_LIMIT: usize = 16 * 1024 * 1024;
const HEADER_ALIAS_GKR_FILE: &str = "positive-gkr.bin";
const HEADER_ALIAS_SOURCE_FILE: &str = "positive-source.pcs";
const HEADER_ALIAS_DEST_FILE: &str = "positive-destination.pcs";
const HEADER_ALIAS_FLIP_GKR_FILE: &str = "paired-flip-gkr.bin";
const HEADER_ALIAS_FLIP_SOURCE_FILE: &str = "paired-flip-source.pcs";
const HEADER_ALIAS_FLIP_DEST_FILE: &str = "paired-flip-destination.pcs";
const HEADER_ALIAS_RESULT_FILE: &str = "RESULT.json";
const HEADER_ALIAS_RESULT_PREFIX: &str = "header_successor_alias_result=";
const HEADER_ALIAS_SETUP_ID: &str = "b830863c57b3b17589b2872e37a36ceabe51aa6b692585fbd199335585c21bfe";
const HEADER_ALIAS_KEY_SHA256: &str = "3D77BC139351C2832EA098B9E683961C171D918708300121145F0DABFBB48740";
const HEADER_ALIAS_COMMITMENT_SHA256: &str = "E87D71503ED0117D3D234293DCF72CBED2758DA652610B846119EA1C92E5D6DD";

fn header_alias_maps() -> Result<(Vec<usize>, Vec<usize>), String> {
    let serializer = crate::serializer::build(None)?;
    let source_local = serializer.layout.bytes.iter().flatten()
        .chain(serializer.layout.length.iter())
        .chain(serializer.layout.fields.n_bits.iter())
        .chain(serializer.layout.fields.height.iter())
        .copied().collect::<Vec<_>>();
    let source = source_local.iter().map(|wire| {
        crate::header_hash::SERIALIZER_OFFSET.checked_add(*wire)
            .ok_or_else(|| "serializer alias wire overflow".to_owned())
    }).collect::<Result<Vec<_>, _>>()?;
    let destination = crate::work_tree_layout::Endpoints::new().header_aliases();
    drop(serializer);
    header_alias_validate(&source, &destination)?;
    Ok((source, destination))
}

fn header_alias_validate(source: &[usize], destination: &[usize]) -> Result<(), String> {
    if source.len() != HEADER_ALIAS_COUNT || destination.len() != HEADER_ALIAS_COUNT {
        return Err("alias cardinality mismatch".into());
    }
    if source.iter().copied().collect::<std::collections::BTreeSet<_>>().len() != source.len() {
        return Err("duplicate source alias".into());
    }
    if destination.iter().copied().collect::<std::collections::BTreeSet<_>>().len() != destination.len() {
        return Err("duplicate destination alias".into());
    }
    if source.iter().any(|wire| *wire >= 1 << PARENT_OWNER_BITS)
        || destination.iter().any(|wire| *wire >= 1 << PARENT_OWNER_BITS)
    {
        return Err("alias wire outside owner bounds".into());
    }
    if source.iter().any(|wire| wire / BANK_WIDTH != HEADER_ALIAS_SOURCE_BANK)
        || destination.iter().any(|wire| wire / BANK_WIDTH != HEADER_ALIAS_DEST_BANK)
    {
        return Err("alias bank mapping mismatch".into());
    }
    if destination.last().copied().unwrap_or(1 << PARENT_OWNER_BITS) >= 1 << PARENT_OWNER_BITS {
        return Err("last destination alias outside owner bounds".into());
    }
    Ok(())
}

fn header_alias_circuit(source: &[usize], destination: &[usize]) -> Result<SparseCircuit, String> {
    header_alias_validate(source, destination)?;
    let mut terms = Vec::with_capacity(HEADER_ALIAS_TERMS);
    for (row, (&left, &right)) in source.iter().zip(destination).enumerate() {
        let left = left & (BANK_WIDTH - 1);
        let right = BANK_WIDTH + (right & (BANK_WIDTH - 1));
        terms.push(Term { row, gate: crate::gkr::Gate {
            left, right: 0, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
        }});
        terms.push(Term { row, gate: crate::gkr::Gate {
            left: right, right: 0, c0: Fr::zero(), c1: -Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
        }});
    }
    let circuit = SparseCircuit { input_len: HEADER_ALIAS_INPUTS, row_count: HEADER_ALIAS_PADDED_ROWS, terms };
    sparse::validate(&circuit, 0).map_err(|error| error.to_string())?;
    Ok(circuit)
}

fn header_alias_report_wires(report: &serde_json::Value, key: &str) -> Result<Vec<usize>, String> {
    report.get(key).and_then(serde_json::Value::as_array)
        .ok_or_else(|| format!("census {key} must be an array"))?
        .iter().map(|value| value.as_u64().and_then(|n| usize::try_from(n).ok())
            .ok_or_else(|| format!("census {key} contains non-native unsigned integer")))
        .collect()
}

fn header_alias_bits_of_bytes(bytes: &[u8]) -> Vec<bool> {
    bytes.iter().flat_map(|byte| (0..8).map(move |bit| (byte >> bit) & 1 != 0)).collect()
}

fn header_alias_bits_of_u32(value: u32) -> Vec<bool> {
    (0..32).map(|bit| (value >> bit) & 1 != 0).collect()
}

fn header_alias_bits_of_len(value: usize) -> Vec<bool> {
    (0..10).map(|bit| (value >> bit) & 1 != 0).collect()
}

fn header_alias_is_bool(value: Fr) -> bool { value.is_zero() || value.is_one() }

fn header_alias_wire_list_digest(wires: &[usize]) -> String {
    let bytes = serde_json::to_vec(wires).expect("serialize canonical alias wire list");
    work_tree_layout::hash_bytes(&bytes)
}

fn header_alias_bind_statement(
    transcript: &mut Transcript,
    source_digest: &str,
    destination_digest: &str,
    setup_id: &[u8; 32],
    commitment: &[u8],
) {
    transcript.append_bytes(b"header-alias-relation", b"ordered serializer-owner7-to-header8-endpoint-owner6-equality-v1");
    transcript.append_bytes(b"header-alias-parent-source", SOURCE_SHA256.as_bytes());
    transcript.append_bytes(b"header-alias-prefix-sha256", SELECTED_HEADER_PREFIX_SHA256.as_bytes());
    transcript.append_bytes(b"header-alias-census-sha256", HEADER_ALIAS_CENSUS_SHA256.as_bytes());
    transcript.append_bytes(b"header-alias-header-id", HEADER_ALIAS_RAW_ID.as_bytes());
    gkr::append_usize(transcript, b"header-alias-record-index", HEADER_ALIAS_RECORD);
    gkr::append_usize(transcript, b"header-alias-raw-length", 278);
    gkr::append_usize(transcript, b"header-alias-height", HEADER_ALIAS_HEIGHT as usize);
    gkr::append_usize(transcript, b"header-alias-n-bits", HEADER_ALIAS_N_BITS as usize);
    gkr::append_usize(transcript, b"header-alias-source-owner", HEADER_ALIAS_SOURCE_OWNER);
    gkr::append_usize(transcript, b"header-alias-source-bank", HEADER_ALIAS_SOURCE_BANK);
    gkr::append_usize(transcript, b"header-alias-source-copy", HEADER_ALIAS_SOURCE_COPY);
    gkr::append_usize(transcript, b"header-alias-destination-owner", HEADER_ALIAS_DEST_OWNER);
    gkr::append_usize(transcript, b"header-alias-destination-bank", HEADER_ALIAS_DEST_BANK);
    gkr::append_usize(transcript, b"header-alias-destination-copy", HEADER_ALIAS_DEST_COPY);
    gkr::append_usize(transcript, b"header-alias-count", HEADER_ALIAS_COUNT);
    gkr::append_usize(transcript, b"header-alias-input-bits", HEADER_ALIAS_INPUT_BITS);
    gkr::append_usize(transcript, b"header-alias-row-bits", HEADER_ALIAS_ROW_BITS);
    transcript.append_bytes(b"header-alias-source-wire-list-blake2b256", source_digest.as_bytes());
    transcript.append_bytes(b"header-alias-destination-wire-list-blake2b256", destination_digest.as_bytes());
    transcript.append_bytes(b"header-alias-coordinate-recipe", b"r0..r15, selector-s; source bank8 owner7; destination bank15 owner6; LSB-first");
    transcript.append_bytes(b"header-alias-selector-composition", b"(1-s)*source+s*destination; always authenticate both role openings");
    transcript.append_bytes(b"header-alias-test24-setup-id", setup_id);
    transcript.append_bytes(b"header-alias-test24-commitment", commitment);
}

fn header_alias_bind_opening(
    transcript: &mut Transcript,
    role: &str,
    point: &[Fr],
    value: Fr,
    setup_id: &[u8; 32],
    commitment: &[u8],
) {
    transcript.append_bytes(b"header-alias-pcs-role", role.as_bytes());
    gkr::append_usize(transcript, b"header-alias-parent-point-width", point.len());
    for coordinate in point { transcript.append_scalar(b"header-alias-parent-point-coordinate", coordinate); }
    transcript.append_scalar(b"header-alias-parent-evaluation", &value);
    transcript.append_bytes(b"header-alias-pcs-setup-id", setup_id);
    transcript.append_bytes(b"header-alias-pcs-commitment", commitment);
}

fn header_alias_parent_point(point: &[Fr], bank: usize, owner: usize) -> Result<Vec<Fr>, String> {
    if point.len() != HEADER_ALIAS_INPUT_BITS { return Err("GKR claim point must have 17 coordinates".into()); }
    if bank >= 16 || owner >= 16 { return Err("bank/owner coordinate outside four-bit range".into()); }
    let mut parent = point[..HEADER_ALIAS_INPUT_BITS - 1].to_vec();
    parent.extend((0..4).map(|bit| Fr::from(((bank >> bit) & 1) as u64)));
    parent.extend((0..4).map(|bit| Fr::from(((owner >> bit) & 1) as u64)));
    if parent.len() != PARENT_LOG_N { return Err("embedded parent point must have 24 coordinates".into()); }
    Ok(parent)
}

fn header_alias_verify_gkr(
    circuit: &SparseCircuit,
    proof: &GkrProof,
    transcript: &mut Transcript,
    source_digest: &str,
    destination_digest: &str,
    setup_id: &[u8; 32],
    commitment: &[u8],
) -> Result<InputClaim, GkrError> {
    let shape = sparse::validate(circuit, 0)?;
    gkr::verify_with_wiring(&[HEADER_ALIAS_INPUT_BITS], HEADER_ALIAS_PADDED_ROWS, proof, transcript,
        |transcript| {
            header_alias_bind_statement(transcript, source_digest, destination_digest, setup_id, commitment);
            sparse::bind(circuit, 0, transcript);
        },
        |layer, row, left, right| {
            if layer != 0 { return Err(GkrError::PointDimension); }
            sparse::wiring(circuit, &shape, row, left, right)
        })
}

fn header_alias_point_json(point: &[Fr]) -> Vec<String> {
    point.iter().map(|coordinate| hex_bytes(&crate::pcs::encode(coordinate).expect("encode field coordinate"))).collect()
}

fn header_alias_opening(
    parent: &PackedFile,
    committed: &crate::packed::PackedCommitted,
    setup: &crate::pcs::Setup,
    post_gkr: &Transcript,
    role: &str,
    point: &[Fr],
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
) -> (Fr, Vec<u8>, Transcript, PackedIoSnapshot, u64) {
    parent.reset_io_metrics();
    let value = parent.evaluate(point).expect("evaluate original packed parent at role point");
    let mut transcript = post_gkr.clone();
    header_alias_bind_opening(&mut transcript, role, point, value, setup_id, commitment_bytes);
    let started = Instant::now();
    let opening = crate::packed::open(committed, parent, point, setup, &mut transcript)
        .expect("create fresh original TEST24 role opening");
    let elapsed_ms = started.elapsed().as_millis() as u64;
    let io = parent.io_metrics_snapshot();
    let bytes = crate::pcs::encode_proof(&opening).expect("encode fresh TEST24 role opening");
    assert_eq!(bytes.len(), HEADER_ALIAS_OPENING_BYTES);
    (value, bytes, transcript, io, elapsed_ms)
}

fn header_alias_verify_opening(
    parent: &PackedFile,
    commitment: &dory_pcs::backends::arkworks::ArkGT,
    encoded: &[u8],
    value: Fr,
    point: &[Fr],
    post_gkr: &Transcript,
    role: &str,
    key: &crate::verifier_key::AdmittedVerifierKey,
    setup_id: &[u8; 32],
    commitment_bytes: &[u8],
) -> Result<(Transcript, PackedIoSnapshot), String> {
    let opening = crate::pcs::decode_proof(encoded, PARENT_LOG_N)?;
    let mut transcript = post_gkr.clone();
    header_alias_bind_opening(&mut transcript, role, point, value, setup_id, commitment_bytes);
    parent.reset_io_metrics();
    crate::pcs::verify_admitted(commitment.clone(), value, point, &opening, key, &mut transcript)?;
    let io = parent.io_metrics_snapshot();
    if io.read_calls != 0 || io.read_bytes != 0 { return Err("PCS verifier performed packed-source reads".into()); }
    Ok((transcript, io))
}

fn header_alias_io_add(total: &mut (u64, u64), snapshot: PackedIoSnapshot) {
    total.0 = total.0.checked_add(snapshot.read_calls).expect("packed read-call counter overflow");
    total.1 = total.1.checked_add(snapshot.read_bytes).expect("packed read-byte counter overflow");
}

fn header_alias_check_composition(point: &[Fr], claim: Fr, source: Fr, destination: Fr) -> Result<(), String> {
    if point.len() != HEADER_ALIAS_INPUT_BITS { return Err("claim composition point must have 17 coordinates".into()); }
    let selector = point[HEADER_ALIAS_INPUT_BITS - 1];
    let composed = (Fr::one() - selector) * source + selector * destination;
    if composed != claim { return Err("selector-weighted parent openings do not equal GKR claim".into()); }
    Ok(())
}

#[test]
fn header_successor_alias_mapping_and_bounds_fail_closed() {
    let (source, destination) = header_alias_maps().expect("derive canonical header alias maps");
    assert_eq!(source.len(), HEADER_ALIAS_COUNT);
    assert_eq!(destination.len(), HEADER_ALIAS_COUNT);
    assert_eq!(HEADER_ALIAS_SOURCE_OWNER * 16 + HEADER_ALIAS_SOURCE_BANK, HEADER_ALIAS_SOURCE_COPY);
    assert_eq!(HEADER_ALIAS_DEST_OWNER * 16 + HEADER_ALIAS_DEST_BANK, HEADER_ALIAS_DEST_COPY);
    let selector_probe = (0..HEADER_ALIAS_INPUT_BITS).map(|index| Fr::from((index + 2) as u64)).collect::<Vec<_>>();
    let source_point = header_alias_parent_point(&selector_probe, HEADER_ALIAS_SOURCE_BANK, HEADER_ALIAS_SOURCE_OWNER)
        .expect("source embedding is exactly 24 coordinates");
    let destination_point = header_alias_parent_point(&selector_probe, HEADER_ALIAS_DEST_BANK, HEADER_ALIAS_DEST_OWNER)
        .expect("destination embedding is exactly 24 coordinates");
    assert_eq!(source_point.len(), PARENT_LOG_N);
    assert_eq!(destination_point.len(), PARENT_LOG_N);
    assert_eq!(&source_point[..16], &selector_probe[..16]);
    assert_eq!(&destination_point[..16], &selector_probe[..16]);
    assert_eq!(source_point[16..20], [Fr::zero(), Fr::zero(), Fr::zero(), Fr::one()]);
    assert_eq!(source_point[20..24], [Fr::one(), Fr::one(), Fr::one(), Fr::zero()]);
    assert_eq!(destination_point[16..20], [Fr::one(), Fr::one(), Fr::one(), Fr::one()]);
    assert_eq!(destination_point[20..24], [Fr::zero(), Fr::one(), Fr::one(), Fr::zero()]);
    let source_probe = Fr::from(3u64);
    let destination_probe = Fr::from(9u64);
    let mut selector_zero = selector_probe.clone();
    selector_zero[16] = Fr::zero();
    header_alias_check_composition(&selector_zero, source_probe, source_probe, destination_probe)
        .expect("source opening is still a required input when selector is zero");
    let mut selector_one = selector_probe;
    selector_one[16] = Fr::one();
    header_alias_check_composition(&selector_one, destination_probe, source_probe, destination_probe)
        .expect("destination opening is still a required input when selector is one");
    let circuit = header_alias_circuit(&source, &destination).expect("build canonical equality residual");
    assert_eq!(circuit.input_len, HEADER_ALIAS_INPUTS);
    assert_eq!(circuit.row_count, HEADER_ALIAS_PADDED_ROWS);
    assert_eq!(circuit.terms.len(), HEADER_ALIAS_TERMS);
    assert!(sparse::validate(&circuit, 0).is_ok());
    let mut wrong_count = source.clone();
    wrong_count.pop();
    assert!(header_alias_validate(&wrong_count, &destination).is_err());
    let mut duplicate = source.clone();
    duplicate[1] = duplicate[0];
    assert!(header_alias_validate(&duplicate, &destination).is_err());
    let mut out_of_bounds = destination.clone();
    out_of_bounds[0] = 1 << PARENT_OWNER_BITS;
    assert!(header_alias_validate(&source, &out_of_bounds).is_err());
}

#[test]
fn native_window16_header_successor_aliases_authenticate_original_parent_pcs24() {
    let whole_started = Instant::now();
    let artifact_dir = std::env::var(HEADER_ALIAS_ARTIFACT_ENV).expect("runner pins fresh alias output directory");
    assert_eq!(fs::read_dir(&artifact_dir).expect("fresh alias output directory").count(), 0);
    let source_path = std::env::var("NIPOPOW_CORE_PROJECTION_WINDOW_FILE").expect("runner pins Window16 source");
    let prefix_path = std::env::var(SELECTED_HEADER_PREFIX_ENV).expect("runner pins mainnet prefix");
    let census_path = std::env::var(HEADER_ALIAS_CENSUS_ENV).expect("runner pins frozen census report");
    let pcs_dir = std::env::var(COMMON_PCS_ARTIFACT_DIR_ENV).expect("runner pins original TEST24 key/commitment");

    let prefix = fs::read(&prefix_path).expect("read pinned mainnet prefix");
    assert_eq!(prefix.len(), 869_449);
    let raw = selected_header_prefix_entry(&prefix, HEADER_ALIAS_RECORD).expect("strictly frame native header8");
    assert_eq!(raw.len(), 278);
    let header = ergo_header_core::Header::decode(&raw, None).expect("decode native header8");
    assert_eq!(hex_bytes(&ergo_header_core::blake2b256(&raw)), HEADER_ALIAS_RAW_ID);
    assert_eq!(header.height, HEADER_ALIAS_HEIGHT);
    assert_eq!(header.n_bits, HEADER_ALIAS_N_BITS);
    assert_eq!(header.encode().expect("canonical header encoding"), raw);
    let fields = crate::serializer::Fields::from_header(&header).expect("map header to canonical serializer fields");
    let serializer = crate::serializer::build(None).expect("build public canonical serializer");
    let assignment = serializer.assign(&fields);
    let source_local = serializer.layout.bytes.iter().flatten()
        .chain(serializer.layout.length.iter())
        .chain(serializer.layout.fields.n_bits.iter())
        .chain(serializer.layout.fields.height.iter())
        .copied().collect::<Vec<_>>();
    let source_aliases = source_local.iter().map(|wire| crate::header_hash::SERIALIZER_OFFSET.checked_add(*wire)
        .expect("serializer alias wire addition is bounded")).collect::<Vec<_>>();
    drop(source_local);
    let destination_aliases = crate::work_tree_layout::Endpoints::new().header_aliases();
    header_alias_validate(&source_aliases, &destination_aliases).expect("validate canonical alias maps");
    assert_eq!(source_aliases.len(), HEADER_ALIAS_COUNT);
    let expected_report: serde_json::Value = serde_json::from_slice(&fs::read(&census_path).expect("read pinned census report"))
        .expect("parse census report JSON");
    assert_eq!(expected_report["schema"].as_str(), Some("header-successor-data-census-v1"));
    assert_eq!(expected_report["target_record_index"].as_u64(), Some(HEADER_ALIAS_RECORD as u64));
    assert_eq!(expected_report["target_raw_length"].as_u64(), Some(raw.len() as u64));
    assert_eq!(expected_report["target_header_id"].as_str(), Some(HEADER_ALIAS_RAW_ID));
    assert_eq!(expected_report["target_height"].as_u64(), Some(HEADER_ALIAS_HEIGHT as u64));
    assert_eq!(expected_report["target_n_bits"].as_u64(), Some(HEADER_ALIAS_N_BITS as u64));
    assert_eq!(expected_report["source_owner_slot"].as_u64(), Some(HEADER_ALIAS_SOURCE_OWNER as u64));
    assert_eq!(expected_report["destination_owner_slot"].as_u64(), Some(HEADER_ALIAS_DEST_OWNER as u64));
    assert_eq!(expected_report["alias_count"].as_u64(), Some(HEADER_ALIAS_COUNT as u64));
    assert_eq!(header_alias_report_wires(&expected_report, "source_alias_wires").unwrap(), source_aliases);
    assert_eq!(header_alias_report_wires(&expected_report, "destination_alias_wires").unwrap(), destination_aliases);
    assert_eq!(expected_report["comparisons"]["source_to_destination"].as_u64(), Some(HEADER_ALIAS_COUNT as u64));
    assert_eq!(expected_report["comparisons"]["source_to_serializer_assignment"].as_u64(), Some(HEADER_ALIAS_COUNT as u64));
    assert_eq!(expected_report["comparisons"]["source_to_independent_raw_fields"].as_u64(), Some(HEADER_ALIAS_COUNT as u64));
    let source_wire_digest = header_alias_wire_list_digest(&source_aliases);
    let destination_wire_digest = header_alias_wire_list_digest(&destination_aliases);
    assert_eq!(source_wire_digest, HEADER_ALIAS_SOURCE_WIRES_BLAKE2B256);
    assert_eq!(destination_wire_digest, HEADER_ALIAS_DEST_WIRES_BLAKE2B256);

    let mut expected = Vec::with_capacity(HEADER_ALIAS_COUNT);
    let mut padded = [0u8; 514];
    padded[..raw.len()].copy_from_slice(&raw);
    expected.extend(header_alias_bits_of_bytes(&padded));
    expected.extend(header_alias_bits_of_len(raw.len()));
    expected.extend(header_alias_bits_of_u32(header.n_bits));
    expected.extend(header_alias_bits_of_u32(header.height));
    assert_eq!(expected.len(), HEADER_ALIAS_COUNT);
    for (index, wire) in source_aliases.iter().enumerate() {
        let local = wire.checked_sub(crate::header_hash::SERIALIZER_OFFSET).expect("serializer alias lower bound");
        assert_eq!(assignment.get(local).copied().unwrap_or(Fr::from(2u64)), Fr::from(expected[index] as u64),
            "canonical serializer output bit {index}");
    }
    drop(expected_report);

    let mut packed = PackedFile::open(&source_path, PARENT_LOG_N).expect("open frozen Window16 packed parent");
    assert_eq!(packed.input_len(), SOURCE_BITS);
    let source_open_io = packed.io_metrics_snapshot();
    assert_eq!((source_open_io.read_calls, source_open_io.read_bytes), (0, 0));
    packed.reset_io_metrics();
    let source_bank = packed.read_copy(BANK_WIDTH, HEADER_ALIAS_SOURCE_COPY).expect("read owner7 serializer bank8");
    let destination_bank = packed.read_copy(BANK_WIDTH, HEADER_ALIAS_DEST_COPY).expect("read owner6 endpoint bank15");
    assert_eq!(source_bank.len(), BANK_WIDTH);
    assert_eq!(destination_bank.len(), BANK_WIDTH);
    let copy_io = packed.io_metrics_snapshot();
    assert_eq!((copy_io.read_calls, copy_io.read_bytes), (2, 16_384));
    assert!(source_bank.iter().chain(&destination_bank).copied().all(header_alias_is_bool));
    for (index, (&source_wire, &destination_wire)) in source_aliases.iter().zip(&destination_aliases).enumerate() {
        let source_value = source_bank[source_wire & (BANK_WIDTH - 1)];
        let destination_value = destination_bank[destination_wire & (BANK_WIDTH - 1)];
        assert_eq!(source_value, destination_value, "packed alias pair {index}");
        assert_eq!(source_value, Fr::from(expected[index] as u64), "header-derived alias bit {index}");
        let assignment_wire = source_wire - crate::header_hash::SERIALIZER_OFFSET;
        assert_eq!(source_value, assignment[assignment_wire], "serializer assignment alias bit {index}");
    }
    drop(serializer);
    drop(assignment);
    drop(fields);
    drop(expected);

    let circuit = header_alias_circuit(&source_aliases, &destination_aliases).expect("build canonical alias residual");
    assert_eq!(circuit.terms.len(), HEADER_ALIAS_TERMS);

    let setup_started = Instant::now();
    let setup = crate::pcs::generate_setup(PARENT_LOG_N).expect("regenerate deterministic TEST24 setup");
    let setup_ms = setup_started.elapsed().as_millis() as u64;
    let setup_id = setup.id;
    assert_eq!(hex_bytes(&setup_id), HEADER_ALIAS_SETUP_ID);
    let key_bytes = crate::pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).expect("encode TEST24 verifier key");
    assert_eq!(key_bytes.len(), 25_584);
    let original_key = fs::read(std::path::Path::new(&pcs_dir).join(COMMON_PCS_KEY_FILE)).expect("read pinned original TEST24 key");
    assert_eq!(key_bytes, original_key, "regenerated verifier key must match original bytes");
    let admitted_key = crate::verifier_key::admit_generated_test_key(PARENT_LOG_N, &key_bytes, setup_id)
        .expect("admit only the generated diagnostic TEST24 key");
    let packed_commit_started = Instant::now();
    packed.reset_io_metrics();
    let committed = crate::packed::commit(&packed, &setup).expect("stream the original packed-parent commitment");
    let commitment_ms = packed_commit_started.elapsed().as_millis() as u64;
    let commitment_io = packed.io_metrics_snapshot();
    let commitment_bytes = crate::pcs::encode_commitment(&committed.commitment).expect("encode original commitment");
    assert_eq!(commitment_bytes.len(), 384);
    let original_commitment_bytes = fs::read(std::path::Path::new(&pcs_dir).join(COMMON_PCS_COMMITMENT_FILE))
        .expect("read pinned original TEST24 commitment");
    assert_eq!(commitment_bytes, original_commitment_bytes, "regenerated commitment must match original bytes");
    let original_commitment = crate::pcs::decode_commitment(&commitment_bytes).expect("decode original commitment");
    let setup_id_bytes = setup_id_from_hex(HEADER_ALIAS_SETUP_ID);
    assert_eq!(setup_id, setup_id_bytes);

    let mut witness = source_bank.clone();
    witness.extend_from_slice(&destination_bank);
    assert_eq!(witness.len(), HEADER_ALIAS_INPUTS);
    let alias_copy_io = (copy_io.read_calls, copy_io.read_bytes);
    drop(source_bank);
    drop(destination_bank);
    let mut positive_io = alias_copy_io;
    header_alias_io_add(&mut positive_io, commitment_io);

    let positive_gkr_started = Instant::now();
    let mut positive_prover_transcript = Transcript::new(HEADER_ALIAS_DOMAIN);
    let (positive_proof, positive_claim) = sparse::prove_with_binding(&circuit, &witness, 0,
        &mut positive_prover_transcript, |transcript| {
            header_alias_bind_statement(transcript, &source_wire_digest, &destination_wire_digest, &setup_id_bytes, &commitment_bytes);
            sparse::bind(&circuit, 0, transcript);
        }).expect("prove full 4,186-row native alias equality");
    let positive_gkr_ms = positive_gkr_started.elapsed().as_millis() as u64;
    let positive_gkr_bytes = gkr::encode_proof(&positive_proof).expect("encode positive alias GKR proof");
    assert_eq!(positive_gkr_bytes.len(), HEADER_ALIAS_GKR_BYTES);
    let positive_source_point = header_alias_parent_point(&positive_claim.point, HEADER_ALIAS_SOURCE_BANK, HEADER_ALIAS_SOURCE_OWNER)
        .expect("embed source claim into 24-coordinate parent point");
    let positive_destination_point = header_alias_parent_point(&positive_claim.point, HEADER_ALIAS_DEST_BANK, HEADER_ALIAS_DEST_OWNER)
        .expect("embed destination claim into distinct 24-coordinate parent point");
    assert_ne!(positive_source_point, positive_destination_point);
    let positive_post_gkr = positive_prover_transcript.clone();
    let (positive_source_value, positive_source_bytes, positive_source_transcript, source_open_io, positive_source_open_ms) =
        header_alias_opening(&packed, &committed, &setup, &positive_post_gkr, "source-owner7-bank8",
            &positive_source_point, &setup_id_bytes, &commitment_bytes);
    let (positive_destination_value, positive_destination_bytes, positive_destination_transcript, destination_open_io, positive_destination_open_ms) =
        header_alias_opening(&packed, &committed, &setup, &positive_post_gkr, "destination-owner6-bank15",
            &positive_destination_point, &setup_id_bytes, &commitment_bytes);
    header_alias_io_add(&mut positive_io, source_open_io);
    header_alias_io_add(&mut positive_io, destination_open_io);
    assert_eq!(positive_source_bytes.len(), HEADER_ALIAS_OPENING_BYTES);
    assert_eq!(positive_destination_bytes.len(), HEADER_ALIAS_OPENING_BYTES);
    let positive_decoded = sparse::decode_proof(&circuit, 0, &positive_gkr_bytes).expect("fresh exact-dimension positive GKR decode");
    let mut positive_verifier_transcript = Transcript::new(HEADER_ALIAS_DOMAIN);
    packed.reset_io_metrics();
    let verified_positive_claim = header_alias_verify_gkr(&circuit, &positive_decoded, &mut positive_verifier_transcript,
        &source_wire_digest, &destination_wire_digest, &setup_id_bytes, &commitment_bytes)
        .expect("fresh positive GKR verification");
    let positive_gkr_verify_io = packed.io_metrics_snapshot();
    assert_eq!(verified_positive_claim, positive_claim);
    assert_eq!((positive_gkr_verify_io.read_calls, positive_gkr_verify_io.read_bytes), (0, 0));
    assert_eq!(positive_verifier_transcript.challenges(), positive_prover_transcript.challenges());
    assert_eq!(positive_verifier_transcript.bytes_absorbed(), positive_prover_transcript.bytes_absorbed());
    let mut positive_prover_continuation = positive_prover_transcript.clone();
    let mut positive_verifier_continuation = positive_verifier_transcript.clone();
    let positive_gkr_continuation_matches = positive_verifier_continuation.challenge_scalar(b"header-alias-post-gkr")
        == positive_prover_continuation.challenge_scalar(b"header-alias-post-gkr");
    assert!(positive_gkr_continuation_matches);
    let verified_positive_source_point = header_alias_parent_point(&verified_positive_claim.point, HEADER_ALIAS_SOURCE_BANK, HEADER_ALIAS_SOURCE_OWNER)
        .expect("derive source opening point from freshly verified GKR claim");
    let verified_positive_destination_point = header_alias_parent_point(&verified_positive_claim.point, HEADER_ALIAS_DEST_BANK, HEADER_ALIAS_DEST_OWNER)
        .expect("derive destination opening point from freshly verified GKR claim");
    assert_eq!(verified_positive_source_point, positive_source_point);
    assert_eq!(verified_positive_destination_point, positive_destination_point);
    let (verified_source_transcript, source_verify_io) = header_alias_verify_opening(&packed, &original_commitment,
        &positive_source_bytes, positive_source_value, &verified_positive_source_point, &positive_verifier_transcript,
        "source-owner7-bank8", &admitted_key, &setup_id_bytes, &commitment_bytes).expect("fresh source-role PCS verification");
    let (verified_destination_transcript, destination_verify_io) = header_alias_verify_opening(&packed, &original_commitment,
        &positive_destination_bytes, positive_destination_value, &verified_positive_destination_point, &positive_verifier_transcript,
        "destination-owner6-bank15", &admitted_key, &setup_id_bytes, &commitment_bytes).expect("fresh destination-role PCS verification");
    assert_eq!(positive_source_transcript.challenges(), verified_source_transcript.challenges());
    assert_eq!(positive_source_transcript.bytes_absorbed(), verified_source_transcript.bytes_absorbed());
    assert_eq!(positive_destination_transcript.challenges(), verified_destination_transcript.challenges());
    assert_eq!(positive_destination_transcript.bytes_absorbed(), verified_destination_transcript.bytes_absorbed());
    assert_eq!((source_verify_io.read_calls + destination_verify_io.read_calls,
        source_verify_io.read_bytes + destination_verify_io.read_bytes), (0, 0));
    let positive_composition_matches = header_alias_check_composition(&verified_positive_claim.point,
        verified_positive_claim.value, positive_source_value, positive_destination_value).is_ok();
    assert!(positive_composition_matches, "fresh consumer composition must bind both verified parent openings");
    write_new_pcs_artifact(&artifact_dir, HEADER_ALIAS_GKR_FILE, &positive_gkr_bytes);
    write_new_pcs_artifact(&artifact_dir, HEADER_ALIAS_SOURCE_FILE, &positive_source_bytes);
    write_new_pcs_artifact(&artifact_dir, HEADER_ALIAS_DEST_FILE, &positive_destination_bytes);

    let mut one_sided = witness.clone();
    let source_mutation_index = source_aliases[0] & (BANK_WIDTH - 1);
    let source_before = one_sided[source_mutation_index];
    let flipped = if source_before.is_zero() { Fr::one() } else { Fr::zero() };
    one_sided[source_mutation_index] = flipped;
    let mut one_sided_transcript = Transcript::new(HEADER_ALIAS_DOMAIN);
    let mut one_sided_bind_calls = 0usize;
    let one_sided_error = match sparse::prove_with_binding(&circuit, &one_sided, 0, &mut one_sided_transcript, |transcript| {
        one_sided_bind_calls += 1;
        header_alias_bind_statement(transcript, &source_wire_digest, &destination_wire_digest, &setup_id_bytes, &commitment_bytes);
        sparse::bind(&circuit, 0, transcript);
    }) {
        Err(error) => error,
        Ok(_) => panic!("one-sided alias flip unexpectedly proved zero residual"),
    };
    assert_eq!(one_sided_error, GkrError::NonzeroOutput);
    assert_eq!(one_sided_bind_calls, 0);
    assert_eq!(one_sided_transcript.challenges(), 0);
    drop(one_sided);

    let mut paired_flip_witness = witness.clone();
    drop(witness);
    let destination_mutation_index = BANK_WIDTH + (destination_aliases[0] & (BANK_WIDTH - 1));
    assert_eq!(paired_flip_witness[source_mutation_index], paired_flip_witness[destination_mutation_index]);
    paired_flip_witness[source_mutation_index] = flipped;
    paired_flip_witness[destination_mutation_index] = flipped;
    let paired_gkr_started = Instant::now();
    let mut paired_prover_transcript = Transcript::new(HEADER_ALIAS_DOMAIN);
    let (paired_proof, paired_claim) = sparse::prove_with_binding(&circuit, &paired_flip_witness, 0,
        &mut paired_prover_transcript, |transcript| {
            header_alias_bind_statement(transcript, &source_wire_digest, &destination_wire_digest, &setup_id_bytes, &commitment_bytes);
            sparse::bind(&circuit, 0, transcript);
        }).expect("fresh zero-residual GKR proof for jointly flipped witness");
    drop(paired_flip_witness);
    assert_ne!(paired_claim.point, positive_claim.point,
        "paired-flip openings must use points from its new GKR claim");
    let paired_gkr_ms = paired_gkr_started.elapsed().as_millis() as u64;
    let paired_gkr_bytes = gkr::encode_proof(&paired_proof).expect("encode paired-flip GKR proof");
    assert_eq!(paired_gkr_bytes.len(), HEADER_ALIAS_GKR_BYTES);
    let paired_source_point = header_alias_parent_point(&paired_claim.point, HEADER_ALIAS_SOURCE_BANK, HEADER_ALIAS_SOURCE_OWNER)
        .expect("derive paired-flip source point from new claim");
    let paired_destination_point = header_alias_parent_point(&paired_claim.point, HEADER_ALIAS_DEST_BANK, HEADER_ALIAS_DEST_OWNER)
        .expect("derive paired-flip destination point from new claim");
    assert_ne!(paired_source_point, paired_destination_point);
    let paired_post_gkr = paired_prover_transcript.clone();
    let (paired_source_value, paired_source_bytes, paired_source_transcript, paired_source_io, paired_source_open_ms) =
        header_alias_opening(&packed, &committed, &setup, &paired_post_gkr, "source-owner7-bank8",
            &paired_source_point, &setup_id_bytes, &commitment_bytes);
    let (paired_destination_value, paired_destination_bytes, paired_destination_transcript, paired_destination_io, paired_destination_open_ms) =
        header_alias_opening(&packed, &committed, &setup, &paired_post_gkr, "destination-owner6-bank15",
            &paired_destination_point, &setup_id_bytes, &commitment_bytes);
    let mut paired_io = (0u64, 0u64);
    header_alias_io_add(&mut paired_io, paired_source_io);
    header_alias_io_add(&mut paired_io, paired_destination_io);
    assert_eq!(paired_source_bytes.len(), HEADER_ALIAS_OPENING_BYTES);
    assert_eq!(paired_destination_bytes.len(), HEADER_ALIAS_OPENING_BYTES);

    let paired_decoded = sparse::decode_proof(&circuit, 0, &paired_gkr_bytes).expect("fresh exact paired GKR decode");
    let mut paired_verifier_transcript = Transcript::new(HEADER_ALIAS_DOMAIN);
    packed.reset_io_metrics();
    let verified_paired_claim = header_alias_verify_gkr(&circuit, &paired_decoded, &mut paired_verifier_transcript,
        &source_wire_digest, &destination_wire_digest, &setup_id_bytes, &commitment_bytes)
        .expect("fresh paired-flip zero-residual GKR verification");
    assert_eq!(verified_paired_claim, paired_claim);
    let paired_gkr_verify_io = packed.io_metrics_snapshot();
    assert_eq!((paired_gkr_verify_io.read_calls, paired_gkr_verify_io.read_bytes), (0, 0));
    let verified_paired_source_point = header_alias_parent_point(&verified_paired_claim.point, HEADER_ALIAS_SOURCE_BANK, HEADER_ALIAS_SOURCE_OWNER)
        .expect("derive paired source point from freshly verified GKR claim");
    let verified_paired_destination_point = header_alias_parent_point(&verified_paired_claim.point, HEADER_ALIAS_DEST_BANK, HEADER_ALIAS_DEST_OWNER)
        .expect("derive paired destination point from freshly verified GKR claim");
    assert_eq!(verified_paired_source_point, paired_source_point);
    assert_eq!(verified_paired_destination_point, paired_destination_point);
    assert_ne!(verified_paired_source_point, verified_positive_source_point);
    assert_ne!(verified_paired_destination_point, verified_positive_destination_point);
    let (paired_source_verify_transcript, paired_source_verify_io) = header_alias_verify_opening(&packed, &original_commitment,
        &paired_source_bytes, paired_source_value, &verified_paired_source_point, &paired_verifier_transcript,
        "source-owner7-bank8", &admitted_key, &setup_id_bytes, &commitment_bytes).expect("fresh paired source opening verifies alone");
    let (paired_destination_verify_transcript, paired_destination_verify_io) = header_alias_verify_opening(&packed, &original_commitment,
        &paired_destination_bytes, paired_destination_value, &verified_paired_destination_point, &paired_verifier_transcript,
        "destination-owner6-bank15", &admitted_key, &setup_id_bytes, &commitment_bytes).expect("fresh paired destination opening verifies alone");
    assert_eq!(paired_source_transcript.challenges(), paired_source_verify_transcript.challenges());
    assert_eq!(paired_source_transcript.bytes_absorbed(), paired_source_verify_transcript.bytes_absorbed());
    assert_eq!(paired_destination_transcript.challenges(), paired_destination_verify_transcript.challenges());
    assert_eq!(paired_destination_transcript.bytes_absorbed(), paired_destination_verify_transcript.bytes_absorbed());
    assert_eq!((paired_source_verify_io.read_calls + paired_destination_verify_io.read_calls,
        paired_source_verify_io.read_bytes + paired_destination_verify_io.read_bytes), (0, 0));
    let paired_composition = header_alias_check_composition(&verified_paired_claim.point,
        verified_paired_claim.value, paired_source_value, paired_destination_value);
    assert!(paired_composition.is_err(),
        "fresh individual original-parent openings must fail only at paired-flip claim composition");
    drop(verified_paired_source_point);
    drop(verified_paired_destination_point);
    drop(verified_positive_source_point);
    drop(verified_positive_destination_point);
    write_new_pcs_artifact(&artifact_dir, HEADER_ALIAS_FLIP_GKR_FILE, &paired_gkr_bytes);
    write_new_pcs_artifact(&artifact_dir, HEADER_ALIAS_FLIP_SOURCE_FILE, &paired_source_bytes);
    write_new_pcs_artifact(&artifact_dir, HEADER_ALIAS_FLIP_DEST_FILE, &paired_destination_bytes);

    let wrong_role = header_alias_verify_opening(&packed, &original_commitment, &positive_source_bytes,
        positive_source_value, &positive_source_point, &positive_verifier_transcript, "destination-owner6-bank15",
        &admitted_key, &setup_id_bytes, &commitment_bytes).is_err();
    let mut wrong_bank_point = positive_source_point.clone();
    wrong_bank_point[16] = if wrong_bank_point[16].is_zero() { Fr::one() } else { Fr::zero() };
    let wrong_bank = header_alias_verify_opening(&packed, &original_commitment, &positive_source_bytes,
        positive_source_value, &wrong_bank_point, &positive_verifier_transcript, "source-owner7-bank8",
        &admitted_key, &setup_id_bytes, &commitment_bytes).is_err();
    let mut wrong_owner_point = positive_source_point.clone();
    wrong_owner_point[20] = if wrong_owner_point[20].is_zero() { Fr::one() } else { Fr::zero() };
    let wrong_owner = header_alias_verify_opening(&packed, &original_commitment, &positive_source_bytes,
        positive_source_value, &wrong_owner_point, &positive_verifier_transcript, "source-owner7-bank8",
        &admitted_key, &setup_id_bytes, &commitment_bytes).is_err();
    let mut wrong_order_point = positive_source_point.clone();
    wrong_order_point[16..20].reverse();
    let wrong_coordinate_order = header_alias_verify_opening(&packed, &original_commitment, &positive_source_bytes,
        positive_source_value, &wrong_order_point, &positive_verifier_transcript, "source-owner7-bank8",
        &admitted_key, &setup_id_bytes, &commitment_bytes).is_err();
    assert!(wrong_role && wrong_bank && wrong_owner && wrong_coordinate_order);
    let mut altered_selector_point = verified_positive_claim.point.clone();
    altered_selector_point[HEADER_ALIAS_INPUT_BITS - 1] += Fr::one();
    let wrong_selector_composition = header_alias_check_composition(&altered_selector_point,
        verified_positive_claim.value, positive_source_value, positive_destination_value).is_err();
    assert!(wrong_selector_composition, "altered field selector weight must fail the shared composition guard");
    drop(verified_positive_claim);
    drop(verified_paired_claim);
    drop(wrong_bank_point);
    drop(wrong_owner_point);
    drop(wrong_order_point);
    drop(altered_selector_point);

    let gkr_truncated = gkr::decode_dimensions(&[HEADER_ALIAS_INPUT_BITS], &positive_gkr_bytes[..positive_gkr_bytes.len() - 1]).is_err();
    let mut gkr_with_trailing = positive_gkr_bytes.clone();
    gkr_with_trailing.push(0);
    let gkr_trailing = gkr::decode_dimensions(&[HEADER_ALIAS_INPUT_BITS], &gkr_with_trailing).is_err();
    let pcs_truncated = crate::pcs::decode_proof(&positive_source_bytes, PARENT_LOG_N).is_ok()
        && crate::pcs::decode_proof(&positive_source_bytes[..positive_source_bytes.len() - 1], PARENT_LOG_N).is_err();
    let mut pcs_with_trailing = positive_source_bytes.clone();
    pcs_with_trailing.push(0);
    let pcs_trailing = crate::pcs::decode_proof(&pcs_with_trailing, PARENT_LOG_N).is_err();
    assert!(gkr_truncated && gkr_trailing && pcs_truncated && pcs_trailing);

    let mut wrong_count = source_aliases.clone();
    wrong_count.pop();
    let invalid_alias_count = header_alias_validate(&wrong_count, &destination_aliases).is_err();
    let mut duplicate_aliases = source_aliases.clone();
    duplicate_aliases[1] = duplicate_aliases[0];
    let duplicate_alias = header_alias_validate(&duplicate_aliases, &destination_aliases).is_err();
    let mut out_of_bounds_aliases = destination_aliases.clone();
    out_of_bounds_aliases[0] = 1 << PARENT_OWNER_BITS;
    let out_of_bounds_alias = header_alias_validate(&source_aliases, &out_of_bounds_aliases).is_err();
    assert!(invalid_alias_count && duplicate_alias && out_of_bounds_alias);
    drop(wrong_count);
    drop(duplicate_aliases);
    drop(out_of_bounds_aliases);
    let point_vectors = [
        &positive_claim.point, &positive_source_point, &positive_destination_point,
        &paired_claim.point, &paired_source_point, &paired_destination_point,
    ];
    let point_storage_bytes = point_vectors.iter().map(|point| point.capacity() * std::mem::size_of::<Fr>()).sum::<usize>()
        + 4 * std::mem::size_of::<Vec<Fr>>() + 2 * std::mem::size_of::<InputClaim>() + std::mem::size_of_val(&point_vectors);
    let retained_relation_bytes = circuit.terms.capacity() * std::mem::size_of::<Term>()
        + std::mem::size_of::<SparseCircuit>()
        + source_aliases.capacity() * std::mem::size_of::<usize>() + std::mem::size_of::<Vec<usize>>()
        + destination_aliases.capacity() * std::mem::size_of::<usize>() + std::mem::size_of::<Vec<usize>>()
        + source_wire_digest.capacity() + std::mem::size_of::<String>()
        + destination_wire_digest.capacity() + std::mem::size_of::<String>()
        + point_storage_bytes;
    assert!(retained_relation_bytes <= HEADER_ALIAS_STATE_LIMIT,
        "retained alias relation/common point state {retained_relation_bytes} exceeds 16 MiB");
    let containers = json!([
        {"name":"sparse_terms","length":circuit.terms.len(),"capacity":circuit.terms.capacity(),"element_bytes":std::mem::size_of::<Term>(),"metadata_bytes":0},
        {"name":"source_alias_wires","length":source_aliases.len(),"capacity":source_aliases.capacity(),"element_bytes":std::mem::size_of::<usize>(),"metadata_bytes":std::mem::size_of::<Vec<usize>>()},
        {"name":"destination_alias_wires","length":destination_aliases.len(),"capacity":destination_aliases.capacity(),"element_bytes":std::mem::size_of::<usize>(),"metadata_bytes":std::mem::size_of::<Vec<usize>>()},
        {"name":"sparse_circuit_metadata","length":1,"capacity":1,"element_bytes":std::mem::size_of::<SparseCircuit>(),"metadata_bytes":0},
        {"name":"wire_list_digests","length":2,"capacity":source_wire_digest.capacity()+destination_wire_digest.capacity(),"element_bytes":1,"metadata_bytes":2*std::mem::size_of::<String>()},
        {"name":"claim_and_parent_points","length":point_vectors.iter().map(|point|point.len()).sum::<usize>(),"capacity":point_vectors.iter().map(|point|point.capacity()).sum::<usize>(),"element_bytes":std::mem::size_of::<Fr>(),"metadata_bytes":4*std::mem::size_of::<Vec<Fr>>()+2*std::mem::size_of::<InputClaim>()+std::mem::size_of_val(&point_vectors)}
    ]);
    let positive_gkr_digest = work_tree_layout::hash_bytes(&positive_gkr_bytes);
    let positive_source_digest = work_tree_layout::hash_bytes(&positive_source_bytes);
    let positive_destination_digest = work_tree_layout::hash_bytes(&positive_destination_bytes);
    let paired_gkr_digest = work_tree_layout::hash_bytes(&paired_gkr_bytes);
    let paired_source_digest = work_tree_layout::hash_bytes(&paired_source_bytes);
    let paired_destination_digest = work_tree_layout::hash_bytes(&paired_destination_bytes);
    let artifact_entry = |name: &str, bytes: &[u8], digest: &str| json!({"name":name,"bytes":bytes.len(),"blake2b256":digest});
    let result = json!({
        "schema":"header-successor-alias-parent-pcs24-v1",
        "test":HEADER_ALIAS_TEST,
        "scope":"single native header-8 alias equality joined to original TEST24 parent openings; diagnostic only",
        "inputs":{"source_bytes":SOURCE_BYTES,"source_sha256":SOURCE_SHA256.to_ascii_lowercase(),
            "prefix_bytes":prefix.len(),"prefix_sha256":SELECTED_HEADER_PREFIX_SHA256.to_ascii_lowercase(),
            "census_report_sha256":HEADER_ALIAS_CENSUS_SHA256.to_ascii_lowercase(),"target_record_index":HEADER_ALIAS_RECORD,
            "raw_length":raw.len(),"header_id":HEADER_ALIAS_RAW_ID,"height":header.height,"n_bits":header.n_bits,
            "source_owner":HEADER_ALIAS_SOURCE_OWNER,"source_bank":HEADER_ALIAS_SOURCE_BANK,"source_copy":HEADER_ALIAS_SOURCE_COPY,
            "destination_owner":HEADER_ALIAS_DEST_OWNER,"destination_bank":HEADER_ALIAS_DEST_BANK,"destination_copy":HEADER_ALIAS_DEST_COPY,
            "alias_count":HEADER_ALIAS_COUNT,"source_wire_list_blake2b256":source_wire_digest,
            "destination_wire_list_blake2b256":destination_wire_digest,"canonical_factories_match_report":true,"header_decode_and_reencode_match":true},
        "statement":{"input_bits":HEADER_ALIAS_INPUT_BITS,"row_bits":HEADER_ALIAS_ROW_BITS,"padded_rows":HEADER_ALIAS_PADDED_ROWS,
            "rows":HEADER_ALIAS_COUNT,"terms":circuit.terms.len(),"witness_bytes":HEADER_ALIAS_WITNESS_BYTES,
            "selector_index":HEADER_ALIAS_INPUT_BITS-1,"selector_semantics":"claim point coordinate 16; selector s is field-valued",
            "source_point_recipe":"r[0..16] || bank8_lsb4 || owner7_lsb4",
            "destination_point_recipe":"r[0..16] || bank15_lsb4 || owner6_lsb4","both_openings_required":true,
            "composition":"(1-s)*source+s*destination"},
        "identity":{"setup_id_hex":HEADER_ALIAS_SETUP_ID,"verifier_key_sha256":HEADER_ALIAS_KEY_SHA256.to_ascii_lowercase(),
            "commitment_sha256":HEADER_ALIAS_COMMITMENT_SHA256.to_ascii_lowercase(),"verifier_key_bytes":key_bytes.len(),
            "commitment_bytes":commitment_bytes.len(),"matches_original_test24":true},
        "positive":{"artifacts":[artifact_entry(HEADER_ALIAS_GKR_FILE,&positive_gkr_bytes,&positive_gkr_digest),
            artifact_entry(HEADER_ALIAS_SOURCE_FILE,&positive_source_bytes,&positive_source_digest),
            artifact_entry(HEADER_ALIAS_DEST_FILE,&positive_destination_bytes,&positive_destination_digest)],
            "gkr":{"verified":true,"proof_bytes":positive_gkr_bytes.len(),"claim_point":header_alias_point_json(&positive_claim.point),
                "claim_value":hex_bytes(&crate::pcs::encode(&positive_claim.value).unwrap()),
                "transcript_continuation_matches":positive_gkr_continuation_matches},
            "pcs":{"source":{"verified":true,"point":header_alias_point_json(&positive_source_point),
                    "value":hex_bytes(&crate::pcs::encode(&positive_source_value).unwrap())},
                "destination":{"verified":true,"point":header_alias_point_json(&positive_destination_point),
                    "value":hex_bytes(&crate::pcs::encode(&positive_destination_value).unwrap())}},
            "composition_matches":positive_composition_matches,
            "verification_io":{"read_calls":0,"read_bytes":0}},
        "paired_flip":{"artifacts":[artifact_entry(HEADER_ALIAS_FLIP_GKR_FILE,&paired_gkr_bytes,&paired_gkr_digest),
            artifact_entry(HEADER_ALIAS_FLIP_SOURCE_FILE,&paired_source_bytes,&paired_source_digest),
            artifact_entry(HEADER_ALIAS_FLIP_DEST_FILE,&paired_destination_bytes,&paired_destination_digest)],
            "gkr_zero_residual_verified":true,"claim_point":header_alias_point_json(&paired_claim.point),
            "source_opening_fresh_and_valid":true,"destination_opening_fresh_and_valid":true,
            "composition_rejected":paired_composition.is_err(),"rejected_at":"claim_composition",
            "verification_io":{"read_calls":0,"read_bytes":0}},
        "negative":{"one_sided_flip":{"rejected":true,"stage":"sparse_prove_residual_check","bind_calls":one_sided_bind_calls,"challenges":one_sided_transcript.challenges()},
            "wrong_role":{"rejected":wrong_role,"stage":"PCS_transcript_role_binding"},
            "wrong_bank":{"rejected":wrong_bank,"stage":"PCS_point_binding"},"wrong_owner":{"rejected":wrong_owner,"stage":"PCS_point_binding"},
            "wrong_coordinate_order":{"rejected":wrong_coordinate_order,"stage":"PCS_point_binding"},
            "wrong_selector_weight":{"rejected":wrong_selector_composition,"stage":"claim_composition"},
            "gkr_truncated":{"rejected":gkr_truncated,"stage":"GKR_decoder"},"gkr_trailing":{"rejected":gkr_trailing,"stage":"GKR_decoder"},
            "pcs_truncated":{"rejected":pcs_truncated,"stage":"PCS_decoder"},"pcs_trailing":{"rejected":pcs_trailing,"stage":"PCS_decoder"},
            "invalid_alias_count":{"rejected":invalid_alias_count,"stage":"preproof_alias_validation"},
            "duplicate_alias":{"rejected":duplicate_alias,"stage":"preproof_alias_validation"},
            "out_of_bounds_alias":{"rejected":out_of_bounds_alias,"stage":"preproof_alias_validation"}},
        "resources":{"positive_source_io":{"read_calls":positive_io.0,"read_bytes":positive_io.1},
            "paired_flip_source_io":{"read_calls":paired_io.0,"read_bytes":paired_io.1},
            "retained_relation_state":{"formula":"actual vector capacities*element size + complete vector/circuit/string metadata",
                "actual_bytes":retained_relation_bytes,"limit_bytes":HEADER_ALIAS_STATE_LIMIT,"containers":containers},
            "witness_bytes":HEADER_ALIAS_WITNESS_BYTES,
            "timings_ms":{"setup":setup_ms,"commitment":commitment_ms,"positive_gkr":positive_gkr_ms,
                "positive_openings":[positive_source_open_ms,positive_destination_open_ms],"paired_flip_gkr":paired_gkr_ms,
                "paired_flip_openings":[paired_source_open_ms,paired_destination_open_ms],"total_inner":whole_started.elapsed().as_millis() as u64}},
        "claims":{"global_proof":false,"production_ready":false,"upstream_accepted":false}
    });
    let result_bytes = serde_json::to_vec_pretty(&result).expect("serialize closed alias result schema");
    write_new_pcs_artifact(&artifact_dir, HEADER_ALIAS_RESULT_FILE, &result_bytes);
    assert_eq!(fs::read_dir(&artifact_dir).expect("inventory exact alias outputs").count(), 7);
    println!("{}{}", HEADER_ALIAS_RESULT_PREFIX, serde_json::to_string(&result).unwrap());
    drop(circuit);
}

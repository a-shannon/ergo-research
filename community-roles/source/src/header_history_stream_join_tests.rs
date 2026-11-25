use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::{fs::OpenOptions, io::Write, path::PathBuf, time::Instant};

use crate::{
    gkr::{self, GkrError, GkrProof, InputClaim},
    header_history_boundary::HeaderHistoryBoundary,
    packed::{self, PackedFile, PackedFileWriter, PackedIoSnapshot},
    pcs,
    sparse::{self, Circuit, Shape, Term},
    sparse_stream_roster, sparse_stream_terms,
    transcript::Transcript,
    verifier_key,
};

const N: u64 = 844_674;
const SLOT_LOG: usize = 20;
const PAIR_START: u64 = 844_672;
const LOCAL_INPUT_BITS: usize = 20;
const COPY_BITS: usize = 1;
const BASE_ROW_BITS: usize = 19;
const FAMILY_BITS: usize = 1;
const INPUT_BITS: usize = 21;
const ROW_BITS: usize = 21;
const INPUT_LEN: usize = 1 << INPUT_BITS;
const ROW_COUNT: usize = 1 << ROW_BITS;
const FAMILY_OFFSET: usize = 1 << BASE_ROW_BITS;
const FAMILY_MASK: usize = 1 << 20;
const SLOT_INPUTS: usize = 1 << LOCAL_INPUT_BITS;
const SLOT_ROWS: usize = 1 << BASE_ROW_BITS;
const CHUNK: usize = 1 << 16;
const CHUNKS_PER_SLOT: usize = SLOT_INPUTS / CHUNK;
const DEFAULT_CACHE_BYTES: usize = 512 * 1024 * 1024;
const SETUP_ID: &str = "94f67a7bd4490c3c563a7e421b4dbfdbe88cc09d090bb85d9ac8226337b73955";
const DOMAIN: &[u8] = b"header-history-stream-join-v1";
const STREAM_PROFILE: &[u8] = b"header-history-eip-roster-diagnostic-v1";
const STREAM_VERSION: &[u8] = b"header-history-eip-roster-v1";
const FAMILY_ROSTER: &[u8] = b"header-row19,daa-eip-row17;slot-at-member-low;family-bit20-v1";
const RELEASE_RULE: &[u8] = b"code-owned-mature-eip-a4-only-v1";

#[derive(Clone, Copy, Debug, Default)]
struct RunCounts {
    loader_calls: usize,
    emitter_passes: usize,
    emitted_terms: usize,
    packed_io: PackedIoSnapshot,
    elapsed_ms: u128,
}

struct RunOutput {
    proof: GkrProof,
    claim: InputClaim,
    transcript: Transcript,
    counts: RunCounts,
}

fn artifact_path(kind: &str, extension: &str) -> PathBuf {
    let root = std::env::var_os("NIPOPOW_HEADER_STREAM_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    assert!(
        root.is_dir(),
        "stream artifact directory must already exist"
    );
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock before Unix epoch")
        .as_nanos();
    root.join(format!(
        "header-stream-{kind}-{}-{nanos}.{extension}",
        std::process::id()
    ))
}

fn write_create_new(path: &std::path::Path, bytes: &[u8]) {
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .expect("create-only stream artifact");
    output.write_all(bytes).expect("write stream artifact");
    output.sync_all().expect("sync stream artifact");
}

fn packed_bytes(bits: &[Fr]) -> Vec<u8> {
    let mut bytes = vec![0u8; bits.len().div_ceil(8)];
    for (index, bit) in bits.iter().enumerate() {
        assert!(
            bit.is_zero() || bit.is_one(),
            "packed witness must be Boolean"
        );
        if bit.is_one() {
            bytes[index / 8] |= 1 << (index % 8);
        }
    }
    bytes
}

fn build_pair_input() -> (Vec<Fr>, usize) {
    let (fixture, headers) = crate::header_history_boundary::tests::fixture();
    let mature =
        crate::header_history_boundary::tests::assignment_for_child(844_673, &fixture, &headers);
    let carry =
        crate::header_history_boundary::tests::assignment_for_child(844_674, &fixture, &headers);
    assert_eq!(mature.len(), SLOT_INPUTS);
    assert_eq!(carry.len(), SLOT_INPUTS);
    let mut input = mature;
    input.extend(carry);
    assert_eq!(input.len(), INPUT_LEN);
    let fixture_header_bytes = headers
        .get(&844_673)
        .expect("fixture contains the mature header")
        .len();
    (input, fixture_header_bytes)
}

fn validate_join_context(family: &HeaderHistoryBoundary, pair_start: u64) -> Result<(), String> {
    if family.history_slots() != N || family.slot_log() != SLOT_LOG {
        return Err("header family differs from the fixed diagnostic context".into());
    }
    family.validate_pair(pair_start)
}

fn visit_join_terms(
    family: &HeaderHistoryBoundary,
    copy: usize,
    sink: &mut dyn FnMut(Term) -> Result<(), String>,
) -> Result<(usize, usize, usize), String> {
    validate_join_context(family, PAIR_START)?;
    if copy >= 2 {
        return Err("stream copy outside the fixed pair".into());
    }
    let slot = PAIR_START + copy as u64;
    let row_base = usize::try_from(slot)
        .ok()
        .and_then(|value| value.checked_mul(SLOT_ROWS))
        .ok_or("header local row base overflow")?;
    let input_base = usize::try_from(slot)
        .ok()
        .and_then(|value| value.checked_mul(SLOT_INPUTS))
        .ok_or("header local input base overflow")?;
    let counts = family.visit_slot_terms(slot, |mut term| {
        term.row = term
            .row
            .checked_sub(row_base)
            .ok_or("global header row precedes selected slot")?;
        term.gate.left = term
            .gate
            .left
            .checked_sub(input_base)
            .ok_or("global left endpoint precedes selected slot")?;
        term.gate.right = term
            .gate
            .right
            .checked_sub(input_base)
            .ok_or("global right endpoint precedes selected slot")?;
        if term.row >= SLOT_ROWS || term.gate.left >= SLOT_INPUTS || term.gate.right >= SLOT_INPUTS
        {
            return Err("translated header term escapes its slot-local shape".into());
        }
        sink(term)
    })?;
    let mut arithmetic_count = 0usize;
    if copy == 0 {
        if !family.eip_is_mature_at(slot) {
            return Err("code-owned EIP maturity selector rejected the mature slot".into());
        }
        for source in family.eip_arithmetic_terms() {
            if source.row >= 1 << 17
                || source.gate.left >= SLOT_INPUTS
                || source.gate.right >= SLOT_INPUTS
            {
                return Err("mapped EIP term escapes its member-local shape".into());
            }
            let mut term = source.clone();
            term.row = term
                .row
                .checked_add(FAMILY_OFFSET)
                .ok_or("EIP family row overflow")?;
            sink(term)?;
            arithmetic_count += 1;
        }
    } else if family.eip_is_mature_at(slot) {
        return Err("code-owned EIP maturity selector unexpectedly admitted carry".into());
    }
    Ok((counts.emitted, counts.omitted_a4, arithmetic_count))
}

fn visit_reference_terms(
    family: &HeaderHistoryBoundary,
    sink: &mut dyn FnMut(Term) -> Result<(), String>,
) -> Result<(), String> {
    for copy in 0..2 {
        let (header_count, omitted, arithmetic_count) =
            visit_join_terms(family, copy, &mut |mut term| {
                let member = term.row >> BASE_ROW_BITS;
                let local_row = term.row & (SLOT_ROWS - 1);
                let member_width = if member == 0 { 19 } else { 17 };
                term.row = (member << 20) | (copy << member_width) | local_row;
                let input_base = copy * SLOT_INPUTS;
                term.gate.left = term
                    .gate
                    .left
                    .checked_add(input_base)
                    .ok_or("reference left endpoint overflow")?;
                term.gate.right = term
                    .gate
                    .right
                    .checked_add(input_base)
                    .ok_or("reference right endpoint overflow")?;
                sink(term)
            })?;
        let expected_header = if copy == 0 { 466_563 } else { 474_755 };
        let expected_omitted = if copy == 0 { 8_192 } else { 0 };
        assert_eq!(header_count, expected_header);
        assert_eq!(omitted, expected_omitted);
        assert_eq!(
            arithmetic_count,
            if copy == 0 {
                family.eip_arithmetic_terms().len()
            } else {
                0
            }
        );
    }
    Ok(())
}

fn collect_reference_terms(family: &HeaderHistoryBoundary) -> Vec<Term> {
    let mut terms =
        Vec::with_capacity(941_318usize.saturating_add(family.eip_arithmetic_terms().len()));
    visit_reference_terms(family, &mut |term| {
        terms.push(term);
        Ok(())
    })
    .expect("bounded explicit reference emission");
    terms
}

fn fixed_prefix(pair_start: u64) -> Vec<Fr> {
    let fixed = pair_start >> 1;
    (0..19).map(|bit| Fr::from((fixed >> bit) & 1)).collect()
}

fn join_coefficients(
    family: &HeaderHistoryBoundary,
    pair_start: u64,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> Result<[Fr; 4], GkrError> {
    if r.len() != ROW_BITS || u.len() != INPUT_BITS || v.len() != INPUT_BITS {
        return Err(GkrError::PointDimension);
    }
    validate_join_context(family, pair_start).map_err(|_| GkrError::PointDimension)?;
    let header = family
        .pair_coefficients(pair_start, &r[..20], u, v)
        .map_err(|_| GkrError::PointDimension)?;
    let prefix = fixed_prefix(pair_start);
    let mut full_r = r[..18].to_vec();
    full_r.extend(prefix.iter().copied());
    let mut full_u = u.to_vec();
    full_u.extend(prefix.iter().copied());
    let mut full_v = v.to_vec();
    full_v.extend(prefix);
    let arithmetic = family
        .eip_arithmetic_coefficients(&full_r, &full_u, &full_v)
        .map_err(|_| GkrError::PointDimension)?;
    let padding = (Fr::one() - r[18]) * (Fr::one() - r[19]);
    let header_family = Fr::one() - r[20];
    Ok(std::array::from_fn(|index| {
        header_family * header[index] + r[20] * padding * arithmetic[index]
    }))
}

fn double_mask_coefficients(
    family: &HeaderHistoryBoundary,
    pair_start: u64,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> Result<[Fr; 4], GkrError> {
    if r.len() != ROW_BITS || u.len() != INPUT_BITS || v.len() != INPUT_BITS {
        return Err(GkrError::PointDimension);
    }
    let header = family
        .pair_coefficients(pair_start, &r[..20], u, v)
        .map_err(|_| GkrError::PointDimension)?;
    let prefix = fixed_prefix(pair_start);
    let mut full_r = r[..18].to_vec();
    full_r.extend(prefix.iter().copied());
    let mut full_u = u.to_vec();
    full_u.extend(prefix.iter().copied());
    let mut full_v = v.to_vec();
    full_v.extend(prefix);
    let arithmetic = family
        .eip_arithmetic_coefficients(&full_r, &full_u, &full_v)
        .map_err(|_| GkrError::PointDimension)?;
    let padding = (Fr::one() - r[18]) * (Fr::one() - r[19]);
    let extra_mature_mask = (Fr::one() - r[17]) * (Fr::one() - u[20]) * (Fr::one() - v[20]);
    Ok(std::array::from_fn(|index| {
        (Fr::one() - r[20]) * header[index]
            + r[20] * padding * extra_mature_mask * arithmetic[index]
    }))
}

fn asymmetric_points() -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    (
        (0..ROW_BITS)
            .map(|i| Fr::from((7 + i * 11) as u64))
            .collect(),
        (0..INPUT_BITS)
            .map(|i| Fr::from((13 + i * 17) as u64))
            .collect(),
        (0..INPUT_BITS)
            .map(|i| Fr::from((19 + i * 23) as u64))
            .collect(),
    )
}

fn sparse_reference_coefficients(circuit: &Circuit, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let shape = Shape {
        input_bits: INPUT_BITS,
        row_bits: ROW_BITS,
        copies: 1,
        input_len: INPUT_LEN,
        row_count: ROW_COUNT,
    };
    sparse::wiring(circuit, &shape, r, u, v).expect("explicit reference wiring")
}

fn bind_join(
    family: &HeaderHistoryBoundary,
    pair_start: u64,
    arithmetic_fingerprint: &str,
    setup_id: &[u8; 32],
    commitment: &[u8],
    transcript: &mut Transcript,
) {
    crate::header_history_boundary::tests::pair_statement(family, pair_start, transcript);
    transcript.append_bytes(b"stream-profile", STREAM_PROFILE);
    transcript.append_bytes(b"stream-version", STREAM_VERSION);
    transcript.append_bytes(b"stream-family-roster", FAMILY_ROSTER);
    transcript.append_u64(b"stream-input-bits", INPUT_BITS as u64);
    transcript.append_u64(b"stream-row-bits", ROW_BITS as u64);
    transcript.append_u64(b"stream-history-slots", N);
    transcript.append_u64(b"stream-slot-log", SLOT_LOG as u64);
    transcript.append_u64(b"stream-pair-start", pair_start);
    transcript.append_bytes(
        b"stream-arithmetic-fingerprint",
        arithmetic_fingerprint.as_bytes(),
    );
    transcript.append_bytes(b"stream-release-rule", RELEASE_RULE);
    transcript.append_bytes(b"stream-setup-id", setup_id);
    transcript.append_bytes(b"stream-commitment", commitment);
}

fn load_slot(source: &PackedFile, copy: usize) -> Result<Vec<Fr>, String> {
    if copy >= 2 {
        return Err("packed slot copy outside two-slot witness".into());
    }
    let mut values = Vec::with_capacity(SLOT_INPUTS);
    let first_chunk = copy * CHUNKS_PER_SLOT;
    for chunk in 0..CHUNKS_PER_SLOT {
        values.extend(source.read_copy(CHUNK, first_chunk + chunk)?);
    }
    if values.len() != SLOT_INPUTS {
        return Err("packed slot loader returned the wrong local width".into());
    }
    Ok(values)
}

fn assert_header_residuals_zero(family: &HeaderHistoryBoundary, slot: u64, local_input: &[Fr]) {
    assert_eq!(local_input.len(), SLOT_INPUTS);
    let row_base = usize::try_from(slot).unwrap() * SLOT_ROWS;
    let input_base = usize::try_from(slot).unwrap() * SLOT_INPUTS;
    let mut residuals = vec![Fr::zero(); SLOT_ROWS];
    family
        .visit_slot_terms(slot, |mut term| {
            term.row -= row_base;
            term.gate.left -= input_base;
            term.gate.right -= input_base;
            residuals[term.row] += term.gate.evaluate(local_input);
            Ok(())
        })
        .unwrap();
    assert!(
        residuals.iter().all(Zero::is_zero),
        "header residuals at slot {slot}"
    );
}

fn run_streamed(
    family: &HeaderHistoryBoundary,
    source: &PackedFile,
    arithmetic_fingerprint: &str,
    setup_id: &[u8; 32],
    commitment: &[u8],
    cache_budget: Option<usize>,
) -> Result<RunOutput, String> {
    validate_join_context(family, PAIR_START)?;
    source.reset_io_metrics();
    let started = Instant::now();
    let mut loader_calls = 0usize;
    let mut emitter_passes = 0usize;
    let mut emitted_terms = 0usize;
    let mut transcript = Transcript::new(DOMAIN);
    let bind = |transcript: &mut Transcript| {
        bind_join(
            family,
            PAIR_START,
            arithmetic_fingerprint,
            setup_id,
            commitment,
            transcript,
        )
    };
    let (proof, claim) = sparse_stream_roster::prove_with_cache_budget_for_test(
        LOCAL_INPUT_BITS,
        COPY_BITS,
        BASE_ROW_BITS,
        FAMILY_BITS,
        &[19, 17],
        cache_budget,
        |copy| {
            loader_calls += 1;
            load_slot(source, copy)
        },
        &mut transcript,
        bind,
        |copy, sink| {
            emitter_passes += 1;
            visit_join_terms(family, copy, &mut |term| {
                emitted_terms += 1;
                sink(term)
            })
            .map(|_| ())
        },
        |r, u, v| join_coefficients(family, PAIR_START, r, u, v).map_err(|error| error.to_string()),
    )?;
    let counts = RunCounts {
        loader_calls,
        emitter_passes,
        emitted_terms,
        packed_io: source.io_metrics_snapshot(),
        elapsed_ms: started.elapsed().as_millis(),
    };
    Ok(RunOutput {
        proof,
        claim,
        transcript,
        counts,
    })
}

fn cache_bound(expected_terms: usize) -> usize {
    let copies = 2usize;
    let width = SLOT_INPUTS;
    let field_bytes = std::mem::size_of::<Fr>();
    let entry_bytes = std::mem::size_of::<(usize, Fr)>();
    let descriptor_bytes = std::mem::size_of::<(Vec<(usize, Fr)>, Vec<(usize, Fr)>, Vec<Fr>)>();
    copies * width * field_bytes
        + ((expected_terms + copies) * 2 * entry_bytes) * 2
        + copies * descriptor_bytes
}

fn assert_same_transcript(left: &Transcript, right: &Transcript) {
    assert_eq!(left.challenges(), right.challenges());
    assert_eq!(left.raw_queries(), right.raw_queries());
    assert_eq!(left.bytes_absorbed(), right.bytes_absorbed());
    let mut left_next = left.clone();
    let mut right_next = right.clone();
    assert_eq!(
        left_next.challenge_scalar(b"stream-transcript-continuation"),
        right_next.challenge_scalar(b"stream-transcript-continuation")
    );
}

fn verify_join(
    family: &HeaderHistoryBoundary,
    arithmetic_fingerprint: &str,
    setup_id: &[u8; 32],
    commitment: &[u8],
    proof: &GkrProof,
    transcript: &mut Transcript,
) -> Result<InputClaim, GkrError> {
    validate_join_context(family, PAIR_START).map_err(|_| GkrError::PointDimension)?;
    gkr::verify_with_wiring(
        &[INPUT_BITS],
        ROW_COUNT,
        proof,
        transcript,
        |transcript| {
            bind_join(
                family,
                PAIR_START,
                arithmetic_fingerprint,
                setup_id,
                commitment,
                transcript,
            )
        },
        |_index, r, u, v| join_coefficients(family, PAIR_START, r, u, v),
    )
}

#[test]
fn heterogeneous_roster_matches_explicit_non_boolean_reference() {
    assert!(HeaderHistoryBoundary::compile(0, SLOT_LOG).is_err());
    assert!(HeaderHistoryBoundary::compile(N, 22).is_err());
    let family = HeaderHistoryBoundary::compile(N, SLOT_LOG).unwrap();
    assert_eq!(
        family.fingerprint(),
        "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76"
    );
    assert!(family.validate_pair(PAIR_START).is_ok());
    assert!(family.validate_pair(PAIR_START + 1).is_err());
    assert!(family.validate_pair(N - 1).is_err());
    let mut sink_calls = 0usize;
    assert!(family
        .visit_slot_terms(1 << SLOT_LOG, |_| {
            sink_calls += 1;
            Ok(())
        })
        .is_err());
    assert_eq!(sink_calls, 0, "invalid slot must fail before the sink");
    assert!(join_coefficients(&family, PAIR_START, &[], &[], &[]).is_err());
    let mut invalid_copy_sink_calls = 0usize;
    assert!(visit_join_terms(&family, 2, &mut |_| {
        invalid_copy_sink_calls += 1;
        Ok(())
    })
    .is_err());
    assert_eq!(
        invalid_copy_sink_calls, 0,
        "invalid copy must fail before the sink"
    );

    let truncated_family = HeaderHistoryBoundary::compile(PAIR_START + 1, SLOT_LOG).unwrap();
    let mut invalid_context_sink_calls = 0usize;
    assert!(visit_join_terms(&truncated_family, 0, &mut |_| {
        invalid_context_sink_calls += 1;
        Ok(())
    })
    .is_err());
    assert_eq!(
        invalid_context_sink_calls, 0,
        "context must fail before traversal"
    );
    let invalid_context_path = artifact_path("invalid-context-packed", "bin");
    let mut invalid_context_writer =
        PackedFileWriter::create_new(&invalid_context_path, 22).unwrap();
    let zero_chunk = [0u8; 8192];
    for _ in 0..64 {
        invalid_context_writer.write_bytes(&zero_chunk).unwrap();
    }
    let invalid_context_source = invalid_context_writer.finish().unwrap();
    assert!(run_streamed(
        &truncated_family,
        &invalid_context_source,
        "unused",
        &[0; 32],
        &[],
        Some(0)
    )
    .is_err());
    assert_eq!(invalid_context_source.io_metrics_snapshot().read_calls, 0);
    assert_eq!(invalid_context_source.io_metrics_snapshot().read_bytes, 0);
    assert!(load_slot(&invalid_context_source, 2).is_err());
    assert_eq!(invalid_context_source.io_metrics_snapshot().read_calls, 0);

    let invalid_roster = sparse_stream_roster::prove_with_cache_budget_for_test(
        LOCAL_INPUT_BITS,
        COPY_BITS,
        BASE_ROW_BITS,
        FAMILY_BITS,
        &[BASE_ROW_BITS + 1],
        Some(0),
        |_| panic!("invalid member shape must fail before loading"),
        &mut Transcript::new(DOMAIN),
        |_| {},
        |_, _| panic!("invalid member shape must fail before visiting terms"),
        |_, _, _| Err("unreachable wiring".into()),
    );
    assert!(invalid_roster.is_err());

    let terms = collect_reference_terms(&family);
    let (r, u, v) = asymmetric_points();
    let circuit = Circuit {
        input_len: INPUT_LEN,
        row_count: ROW_COUNT,
        terms,
    };
    let expected = sparse_reference_coefficients(&circuit, &r, &u, &v);
    let actual = join_coefficients(&family, PAIR_START, &r, &u, &v).unwrap();
    assert_eq!(
        actual, expected,
        "analytic coefficients equal explicit term wiring"
    );

    let header = family
        .pair_coefficients(PAIR_START, &r[..20], &u, &v)
        .unwrap();
    let prefix = fixed_prefix(PAIR_START);
    let mut full_r = r[..18].to_vec();
    full_r.extend(prefix.iter().copied());
    let mut full_u = u.clone();
    full_u.extend(prefix.iter().copied());
    let mut full_v = v.clone();
    full_v.extend(prefix);
    let arithmetic = family
        .eip_arithmetic_coefficients(&full_r, &full_u, &full_v)
        .unwrap();
    let padding = (Fr::one() - r[18]) * (Fr::one() - r[19]);
    let swapped_family: [Fr; 4] = std::array::from_fn(|index| {
        r[20] * header[index] + (Fr::one() - r[20]) * padding * arithmetic[index]
    });
    assert_ne!(swapped_family, expected, "family-tag mutant must be causal");

    let wrong_member_terms = {
        let mut changed = circuit.terms.clone();
        for term in &mut changed {
            if term.row >> 20 == 0 && ((term.row >> 19) & 1) == 1 {
                term.row = (term.row & !(1 << 19)) | (1 << 18);
            }
        }
        changed
    };
    assert_ne!(
        sparse_reference_coefficients(
            &Circuit {
                input_len: INPUT_LEN,
                row_count: ROW_COUNT,
                terms: wrong_member_terms
            },
            &r,
            &u,
            &v,
        ),
        expected,
        "member-local copy-bit mutant must be causal"
    );

    let wrong_mask = double_mask_coefficients(&family, PAIR_START, &r, &u, &v).unwrap();
    assert_ne!(
        wrong_mask, expected,
        "wrong/double mature mask must be causal"
    );
}

#[test]
fn native_arithmetic_cell_mutant_fails_only_the_arithmetic_owner() {
    let family = HeaderHistoryBoundary::compile(N, SLOT_LOG).unwrap();
    let (input, _) = build_pair_input();
    let terms = family.eip_arithmetic_terms();
    let mut selected = None;
    for row_terms in terms.chunk_by(|left, right| left.row == right.row) {
        // A Boolean gate admits both bit values. Select a native arithmetic
        // row with multiple terms, then keep the altered cell Boolean.
        if row_terms.len() < 2 {
            continue;
        }
        for wire in row_terms
            .iter()
            .flat_map(|term| [term.gate.left, term.gate.right])
        {
            if !(663_552..671_744).contains(&wire)
                && !(688_128..720_896).contains(&wire)
                && !(819_200..851_968).contains(&wire)
                && !(991_232..999_424).contains(&wire)
            {
                continue;
            }
            let original = input[wire];
            if original != Fr::zero() && original != Fr::one() {
                continue;
            }
            let changed = Fr::one() - original;
            let row_residual = row_terms.iter().fold(Fr::zero(), |sum, other| {
                let gate = &other.gate;
                let left = if gate.left == wire {
                    changed
                } else {
                    input[gate.left]
                };
                let right = if gate.right == wire {
                    changed
                } else {
                    input[gate.right]
                };
                sum + gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right
            });
            if !row_residual.is_zero() {
                selected = Some((wire, row_terms[0].row, row_residual));
                break;
            }
        }
        if selected.is_some() {
            break;
        }
    }
    let (wire, bad_row, residual) = selected.expect("find one causal native DAA cell");
    let mut mutant_input = input.clone();
    mutant_input[wire] = Fr::one() - input[wire];
    assert_ne!(mutant_input[wire], input[wire]);
    assert!(mutant_input[wire].is_zero() || mutant_input[wire].is_one());
    let honest_row = terms
        .iter()
        .filter(|term| term.row == bad_row)
        .fold(Fr::zero(), |sum, term| {
            sum + term.gate.evaluate(&input[..SLOT_INPUTS])
        });
    let mutant_row = terms
        .iter()
        .filter(|term| term.row == bad_row)
        .fold(Fr::zero(), |sum, term| {
            sum + term.gate.evaluate(&mutant_input[..SLOT_INPUTS])
        });
    assert!(honest_row.is_zero());
    assert_eq!(mutant_row, residual);
    assert!(!residual.is_zero(), "named arithmetic row must be nonzero");
    for term in family.eip_arithmetic_terms() {
        assert!(term.gate.left < SLOT_INPUTS && term.gate.right < SLOT_INPUTS);
    }
    assert_header_residuals_zero(&family, PAIR_START, &input[..SLOT_INPUTS]);
    assert_header_residuals_zero(&family, PAIR_START, &mutant_input[..SLOT_INPUTS]);

    let mut passes = 0usize;
    let mut transcript = Transcript::new(DOMAIN);
    let error = sparse_stream_roster::prove_with_cache_budget_for_test(
        LOCAL_INPUT_BITS,
        COPY_BITS,
        BASE_ROW_BITS,
        FAMILY_BITS,
        &[19, 17],
        Some(0),
        |copy| Ok(mutant_input[copy * SLOT_INPUTS..(copy + 1) * SLOT_INPUTS].to_vec()),
        &mut transcript,
        |_| {},
        |copy, sink| {
            passes += 1;
            visit_join_terms(&family, copy, sink).map(|_| ())
        },
        |r, u, v| {
            join_coefficients(&family, PAIR_START, r, u, v).map_err(|error| error.to_string())
        },
    )
    .expect_err("nonzero constrained arithmetic residual rejects in producer baseline pass");
    assert!(
        error.contains("NonzeroOutput") || error.to_lowercase().contains("nonzero"),
        "{error}"
    );
    assert!(passes > 0);
    eprintln!("arithmetic_mutant wire={wire} row={bad_row} residual={residual}");
}

#[test]
fn streamed_join_matches_resident_reference_and_one_pcs22_opening() {
    let test_started = Instant::now();
    let context_started = Instant::now();
    let family = HeaderHistoryBoundary::compile(N, SLOT_LOG).unwrap();
    family.validate_pair(PAIR_START).unwrap();
    let arithmetic_fingerprint = family.eip_arithmetic_fingerprint();
    let context_ms = context_started.elapsed().as_millis();
    let assignment_started = Instant::now();
    let (resident_input, fixture_header_bytes) = build_pair_input();
    let assignment_ms = assignment_started.elapsed().as_millis();
    let packed_path = artifact_path("packed", "bin");
    let packing_started = Instant::now();
    let mut writer = PackedFileWriter::create_new(&packed_path, 22).unwrap();
    let lower_half = packed_bytes(&resident_input);
    assert_eq!(lower_half.len(), 1 << 18);
    writer.write_bytes(&lower_half).unwrap();
    let zero_chunk = [0u8; 8192];
    for _ in 0..32 {
        writer.write_bytes(&zero_chunk).unwrap();
    }
    let source = writer.finish().unwrap();
    let packing_ms = packing_started.elapsed().as_millis();
    assert_eq!(source.input_len(), 1 << 22);
    assert_eq!(std::fs::metadata(&packed_path).unwrap().len(), 1 << 19);

    let setup_started = Instant::now();
    let setup = pcs::generate_setup(22).unwrap();
    let key_bytes = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    let admitted_key = verifier_key::admit(22, key_bytes).unwrap();
    assert_eq!(setup.id, *admitted_key.id());
    assert_eq!(hex(&setup.id), SETUP_ID);
    let setup_ms = setup_started.elapsed().as_millis();
    let setup_id = setup.id;
    let commit_started = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap();
    let commit_ms = commit_started.elapsed().as_millis();

    let reference_terms = collect_reference_terms(&family);
    let expected_terms = reference_terms.len();
    assert_eq!(
        INPUT_BITS + ROW_BITS,
        42,
        "both GKR dimensions remain within the existing 24-bit cap"
    );
    let (r, u, v) = asymmetric_points();
    let reference_shape = Shape {
        input_bits: INPUT_BITS,
        row_bits: ROW_BITS,
        copies: 1,
        input_len: INPUT_LEN,
        row_count: ROW_COUNT,
    };
    let reference_circuit = Circuit {
        input_len: INPUT_LEN,
        row_count: ROW_COUNT,
        terms: reference_terms,
    };
    assert_eq!(
        sparse::wiring(&reference_circuit, &reference_shape, &r, &u, &v).unwrap(),
        join_coefficients(&family, PAIR_START, &r, &u, &v).unwrap()
    );
    assert_header_residuals_zero(&family, PAIR_START, &resident_input[..SLOT_INPUTS]);
    let reference_started = Instant::now();
    let mut reference_transcript = Transcript::new(DOMAIN);
    let (reference_proof, reference_claim) = sparse_stream_terms::prove_with_term_source(
        INPUT_LEN,
        ROW_COUNT,
        expected_terms,
        &resident_input,
        &mut reference_transcript,
        |transcript| {
            bind_join(
                &family,
                PAIR_START,
                &arithmetic_fingerprint,
                &setup_id,
                &commitment_bytes,
                transcript,
            )
        },
        |sink| {
            for term in &reference_circuit.terms {
                sink(term.clone())?;
            }
            Ok(())
        },
        |r, u, v| {
            join_coefficients(&family, PAIR_START, r, u, v)
                .map_err(|_| "reference coefficient point rejected".into())
        },
    )
    .unwrap();
    let reference_ms = reference_started.elapsed().as_millis();
    assert_eq!(reference_claim.point.len(), INPUT_BITS);
    drop(reference_circuit);
    drop(reference_shape);
    drop(resident_input);

    let cached = run_streamed(
        &family,
        &source,
        &arithmetic_fingerprint,
        &setup_id,
        &commitment_bytes,
        None,
    )
    .unwrap();
    let replay = run_streamed(
        &family,
        &source,
        &arithmetic_fingerprint,
        &setup_id,
        &commitment_bytes,
        Some(0),
    )
    .unwrap();
    assert_eq!(
        gkr::encode_proof(&cached.proof).unwrap(),
        gkr::encode_proof(&reference_proof).unwrap()
    );
    assert_eq!(
        gkr::encode_proof(&replay.proof).unwrap(),
        gkr::encode_proof(&reference_proof).unwrap()
    );
    assert_eq!(cached.claim, reference_claim);
    assert_eq!(replay.claim, reference_claim);
    assert_same_transcript(&cached.transcript, &reference_transcript);
    assert_same_transcript(&replay.transcript, &reference_transcript);

    let expected_cache_bound = cache_bound(expected_terms);
    assert!(expected_cache_bound <= DEFAULT_CACHE_BYTES,
        "HOLD: exact existing cache bound {expected_cache_bound} exceeds the default 512 MiB branch");
    assert!(
        cached.counts.loader_calls < replay.counts.loader_calls,
        "HOLD: measured default and forced-replay loader branches are not distinct"
    );
    assert!(
        cached.counts.emitter_passes < replay.counts.emitter_passes,
        "HOLD: measured default and forced-replay emitter branches are not distinct"
    );
    assert!(
        cached.counts.emitted_terms < replay.counts.emitted_terms,
        "measured default cache must reduce term replay work"
    );
    assert_eq!(
        cached.counts.packed_io.read_calls,
        (cached.counts.loader_calls * CHUNKS_PER_SLOT) as u64
    );
    assert_eq!(
        replay.counts.packed_io.read_calls,
        (replay.counts.loader_calls * CHUNKS_PER_SLOT) as u64
    );

    let mut verifier_transcript = Transcript::new(DOMAIN);
    let gkr_verify_started = Instant::now();
    let verified_claim = verify_join(
        &family,
        &arithmetic_fingerprint,
        &setup_id,
        &commitment_bytes,
        &cached.proof,
        &mut verifier_transcript,
    )
    .unwrap();
    let gkr_verify_ms = gkr_verify_started.elapsed().as_millis();
    assert_eq!(verified_claim, cached.claim);
    assert_same_transcript(&cached.transcript, &verifier_transcript);
    let mut wrong_mask_transcript = Transcript::new(DOMAIN);
    let wrong_mask_result = gkr::verify_with_wiring(
        &[INPUT_BITS],
        ROW_COUNT,
        &cached.proof,
        &mut wrong_mask_transcript,
        |transcript| {
            bind_join(
                &family,
                PAIR_START,
                &arithmetic_fingerprint,
                &setup_id,
                &commitment_bytes,
                transcript,
            )
        },
        |_index, r, u, v| double_mask_coefficients(&family, PAIR_START, r, u, v),
    );
    assert_eq!(
        wrong_mask_result.unwrap_err(),
        GkrError::TerminalExpression,
        "honest proof with a same-context double mature mask fails at terminal wiring"
    );
    let post_gkr_transcript = verifier_transcript.clone();
    let mut opening_point = verified_claim.point.clone();
    opening_point.push(Fr::zero());
    assert_eq!(opening_point.len(), 22);
    let pcs_started = Instant::now();
    let packed_value = source.evaluate(&opening_point).unwrap();
    assert_eq!(packed_value, verified_claim.value);
    let mut opening_transcript = cached.transcript.clone();
    let opening = packed::open(
        &committed,
        &source,
        &opening_point,
        &setup,
        &mut opening_transcript,
    )
    .unwrap();
    let mut pcs_verifier_transcript = post_gkr_transcript.clone();
    pcs::verify_admitted(
        committed.commitment.clone(),
        verified_claim.value,
        &opening_point,
        &opening,
        &admitted_key,
        &mut pcs_verifier_transcript,
    )
    .unwrap();
    assert_same_transcript(&opening_transcript, &pcs_verifier_transcript);
    let pcs_ms = pcs_started.elapsed().as_millis();

    let mut changed_commitment = commitment_bytes.clone();
    changed_commitment[0] ^= 1;
    let mut changed_binding_transcript = Transcript::new(DOMAIN);
    assert!(verify_join(
        &family,
        &arithmetic_fingerprint,
        &setup_id,
        &changed_commitment,
        &cached.proof,
        &mut changed_binding_transcript,
    )
    .is_err());

    let mut changed_opening_transcript = post_gkr_transcript;
    assert!(pcs::verify_admitted(
        committed.commitment.clone(),
        verified_claim.value + Fr::one(),
        &opening_point,
        &opening,
        &admitted_key,
        &mut changed_opening_transcript,
    )
    .is_err());

    let proof_path = artifact_path("gkr-proof", "bin");
    write_create_new(&proof_path, &gkr::encode_proof(&cached.proof).unwrap());
    let replay_proof_path = artifact_path("gkr-replay-proof", "bin");
    write_create_new(
        &replay_proof_path,
        &gkr::encode_proof(&replay.proof).unwrap(),
    );
    let pcs_proof_path = artifact_path("pcs-proof", "bin");
    write_create_new(&pcs_proof_path, &pcs::encode_proof(&opening).unwrap());
    let receipt_path = artifact_path("receipt", "json");
    let receipt = serde_json::json!({
        "profile": String::from_utf8_lossy(STREAM_PROFILE),
        "version": String::from_utf8_lossy(STREAM_VERSION),
        "N": N,
        "h": SLOT_LOG,
        "pair_start": PAIR_START,
        "header_fingerprint": family.fingerprint(),
        "arithmetic_fingerprint": arithmetic_fingerprint,
        "setup_id": hex(&setup_id),
        "fixture_mature_header_bytes": fixture_header_bytes,
        "reference_terms": expected_terms,
        "reference_ms": reference_ms,
        "context_ms": context_ms,
        "assignment_ms": assignment_ms,
        "packing_ms": packing_ms,
        "setup_ms": setup_ms,
        "commit_ms": commit_ms,
        "gkr_verify_ms": gkr_verify_ms,
        "pcs_open_and_verify_ms": pcs_ms,
        "cache_bound_bytes": expected_cache_bound,
        "cached": {
            "loader_calls": cached.counts.loader_calls,
            "emitter_passes": cached.counts.emitter_passes,
            "emitted_terms": cached.counts.emitted_terms,
            "packed_read_calls": cached.counts.packed_io.read_calls,
            "packed_read_bytes": cached.counts.packed_io.read_bytes,
            "elapsed_ms": cached.counts.elapsed_ms
        },
        "forced_replay": {
            "loader_calls": replay.counts.loader_calls,
            "emitter_passes": replay.counts.emitter_passes,
            "emitted_terms": replay.counts.emitted_terms,
            "packed_read_calls": replay.counts.packed_io.read_calls,
            "packed_read_bytes": replay.counts.packed_io.read_bytes,
            "elapsed_ms": replay.counts.elapsed_ms
        },
        "claim_value": cached.claim.value.to_string(),
        "packed_value": packed_value.to_string(),
        "pcs22_verified": true,
        "whole_test_ms": test_started.elapsed().as_millis(),
        "authority_ceiling": "bounded two-slot conditional header and mapped EIP arithmetic diagnostic; no full-history, imports, compression, adjacency, or backend adoption"
    });
    write_create_new(&receipt_path, receipt.to_string().as_bytes());
    eprintln!("header_stream_join context_ms={context_ms} assignment_ms={assignment_ms} packing_ms={packing_ms} setup_ms={setup_ms} commit_ms={commit_ms} reference_ms={reference_ms} cached={:?} replay={:?} cache_bound={expected_cache_bound}", cached.counts, replay.counts);
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

mod growth_tests {
    use super::*;

    const COPIES: usize = 8;
    const COPY_LOG: usize = 3;
    const GROW_BITS: usize = 23;
    const GROW_LEN: usize = 1 << GROW_BITS;
    const TERMS: usize = 4_221_890;
    const CACHE_BOUND: usize = 943_939_712;
    const GROW_DOMAIN: &[u8] = b"header-history-growth-v1";

    fn validate(family: &HeaderHistoryBoundary, start: u64) -> Result<(), String> {
        if family.history_slots() != N
            || family.slot_log() != SLOT_LOG
            || start != PAIR_START
            || start & (COPIES as u64 - 1) != 0
            || start
                .checked_add(COPIES as u64)
                .is_none_or(|end| end > 1u64 << SLOT_LOG)
        {
            return Err("growth group differs from its fixed diagnostic context".into());
        }
        Ok(())
    }

    fn visit(
        family: &HeaderHistoryBoundary,
        start: u64,
        copy: usize,
        sink: &mut dyn FnMut(Term) -> Result<(), String>,
    ) -> Result<(usize, usize), String> {
        validate(family, start)?;
        if copy >= COPIES {
            return Err("growth copy outside fixed group".into());
        }
        let slot = start + copy as u64;
        let row_base = (slot as usize)
            .checked_mul(SLOT_ROWS)
            .ok_or("growth row overflow")?;
        let input_base = (slot as usize)
            .checked_mul(SLOT_INPUTS)
            .ok_or("growth input overflow")?;
        let counts = family.visit_slot_terms(slot, |mut term| {
            term.row = term
                .row
                .checked_sub(row_base)
                .ok_or("growth row translation")?;
            term.gate.left = term
                .gate
                .left
                .checked_sub(input_base)
                .ok_or("growth left translation")?;
            term.gate.right = term
                .gate
                .right
                .checked_sub(input_base)
                .ok_or("growth right translation")?;
            if term.row >= SLOT_ROWS
                || term.gate.left >= SLOT_INPUTS
                || term.gate.right >= SLOT_INPUTS
            {
                return Err("growth header term escapes local shape".into());
            }
            sink(term)
        })?;
        let mut arithmetic = 0;
        if family.eip_is_mature_at(slot) {
            for original in family.eip_arithmetic_terms() {
                if original.row >= 1 << 17
                    || original.gate.left >= SLOT_INPUTS
                    || original.gate.right >= SLOT_INPUTS
                {
                    return Err("growth arithmetic term escapes local shape".into());
                }
                let mut term = original.clone();
                term.row += FAMILY_OFFSET;
                sink(term)?;
                arithmetic += 1;
            }
        }
        if counts.emitted != if copy == 0 { 466_563 } else { 474_755 }
            || counts.omitted_a4 != if copy == 0 { 8192 } else { 0 }
            || arithmetic != if copy == 0 { 432_042 } else { 0 }
        {
            return Err("growth canonical per-copy count changed".into());
        }
        Ok((counts.emitted, arithmetic))
    }

    fn load(
        source: &PackedFile,
        family: &HeaderHistoryBoundary,
        start: u64,
        copy: usize,
    ) -> Result<Vec<Fr>, String> {
        validate(family, start)?;
        if copy >= COPIES || source.input_len() != GROW_LEN {
            return Err("growth packed shape/copy rejected".into());
        }
        let mut input = Vec::with_capacity(SLOT_INPUTS);
        for chunk in 0..CHUNKS_PER_SLOT {
            input.extend(source.read_copy(CHUNK, copy * CHUNKS_PER_SLOT + chunk)?);
        }
        if input.len() != SLOT_INPUTS {
            return Err("growth loaded width mismatch".into());
        }
        Ok(input)
    }

    fn coefficients(
        family: &HeaderHistoryBoundary,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
        double_mask: bool,
    ) -> Result<[Fr; 4], GkrError> {
        if r.len() != GROW_BITS || u.len() != GROW_BITS || v.len() != GROW_BITS {
            return Err(GkrError::PointDimension);
        }
        validate(family, PAIR_START).map_err(|_| GkrError::PointDimension)?;
        let prefix: Vec<Fr> = (0..17)
            .map(|bit| Fr::from(((PAIR_START >> COPY_LOG) >> bit) & 1))
            .collect();
        let mut hr = r[..22].to_vec();
        hr.extend_from_slice(&prefix);
        let mut ar = r[..20].to_vec();
        ar.extend_from_slice(&prefix);
        let mut full_u = u.to_vec();
        full_u.extend_from_slice(&prefix);
        let mut full_v = v.to_vec();
        full_v.extend_from_slice(&prefix);
        let h = family
            .coefficients(&hr, &full_u, &full_v)
            .map_err(|_| GkrError::PointDimension)?;
        let a = family
            .eip_arithmetic_coefficients(&ar, &full_u, &full_v)
            .map_err(|_| GkrError::PointDimension)?;
        let extra = if double_mask {
            r[17..20]
                .iter()
                .chain(u[20..23].iter())
                .chain(v[20..23].iter())
                .fold(Fr::one(), |scale, coordinate| {
                    scale * (Fr::one() - coordinate)
                })
        } else {
            Fr::one()
        };
        let a_scale = r[22] * (Fr::one() - r[20]) * (Fr::one() - r[21]) * extra;
        Ok(std::array::from_fn(|i| {
            (Fr::one() - r[22]) * h[i] + a_scale * a[i]
        }))
    }

    fn bind(
        family: &HeaderHistoryBoundary,
        arithmetic_fingerprint: &str,
        transcript: &mut Transcript,
    ) {
        transcript.append_bytes(b"growth-profile", b"eight-copy-header-eip-resource-only-v1");
        transcript.append_bytes(b"growth-dummy", b"carry844674-repeated-complete-header-v1");
        transcript.append_bytes(b"growth-roster", b"header19,arith17;copy3;family22-v1");
        transcript.append_u64(b"growth-N", N);
        transcript.append_u64(b"growth-log", SLOT_LOG as u64);
        transcript.append_u64(b"growth-start", PAIR_START);
        transcript.append_u64(b"growth-input", GROW_BITS as u64);
        transcript.append_u64(b"growth-row", GROW_BITS as u64);
        transcript.append_bytes(b"growth-header", family.fingerprint().as_bytes());
        transcript.append_bytes(b"growth-arithmetic", arithmetic_fingerprint.as_bytes());
    }

    fn local_circuits(family: &HeaderHistoryBoundary, copy: usize) -> (Circuit, Circuit) {
        let mut header = Vec::new();
        let mut arithmetic = Vec::new();
        visit(family, PAIR_START, copy, &mut |mut term| {
            if term.row < FAMILY_OFFSET {
                header.push(term);
            } else {
                term.row -= FAMILY_OFFSET;
                arithmetic.push(term);
            }
            Ok(())
        })
        .unwrap();
        (
            Circuit {
                input_len: SLOT_INPUTS,
                row_count: SLOT_ROWS,
                terms: header,
            },
            Circuit {
                input_len: SLOT_INPUTS,
                row_count: 1 << 17,
                terms: arithmetic,
            },
        )
    }

    fn local_coefficients(circuit: &Circuit, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let shape = sparse::validate(circuit, 0).unwrap();
        sparse::wiring(circuit, &shape, r, u, v).unwrap()
    }

    fn eq_copy(point: &[Fr], copy: usize) -> Fr {
        point
            .iter()
            .enumerate()
            .fold(Fr::one(), |weight, (bit, value)| {
                weight
                    * if (copy >> bit) & 1 == 1 {
                        *value
                    } else {
                        Fr::one() - value
                    }
            })
    }

    fn reference(
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
        mature: &[Fr; 4],
        carry: &[Fr; 4],
        arithmetic: &[Fr; 4],
    ) -> [Fr; 4] {
        let mut result = [Fr::zero(); 4];
        for copy in 0..COPIES {
            let h_scale = (Fr::one() - r[22])
                * eq_copy(&r[19..22], copy)
                * eq_copy(&u[20..23], copy)
                * eq_copy(&v[20..23], copy);
            let h = if copy == 0 { mature } else { carry };
            for i in 0..4 {
                result[i] += h_scale * h[i];
            }
        }
        let a_scale = r[22]
            * (Fr::one() - r[20])
            * (Fr::one() - r[21])
            * eq_copy(&r[17..20], 0)
            * eq_copy(&u[20..23], 0)
            * eq_copy(&v[20..23], 0);
        for i in 0..4 {
            result[i] += a_scale * arithmetic[i];
        }
        result
    }

    fn set_copy(point: &mut [Fr], start: usize, copy: usize) {
        for bit in 0..COPY_LOG {
            point[start + bit] = Fr::from(((copy >> bit) & 1) as u64);
        }
    }

    #[test]
    fn growth_coefficients_counts_and_entry_guards() {
        let family = HeaderHistoryBoundary::compile(N, SLOT_LOG).unwrap();
        let (mature, arithmetic) = local_circuits(&family, 0);
        let (carry, empty) = local_circuits(&family, 1);
        assert!(empty.terms.is_empty());
        let mut total = mature.terms.len() + arithmetic.terms.len() + carry.terms.len();
        for copy in 2..COPIES {
            let (dummy, empty) = local_circuits(&family, copy);
            assert_eq!(dummy, carry);
            assert!(empty.terms.is_empty());
            assert!(!family.eip_is_mature_at(PAIR_START + copy as u64));
            total += dummy.terms.len();
        }
        assert_eq!(total, TERMS);
        let measured_bound = COPIES * SLOT_INPUTS * std::mem::size_of::<Fr>()
            + (TERMS + COPIES) * 4 * std::mem::size_of::<(usize, Fr)>()
            + COPIES * std::mem::size_of::<(Vec<(usize, Fr)>, Vec<(usize, Fr)>, Vec<Fr>)>();
        assert_eq!(measured_bound, CACHE_BOUND);
        assert!(CACHE_BOUND > DEFAULT_CACHE_BYTES);
        let r: Vec<Fr> = (0..GROW_BITS)
            .map(|i| Fr::from((7 + 11 * i) as u64))
            .collect();
        let u: Vec<Fr> = (0..GROW_BITS)
            .map(|i| Fr::from((13 + 17 * i) as u64))
            .collect();
        let v: Vec<Fr> = (0..GROW_BITS)
            .map(|i| Fr::from((19 + 23 * i) as u64))
            .collect();
        let h0 = local_coefficients(&mature, &r[..19], &u[..20], &v[..20]);
        let h1 = local_coefficients(&carry, &r[..19], &u[..20], &v[..20]);
        let a0 = local_coefficients(&arithmetic, &r[..17], &u[..20], &v[..20]);
        assert_eq!(
            coefficients(&family, &r, &u, &v, false).unwrap(),
            reference(&r, &u, &v, &h0, &h1, &a0)
        );
        assert_ne!(
            coefficients(&family, &r, &u, &v, true).unwrap(),
            reference(&r, &u, &v, &h0, &h1, &a0)
        );
        for member in 0..2 {
            for copy in 0..COPIES {
                for mismatch in 0..4 {
                    let mut row = r.clone();
                    let mut left = u.clone();
                    let mut right = v.clone();
                    row[22] = Fr::from(member as u64);
                    if member == 1 {
                        row[20] = Fr::zero();
                        row[21] = Fr::zero();
                    }
                    let row_copy = if mismatch == 1 {
                        (copy + 1) % COPIES
                    } else {
                        copy
                    };
                    let left_copy = if mismatch == 2 {
                        (copy + 1) % COPIES
                    } else {
                        copy
                    };
                    let right_copy = if mismatch == 3 {
                        (copy + 1) % COPIES
                    } else {
                        copy
                    };
                    set_copy(&mut row, if member == 0 { 19 } else { 17 }, row_copy);
                    set_copy(&mut left, 20, left_copy);
                    set_copy(&mut right, 20, right_copy);
                    let expected = reference(&row, &left, &right, &h0, &h1, &a0);
                    if mismatch != 0 {
                        assert_eq!(expected, [Fr::zero(); 4]);
                    }
                    assert_eq!(
                        coefficients(&family, &row, &left, &right, false).unwrap(),
                        expected
                    );
                }
            }
        }
        assert!(coefficients(&family, &[], &[], &[], false).is_err());
        let truncated = HeaderHistoryBoundary::compile(PAIR_START + 1, SLOT_LOG).unwrap();
        for (context, start, copy) in [
            (&truncated, PAIR_START, 0),
            (&family, PAIR_START + 1, 0),
            (&family, PAIR_START, COPIES),
        ] {
            let mut calls = 0;
            assert!(visit(context, start, copy, &mut |_| {
                calls += 1;
                Ok(())
            })
            .is_err());
            assert_eq!(calls, 0);
        }
        let path = artifact_path("growth-invalid-packed", "bin");
        let mut writer = PackedFileWriter::create_new(&path, GROW_BITS).unwrap();
        for _ in 0..128 {
            writer.write_bytes(&[0; 8192]).unwrap();
        }
        let source = writer.finish().unwrap();
        for (context, start, copy) in [
            (&truncated, PAIR_START, 0),
            (&family, PAIR_START + 1, 0),
            (&family, PAIR_START, COPIES),
        ] {
            assert!(load(&source, context, start, copy).is_err());
        }
        assert_eq!(source.io_metrics_snapshot().read_calls, 0);
        assert_eq!(source.io_metrics_snapshot().read_bytes, 0);
        let (input, _) = build_pair_input();
        for copy in 0..COPIES {
            let local = if copy == 0 {
                &input[..SLOT_INPUTS]
            } else {
                &input[SLOT_INPUTS..]
            };
            assert_header_residuals_zero(&family, PAIR_START + copy as u64, local);
        }
    }

    #[test]
    fn growth_default_cache_overflow_proof_and_packed_mle() {
        let whole = Instant::now();
        eprintln!("growth phase=context");
        let family = HeaderHistoryBoundary::compile(N, SLOT_LOG).unwrap();
        validate(&family, PAIR_START).unwrap();
        let arithmetic_fingerprint = family.eip_arithmetic_fingerprint();
        eprintln!("growth phase=assignment-packing");
        let (input, _) = build_pair_input();
        let mature = packed_bytes(&input[..SLOT_INPUTS]);
        let carry = packed_bytes(&input[SLOT_INPUTS..]);
        let path = artifact_path("growth-packed", "bin");
        let mut writer = PackedFileWriter::create_new(&path, GROW_BITS).unwrap();
        writer.write_bytes(&mature).unwrap();
        for _ in 1..COPIES {
            writer.write_bytes(&carry).unwrap();
        }
        let source = writer.finish().unwrap();
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 1 << 20);
        drop(input);
        drop(mature);
        drop(carry);
        source.reset_io_metrics();
        let mut loads = 0usize;
        let mut passes = 0usize;
        let mut visited = 0usize;
        let mut producer = Transcript::new(GROW_DOMAIN);
        eprintln!("growth phase=producer");
        let started = Instant::now();
        let (proof, claim) = sparse_stream_roster::prove_with_cache_budget_for_test(
            LOCAL_INPUT_BITS,
            COPY_LOG,
            BASE_ROW_BITS,
            FAMILY_BITS,
            &[19, 17],
            None,
            |copy| {
                loads += 1;
                load(&source, &family, PAIR_START, copy)
            },
            &mut producer,
            |transcript| bind(&family, &arithmetic_fingerprint, transcript),
            |copy, sink| {
                passes += 1;
                visit(&family, PAIR_START, copy, &mut |term| {
                    visited += 1;
                    sink(term)
                })
                .map(|_| ())
            },
            |r, u, v| coefficients(&family, r, u, v, false).map_err(|error| error.to_string()),
        )
        .unwrap();
        let producer_ms = started.elapsed().as_millis();
        let io = source.io_metrics_snapshot();
        assert_eq!(loads, 360);
        assert_eq!(passes, 360);
        assert_eq!(visited, 45 * TERMS);
        assert_eq!(io.read_calls, 5760);
        assert_eq!(io.read_bytes, 47_185_920);
        eprintln!("growth phase=verifier producer_ms={producer_ms} loads={loads} passes={passes} visited={visited}");
        let started = Instant::now();
        let mut consumer = Transcript::new(GROW_DOMAIN);
        let verified = gkr::verify_with_wiring(
            &[GROW_BITS],
            GROW_LEN,
            &proof,
            &mut consumer,
            |transcript| bind(&family, &arithmetic_fingerprint, transcript),
            |_, r, u, v| coefficients(&family, r, u, v, false),
        )
        .unwrap();
        assert_eq!(verified, claim);
        assert_same_transcript(&producer, &consumer);
        let verifier_ms = started.elapsed().as_millis();
        let mut wrong = Transcript::new(GROW_DOMAIN);
        assert_eq!(
            gkr::verify_with_wiring(
                &[GROW_BITS],
                GROW_LEN,
                &proof,
                &mut wrong,
                |transcript| bind(&family, &arithmetic_fingerprint, transcript),
                |_, r, u, v| coefficients(&family, r, u, v, true),
            )
            .unwrap_err(),
            GkrError::TerminalExpression
        );
        eprintln!("growth phase=packed-mle");
        let started = Instant::now();
        let value = source.evaluate(&verified.point).unwrap();
        assert_eq!(value, verified.value);
        let mle_ms = started.elapsed().as_millis();
        let encoded = gkr::encode_proof(&proof).unwrap();
        write_create_new(&artifact_path("growth-proof", "bin"), &encoded);
        let receipt = serde_json::json!({
            "profile":"eight-copy-header-eip-resource-only-v1", "N":N, "slot_log":SLOT_LOG,
            "start":PAIR_START, "copies":COPIES, "input_bits":GROW_BITS, "row_bits":GROW_BITS,
            "header_fingerprint":family.fingerprint(), "arithmetic_fingerprint":arithmetic_fingerprint,
            "dummy":"six copies of valid carry844674; complete header relation, no historical dummy authentication",
            "terms":TERMS, "cache_bound_bytes":CACHE_BOUND, "default_cache_bytes":DEFAULT_CACHE_BYTES,
            "loader_calls":loads, "emitter_passes":passes, "term_visits":visited,
            "packed_read_calls":io.read_calls, "packed_read_bytes":io.read_bytes,
            "producer_ms":producer_ms, "verifier_ms":verifier_ms, "packed_mle_ms":mle_ms,
            "proof_bytes":encoded.len(), "claim_value":claim.value.to_string(), "packed_value":value.to_string(),
            "whole_test_ms":whole.elapsed().as_millis(), "pcs":false,
            "authority_ceiling":"GKR cache-overflow resource diagnostic only; no light-client authentication, historical admission or release readiness"
        });
        write_create_new(
            &artifact_path("growth-receipt", "json"),
            receipt.to_string().as_bytes(),
        );
        eprintln!(
            "growth phase=done producer_ms={producer_ms} verifier_ms={verifier_ms} mle_ms={mle_ms}"
        );
    }
}

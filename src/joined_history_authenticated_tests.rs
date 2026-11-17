use std::{fs, path::PathBuf};

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{digest::consts::U32, Blake2b, Digest};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;

use crate::{
    daa_history_roster::OwnerClass,
    gkr::{self, GkrError, InputClaim},
    native_prefix_auth_plan::role0_sha256,
    native_work_relation::NativeWorkRelation,
    packed_owner_assembly::{
        validate_native_plan_input, NativeOwnerProducer, NativePrefix,
    },
    pcs::{self, Committed, Setup},
    retained_header_pairs::{
        build_one_for_history, RetainedPairSummary, OWNER_RETAINED_TERMS,
        OWNER_RETIRED_TERMS, PAIR_INPUT_LEN, PAIR_RETAINED_TERMS, PAIR_ROW_COUNT,
        PAIR_STARTS, SLOT_INPUT_WIDTH,
    },
    sparse::{self, Circuit, Term},
    transcript::Transcript,
    verifier_key::{self, AdmittedVerifierKey},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH,
};

use super::{
    JoinedHistoryDiagnosticVerifier, JoinedHistoryProofBundle,
    JoinedHistoryProofEntry, JoinedProofKind, JOINED_INPUT_LOG,
};

const FIXTURE_ENV: &str = "NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR";
const FIXTURE_NAME: &str = "mainnet-prefix-first-3073-u32le-v1.bin";
const FIXTURE_BYTES: usize = 869_449;
const FIXTURE_SHA256: &str =
    "ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const FIXTURE_BLAKE2B256: &str =
    "8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
const RAW_RECORDS: usize = 4;
const RAW_END: usize = 1_128;
const X_LEN: usize = 1 << JOINED_INPUT_LOG;
const BAD_X_BIT: usize = 1_844_480;
const BAD_PAIR_ROW: usize = 930_438;
const BAD_PAIR_RIGHT: usize = 1_703_948;

fn emit(stage: &str, detail: &str) {
    println!("C557_JOINED_STAGE|{stage}|{detail}");
}

fn hex_upper(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02X}")).collect()
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex_upper(&role0_sha256(bytes).expect("native SHA-256 of the fixture"))
}

fn blake2b256_hex(bytes: &[u8]) -> String {
    hex_upper(&Blake2b::<U32>::digest(bytes))
}

fn scalar_hex(value: &Fr) -> String {
    let mut bytes = Vec::with_capacity(32);
    value.serialize_compressed(&mut bytes).expect("Vec serialization");
    hex_upper(&bytes)
}

fn point_hex(point: &[Fr]) -> String {
    let mut bytes = Vec::with_capacity(point.len() * 32);
    for coordinate in point {
        coordinate.serialize_compressed(&mut bytes).expect("Vec serialization");
    }
    hex_upper(&bytes)
}

fn read_first_four(bundle: &[u8]) -> (Vec<Vec<u8>>, Vec<usize>, usize) {
    let mut raws = Vec::with_capacity(RAW_RECORDS);
    let mut lengths = Vec::with_capacity(RAW_RECORDS);
    let mut offset = 0usize;
    for _ in 0..RAW_RECORDS {
        let length_end = offset.checked_add(4).expect("RAW length offset");
        let length_bytes: [u8; 4] = bundle
            .get(offset..length_end)
            .expect("four-byte RAW length")
            .try_into()
            .expect("four-byte RAW length shape");
        let length = u32::from_le_bytes(length_bytes) as usize;
        assert_eq!(length, 278, "first four pinned RAW lengths");
        offset = length_end;
        let raw_end = offset.checked_add(length).expect("RAW end offset");
        raws.push(
            bundle
                .get(offset..raw_end)
                .expect("complete pinned RAW")
                .to_vec(),
        );
        lengths.push(length);
        offset = raw_end;
    }
    assert_eq!(offset, RAW_END, "first four RAWs end at byte 1128");
    (raws, lengths, offset)
}

fn real_prefix_fixture() -> (PathBuf, Vec<Vec<u8>>, NativePrefix) {
    let directory = PathBuf::from(
        std::env::var_os(FIXTURE_ENV)
            .expect("NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR must be set explicitly"),
    );
    let path = directory.join(FIXTURE_NAME);
    let bundle = fs::read(&path).expect("read the pinned offline prefix bundle");
    assert_eq!(bundle.len(), FIXTURE_BYTES, "whole-file size");
    let sha256 = sha256_hex(&bundle);
    assert_eq!(sha256, FIXTURE_SHA256, "whole-file SHA-256");
    let blake2b256 = blake2b256_hex(&bundle);
    assert_eq!(blake2b256, FIXTURE_BLAKE2B256, "whole-file BLAKE2b-256");

    let (raws, lengths, offset) = read_first_four(&bundle);
    let input = NativePrefix::from_raw_iter(
        RAW_RECORDS,
        raws.iter().cloned().map(Ok::<Vec<u8>, String>),
    )
    .expect("parse exactly the first four pinned RAWs");
    assert_eq!(input.header_count(), 4);
    assert_eq!(input.genuine_count(), 3);
    assert_eq!(input.slot_count(), 4);
    assert_eq!(input.leaf_count(), 4);
    assert_eq!(input.node_count(), 4);
    assert_eq!(lengths, [278; RAW_RECORDS]);
    assert_eq!(offset, RAW_END);
    (path, raws, input)
}

fn produce_same_x(parent: &WorkTreeHistoryPlan, input: &NativePrefix) -> Vec<Fr> {
    validate_native_plan_input(parent, input).unwrap();
    let producer = NativeOwnerProducer::new_for_history(parent, input).unwrap();
    let expected_classes = [
        OwnerClass::Genesis,
        OwnerClass::Initial,
        OwnerClass::Carry,
        OwnerClass::Carry,
    ];
    let mut x = Vec::new();
    x.try_reserve_exact(X_LEN).expect("reserve the one shared X");
    for owner in 0..RAW_RECORDS {
        let row = producer.produce(owner).unwrap();
        assert_eq!(row.owner(), owner);
        assert_eq!(row.class(), expected_classes[owner]);
        assert_eq!(row.packed_bytes().len(), WIDTH / 8);
        for wire in 0..WIDTH {
            let bit = (row.packed_bytes()[wire / 8] >> (wire % 8)) & 1;
            x.push(Fr::from(bit as u64));
        }
    }
    assert_eq!(x.len(), X_LEN, "one complete owner-major 2^22 X");
    x
}

fn work_terms(relation: &NativeWorkRelation<'_>) -> Vec<Term> {
    let mut terms = Vec::new();
    let count = relation
        .visit_terms(|term| {
            terms.push(term);
            Ok(())
        })
        .unwrap();
    assert_eq!(count, 25_522);
    assert_eq!(terms.len(), count);
    terms
}

fn checked_pair_terms(
    parent: &WorkTreeHistoryPlan,
    start: u64,
) -> (RetainedPairSummary, Vec<Term>) {
    let pair = build_one_for_history(parent, start).unwrap();
    let summary = pair.checked_summary().unwrap();
    let terms = pair.into_terms();
    assert_eq!(summary.start, start);
    assert_eq!(summary.term_count, PAIR_RETAINED_TERMS);
    assert_eq!(summary.owner_terms, [OWNER_RETAINED_TERMS; 2]);
    assert_eq!(summary.omitted_worktree, [OWNER_RETIRED_TERMS; 2]);
    assert_eq!(summary.omitted_a4, [0; 2]);
    assert_eq!(terms.len(), summary.term_count);
    (summary, terms)
}

fn residual_support(terms: &[Term], input: &[Fr], row_count: usize) -> Vec<(usize, Fr)> {
    let mut rows = vec![Fr::zero(); row_count];
    for term in terms {
        assert!(term.row < row_count);
        assert!(term.gate.left < input.len() && term.gate.right < input.len());
        let left = input[term.gate.left];
        let right = input[term.gate.right];
        rows[term.row] += term.gate.c0
            + term.gate.c1 * left
            + term.gate.c2 * right
            + term.gate.c3 * left * right;
    }
    rows.into_iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some((row, value)))
        .collect()
}

struct ProvedEntry {
    entry: JoinedHistoryProofEntry,
    claim: InputClaim,
    full_point: Vec<Fr>,
    gkr_transcript_bytes: u64,
    gkr_challenges: u64,
}

fn prove_and_open(
    verifier: &JoinedHistoryDiagnosticVerifier<'_>,
    kind: JoinedProofKind,
    terms: Vec<Term>,
    input: &[Fr],
    committed: &Committed,
    setup: &Setup,
) -> ProvedEntry {
    assert_eq!(input.len(), 1usize << kind.input_log());
    let circuit = Circuit {
        input_len: input.len(),
        row_count: 1usize << kind.row_log(),
        terms,
    };
    let mut transcript = Transcript::new(kind.domain());
    let (proof, claim) = sparse::prove_with_binding(
        &circuit,
        input,
        0,
        &mut transcript,
        |transcript| verifier.bind_gkr(kind, transcript).expect("joined prechallenge bind"),
    )
    .expect("prove one joined relation");
    assert_eq!(gkr::mle(input, &claim.point).unwrap(), claim.value);
    assert_eq!(claim.point.len(), kind.input_log());
    let full_point = match kind {
        JoinedProofKind::Work => claim.point.clone(),
        JoinedProofKind::Pair0 | JoinedProofKind::Pair2 => super::append_pair_bit(
            &claim.point,
            (kind.pair_start().unwrap() >> 1) as u8,
            kind.input_log(),
        )
        .unwrap(),
    };
    assert_eq!(full_point.len(), JOINED_INPUT_LOG);
    let gkr_bytes = gkr::encode_proof(&proof).unwrap();
    let gkr_transcript_bytes = transcript.bytes_absorbed();
    let gkr_challenges = transcript.challenges();
    drop(proof);
    drop(circuit); // release the only work/pair term vector before PCS open

    super::joined_pcs_separator(kind, &mut transcript);
    let pcs_proof = pcs::open(committed, &full_point, setup, &mut transcript)
        .expect("open the one full-X commitment at q22");
    let pcs_bytes = pcs::encode_proof(&pcs_proof).unwrap();
    ProvedEntry {
        entry: JoinedHistoryProofEntry {
            kind_tag: kind.tag(),
            gkr_bytes,
            pcs_bytes,
        },
        claim,
        full_point,
        gkr_transcript_bytes,
        gkr_challenges,
    }
}

fn emit_proved(stage: &str, kind: JoinedProofKind, proof: &ProvedEntry) {
    emit(
        stage,
        &format!(
            "kind={} gkr_bytes={} pcs_bytes={} gkr_input_log={} pcs_input_log=22 claim_value={} pcs_point_hex={}",
            kind.tag(),
            proof.entry.gkr_bytes.len(),
            proof.entry.pcs_bytes.len(),
            kind.input_log(),
            scalar_hex(&proof.claim.value),
            point_hex(&proof.full_point),
        ),
    );
}

fn setup_and_admitted_key() -> (Setup, AdmittedVerifierKey) {
    let setup = pcs::generate_setup(JOINED_INPUT_LOG).unwrap();
    let key_bytes = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    let regenerated = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    assert_eq!(regenerated.as_slice(), key_bytes.as_slice(), "log22 setup fixture drift");
    let key = verifier_key::admit(JOINED_INPUT_LOG, key_bytes).unwrap();
    assert_eq!(key.log_n(), JOINED_INPUT_LOG);
    assert_eq!(key.id(), &setup.id);
    (setup, key)
}

fn assert_kind_domains(verifier: &JoinedHistoryDiagnosticVerifier<'_>) {
    let kinds = [JoinedProofKind::Work, JoinedProofKind::Pair0, JoinedProofKind::Pair2];
    let mut challenges = Vec::with_capacity(kinds.len());
    for kind in kinds {
        let mut transcript = Transcript::new(kind.domain());
        assert_eq!(transcript.challenges(), 0);
        verifier.bind_gkr(kind, &mut transcript).unwrap();
        assert_eq!(transcript.challenges(), 0, "all context binds precede challenges");
        challenges.push(transcript.challenge_scalar(b"c557-kind-domain-differential"));
    }
    assert_ne!(challenges[0], challenges[1]);
    assert_ne!(challenges[0], challenges[2]);
    assert_ne!(challenges[1], challenges[2]);
}

fn assert_bundle_preflight_negatives(
    verifier: &JoinedHistoryDiagnosticVerifier<'_>,
    bundle: &JoinedHistoryProofBundle,
) {
    {
        let mut wrong_root = bundle.clone();
        wrong_root.header.root[0] ^= 1;
        let error = verifier.verify_bundle(&wrong_root).unwrap_err();
        assert!(error.contains("header"), "root-only header fault: {error}");
    }
    {
        let mut wrong_total = bundle.clone();
        wrong_total.header.total_be28[0] ^= 1;
        let error = verifier.verify_bundle(&wrong_total).unwrap_err();
        assert!(error.contains("header"), "total-only header fault: {error}");
    }
    {
        let mut wrong_headers = bundle.clone();
        wrong_headers.header.headers = 3;
        let error = verifier.verify_bundle(&wrong_headers).unwrap_err();
        assert!(error.contains("header"), "headers-only header fault: {error}");
    }
    {
        let mut wrong_slot_log = bundle.clone();
        wrong_slot_log.header.slot_log = 3;
        let error = verifier.verify_bundle(&wrong_slot_log).unwrap_err();
        assert!(error.contains("header"), "slot-log-only header fault: {error}");
    }
    {
        let mut wrong_pairs = bundle.clone();
        wrong_pairs.header.pair_starts = [2, 0];
        let error = verifier.verify_bundle(&wrong_pairs).unwrap_err();
        assert!(error.contains("header"), "pair-order-only header fault: {error}");
    }
    {
        let mut foreign_key = bundle.clone();
        foreign_key.header.key_id[0] ^= 1;
        let error = verifier.verify_bundle(&foreign_key).unwrap_err();
        assert!(error.contains("header"), "key-id-only header fault: {error}");
    }
    {
        let mut foreign_commitment = bundle.clone();
        foreign_commitment.header.canonical_commitment[0] ^= 1;
        let error = verifier.verify_bundle(&foreign_commitment).unwrap_err();
        assert!(error.contains("header"), "commitment-byte-only header fault: {error}");
    }

    let malformed_commitment = match JoinedHistoryDiagnosticVerifier::new(
        verifier.parent,
        verifier.key,
        &[],
    ) {
        Err(error) => error,
        Ok(_) => panic!("empty commitment bytes unexpectedly admitted"),
    };
    assert!(malformed_commitment.contains("commitment"));

    {
        let mut missing = bundle.clone();
        missing.entries.remove(1);
        assert!(verifier.verify_bundle(&missing).unwrap_err().contains("exactly three"));
    }
    {
        let mut trailing = bundle.clone();
        trailing.entries.push(bundle.entries[2].clone());
        assert!(verifier.verify_bundle(&trailing).unwrap_err().contains("exactly three"));
    }
    {
        let mut swapped = bundle.clone();
        swapped.entries.swap(1, 2);
        assert!(verifier.verify_bundle(&swapped).unwrap_err().contains("order/coverage"));
    }
    {
        let mut duplicate = bundle.clone();
        duplicate.entries[1] = bundle.entries[0].clone();
        assert!(verifier.verify_bundle(&duplicate).unwrap_err().contains("order/coverage"));
    }
    {
        let mut unknown = bundle.clone();
        unknown.entries[1].kind_tag = 255;
        assert!(verifier.verify_bundle(&unknown).unwrap_err().contains("unknown"));
    }
}

fn term_coefficients(term: &Term, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let weight = crate::work_tree_wiring::eq_index(r, term.row)
        * crate::work_tree_wiring::eq_index(u, term.gate.left)
        * crate::work_tree_wiring::eq_index(v, term.gate.right);
    [
        weight * term.gate.c0,
        weight * term.gate.c1,
        weight * term.gate.c2,
        weight * term.gate.c3,
    ]
}

fn verify_omitted_term_control(
    verifier: &JoinedHistoryDiagnosticVerifier<'_>,
    kind: JoinedProofKind,
    entry: &JoinedHistoryProofEntry,
    removed: &Term,
    producer_claim: &InputClaim,
    gkr_transcript_bytes: u64,
    gkr_challenges: u64,
) {
    assert_eq!(kind, JoinedProofKind::Pair0);
    let proof = gkr::decode_dimensions(&[kind.input_log()], &entry.gkr_bytes).unwrap();
    assert_eq!(gkr::encode_proof(&proof).unwrap(), entry.gkr_bytes);
    let mut transcript = Transcript::new(kind.domain());
    verifier.bind_gkr(kind, &mut transcript).unwrap();
    let claim = gkr::verify_with_wiring(
        &[kind.input_log()],
        kind.output_width(),
        &proof,
        &mut transcript,
        |_| {},
        |layer, r, u, v| {
            if layer != 0 {
                return Err(GkrError::ProofLayerCount);
            }
            let global_r = super::append_pair_bit(r, 0, 20)
                .map_err(|_| GkrError::PointDimension)?;
            let global_u = super::append_pair_bit(u, 0, 21)
                .map_err(|_| GkrError::PointDimension)?;
            let global_v = super::append_pair_bit(v, 0, 21)
                .map_err(|_| GkrError::PointDimension)?;
            let mut coefficients = verifier
                .parent
                .coefficients(&global_r, &global_u, &global_v)
                .map_err(|_| GkrError::PointDimension)?;
            let omitted = term_coefficients(removed, &global_r, &global_u, &global_v);
            for (value, term_value) in coefficients.iter_mut().zip(omitted) {
                *value -= term_value;
            }
            Ok(coefficients)
        },
    )
    .expect("parent analytic coefficients minus the isolated Term");
    assert_eq!(claim.point, producer_claim.point);
    assert_eq!(claim.value, producer_claim.value);
    assert_eq!(transcript.bytes_absorbed(), gkr_transcript_bytes);
    assert_eq!(transcript.challenges(), gkr_challenges);

    let full_point = super::append_pair_bit(&claim.point, 0, 21).unwrap();
    assert_eq!(full_point, super::append_pair_bit(&producer_claim.point, 0, 21).unwrap());
    let pcs_proof = pcs::decode_proof(&entry.pcs_bytes, JOINED_INPUT_LOG).unwrap();
    super::joined_pcs_separator(kind, &mut transcript);
    pcs::verify_admitted(
        verifier.commitment,
        claim.value,
        &full_point,
        &pcs_proof,
        verifier.key,
        &mut transcript,
    )
    .expect("the same PCS bytes accept under the exact omitted-Term analytic control");
}

#[test]
#[ignore = "bounded C557 real-prefix joined three-claim Gate2; requires admitted native run"]
fn real_prefix_joined_history_three_claims_gate2() {
    emit("start", "headers=4 slots=4 pair_starts=0,2 input_log=22 proof=GKR+PCS");

    let (fixture_path, raws, native) = real_prefix_fixture();
    let parent = WorkTreeHistoryPlan::compile(
        4,
        2,
        native.root(),
        native.total_be28(),
    )
    .unwrap();
    validate_native_plan_input(&parent, &native).unwrap();
    let mut x = produce_same_x(&parent, &native);
    let root = hex_upper(&parent.descriptor().root);
    let total = hex_upper(&parent.work_profile().total_be28);
    assert_eq!(raws.len(), RAW_RECORDS);
    drop(native);
    drop(raws);
    emit(
        "fixture",
        &format!(
            "file={} bytes={} sha256={} blake2b256={} raw_lengths=278,278,278,278 raw_end=1128 root={} total={} owners=4 owner_major=true x_fields={} native_prefix=true",
            fixture_path.file_name().unwrap().to_string_lossy(),
            FIXTURE_BYTES,
            FIXTURE_SHA256,
            FIXTURE_BLAKE2B256,
            root,
            total,
            x.len(),
        ),
    );

    let (setup, key) = setup_and_admitted_key();
    let committed = pcs::commit(&x, &setup).unwrap();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap();
    let verifier = JoinedHistoryDiagnosticVerifier::new(&parent, &key, &commitment_bytes).unwrap();
    assert_kind_domains(&verifier);
    emit(
        "commit",
        &format!(
            "log_n=22 x_fields={} commitment_bytes={} commitment_blake2b256={} key_id={} work_term_hash={} pair_source_fingerprint={} same_x=true",
            x.len(),
            commitment_bytes.len(),
            blake2b256_hex(&commitment_bytes),
            hex_upper(key.id()),
            verifier.work_term_hash,
            verifier.pair_source_fingerprint,
        ),
    );

    let work = prove_and_open(
        &verifier,
        JoinedProofKind::Work,
        work_terms(&verifier.work_relation),
        &x,
        &committed,
        &setup,
    );
    emit_proved("work", JoinedProofKind::Work, &work);

    let (pair0_summary, pair0_terms) = checked_pair_terms(&parent, PAIR_STARTS[0]);
    assert_eq!(pair0_summary.term_count, PAIR_RETAINED_TERMS);
    let pair0 = prove_and_open(
        &verifier,
        JoinedProofKind::Pair0,
        pair0_terms,
        &x[..PAIR_INPUT_LEN],
        &committed,
        &setup,
    );
    emit_proved("pair0", JoinedProofKind::Pair0, &pair0);

    let (pair2_summary, pair2_terms) = checked_pair_terms(&parent, PAIR_STARTS[1]);
    assert_eq!(pair2_summary.term_count, PAIR_RETAINED_TERMS);
    let pair2_base = PAIR_STARTS[1] as usize * SLOT_INPUT_WIDTH;
    let pair2_input = &x[pair2_base..pair2_base + PAIR_INPUT_LEN];
    let pair2 = prove_and_open(
        &verifier,
        JoinedProofKind::Pair2,
        pair2_terms,
        pair2_input,
        &committed,
        &setup,
    );
    emit_proved("pair2", JoinedProofKind::Pair2, &pair2);

    let bundle = JoinedHistoryProofBundle {
        header: verifier.expected_header(),
        entries: vec![work.entry, pair0.entry, pair2.entry],
    };
    verifier.verify_bundle(&bundle).expect("exact ordered three-claim bundle");

    assert_bundle_preflight_negatives(&verifier, &bundle);
    let mut transplanted = bundle.clone();
    transplanted.entries[1].gkr_bytes = transplanted.entries[2].gkr_bytes.clone();
    let transplant_error = verifier.verify_bundle(&transplanted).unwrap_err();
    assert!(transplant_error.contains("joined history GKR rejected"), "{transplant_error}");
    assert!(!transplant_error.contains("header"), "{transplant_error}");
    drop(transplanted);
    emit(
        "publicbundle",
        "entries=3 order=Work,Pair0,Pair2 one_key22=true one_canonical_C=true pcs_log_n=22 header_context_faults=reject structure_faults=reject matching_header_body_transplant=reaches_GKR_and_rejects accepted=true",
    );

    let JoinedHistoryProofBundle { header: _, entries: good_entries } = bundle;
    drop(verifier);
    drop(committed);

    let saved_bit = x[BAD_X_BIT];
    assert!(saved_bit.is_zero() || saved_bit.is_one());
    x[BAD_X_BIT] = Fr::one() - saved_bit;

    let bad_work_terms = work_terms(&NativeWorkRelation::new(&parent).unwrap());
    assert!(residual_support(&bad_work_terms, &x, 1 << 18).is_empty());
    drop(bad_work_terms);

    let (pair2_check, pair2_terms_check) = checked_pair_terms(&parent, PAIR_STARTS[1]);
    assert_eq!(pair2_check.term_count, PAIR_RETAINED_TERMS);
    assert!(residual_support(
        &pair2_terms_check,
        &x[pair2_base..pair2_base + PAIR_INPUT_LEN],
        PAIR_ROW_COUNT,
    )
    .is_empty());
    drop(pair2_terms_check);

    let (pair0_check, mut bad_pair0_terms) = checked_pair_terms(&parent, PAIR_STARTS[0]);
    assert_eq!(pair0_check.term_count, PAIR_RETAINED_TERMS);
    let bad_support = residual_support(&bad_pair0_terms, &x[..PAIR_INPUT_LEN], PAIR_ROW_COUNT);
    let expected_residual = Fr::one() - Fr::from(2u64) * saved_bit;
    assert_eq!(bad_support, vec![(BAD_PAIR_ROW, expected_residual)]);
    let matches: Vec<usize> = bad_pair0_terms
        .iter()
        .enumerate()
        .filter_map(|(index, term)| {
            (term.row == BAD_PAIR_ROW
                && term.gate.left == BAD_X_BIT
                && term.gate.right == BAD_PAIR_RIGHT
                && term.gate.c0.is_zero()
                && term.gate.c1.is_one()
                && term.gate.c2 == -Fr::one()
                && term.gate.c3.is_zero())
            .then_some(index)
        })
        .collect();
    assert_eq!(matches.len(), 1, "exact retained copy Term");
    let removed = bad_pair0_terms.remove(matches[0]);
    assert!(residual_support(&bad_pair0_terms, &x[..PAIR_INPUT_LEN], PAIR_ROW_COUNT).is_empty());

    let bad_committed = pcs::commit(&x, &setup).unwrap();
    let bad_commitment_bytes = pcs::encode_commitment(&bad_committed.commitment).unwrap();
    assert_ne!(bad_commitment_bytes, commitment_bytes, "bit mutant uses a new full-X C");
    let bad_verifier = JoinedHistoryDiagnosticVerifier::new(&parent, &key, &bad_commitment_bytes)
        .unwrap();
    let context_substitution = JoinedHistoryProofBundle {
        header: bad_verifier.expected_header(),
        entries: good_entries,
    };
    let transplanted_context_gkr = context_substitution.entries[0].gkr_bytes.len();
    let transplanted_context_error = bad_verifier.verify_bundle(&context_substitution).unwrap_err();
    assert!(
        transplanted_context_error.contains("joined history GKR rejected"),
        "{transplanted_context_error}"
    );
    assert!(!transplanted_context_error.contains("header"), "{transplanted_context_error}");
    assert!(!transplanted_context_error.contains("extent"), "{transplanted_context_error}");
    assert!(!transplanted_context_error.contains("PCS"), "{transplanted_context_error}");
    emit(
        "contextsubstitutiongkrreject",
        &format!(
            "header_matches_bad_C=true original_good_bodies=true entries=3 first_work_gkr_bytes={} reject=GKR header_error=false extent_error=false PCS_error=false",
            transplanted_context_gkr,
        ),
    );
    drop(context_substitution);
    let bad_pair0 = prove_and_open(
        &bad_verifier,
        JoinedProofKind::Pair0,
        bad_pair0_terms,
        &x[..PAIR_INPUT_LEN],
        &bad_committed,
        &setup,
    );
    let mutant_gkr_hash = blake2b256_hex(&bad_pair0.entry.gkr_bytes);
    let mutant_pcs_hash = blake2b256_hex(&bad_pair0.entry.pcs_bytes);
    let rejected = bad_verifier
        .replay_entry(
            JoinedProofKind::Pair0,
            &bad_pair0.entry.gkr_bytes,
            &bad_pair0.entry.pcs_bytes,
        )
        .unwrap_err();
    assert!(rejected.contains("TerminalExpression"), "{rejected}");
    emit(
        "mutantprivate_realreject",
        &format!(
            "pair0_row={} residual={} gkr_bytes={} pcs_bytes={} gkr_rejection=TerminalExpression claim_value={} full_q22={} omitted_term_proof=true same_joined_context=true",
            BAD_PAIR_ROW,
            scalar_hex(&expected_residual),
            bad_pair0.entry.gkr_bytes.len(),
            bad_pair0.entry.pcs_bytes.len(),
            scalar_hex(&bad_pair0.claim.value),
            point_hex(&bad_pair0.full_point),
        ),
    );

    verify_omitted_term_control(
        &bad_verifier,
        JoinedProofKind::Pair0,
        &bad_pair0.entry,
        &removed,
        &bad_pair0.claim,
        bad_pair0.gkr_transcript_bytes,
        bad_pair0.gkr_challenges,
    );
    assert_eq!(bad_pair0.entry.gkr_bytes.len(), 4_800);
    assert_eq!(blake2b256_hex(&bad_pair0.entry.gkr_bytes), mutant_gkr_hash);
    assert_eq!(blake2b256_hex(&bad_pair0.entry.pcs_bytes), mutant_pcs_hash);
    x[BAD_X_BIT] = saved_bit;
    assert_eq!(x[BAD_X_BIT], saved_bit, "restore the mutated source bit");
    emit(
        "omittedsameCPCS",
        &format!(
            "gkr_bytes={} pcs_bytes={} same_gkr=true same_claim=true same_pair0_C=true same_key=true same_transcript_prefix=true pcs_accepts=true omitted_term_count=1 bit_restored=true",
            bad_pair0.entry.gkr_bytes.len(),
            bad_pair0.entry.pcs_bytes.len(),
        ),
    );

    drop(bad_committed);
    emit(
        "PASS",
        "fixture=real_offline_prefix owners=4 shared_X=1 key22=1 C_per_positive_triplet=1 work=true pair0=true pair2=true public_bundle=true C_context_substitution_GKR_reject=true mutant_terminal_reject=true omitted_same_C_PCS_control=true bit_restored=true full_history=false production_crypto_or_acceptance=false",
    );
}

const C558_TREE_LOCAL_ROW_BITS: usize = 16;
const C558_TREE_FAMILY_COUNT: usize = 23;
const C558_TREE_BASE_FAMILIES: usize = 20;
const C558_TREE_PUBLIC_ROOT_FAMILY: usize = 9;
const C558_TREE_B4_FAMILY: usize = 16;
const C558_TREE_FAMILY_NAMES: [&str; C558_TREE_FAMILY_COUNT] = [
    "header_to_leaf_raw_length_nbits_height",
    "node_profile_output_core_alias",
    "node_message_child_0",
    "node_message_child_1",
    "profile_digest_fanout",
    "level_1_child_0",
    "level_1_child_1",
    "level_2_child_0",
    "level_2_child_1",
    "public_root",
    "inactive_tree_endpoints",
    "padding_leaf_unused_header_aliases",
    "profile_slot_unused_child_endpoints",
    "endpoint_bank_padding",
    "B2_fixed_hash",
    "B3_leaf_hash",
    "B4_work",
    "work_first_lower_zero",
    "work_interval_continuity",
    "work_public_total",
    "daa_genesis",
    "daa_inherit_height3",
    "daa_inherit_height4",
];

struct C558ResidualSupport {
    rows: Vec<usize>,
    family_rows: Vec<usize>,
}

fn emit_c558_tree_stage(stage: &str, detail: &str) {
    println!("C558_TREE_STAGE|{stage}|{detail}");
}

fn c558_tree_family_counts(circuit: &Circuit) -> Vec<usize> {
    let mut counts = vec![0usize; C558_TREE_FAMILY_COUNT];
    for term in &circuit.terms {
        let family = term.row >> C558_TREE_LOCAL_ROW_BITS;
        assert!(family < counts.len(), "H4 term has unknown family tag: row={}", term.row);
        counts[family] += 1;
    }
    counts
}

fn c558_tree_family_hashes(circuit: &Circuit) -> Vec<String> {
    let mut grouped = vec![Vec::<Term>::new(); C558_TREE_FAMILY_COUNT];
    for term in &circuit.terms {
        let family = term.row >> C558_TREE_LOCAL_ROW_BITS;
        assert!(family < grouped.len(), "H4 term has unknown family tag: row={}", term.row);
        grouped[family].push(term.clone());
    }
    grouped
        .iter()
        .map(|terms| crate::work_tree_layout::hash_terms(terms))
        .collect()
}

fn c558_tree_census_text(counts: &[usize]) -> String {
    C558_TREE_FAMILY_NAMES
        .iter()
        .zip(counts)
        .map(|(name, count)| format!("{name}:{count}"))
        .collect::<Vec<_>>()
        .join(",")
}

fn c558_direct_residuals(circuit: &Circuit, input: &[Fr]) -> Vec<Fr> {
    assert_eq!(input.len(), circuit.input_len, "H4 direct residual input length");
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        rows[term.row] += term.gate.evaluate(input);
    }
    rows
}

fn c558_scan_residuals(residuals: &[Fr]) -> C558ResidualSupport {
    let mut rows = Vec::new();
    let mut family_rows = vec![0usize; 1 << (21 - C558_TREE_LOCAL_ROW_BITS)];
    for (row, residual) in residuals.iter().enumerate() {
        if !residual.is_zero() {
            rows.push(row);
            family_rows[row >> C558_TREE_LOCAL_ROW_BITS] += 1;
        }
    }
    C558ResidualSupport { rows, family_rows }
}

fn c558_residual_diagnostic(circuit: &Circuit, support: &C558ResidualSupport) -> String {
    let mut row_details = Vec::new();
    for &row in support.rows.iter().take(12) {
        let family = row >> C558_TREE_LOCAL_ROW_BITS;
        let role = C558_TREE_FAMILY_NAMES.get(family).copied().unwrap_or("unknown");
        let mut wires = Vec::new();
        let mut term_count = 0usize;
        for term in circuit.terms.iter().filter(|term| term.row == row) {
            term_count += 1;
            wires.push(term.gate.left);
            wires.push(term.gate.right);
        }
        wires.sort_unstable();
        wires.dedup();
        row_details.push(format!("{role}[{family}]row={row}terms={term_count}wires={wires:?}"));
    }
    let family_details = support
        .family_rows
        .iter()
        .enumerate()
        .filter(|(_, count)| **count != 0)
        .map(|(family, count)| {
            format!(
                "{}[{family}]={count}",
                C558_TREE_FAMILY_NAMES.get(family).copied().unwrap_or("unknown")
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "nonzero_rows={} family_rows=[{}] first_rows=[{}]",
        support.rows.len(),
        family_details,
        row_details.join(";")
    )
}

fn c558_assert_exact_support(
    label: &str,
    circuit: &Circuit,
    input: &[Fr],
    expected_rows: &[usize],
) -> String {
    let residuals = c558_direct_residuals(circuit, input);
    let support = c558_scan_residuals(&residuals);
    let diagnostic = c558_residual_diagnostic(circuit, &support);
    assert!(
        support.rows.as_slice() == expected_rows,
        "{label}: residual support differs from the source-reviewed rows; {diagnostic} expected_rows={expected_rows:?}"
    );
    drop(residuals);
    diagnostic
}

fn c558_flip_boolean(input: &mut [Fr], index: usize) -> Fr {
    let old = input[index];
    assert!(old.is_zero() || old.is_one(), "selected C558 X wire is not Boolean");
    input[index] = if old.is_zero() { Fr::one() } else { Fr::zero() };
    old
}

#[test]
#[ignore = "bounded C558 no-curve real-prefix native-X Gate1; requires separately admitted native run"]
fn real_prefix_h4_tree_native_x_gate1() {
    emit_c558_tree_stage("fixture", "loader=real_prefix_fixture raw_records=4 raw_lengths=278,278,278,278 raw_end=1128");
    let (fixture_path, raws, native) = real_prefix_fixture();
    let parent = WorkTreeHistoryPlan::compile(4, 2, native.root(), native.total_be28()).unwrap();
    validate_native_plan_input(&parent, &native).unwrap();
    let root = parent.descriptor().root;
    let total = parent.work_profile().total_be28;
    let mut x = produce_same_x(&parent, &native);
    assert_eq!(x.len(), X_LEN, "complete native owner-major C557 X");
    emit_c558_tree_stage(
        "production",
        "producer=NativeOwnerProducer classes=genesis,initial,carry,carry owners=4 owner_major=true map=false zero_advice=false",
    );
    emit_c558_tree_stage(
        "context",
        &format!(
            "root={} total_work_be28={} x_fields={}",
            hex_upper(&root),
            hex_upper(&total),
            x.len()
        ),
    );
    drop(native);
    drop(raws);
    drop(parent);

    let plan = crate::h4_analytic::Plan::new(root, total).unwrap();
    let tree = plan.tree_circuit().unwrap();
    let shape = sparse::validate(&tree, 0).unwrap();
    assert_eq!(tree.input_len, 1 << 22, "H4 X dimension");
    assert_eq!(tree.row_count, 1 << 21, "H4 row dimension");
    assert_eq!(tree.terms.len(), 126_573, "H4 term census");
    let source_counts = plan.tree_family_term_counts_for_test().unwrap();
    let emitted_counts = c558_tree_family_counts(&tree);
    assert_eq!(source_counts.len(), C558_TREE_FAMILY_COUNT);
    assert_eq!(source_counts[..C558_TREE_BASE_FAMILIES].iter().sum::<usize>(), 125_901);
    assert_eq!(&source_counts[C558_TREE_BASE_FAMILIES..], &[224, 224, 224]);
    assert_eq!(source_counts.iter().sum::<usize>(), 126_573);
    assert_eq!(emitted_counts, source_counts, "all 23 row-tag family counts");
    emit_c558_tree_stage(
        "census",
        &format!(
            "input_len={} row_count={} terms={} families={}",
            tree.input_len,
            tree.row_count,
            tree.terms.len(),
            c558_tree_census_text(&emitted_counts)
        ),
    );
    let baseline_family_hashes = c558_tree_family_hashes(&tree);

    let positive_residuals = c558_direct_residuals(&tree, &x);
    let positive_support = c558_scan_residuals(&positive_residuals);
    let positive_diagnostic = c558_residual_diagnostic(&tree, &positive_support);
    assert!(
        positive_support.rows.is_empty(),
        "native C557 X does not satisfy the direct H4 tree relation; {positive_diagnostic}"
    );
    drop(positive_residuals);
    emit_c558_tree_stage("positive", "all_rows_zero=true proof=false");

    let r: Vec<_> = (0..21).map(|i| Fr::from(1009 + 37 * (i as u64))).collect();
    let u: Vec<_> = (0..22).map(|i| Fr::from(2027 + 41 * (i as u64))).collect();
    let v: Vec<_> = (0..22).map(|i| Fr::from(4099 + 43 * (i as u64))).collect();
    assert!(r.iter().chain(&u).chain(&v).all(|value| !value.is_zero() && !value.is_one()));
    let analytic = plan.tree_coefficients_for_test(&r, &u, &v).unwrap();
    let emitted = sparse::wiring(&tree, &shape, &r, &u, &v).unwrap();
    assert_eq!(emitted, analytic, "same-plan emitted versus analytic H4 coefficients");
    assert!(plan.tree_coefficients_for_test(&r[..20], &u, &v).is_err(), "analytic r dimension");
    assert!(plan.tree_coefficients_for_test(&r, &u[..21], &v).is_err(), "analytic u dimension");
    assert!(plan.tree_coefficients_for_test(&r, &u, &v[..21]).is_err(), "analytic v dimension");
    assert!(sparse::wiring(&tree, &shape, &r[..20], &u, &v).is_err(), "emitted r dimension");
    assert!(sparse::wiring(&tree, &shape, &r, &u[..21], &v).is_err(), "emitted u dimension");
    assert!(sparse::wiring(&tree, &shape, &r, &u, &v[..21]).is_err(), "emitted v dimension");
    drop((r, u, v));
    drop(plan);
    emit_c558_tree_stage(
        "differential",
        "points=1 non_boolean=true dimensions=21,22,22 coefficients=4 exact=true invalid_r_u_v=rejected analytic_and_emitted=true",
    );

    let endpoints = crate::work_tree_layout::Endpoints::new();
    let leaf_wire = endpoints.raw[0];
    let leaf_index = leaf_wire;
    let saved_leaf = c558_flip_boolean(&mut x, leaf_index);
    let expected_leaf_rows = [8_192usize, 984_408]; // (15 << 16) + 64 + 512 + 99 * 8
    let leaf_support = c558_assert_exact_support(
        "single raw[0] bit changes B1 successor alias and B3 leaf message",
        &tree,
        &x,
        &expected_leaf_rows,
    );
    x[leaf_index] = saved_leaf;
    assert_eq!(x[leaf_index], saved_leaf, "restore the selected RAW-derived leaf bit");
    emit_c558_tree_stage(
        "negative_leaf",
        &format!("raw_endpoint_wire={leaf_wire} bit=0 restored=true {leaf_support}"),
    );

    let work_wire = endpoints.work[0];
    let daa_group0_tags = [20usize, 21usize];
    let daa_group1_tags = [21usize, 22usize];
    let daa_group2_tags = [22usize];
    for (group, owner, daa_tags) in [
        (0usize, 0usize, &daa_group0_tags[..]),
        (1usize, 1usize, &daa_group1_tags[..]),
        (2usize, 2usize, &daa_group2_tags[..]),
    ] {
        let input_index = owner * WIDTH + work_wire;
        let saved_work = c558_flip_boolean(&mut x, input_index);
        let b4_base = (C558_TREE_B4_FAMILY << 16) + owner * 2_048;
        let mut expected_rows = vec![b4_base + 1_187, b4_base + 1_433, b4_base + 1_434];
        expected_rows.extend(daa_tags.iter().map(|family| *family << 16));
        expected_rows.sort_unstable();
        let support = c558_assert_exact_support(
            &format!("single DAA group {group} work bit 0"),
            &tree,
            &x,
            &expected_rows,
        );
        x[input_index] = saved_work;
        assert_eq!(x[input_index], saved_work, "restore the selected DAA work bit");
        emit_c558_tree_stage(
            &format!("negative_daa_{group}"),
            &format!("owner={owner} work_wire={work_wire} bit=0 restored=true {support}"),
        );
    }
    drop(shape);
    drop(tree);

    let mut wrong_root = root;
    wrong_root[0] ^= 1;
    let wrong_descriptor = crate::work_tree_wiring::Descriptor::new(4, wrong_root).unwrap();
    let wrong_plan = crate::h4_analytic::Plan::new(wrong_root, total).unwrap();
    let wrong_tree = wrong_plan.tree_circuit().unwrap();
    assert_eq!(wrong_tree.input_len, 1 << 22);
    assert_eq!(wrong_tree.row_count, 1 << 21);
    assert_eq!(wrong_tree.terms.len(), 126_573);
    assert_eq!(
        wrong_plan.tree_family_term_counts_for_test().unwrap(),
        source_counts,
        "single public-root-bit context fault preserves every family count"
    );
    let wrong_family_hashes = c558_tree_family_hashes(&wrong_tree);
    for family in 0..C558_TREE_FAMILY_COUNT {
        if family == C558_TREE_PUBLIC_ROOT_FAMILY {
            assert_ne!(
                wrong_family_hashes[family], baseline_family_hashes[family],
                "public_root family must bind the changed root bit"
            );
        } else {
            assert_eq!(
                wrong_family_hashes[family], baseline_family_hashes[family],
                "root context mutation changed unrelated family {}",
                C558_TREE_FAMILY_NAMES[family]
            );
        }
    }
    let expected_root_rows = [
        (C558_TREE_PUBLIC_ROOT_FAMILY << 16) + wrong_descriptor.root_node_slot * 256,
    ];
    let root_support = c558_assert_exact_support(
        "single public-root bit with fixed X and total",
        &wrong_tree,
        &x,
        &expected_root_rows,
    );
    emit_c558_tree_stage(
        "negative_root",
        &format!("changed_root_bit=0 x_fixed=true total_unchanged=true {root_support}"),
    );
    drop(wrong_tree);
    drop(wrong_plan);
    emit_c558_tree_stage(
        "PASS",
        "direct_h4_residual_gate1=true no_curve=true proof=false full_history=false adjacency=false all_retarget_or_S_rules=false",
    );
}

fn emit_c559(stage: &str, detail: &str) {
    println!("C559_TREE_PROOF_STAGE|{stage}|{detail}");
}

fn c559_tree_family_hashes(circuit: &Circuit) -> Vec<String> {
    // The canonical emitter appends each tagged family contiguously. Hash its
    // borrowed slice instead of cloning the complete term roster into groups.
    let mut cursor = 0usize;
    let mut hashes = Vec::with_capacity(23);
    for family in 0..23 {
        let start = cursor;
        while cursor < circuit.terms.len() && circuit.terms[cursor].row >> 16 == family {
            cursor += 1;
        }
        hashes.push(crate::work_tree_layout::hash_terms(&circuit.terms[start..cursor]));
    }
    assert_eq!(cursor, circuit.terms.len(), "canonical contiguous family order");
    hashes
}

fn c559_preflight_negatives(
    verifier: &super::Core3TreeDiagnosticVerifier<'_>,
    good: &super::Core3TreeProofBundle,
) {
    fn header_fault(verifier: &super::Core3TreeDiagnosticVerifier<'_>,
        good: &super::Core3TreeProofBundle,
        change: impl FnOnce(&mut super::Core3TreeProofHeader))
    {
        let mut bad = good.clone();
        change(&mut bad.header);
        let error = verifier.verify_bundle(&bad).unwrap_err();
        assert!(error.contains("header"), "{error}");
    }
    header_fault(verifier, good, |h| h.core3.root[0] ^= 1);
    header_fault(verifier, good, |h| h.core3.total_be28[0] ^= 1);
    header_fault(verifier, good, |h| h.core3.headers = 3);
    header_fault(verifier, good, |h| h.core3.slot_log = 3);
    header_fault(verifier, good, |h| h.core3.pair_starts.swap(0, 1));
    header_fault(verifier, good, |h| h.core3.key_id[0] ^= 1);
    header_fault(verifier, good, |h| h.core3.canonical_commitment[0] ^= 1);
    header_fault(verifier, good, |h| h.version += 1);
    header_fault(verifier, good, |h| h.profile[0] ^= 1);
    header_fault(verifier, good, |h| h.coverage.swap(2, 3));
    header_fault(verifier, good, |h| h.pcs_input_log = 21);
    header_fault(verifier, good, |h| h.tree_input_log = 21);
    header_fault(verifier, good, |h| h.tree_row_log = 20);
    header_fault(verifier, good, |h| h.tree_terms -= 1);
    header_fault(verifier, good, |h| h.tree_families -= 1);
    header_fault(verifier, good, |h| h.tree_source.push('0'));
    for (fault, expected) in [(0, "exactly four"), (1, "exactly four"),
        (2, "order/coverage"), (3, "order/coverage"), (4, "unknown")]
    {
        let mut bad = good.clone();
        match fault {
            0 => { bad.entries.pop(); }
            1 => bad.entries.push(good.entries[3].clone()),
            2 => bad.entries.swap(2, 3),
            3 => bad.entries[3].kind_tag = 2,
            4 => bad.entries[3].kind_tag = 255,
            _ => unreachable!(),
        }
        let error = verifier.verify_bundle(&bad).unwrap_err();
        assert!(error.contains(expected), "{error}");
    }
    // New wrapper extents are checked for every role before the Core3 replay.
    for index in 0..4 {
        for pcs_body in [false, true] {
            let mut bad = good.clone();
            if pcs_body { bad.entries[index].pcs_bytes.push(0); }
            else { bad.entries[index].gkr_bytes.push(0); }
            let error = verifier.verify_bundle(&bad).unwrap_err();
            assert!(error.contains("extent"), "{error}");
        }
    }
}

fn c559_prove_tree(
    verifier: &super::Core3TreeDiagnosticVerifier<'_>,
    x: &[Fr], committed: &Committed, setup: &Setup,
    omitted_circuit: Option<Circuit>,
) -> ProvedEntry {
    let mut transcript = Transcript::new(super::CORE3_TREE_DOMAIN);
    verifier.bind_tree_outer(&mut transcript).unwrap();
    assert_eq!(transcript.challenges(), 0);
    let (proof, claim) = match omitted_circuit {
        None => verifier.tree.prove_tree(x, &mut transcript).unwrap(),
        Some(circuit) => {
            let result = sparse::prove_with_binding(&circuit, x, 0, &mut transcript,
                |t| verifier.tree.bind_tree_for_test(t).unwrap()).unwrap();
            drop(circuit);
            result
        }
    };
    assert_eq!(claim.point.len(), 22);
    assert_eq!(gkr::mle(x, &claim.point).unwrap(), claim.value);
    let gkr_bytes = gkr::encode_proof(&proof).unwrap();
    assert_eq!(gkr_bytes.len(), 5_024);
    let gkr_transcript_bytes = transcript.bytes_absorbed();
    let gkr_challenges = transcript.challenges();
    drop(proof); // the ordinary prover's circuit has also been released
    super::core3_tree_pcs_separator(&mut transcript);
    let pcs_proof = pcs::open(committed, &claim.point, setup, &mut transcript).unwrap();
    let pcs_bytes = pcs::encode_proof(&pcs_proof).unwrap();
    assert_eq!(pcs_bytes.len(), 29_421);
    ProvedEntry { entry: JoinedHistoryProofEntry { kind_tag: 3, gkr_bytes, pcs_bytes },
        full_point: claim.point.clone(), claim, gkr_transcript_bytes, gkr_challenges }
}

fn c559_omitted_tree_control(
    verifier: &super::Core3TreeDiagnosticVerifier<'_>,
    mutant: &ProvedEntry, removed: &Term,
) {
    let proof = gkr::decode_dimensions(&[22], &mutant.entry.gkr_bytes).unwrap();
    assert_eq!(gkr::encode_proof(&proof).unwrap(), mutant.entry.gkr_bytes);
    let mut transcript = Transcript::new(super::CORE3_TREE_DOMAIN);
    verifier.bind_tree_outer(&mut transcript).unwrap();
    let claim = gkr::verify_with_wiring(&[22], 1 << 21, &proof, &mut transcript,
        |t| verifier.tree.bind_tree_for_test(t).unwrap(),
        |layer, r, u, v| {
            if layer != 0 { return Err(GkrError::ProofLayerCount); }
            let mut coefficients = verifier.tree.tree_coefficients_for_test(r, u, v)
                .map_err(|_| GkrError::PointDimension)?;
            // Three O(log) eq_index evaluations, no dense input/row tables.
            for (value, term) in coefficients.iter_mut().zip(term_coefficients(removed, r, u, v)) {
                *value -= term;
            }
            Ok(coefficients)
        }).expect("exact full H4 analytic relation minus one complete root Term");
    assert_eq!(claim.point, mutant.claim.point);
    assert_eq!(claim.value, mutant.claim.value);
    assert_eq!(claim.point, mutant.full_point);
    assert_eq!(transcript.bytes_absorbed(), mutant.gkr_transcript_bytes);
    assert_eq!(transcript.challenges(), mutant.gkr_challenges);
    let pcs_proof = pcs::decode_proof(&mutant.entry.pcs_bytes, 22).unwrap();
    super::core3_tree_pcs_separator(&mut transcript);
    pcs::verify_admitted(verifier.core3.commitment, claim.value, &claim.point,
        &pcs_proof, verifier.core3.key, &mut transcript)
        .expect("identical GKR/query/value/C/key/PCS and transcript control accepts");
}

fn c559_export_case(path: &std::path::Path, bundle: &super::Core3TreeProofBundle,
    witness_ms: u128, setup_ms: u128, commit_ms: u128, admission_ms: u128,
    proof_ms: u128, verify_ms: u128)
{
    use std::io::Write;
    const CASE_BOUND: usize = 1_048_576;
    const BODY_BOUND: usize = 32_768;
    fn create(path: &std::path::Path, name: &str, bytes: &[u8]) {
        let mut file = fs::OpenOptions::new().write(true).create_new(true)
            .open(path.join(name)).expect("create-only C559 case file");
        file.write_all(bytes).expect("complete case write");
        file.flush().expect("flush case file");
        file.sync_all().expect("sync case file");
        assert_eq!(file.metadata().unwrap().len(), bytes.len() as u64);
    }
    let roles = ["work", "pair0", "pair2", "tree"];
    let mut files: Vec<(String, Vec<u8>)> = Vec::with_capacity(12);
    let mut bodies = Vec::with_capacity(4);
    for (index, (entry, role)) in bundle.entries.iter().zip(roles).enumerate() {
        assert_eq!(entry.kind_tag, index as u8);
        let mut record = serde_json::json!({"role":role,"tag":index,
            "gkr_input_log":if index == 1 || index == 2 {21} else {22},
            "row_log":if index == 0 {18} else if index == 3 {21} else {20},
            "pcs_input_log":22});
        for (kind, bytes) in [("gkr", &entry.gkr_bytes), ("pcs", &entry.pcs_bytes)] {
            assert!(bytes.len() <= BODY_BOUND);
            let name = format!("{role}.{kind}.bin");
            record[kind] = serde_json::json!({"file":name,"bytes":bytes.len(),
                "blake2b256":blake2b256_hex(bytes)});
            files.push((name, bytes.clone()));
        }
        bodies.push(record);
    }
    let h = &bundle.header;
    let key = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    files.push(("commitment.bin".into(), h.core3.canonical_commitment.clone()));
    files.push(("log22.vk".into(), key.to_vec()));
    let context = serde_json::json!({
        "schema":"nipopow-c559-internal-four-claim-case-v1",
        "version":h.version,"profile":std::str::from_utf8(&h.profile).unwrap(),
        "coverage":h.coverage,"root":hex_upper(&h.core3.root),
        "total_be28":hex_upper(&h.core3.total_be28),"headers":h.core3.headers,
        "slot_log":h.core3.slot_log,"pair_starts":h.core3.pair_starts,
        "key_log_n":h.pcs_input_log,"key_id":hex_upper(&h.core3.key_id),
        "key_file":"log22.vk","key_blake2b256":blake2b256_hex(key),
        "pcs_mode":"Transparent-dory-v1","vendor":hex_upper(pcs::VENDOR_PIN),
        "commitment_file":"commitment.bin",
        "commitment_hex":hex_upper(&h.core3.canonical_commitment),
        "commitment_blake2b256":blake2b256_hex(&h.core3.canonical_commitment),
        "tree_source_blake2b256":h.tree_source,
        "tree_input_log":h.tree_input_log,"tree_row_log":h.tree_row_log,
        "tree_terms":h.tree_terms,"tree_families":h.tree_families,
        "tree_domain":std::str::from_utf8(super::CORE3_TREE_DOMAIN).unwrap(),
        "bodies":bodies,"measurements_ms":{"witness":witness_ms,"setup_and_key":setup_ms,
            "commit":commit_ms,"verifier_plan_admission":admission_ms,
            "proof_production":proof_ms,"verification_only":verify_ms}
    });
    files.push(("context.json".into(), serde_json::to_vec_pretty(&context).unwrap()));
    let manifest: Vec<_> = files.iter().map(|(name, bytes)|
        serde_json::json!({"file":name,"bytes":bytes.len(),
            "blake2b256":blake2b256_hex(bytes)})).collect();
    files.push(("files.json".into(), serde_json::to_vec_pretty(&manifest).unwrap()));
    let total = files.iter().try_fold(0usize, |total, (_, bytes)| total.checked_add(bytes.len()))
        .expect("bounded case size sum");
    assert!(total <= CASE_BOUND, "C559 case exceeds one MiB");
    assert!(!path.exists(), "C559 case output must be absent");
    fs::create_dir(path).expect("create fresh project-local case directory");
    for (name, bytes) in &files { create(path, name, bytes); }
    emit_c559("export", &format!("files={} body_files=8 bytes={total} create_new=true flushed=true", files.len()));
}

#[test]
#[ignore = "bounded C559 fresh four-claim proof/export; requires separately admitted native run"]
fn real_prefix_core3_tree_four_claims_one_run() {
    use std::time::Instant;
    let case_dir = PathBuf::from(std::env::var_os("NIPOPOW_C559_CASE_DIR")
        .expect("NIPOPOW_C559_CASE_DIR must be explicit"));
    assert!(case_dir.is_absolute() && !case_dir.exists());
    assert!(case_dir.parent().expect("case parent").is_dir());
    emit_c559("fixture", "loader=real_prefix_fixture raw_records=4 raw_lengths=278,278,278,278 raw_end=1128");
    let witness_start = Instant::now();
    let (_fixture_path, raws, native) = real_prefix_fixture();
    let parent = WorkTreeHistoryPlan::compile(4, 2, native.root(), native.total_be28()).unwrap();
    validate_native_plan_input(&parent, &native).unwrap();
    let x = produce_same_x(&parent, &native);
    let witness_ms = witness_start.elapsed().as_millis();
    drop(native);
    drop(raws);
    emit_c559("production", &format!("producer=NativeOwnerProducer owners=4 x_fields={} witness_ms={witness_ms}", x.len()));
    let start = Instant::now();
    let (setup, key) = setup_and_admitted_key();
    let setup_ms = start.elapsed().as_millis();
    emit_c559("setup", &format!("key_log=22 admitted=true setup_ms={setup_ms}"));
    let start = Instant::now();
    let committed = pcs::commit(&x, &setup).unwrap();
    let canonical_c = pcs::encode_commitment(&committed.commitment).unwrap();
    let commit_ms = start.elapsed().as_millis();
    let start = Instant::now();
    let verifier = super::Core3TreeDiagnosticVerifier::new(&parent, &key, &canonical_c).unwrap();
    let mut admission_ms = start.elapsed().as_millis();
    assert_kind_domains(&verifier.core3);
    let mut prechallenge = Transcript::new(super::CORE3_TREE_DOMAIN);
    verifier.bind_tree_outer(&mut prechallenge).unwrap();
    verifier.tree.bind_tree_for_test(&mut prechallenge).unwrap();
    assert_eq!(prechallenge.challenges(), 0);
    drop(prechallenge);
    emit_c559("commit", &format!("commitment_bytes={} shared_C=1 commit_ms={commit_ms} verifier_plan_admission_ms={admission_ms}", canonical_c.len()));

    let mut proof_ms = 0u128;
    let start = Instant::now();
    let work = prove_and_open(&verifier.core3, JoinedProofKind::Work,
        work_terms(&verifier.core3.work_relation), &x, &committed, &setup);
    proof_ms += start.elapsed().as_millis();
    emit_c559("core3work", &format!("gkr_bytes={} pcs_bytes={}", work.entry.gkr_bytes.len(), work.entry.pcs_bytes.len()));
    let start = Instant::now();
    let (_, pair0_terms) = checked_pair_terms(&parent, PAIR_STARTS[0]);
    let pair0 = prove_and_open(&verifier.core3, JoinedProofKind::Pair0,
        pair0_terms, &x[..PAIR_INPUT_LEN], &committed, &setup);
    proof_ms += start.elapsed().as_millis();
    emit_c559("pair0", &format!("gkr_bytes={} pcs_bytes={}", pair0.entry.gkr_bytes.len(), pair0.entry.pcs_bytes.len()));
    let start = Instant::now();
    let (_, pair2_terms) = checked_pair_terms(&parent, PAIR_STARTS[1]);
    let pair2_base = PAIR_STARTS[1] as usize * SLOT_INPUT_WIDTH;
    let pair2 = prove_and_open(&verifier.core3, JoinedProofKind::Pair2,
        pair2_terms, &x[pair2_base..pair2_base + PAIR_INPUT_LEN], &committed, &setup);
    proof_ms += start.elapsed().as_millis();
    emit_c559("pair2", &format!("gkr_bytes={} pcs_bytes={}", pair2.entry.gkr_bytes.len(), pair2.entry.pcs_bytes.len()));

    let baseline_family_hashes = {
        let tree = verifier.tree.tree_circuit().unwrap();
        assert_eq!((tree.input_len, tree.row_count, tree.terms.len()), (1 << 22, 1 << 21, 126_573));
        c558_assert_exact_support("positive same-X tree", &tree, &x, &[]);
        c559_tree_family_hashes(&tree)
    }; // release the census circuit and residuals before proof/PCS production
    let start = Instant::now();
    let tree = c559_prove_tree(&verifier, &x, &committed, &setup, None);
    proof_ms += start.elapsed().as_millis();
    emit_c559("treepositive", &format!("gkr_bytes={} pcs_bytes={} global_q22=true", tree.entry.gkr_bytes.len(), tree.entry.pcs_bytes.len()));
    let bundle = super::Core3TreeProofBundle { header: verifier.expected_header(),
        entries: vec![work.entry, pair0.entry, pair2.entry, tree.entry] };
    verifier.verify_bundle(&bundle).expect("four ordinary GKR+PCS paths under one C/key");
    emit_c559("public4verified", "entries=4 order=Work,Pair0,Pair2,Tree all_PCS=true accepted=true");
    c559_preflight_negatives(&verifier, &bundle);
    emit_c559("negativeheaders", "header_faults=16 coverage_faults=5 trailing_body_faults=8 rejected=true");
    for (target, source) in [(0usize, 3usize), (3, 0)] {
        let mut bad = bundle.clone();
        bad.entries[target].gkr_bytes = bundle.entries[source].gkr_bytes.clone();
        let error = verifier.verify_bundle(&bad).unwrap_err();
        assert!(error.contains("GKR rejected"), "{error}");
        assert!(!error.contains("header") && !error.contains("extent"), "{error}");
    }
    emit_c559("contextbody", "Tree_to_Work_and_Work_to_Tree=true matching_header=true equal_extent5024=true reaches_GKR_reject=true");

    // The H4 plan retains term vectors. Release the positive plan before
    // constructing the changed-root plan; only encoded good bodies survive.
    drop(verifier);

    let mut wrong_root = parent.descriptor().root;
    wrong_root[0] ^= 1;
    {
        let wrong_parent = WorkTreeHistoryPlan::compile(4, 2, wrong_root, parent.work_profile().total_be28).unwrap();
        let wrong = super::Core3TreeDiagnosticVerifier::new(&wrong_parent, &key, &canonical_c).unwrap();
        let context_transplant = super::Core3TreeProofBundle {
            header: wrong.expected_header(), entries: bundle.entries.clone() };
        let error = wrong.verify_bundle(&context_transplant).unwrap_err();
        assert!(error.contains("joined history GKR rejected"), "{error}");
        assert!(!error.contains("header") && !error.contains("extent"), "{error}");
        drop(context_transplant);
        let mut wrong_tree = wrong.tree.tree_circuit().unwrap();
        let wrong_hashes = c559_tree_family_hashes(&wrong_tree);
        for family in 0..23 {
            if family == 9 { assert_ne!(wrong_hashes[family], baseline_family_hashes[family]); }
            else { assert_eq!(wrong_hashes[family], baseline_family_hashes[family]); }
        }
        let descriptor = crate::work_tree_wiring::Descriptor::new(4, wrong_root).unwrap();
        let root_row = (9 << 16) + descriptor.root_node_slot * 256;
        assert_eq!(root_row, 590_336);
        let support = c558_assert_exact_support("wrong-public-root only", &wrong_tree, &x, &[root_row]);
        let source_wire = descriptor.root_node_slot * WIDTH + crate::work_tree_layout::Endpoints::new().node[0];
        let expected = Term { row: root_row, gate: gkr::Gate {
            left: source_wire, right: 0, c0: -Fr::from((wrong_root[0] & 1) as u64),
            c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } };
        let positions: Vec<_> = wrong_tree.terms.iter().enumerate()
            .filter_map(|(i, term)| (term == &expected).then_some(i)).collect();
        assert_eq!(positions.len(), 1, "exact complete public-root Term");
        let removed = wrong_tree.terms.remove(positions[0]);
        assert_eq!(removed, expected);
        c558_assert_exact_support("exact omitted-root-Term circuit", &wrong_tree, &x, &[]);
        emit_c559("tree_wrong_root", &format!("root_bit=0 x_fixed=true C_fixed=true total_fixed=true only_public_root_changed=true removed_terms=1 {support}"));
        let start = Instant::now();
        let mutant = c559_prove_tree(&wrong, &x, &committed, &setup, Some(wrong_tree));
        proof_ms += start.elapsed().as_millis();
        let gkr_hash = blake2b256_hex(&mutant.entry.gkr_bytes);
        let pcs_hash = blake2b256_hex(&mutant.entry.pcs_bytes);
        let rejected = wrong.replay_tree_entry(&mutant.entry.gkr_bytes, &mutant.entry.pcs_bytes).unwrap_err();
        assert!(rejected.contains("TerminalExpression"), "{rejected}");
        emit_c559("treeMutantRealReject", "shared_private_path=true rejection=TerminalExpression same_wrong_context=true canonical_binder=true");
        c559_omitted_tree_control(&wrong, &mutant, &removed);
        assert_eq!(blake2b256_hex(&mutant.entry.gkr_bytes), gkr_hash);
        assert_eq!(blake2b256_hex(&mutant.entry.pcs_bytes), pcs_hash);
        emit_c559("omittedsameCcontrol", "identical_GKR_q_value_C_key_PCS=true identical_transcript_prefix=true exact_one_Term_subtraction=true accepted=true source_unchanged=true");
    }
    drop(committed);
    drop(setup);
    drop(x);
    emit_c559("proofproduction", &format!("proof_production_ms={proof_ms} fresh_positive_components=4 fresh_mutant_components=1 prover_and_X_released=true"));
    let start = Instant::now();
    let verifier = super::Core3TreeDiagnosticVerifier::new(&parent, &key, &canonical_c).unwrap();
    admission_ms += start.elapsed().as_millis();
    let start = Instant::now();
    verifier.verify_bundle(&bundle).expect("verification-only encoded public4 replay");
    let verify_ms = start.elapsed().as_millis();
    emit_c559("verify_only", &format!("verification_only_ms={verify_ms} verifier_plan_admission_ms={admission_ms} encoded_entries=4 all_PCS=true witness_or_prover_access=false"));
    c559_export_case(&case_dir, &bundle, witness_ms, setup_ms, commit_ms, admission_ms, proof_ms, verify_ms);
    emit_c559("PASS", "fresh_one_run=true roles=4 same_X_C_key=true semantic_negative=true export_only=true full_history=false production_crypto_or_delivery=false");
}

use super::*;

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;

use crate::{
    daa_work_actions::DaaWorkActions,
    gkr::{self, GkrError, InputClaim},
    pcs::{self, Committed, Setup},
    sparse::{self, Circuit},
    transcript::Transcript,
    verifier_key::{self, AdmittedVerifierKey},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{Endpoints, WIDTH},
};

const INPUT_LOG: usize = 22;
const GENESIS_WORK_FOR_FIXTURE: u64 = 0x0117_6500_0000;
const INPUT_LEN: usize = 1usize << INPUT_LOG;
const ROW_COUNT: usize = 4;

fn public_plan() -> WorkTreeHistoryPlan {
    WorkTreeHistoryPlan::compile(3, 2, [7; 32], [0; 28]).unwrap()
}

fn setup_and_admitted_key() -> (Setup, AdmittedVerifierKey) {
    let setup = pcs::generate_setup(INPUT_LOG).unwrap();
    let key_bytes = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    let regenerated = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    assert_eq!(regenerated.as_slice(), key_bytes.as_slice(), "log22 setup fixture drift");
    let key = verifier_key::admit(INPUT_LOG, key_bytes).unwrap();
    assert_eq!(key.log_n(), INPUT_LOG);
    assert_eq!(key.id(), &setup.id);
    (setup, key)
}

fn numeric_circuit(plan: &WorkTreeHistoryPlan) -> Circuit {
    let actions = DaaWorkActions::new(plan).unwrap();
    assert_eq!(actions.input_log(), INPUT_LOG);
    assert_eq!(actions.row_log(), 2);
    let mut terms = Vec::new();
    let mut counts = [0usize; ROW_COUNT];
    for owner in 0..ROW_COUNT {
        counts[owner] = actions.visit_owner(owner, |term| {
            terms.push(term);
            Ok(())
        }).unwrap();
    }
    assert_eq!(counts[0], 0);
    assert_eq!(counts[1], 225, "one genesis-work row plus its constant");
    assert_eq!(counts[2], 448, "one Carry row compares both parent endpoints");
    assert_eq!(counts[3], 0);
    Circuit { input_len: INPUT_LEN, row_count: ROW_COUNT, terms }
}

fn genesis_work_bit(bit: usize) -> u64 {
    if bit < u64::BITS as usize { (GENESIS_WORK_FOR_FIXTURE >> bit) & 1 } else { 0 }
}

fn public_numeric_input() -> Vec<Fr> {
    // Every field coordinate is explicitly initialized for this numeric-family
    // fixture; this is not a claim about omitted history rows.
    let mut input = vec![Fr::zero(); INPUT_LEN];
    let work = Endpoints::new().work;
    assert_eq!(work.len(), 224);
    for owner in [0usize, 1usize] {
        let base = owner * WIDTH;
        for (bit, &local) in work.iter().enumerate() {
            input[base + local] = Fr::from(genesis_work_bit(bit));
        }
    }
    input[7] = Fr::from(2u64);
    input
}

fn uses_wire(circuit: &Circuit, wire: usize) -> bool {
    circuit.terms.iter().any(|term| term.gate.left == wire || term.gate.right == wire)
}

fn produce_gkr(
    phase: &str, verifier: &NumericDaaVerifier<'_>, circuit: &Circuit, input: &[Fr],
) -> (Vec<u8>, InputClaim, Transcript) {
    println!("C553_NUMERIC_DAA_STAGE {phase}_gkr_start");
    let mut transcript = Transcript::new(DOMAIN);
    let (proof, claim) = sparse::prove_with_binding(
        circuit, input, 0, &mut transcript, |t| verifier.bind_gkr(t),
    ).unwrap();
    assert_eq!(gkr::mle(input, &claim.point).unwrap(), claim.value,
        "producer claim must equal the witness MLE");
    println!("C553_NUMERIC_DAA_STAGE {phase}_gkr_done");
    (gkr::encode_proof(&proof).unwrap(), claim, transcript)
}

fn produce_authenticated_pair(
    phase: &str,
    verifier: &NumericDaaVerifier<'_>, circuit: &Circuit, input: &[Fr],
    committed: &Committed, setup: &Setup,
) -> (Vec<u8>, Vec<u8>, InputClaim) {
    let (gkr_bytes, claim, mut transcript) = produce_gkr(phase, verifier, circuit, input);
    println!("C553_NUMERIC_DAA_STAGE {phase}_pcs_start");
    pcs_separator(&mut transcript);
    let pcs = pcs::open(committed, &claim.point, setup, &mut transcript).unwrap();
    println!("C553_NUMERIC_DAA_STAGE {phase}_pcs_done");
    (gkr_bytes, pcs::encode_proof(&pcs).unwrap(), claim)
}

fn shifted_work_circuit(circuit: &Circuit) -> Circuit {
    let mut shifted = circuit.clone();
    for term in &mut shifted.terms {
        // Constant gates keep their global wire zero. Only actual linear work
        // reads move by one, matching the isolated source-wire mutant.
        if !term.gate.c1.is_zero() {
            term.gate.left = term.gate.left.checked_add(1).unwrap();
        }
    }
    shifted
}

fn shifted_work_input() -> Vec<Fr> {
    let mut input = public_numeric_input();
    let work = Endpoints::new().work;
    for owner in [0usize, 1usize] {
        let base = owner * WIDTH;
        for (bit, &local) in work.iter().enumerate() {
            input[base + local + 1] = Fr::from(genesis_work_bit(bit));
        }
    }
    input
}

#[test]
#[ignore = "bounded authenticated numeric DAA diagnostic"]
fn authenticated_numeric_daa_public_bytes_join() {
    println!("C553_NUMERIC_DAA_STAGE setup22");
    let plan = public_plan();
    let circuit = numeric_circuit(&plan);
    let (setup, key) = setup_and_admitted_key();
    let input_a = public_numeric_input();
    assert_eq!(input_a.len(), INPUT_LEN);
    assert_eq!(input_a[7], Fr::from(2u64));
    assert!(!uses_wire(&circuit, 7), "Fr(2) fixture coordinate must be outside this family");

    println!("C553_NUMERIC_DAA_STAGE positive_commit_start terms={}", circuit.terms.len());
    let committed_a = pcs::commit(&input_a, &setup).unwrap();
    let commitment_a = pcs::encode_commitment(&committed_a.commitment).unwrap();
    println!("C553_NUMERIC_DAA_STAGE positive_commit_done");
    let verifier_a = NumericDaaVerifier::new(&plan, &key, &commitment_a).unwrap();
    let (gkr_a, pcs_a, claim_a) = produce_authenticated_pair(
        "positive", &verifier_a, &circuit, &input_a, &committed_a, &setup,
    );
    verifier_a.verify(&gkr_a, &pcs_a).unwrap();
    println!("C553_NUMERIC_DAA_STAGE positive_verified gkr_bytes={} pcs_bytes={}", gkr_a.len(), pcs_a.len());

    // Reuse the green proof bytes to check each boundary without rebuilding a
    // prover fixture. These are transport faults, not relation mutations.
    let mut truncated_gkr = gkr_a.clone(); truncated_gkr.pop();
    assert!(verifier_a.verify(&truncated_gkr, &pcs_a).is_err());
    let mut trailing_gkr = gkr_a.clone(); trailing_gkr.push(0);
    assert!(verifier_a.verify(&trailing_gkr, &pcs_a).is_err());
    let mut noncanonical_gkr = gkr_a.clone(); noncanonical_gkr[..32].fill(0xff);
    assert!(verifier_a.verify(&noncanonical_gkr, &pcs_a).is_err());
    let mut truncated_pcs = pcs_a.clone(); truncated_pcs.pop();
    assert!(verifier_a.verify(&gkr_a, &truncated_pcs).is_err());
    let mut trailing_pcs = pcs_a.clone(); trailing_pcs.push(0);
    assert!(verifier_a.verify(&gkr_a, &trailing_pcs).is_err());
    let mut noncanonical_pcs = pcs_a.clone(); noncanonical_pcs[..32].fill(0xff);
    assert!(verifier_a.verify(&gkr_a, &noncanonical_pcs).is_err());

    {
        let wrong_root = WorkTreeHistoryPlan::compile(3, 2, [8; 32], [0; 28]).unwrap();
        let wrong_verifier = NumericDaaVerifier::new(&wrong_root, &key, &commitment_a).unwrap();
        assert!(wrong_verifier.verify(&gkr_a, &pcs_a).is_err());
    }
    {
        let wrong_total = WorkTreeHistoryPlan::compile(3, 2, [7; 32], [0x35; 28]).unwrap();
        let wrong_verifier = NumericDaaVerifier::new(&wrong_total, &key, &commitment_a).unwrap();
        assert!(wrong_verifier.verify(&gkr_a, &pcs_a).is_err());
    }
    {
        let wrong_n = WorkTreeHistoryPlan::compile(4, 2, [7; 32], [0; 28]).unwrap();
        let wrong_verifier = NumericDaaVerifier::new(&wrong_n, &key, &commitment_a).unwrap();
        assert!(wrong_verifier.verify(&gkr_a, &pcs_a).is_err());
    }
    let key18 = verifier_key::admit(18, include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert_eq!(NumericDaaVerifier::new(&plan, &key18, &commitment_a).err().unwrap(),
        "numeric DAA key/input dimensions differ");
    {
        let wrong_slots = WorkTreeHistoryPlan::compile(5, 3, [7; 32], [0; 28]).unwrap();
        assert_eq!(NumericDaaVerifier::new(&wrong_slots, &key, &commitment_a).err().unwrap(),
            "numeric DAA key/input dimensions differ");
    }
    let mut trailing_commitment = commitment_a.clone();
    trailing_commitment.push(0);
    assert!(NumericDaaVerifier::new(&plan, &key, &trailing_commitment).err().unwrap()
        .starts_with("numeric DAA commitment rejected:"));
    drop(committed_a);

    println!("C553_NUMERIC_DAA_STAGE cross_x_value_binding");
    assert_eq!(claim_a.point.len(), INPUT_LOG);
    let mut input_b = input_a.clone();
    input_b[7] += Fr::one();
    assert_eq!(input_a[7], Fr::from(2u64));
    assert_eq!(input_b[7], Fr::from(3u64));
    assert!(!uses_wire(&circuit, 7));

    println!("C553_NUMERIC_DAA_STAGE cross_b_commit_start");
    let committed_b = pcs::commit(&input_b, &setup).unwrap();
    let commitment_b = pcs::encode_commitment(&committed_b.commitment).unwrap();
    println!("C553_NUMERIC_DAA_STAGE cross_b_commit_done");
    let verifier_b = NumericDaaVerifier::new(&plan, &key, &commitment_b).unwrap();
    // First rule out a proof already bound to C_A when the expected statement
    // is C_B. The context/key/plan are otherwise the same.
    assert!(verifier_b.verify(&gkr_a, &pcs_a).is_err(),
        "positive proof A must not transfer to C_B");

    // Now bind C_B before proving GKR from the unchanged A witness.
    let (gkr_from_a, claim_from_a, mut producer_transcript) =
        produce_gkr("cross_x", &verifier_b, &circuit, &input_a);
    let value_b = gkr::mle(&input_b, &claim_from_a.point).unwrap();
    assert_ne!(claim_from_a.value, value_b,
        "fixed wire-7 common-X mutant has zero MLE delta at this derived point");
    let (replayed_claim, _) = verifier_b.replay_gkr(&gkr_from_a).unwrap();
    assert_eq!(replayed_claim, claim_from_a);
    println!("C553_NUMERIC_DAA_STAGE cross_b_pcs_start");
    pcs_separator(&mut producer_transcript);
    let pcs_from_b = pcs::open(&committed_b, &claim_from_a.point, &setup,
        &mut producer_transcript).unwrap();
    let pcs_from_b = pcs::encode_proof(&pcs_from_b).unwrap();
    println!("C553_NUMERIC_DAA_STAGE cross_b_pcs_done");
    let cross_error = verifier_b.verify(&gkr_from_a, &pcs_from_b).unwrap_err();
    assert!(cross_error.starts_with("numeric DAA PCS rejected:"),
        "cross-X fixture must reach the PCS value predicate: {cross_error}");

    // Isolated one-fault control: substitute only the value supplied to PCS.
    let mut one_fault = verifier_b.replay_gkr(&gkr_from_a).unwrap();
    one_fault.0.value = value_b;
    pcs_separator(&mut one_fault.1);
    let pcs_proof_b = pcs::decode_proof(&pcs_from_b, INPUT_LOG).unwrap();
    pcs::verify_admitted(committed_b.commitment.clone(), one_fault.0.value,
        &one_fault.0.point, &pcs_proof_b, &key, &mut one_fault.1).unwrap();
    println!("C553_NUMERIC_DAA_CROSS_X_PASS changed_wire=7 gkr_value_differs_from_committed_value=true one_fault_pcs_accepts=true");
    drop(committed_b);
    drop(input_b);
    drop(input_a);

    println!("C553_NUMERIC_DAA_STAGE source_wire_mutant");
    let wrong_circuit = shifted_work_circuit(&circuit);
    let wrong_input = shifted_work_input();
    println!("C553_NUMERIC_DAA_STAGE wrongwire_commit_start");
    let committed_wrong = pcs::commit(&wrong_input, &setup).unwrap();
    let commitment_wrong = pcs::encode_commitment(&committed_wrong.commitment).unwrap();
    println!("C553_NUMERIC_DAA_STAGE wrongwire_commit_done");
    let wrong_verifier = NumericDaaVerifier::new(&plan, &key, &commitment_wrong).unwrap();
    let (wrong_gkr, wrong_claim, mut wrong_producer_transcript) =
        produce_gkr("wrongwire", &wrong_verifier, &wrong_circuit, &wrong_input);
    println!("C553_NUMERIC_DAA_STAGE wrongwire_pcs_start");
    pcs_separator(&mut wrong_producer_transcript);
    let wrong_pcs = pcs::open(&committed_wrong, &wrong_claim.point, &setup,
        &mut wrong_producer_transcript).unwrap();
    let wrong_pcs_bytes = pcs::encode_proof(&wrong_pcs).unwrap();
    println!("C553_NUMERIC_DAA_STAGE wrongwire_pcs_done");
    let rejected = wrong_verifier.verify(&wrong_gkr, &wrong_pcs_bytes).unwrap_err();
    assert!(rejected.contains("TerminalExpression"),
        "real implicit DAA coefficients must reject the shifted wire: {rejected}");

    // Isolated one-fault control: materialize only the shifted test circuit's
    // sparse wiring while keeping the real context binder, commitment and PCS.
    let shape = sparse::validate(&wrong_circuit, 0).unwrap();
    let wrong_proof = gkr::decode_dimensions(&[INPUT_LOG], &wrong_gkr).unwrap();
    let mut wrong_transcript = Transcript::new(DOMAIN);
    let materialized_claim = gkr::verify_with_wiring(
        &[INPUT_LOG], ROW_COUNT, &wrong_proof, &mut wrong_transcript,
        |t| wrong_verifier.bind_gkr(t),
        |layer, r, u, v| {
            if layer != 0 { return Err(GkrError::ProofLayerCount); }
            sparse::wiring(&wrong_circuit, &shape, r, u, v)
        },
    ).unwrap();
    assert_eq!(materialized_claim, wrong_claim);
    pcs_separator(&mut wrong_transcript);
    pcs::verify_admitted(committed_wrong.commitment.clone(), materialized_claim.value,
        &materialized_claim.point, &wrong_pcs, &key, &mut wrong_transcript).unwrap();
    println!("C553_NUMERIC_DAA_WRONG_WIRE_PASS real_implicit_rejects=true materialized_one_fault_accepts=true");

    println!("C553_NUMERIC_DAA_AUTHENTICATED_PASS input_log={} rows={} terms={} malformed_rejects=6 context_rejects=3 dimension_rejects=2 commitment_encoding_rejects=1 cross_x_rejects=1 wrong_wire_rejects=1 isolated_mutants_accept=2",
        INPUT_LOG, ROW_COUNT, circuit.terms.len());
}

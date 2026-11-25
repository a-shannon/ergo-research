use std::{collections::{BTreeMap, BTreeSet}, convert::TryFrom};

use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};

use crate::{
    daa_history_roster::OwnerClass,
    short_daa_layout::Profile,
    sparse::Term,
    sparse_stream_roster::{global_edge_row, EdgeTerm},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH,
    work_tree_wiring::eq_index,
};

use super::{
    checked_mul_u128, power_of_two, EndpointSide, GlobalProducerEndpointPlan,
    GlobalProducerRole, ProducerEndpointShape, WORK_MEMBER_ROW_BITS,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ExactTermKey {
    source_slot: usize,
    family_row: usize,
    row: usize,
    left: usize,
    right: usize,
    coefficients: [[u8; 32]; 4],
}

type Multiset = BTreeMap<ExactTermKey, u128>;

const C563_DOMAIN: &[u8] = b"native-released-header-n3-diagnostic-v1";

fn c563_same_transcript(actual: &crate::transcript::Transcript, expected: &crate::transcript::Transcript) {
    assert_eq!((actual.challenges(), actual.raw_queries(), actual.bytes_absorbed()),
        (expected.challenges(), expected.raw_queries(), expected.bytes_absorbed()));
    let mut actual = actual.clone();
    let mut expected = expected.clone();
    assert_eq!(actual.try_challenge_scalar(b"c563-continuation").unwrap(),
        expected.try_challenge_scalar(b"c563-continuation").unwrap());
}

fn c563_fixture() -> (crate::packed_owner_assembly::NativePrefix, WorkTreeHistoryPlan) {
    let pack: serde_json::Value = serde_json::from_str(include_str!(
        "../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
    let raw = (0..3).map(|i| {
        let text = pack["networks"]["mainnet"]["source_headers_hex"][i].as_str().unwrap();
        let bytes: Vec<u8> = text.as_bytes().chunks_exact(2).map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap()
        }).collect();
        assert_eq!(bytes.len(), 278);
        Ok(bytes)
    });
    let native = crate::packed_owner_assembly::NativePrefix::from_raw_iter(3, raw).unwrap();
    let parent = WorkTreeHistoryPlan::compile(3, 2, native.root(), native.total_be28()).unwrap();
    (native, parent)
}

/// Exercise each previously open RIGHT predicate without changing another field.
fn c563_right_and_coefficient_controls(plan: &GlobalProducerEndpointPlan<'_>) -> Result<(), String> {
    for role in [GlobalProducerRole::Work, GlobalProducerRole::DaaRoster, GlobalProducerRole::ReleasedHeader] {
        let shape = plan.shape(role)?;
        let mut sample = None;
        plan.visit_endpoint(role, EndpointSide::Right, 0, |edge| {
            if sample.is_none() { sample = Some(edge); }
            Ok(())
        })?;
        let sample = sample.ok_or("C563 RIGHT sample absent")?;
        let mut outside = sample.clone();
        outside.term.gate.right = power_of_two(shape.input_log)?;
        let mut count = 0;
        let mut calls = 0;
        let error = GlobalProducerEndpointPlan::send_edge(&shape, role, EndpointSide::Right, 0,
            outside, &mut |_| { calls += 1; Ok(()) }, &mut count).unwrap_err();
        if !error.contains("outside") || calls != 0 || count != 0 {
            return Err(format!("C563 {role:?} RIGHT range did not fail at range check: {error}"));
        }
        let mut partition = sample.clone();
        partition.term.gate.right += WIDTH;
        GlobalProducerEndpointPlan::validate_edge_shape(&shape, &partition)?;
        let error = GlobalProducerEndpointPlan::send_edge(&shape, role, EndpointSide::Right, 0,
            partition, &mut |_| { calls += 1; Ok(()) }, &mut count).unwrap_err();
        if !error.contains("partition") || calls != 0 || count != 0 {
            return Err(format!("C563 {role:?} RIGHT partition did not fail at partition check: {error}"));
        }
        let mut calls = 0;
        let error = plan.visit_endpoint(role, EndpointSide::Right, 0, |_| {
            calls += 1;
            Err("C563 RIGHT first sink stop".into())
        }).unwrap_err();
        if error != "C563 RIGHT first sink stop" || calls != 1 {
            return Err(format!("C563 {role:?} RIGHT did not preserve first sink error"));
        }

        let (r, u, v) = asymmetric_points(&shape);
        let weights = CoefficientWeights::new(&r, &u, &v)?;
        let (baseline, coefficients, _) = actual_for_endpoint(plan, role, EndpointSide::Right, 0, &weights)?;
        let original_key = key(&sample);
        if !baseline.contains_key(&original_key) { return Err("C563 coefficient sample absent".into()); }
        let before = contribution(&sample, &weights)?;
        for field in [0, 2, 3] {
            let mut mutant = sample.clone();
            match field {
                0 => mutant.term.gate.c0 += Fr::one(),
                2 => mutant.term.gate.c2 += Fr::one(),
                3 => mutant.term.gate.c3 += Fr::one(),
                _ => unreachable!(),
            }
            let mut changed = baseline.clone();
            remove_one(&mut changed, &original_key)?;
            add_one(&mut changed, key(&mutant))?;
            let changed_coefficients = add_coefficient_vectors(
                subtract_coefficient_vectors(coefficients, before), contribution(&mutant, &weights)?);
            if occurrence_delta(&baseline, &changed)? != 2 || changed_coefficients == coefficients {
                return Err(format!("C563 {role:?} c{field} occurrence was not distinguished"));
            }
            for coordinate in 0..4 {
                if (changed_coefficients[coordinate] != coefficients[coordinate]) != (coordinate == field) {
                    return Err("C563 isolated coefficient fault changed another coordinate".into());
                }
            }
        }
    }
    Ok(())
}

fn c563_header_locality_controls(plan: &GlobalProducerEndpointPlan<'_>) -> Result<(), String> {
    let shape = plan.shape(GlobalProducerRole::ReleasedHeader)?;
    let mut sample = None;
    plan.roster.visit_header_terms(0, |term| {
        if sample.is_none() { sample = Some(reference_roster_edge(&shape, term)?); }
        Ok(())
    })?;
    let sample = sample.ok_or("C563 HEADER sample absent")?;
    GlobalProducerEndpointPlan::validate_header_locality(&shape, 0, &sample)?;
    for field in 0..3 {
        let mut changed = sample.clone();
        match field {
            0 => {
                changed.source_slot = 1;
                changed.term.row = global_edge_row(1, changed.family_row, shape.slot_log, 19, 0, &[19])?;
            }
            1 => changed.term.gate.left += WIDTH,
            2 => changed.term.gate.right += WIDTH,
            _ => unreachable!(),
        }
        GlobalProducerEndpointPlan::validate_edge_shape(&shape, &changed)?;
        if GlobalProducerEndpointPlan::validate_header_locality(&shape, 0, &changed).is_ok() {
            return Err(format!("C563 HEADER foreign field {field} accepted"));
        }
    }
    Ok(())
}

/// Native N3 is deliberately a diagnostic of retained HEADER, not active A4 release.
#[test]
#[ignore = "bounded native ReleasedHEADER/GKR/PCS join; run only through an admitted controller"]
fn native_n3_released_header_producer_join() {
    use crate::{gkr, packed, pcs, sparse, transcript::Transcript, verifier_key};
    use crate::packed_owner_assembly::{NativeOwnerProducer, NativePcsSource};
    use std::time::Instant;

    let started = Instant::now();
    println!("C563_NATIVE_HEADER_STAGE|start");
    let construction = Instant::now();
    let (native, parent) = c563_fixture();
    let plan = GlobalProducerEndpointPlan::new(&parent).unwrap();
    let producer = NativeOwnerProducer::new_for_history(&parent, &native).unwrap();
    let source = NativePcsSource::new(&producer).unwrap();
    let admission = super::NativeReleasedHeaderAdmission::new(&plan, &source).unwrap();
    let construction_ms = construction.elapsed().as_millis();

    // Build the reference X directly from complete packed native rows, independently
    // of the new Fr loader. No selected-wire export or assumed zero region is used.
    let residual_started = Instant::now();
    let mut input = Vec::with_capacity(4 * WIDTH);
    for owner in 0..4 {
        let packed = source.read_owner(owner).unwrap();
        assert_eq!(packed.owner(), owner);
        assert_eq!(packed.packed_bytes().len() * 8, WIDTH);
        if owner == 3 {
            assert_eq!(packed.class(), OwnerClass::Padding);
            assert!(packed.packed_bytes().iter().any(|byte| *byte != 0));
        }
        for byte in packed.packed_bytes() {
            input.extend((0..8).map(|bit| Fr::from(((byte >> bit) & 1) as u64)));
        }
    }
    assert_eq!(input.len(), 1 << 22);
    assert_eq!(input.capacity(), 1 << 22);
    let shape = plan.shape(GlobalProducerRole::ReleasedHeader).unwrap();
    assert_eq!((shape.input_log, shape.row_log, shape.slot_log, shape.slots), (22, 21, 2, 4));
    let mut local_terms: Vec<Term> = Vec::with_capacity(396_561);
    let mut total = 0usize;
    for owner in 0..4 {
        let mut residual = vec![Fr::zero(); 1 << 19];
        let mut position = 0usize;
        let counts = plan.roster.visit_header_terms(owner as u64, |global| {
            // Independent arithmetic normalization, retaining every occurrence in order.
            assert_eq!(global.row >> 19, owner);
            assert_eq!(global.gate.left / WIDTH, owner);
            assert_eq!(global.gate.right / WIDTH, owner);
            residual[global.row & ((1 << 19) - 1)] += global.gate.evaluate(&input);
            let mut local = global;
            local.row -= owner * (1 << 19);
            local.gate.left -= owner * WIDTH;
            local.gate.right -= owner * WIDTH;
            if owner == 0 { local_terms.push(local); }
            else { assert_eq!(local, local_terms[position], "normalized owner {owner}, occurrence {position}"); }
            position += 1;
            Ok(())
        }).unwrap();
        assert_eq!(counts.emitted, 396_561);
        assert_eq!(position, 396_561);
        assert!(residual.iter().all(Zero::is_zero), "native HEADER residual at owner {owner}");
        total += position;
        let mut normalized_count = 0;
        admission.visit_owner_terms(owner, &mut |term| {
            assert_eq!(term, local_terms[normalized_count]);
            normalized_count += 1;
            Ok(())
        }).unwrap();
        assert_eq!(normalized_count, position);
    }
    assert_eq!(total, 1_586_244);
    assert_eq!(plan.global_census(GlobalProducerRole::ReleasedHeader).unwrap().terms, total as u128);
    assert_eq!(local_terms.len(), 396_561);
    let circuit = sparse::Circuit { input_len: WIDTH, row_count: 1 << 19, terms: local_terms };
    let repeated_shape = sparse::validate(&circuit, 2).unwrap();
    assert_eq!((repeated_shape.input_bits + 2, repeated_shape.row_bits + 2), (22, 21));
    let input_capacity_bytes = input.capacity() * std::mem::size_of::<Fr>();
    let term_capacity_bytes = circuit.terms.capacity() * std::mem::size_of::<Term>();
    let residual_ms = residual_started.elapsed().as_millis();
    println!("C563_NATIVE_HEADER_STAGE|residuals");

    let negatives_started = Instant::now();
    // A separate, valid and byte-identical parent is still the wrong borrowed parent.
    let other_parent = WorkTreeHistoryPlan::compile(3, 2, native.root(), native.total_be28()).unwrap();
    assert!(source.require_parent(&other_parent).unwrap_err().contains("parent"));
    let other_plan = GlobalProducerEndpointPlan::new(&other_parent).unwrap();
    assert!(super::NativeReleasedHeaderAdmission::new(&other_plan, &source).is_err());
    assert!(source.read_owner(4).is_err());
    assert!(admission.load_owner(4).is_err());
    c563_right_and_coefficient_controls(&plan).unwrap();
    c563_header_locality_controls(&plan).unwrap();

    // A retained A4 anchor has zero residual for this honest native X, yet its
    // absence changes the exact relation. Residual success cannot authorize it.
    let anchor_index = circuit.terms.iter().position(|term| (348_440..356_632).contains(&term.row)).unwrap();
    let anchor = &circuit.terms[anchor_index];
    crate::daa_history_roster::validate_a4_identity(anchor, 0, 0, anchor.row - 348_440).unwrap();
    assert!(anchor.gate.evaluate(&input).is_zero());
    let mut omitted = circuit.terms.clone();
    omitted.remove(anchor_index);
    assert_ne!(omitted.len(), circuit.terms.len());
    assert_ne!(omitted, circuit.terms);
    let header_shape = plan.shape(GlobalProducerRole::ReleasedHeader).unwrap();
    let weights = CoefficientWeights::new(&asymmetric_points(&header_shape).0,
        &asymmetric_points(&header_shape).1, &asymmetric_points(&header_shape).2).unwrap();
    let edge = reference_roster_edge(&header_shape, anchor.clone()).unwrap();
    assert!(contribution(&edge, &weights).unwrap().iter().any(|v| !v.is_zero()));
    drop(omitted);

    // Malformed caller vectors are negative controls of the reused grouped
    // enforcement only; they are never passed as a positive native assignment.
    let grouping = crate::sparse_stream_roster::GroupedVAdmission::try_new(2, &[0; 4], &[396_561]).unwrap();
    let mut omission_transcript = Transcript::new(C563_DOMAIN);
    let omission_before = omission_transcript.clone();
    let omission_error = crate::sparse_stream_roster::prove_with_boolean_u_grouped_v_for_test(
        20, 2, 19, 0, &[19], Some(0), &grouping,
        |owner| admission.load_owner(owner), &mut omission_transcript, |_| {},
        |owner, sink| {
            let mut position = 0;
            admission.visit_owner_terms(owner, &mut |term| {
                let skip = owner == 0 && position == anchor_index;
                position += 1;
                if skip { Ok(()) } else { sink(term) }
            })
        }, |r, u, v| admission.coefficients(r, u, v)).unwrap_err();
    assert_eq!(omission_error, "grouped V owner census differs from its admitted topology");
    c563_same_transcript(&omission_transcript, &omission_before);
    for non_boolean in [false, true] {
        let mut transcript = Transcript::new(C563_DOMAIN);
        let result = crate::sparse_stream_roster::prove_with_boolean_u_grouped_v_for_test(
            20, 2, 19, 0, &[19], Some(0), &grouping,
            |_| {
                let width = if non_boolean { WIDTH } else { WIDTH - 1 };
                let mut values = vec![Fr::zero(); width];
                if non_boolean { values[width - 1] = Fr::from(2u64); }
                Ok(values)
            }, &mut transcript, |_| {},
            |owner, sink| admission.visit_owner_terms(owner, sink),
            |r, u, v| admission.coefficients(r, u, v));
        let error = result.unwrap_err();
        assert!(error.contains(if non_boolean { "not Boolean" } else { "length or capacity" }), "{error}");
    }
    let negative_boundaries_ms = negatives_started.elapsed().as_millis();
    println!("C563_NATIVE_HEADER_STAGE|negative_boundaries");

    // The first commitment is created only after the full native residual gate.
    let setup_started = Instant::now();
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    let setup = pcs::generate_setup(22).unwrap();
    assert_eq!(&setup.id, key.id());
    assert_eq!(pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier.clone())).unwrap(),
        include_bytes!("../fixtures/verifier-keys-v1/log22.vk"));
    let passes_before_context = source.pass_count_for_test();
    for field in 0..3 {
        let mut wrong_setup = setup.clone();
        match field {
            0 => wrong_setup.id[0] ^= 1,
            1 => wrong_setup.log_n = 21,
            2 => wrong_setup.verifier.chi.clear(),
            _ => unreachable!(),
        }
        assert!(admission.prepare_context(&wrong_setup, &key).is_err(), "setup field {field}");
        assert_eq!(source.pass_count_for_test(), passes_before_context);
    }
    let wrong_key = verifier_key::admit(18, include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert!(admission.prepare_context(&setup, &wrong_key).is_err());
    assert_eq!(source.pass_count_for_test(), passes_before_context);
    let mut context = admission.prepare_context(&setup, &key).unwrap();
    assert_eq!(source.pass_count_for_test(), passes_before_context + 1);
    let encoded_commitment = pcs::encode_commitment(&context.committed().commitment()).unwrap();
    assert_eq!(context.commitment_bytes(), encoded_commitment.as_slice());
    let setup_commit_ms = setup_started.elapsed().as_millis();
    println!("C563_NATIVE_HEADER_STAGE|context");

    let grouped_started = Instant::now();
    let mut grouped_transcript = Transcript::new(C563_DOMAIN);
    let (proof, claim, grouped_stats, u_stats) = admission.prove_on(&context, &mut grouped_transcript).unwrap();
    let grouped_ms = grouped_started.elapsed().as_millis();
    assert_eq!(proof.layers.len(), 1);
    assert_eq!(proof.layers[0].rounds.len(), 44);
    assert!(proof.layers[0].rounds.iter().all(|message| message.len() == 3));
    assert_eq!(proof.layers[0].line_coefficients.len(), 23);
    assert_eq!(claim.point.len(), 22);
    assert_eq!(grouped_stats.group_count, 1);
    assert_eq!(grouped_stats.group_owner_counts, vec![4]);
    assert_eq!(grouped_stats.group_term_counts, vec![396_561]);
    assert_eq!(grouped_stats.baseline_term_callbacks, 1_586_244);
    assert_eq!(u_stats.boolean_checked_loads, 100);
    assert_eq!(u_stats.boolean_checked_fields, 100 * WIDTH);
    assert_eq!(u_stats.prefix_builds, 21);
    assert_eq!(u_stats.owner_term_selections, 33_311_124);
    assert_eq!(u_stats.shared_term_iterations, 8_327_781);
    println!("C563_NATIVE_HEADER_STAGE|grouped");

    let dense_started = Instant::now();
    let mut dense_transcript = Transcript::new(C563_DOMAIN);
    let (dense_proof, dense_claim) = sparse::prove_with_binding(&circuit, &input, 2, &mut dense_transcript,
        |t| admission.bind(&context, t).unwrap()).unwrap();
    let dense_ms = dense_started.elapsed().as_millis();
    assert_eq!(proof, dense_proof);
    assert_eq!(claim, dense_claim);
    let proof_bytes = gkr::encode_proof(&proof).unwrap();
    assert_eq!(proof_bytes, gkr::encode_proof(&dense_proof).unwrap());
    let decoded = sparse::decode_proof(&circuit, 2, &proof_bytes).unwrap();
    assert_eq!(decoded, proof);
    c563_same_transcript(&grouped_transcript, &dense_transcript);
    println!("C563_NATIVE_HEADER_STAGE|dense");

    let verify_started = Instant::now();
    let mut verified_transcript = Transcript::new(C563_DOMAIN);
    assert_eq!(admission.verify_on(&context, &decoded, &mut verified_transcript).unwrap(), claim);
    c563_same_transcript(&verified_transcript, &grouped_transcript);
    let gkr_verify_ms = verify_started.elapsed().as_millis();
    let mle_started = Instant::now();
    assert_eq!(gkr::mle(&input, &claim.point).unwrap(), claim.value);
    let independent_mle_ms = mle_started.elapsed().as_millis();
    let proof_negative_started = Instant::now();
    for field in 0..4 {
        let mut mutant = proof.clone();
        match field {
            0 => mutant.layers[0].rounds[0][0] += Fr::one(),
            1 => mutant.layers[0].rounds[22][0] += Fr::one(),
            2 => mutant.layers[0].left_value += Fr::one(),
            3 => mutant.layers[0].line_coefficients[0] += Fr::one(),
            _ => unreachable!(),
        }
        let mut transcript = Transcript::new(C563_DOMAIN);
        let before = transcript.clone();
        assert!(admission.verify_on(&context, &mutant, &mut transcript).is_err(), "proof field {field}");
        c563_same_transcript(&transcript, &before);
    }
    for field in 0..3 {
        match field {
            0 => context.source_binding[0] ^= 1,
            1 => context.key_id[0] ^= 1,
            2 => context.commitment_bytes[0] ^= 1,
            _ => unreachable!(),
        }
        let mut transcript = Transcript::new(C563_DOMAIN);
        let before = transcript.clone();
        assert!(admission.verify_on(&context, &proof, &mut transcript).is_err(), "context field {field}");
        c563_same_transcript(&transcript, &before);
        match field {
            0 => context.source_binding[0] ^= 1,
            1 => context.key_id[0] ^= 1,
            2 => context.commitment_bytes[0] ^= 1,
            _ => unreachable!(),
        }
    }
    let mut already_challenged = Transcript::new(C563_DOMAIN);
    already_challenged.try_challenge_scalar(b"before-native-admission").unwrap();
    let before = already_challenged.clone();
    assert!(admission.prove_on(&context, &mut already_challenged).is_err());
    c563_same_transcript(&already_challenged, &before);
    let proof_negative_ms = proof_negative_started.elapsed().as_millis();
    println!("C563_NATIVE_HEADER_STAGE|gkr_verified");

    // Release reference-only storage before the authenticated native PCS pass.
    drop(input);
    drop(circuit);
    drop(dense_proof);
    let opening_started = Instant::now();
    let mut opening_transcript = grouped_transcript.clone();
    let opening = packed::open_native(&source, context.committed(), &setup,
        &claim.point, &mut opening_transcript).unwrap();
    let native_open_ms = opening_started.elapsed().as_millis();
    let pcs_verify_started = Instant::now();
    pcs::verify_admitted(context.committed().commitment(), claim.value, &claim.point,
        &opening, &key, &mut verified_transcript).unwrap();
    c563_same_transcript(&opening_transcript, &verified_transcript);
    let pcs_verify_ms = pcs_verify_started.elapsed().as_millis();
    let opening_bytes = pcs::encode_proof(&opening).unwrap();
    let pcs_negative_started = Instant::now();
    let mut wrong_dimension = claim.point.clone();
    wrong_dimension.pop();
    assert!(pcs::verify_admitted(context.committed().commitment(), claim.value, &wrong_dimension,
        &opening, &key, &mut grouped_transcript.clone()).is_err());
    assert!(pcs::verify_admitted(context.committed().commitment(), claim.value + Fr::one(), &claim.point,
        &opening, &key, &mut grouped_transcript.clone()).is_err());
    let pcs_negative_ms = pcs_negative_started.elapsed().as_millis();
    println!("C563_NATIVE_HEADER_STAGE|pcs_verified");
    println!("C563_NATIVE_HEADER_METRICS|construction_ms={construction_ms}|residual_ms={residual_ms}|negative_boundaries_ms={negative_boundaries_ms}|setup_commit_ms={setup_commit_ms}|grouped_ms={grouped_ms}|dense_ms={dense_ms}|gkr_verify_ms={gkr_verify_ms}|independent_mle_ms={independent_mle_ms}|proof_negative_ms={proof_negative_ms}|native_open_ms={native_open_ms}|pcs_verify_ms={pcs_verify_ms}|pcs_negative_ms={pcs_negative_ms}|total_ms={}|input_capacity_bytes={input_capacity_bytes}|term_capacity_bytes={term_capacity_bytes}|term_size={}|gkr_bytes={}|pcs_bytes={}|source_passes={}|groups={}|baseline_callbacks={}|u_checked_loads={}|u_checked_fields={}|u_selections={}|u_shared_iterations={}|u_capacity_bytes={}|v_capacity_bytes={}|u_preweight_ns={}|u_selection_ns={}|u_x_fold_ns={}|v_baseline_ns={}|v_bank_ns={}|v_local_ns={}|v_handoff_ns={}",
        started.elapsed().as_millis(), std::mem::size_of::<Term>(), proof_bytes.len(), opening_bytes.len(),
        source.pass_count_for_test(), grouped_stats.group_count, grouped_stats.baseline_term_callbacks,
        u_stats.boolean_checked_loads, u_stats.boolean_checked_fields, u_stats.owner_term_selections,
        u_stats.shared_term_iterations, u_stats.u_state_peak_capacity_bytes, grouped_stats.grouped_state_peak_capacity_bytes,
        u_stats.u_prefix_preweight_elapsed_ns, u_stats.u_owner_selection_elapsed_ns, u_stats.u_x_fold_elapsed_ns,
        grouped_stats.baseline_elapsed_ns, grouped_stats.bank_build_elapsed_ns, grouped_stats.local_v_elapsed_ns,
        grouped_stats.owner_handoff_elapsed_ns);
    println!("C563_NATIVE_HEADER_STAGE|PASS");
}

/// Same-process source drop establishes the public HEADER seam, not cold-process
/// memory, whole-client synchronization or authenticated chain history.
#[test]
#[ignore = "bounded native public HEADER/GKR/PCS join; run only through an admitted controller"]
fn native_n3_public_header_consumer() {
    use blake2::{digest::consts::U32, Blake2b, Digest};
    use crate::{gkr, packed, pcs, transcript::Transcript, verifier_key};
    use crate::packed_owner_assembly::{NativeOwnerProducer, NativePcsSource};
    use super::{NativeHeaderPublicStatement, NativeHeaderPublicVerifier, NativeHeaderVerificationError as Error};
    use std::time::Instant;

    let started = Instant::now();
    println!("C564_PUBLIC_HEADER_STAGE|start");
    // Only public bytes, an expected claim, transcript ledgers and timing scalars
    // escape. No native prefix, source, producer, X, setup or context does.
    let (root, total, commitment_bytes, proof_bytes, opening_bytes, expected_claim,
        prover_final, producer_bound, producer_construct_ms, setup_commit_ms, prove_ms, open_ms) = {
        let construction = Instant::now();
        let (native, parent) = c563_fixture();
        let root = native.root();
        let total = native.total_be28();
        let plan = GlobalProducerEndpointPlan::new(&parent).unwrap();
        let producer = NativeOwnerProducer::new_for_history(&parent, &native).unwrap();
        let source = NativePcsSource::new(&producer).unwrap();
        let admission = super::NativeReleasedHeaderAdmission::new(&plan, &source).unwrap();
        let producer_construct_ms = construction.elapsed().as_millis();
        // Freeze the OLD literal recipe independently of the factored helper.
        assert_eq!((WIDTH, NativePcsSource::ROW_BITS), (1_048_576, 2_048));
        let mut profile_bytes = crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile: [u8; 32] = Blake2b::<U32>::digest(&profile_bytes).into();
        let mut old_binding = Blake2b::<U32>::new();
        old_binding.update(b"nipopow-native-owner-pcs-source-n3-h2-v1");
        for value in [3u64, 2, 4, 1_048_576, 2_048] { old_binding.update(value.to_le_bytes()); }
        old_binding.update(root);
        old_binding.update(total);
        old_binding.update(profile);
        let old_binding: [u8; 32] = old_binding.finalize().into();
        assert_eq!(source.binding(), old_binding);
        assert_eq!(NativePcsSource::public_binding(&parent).unwrap(), old_binding);

        let setup_started = Instant::now();
        let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
        let setup = pcs::generate_setup(22).unwrap();
        assert_eq!(&setup.id, key.id());
        let context = admission.prepare_context(&setup, &key).unwrap();
        let commitment_bytes = context.commitment_bytes().to_vec();
        assert_eq!(pcs::encode_commitment(&context.committed().commitment()).unwrap(), commitment_bytes);
        let setup_commit_ms = setup_started.elapsed().as_millis();
        let mut producer_bound = Transcript::new(C563_DOMAIN);
        admission.bind(&context, &mut producer_bound).unwrap();
        let mut old_bound = Transcript::new(C563_DOMAIN);
        old_bound.append_bytes(b"native-header-role", b"ReleasedHEADER-N3-v1");
        old_bound.append_bytes(b"native-header-source", &old_binding);
        for value in [3, 2, 4, 20, 22, 21] { old_bound.append_u64(b"native-header-dimension", value); }
        old_bound.append_bytes(b"native-header-key22", key.id());
        old_bound.append_bytes(b"native-header-C", &commitment_bytes);
        plan.roster.bind(&mut old_bound);
        c563_same_transcript(&producer_bound, &old_bound);
        {
            // Compare before proving, using a separately compiled public parent.
            let public_parent = WorkTreeHistoryPlan::compile(3, 2, root, total).unwrap();
            let statement = NativeHeaderPublicStatement::new(root, total, &key, &commitment_bytes).unwrap();
            let public = NativeHeaderPublicVerifier::new(&public_parent, statement, &key).unwrap();
            let mut public_bound = Transcript::new(C563_DOMAIN);
            public.bind(&mut public_bound).unwrap();
            c563_same_transcript(&public_bound, &producer_bound);
        }
        let prove_started = Instant::now();
        let mut prover = Transcript::new(C563_DOMAIN);
        let (proof, claim, grouped, boolean_u) = admission.prove_on(&context, &mut prover).unwrap();
        let prove_ms = prove_started.elapsed().as_millis();
        assert_eq!((proof.layers.len(), proof.layers[0].rounds.len(), proof.layers[0].line_coefficients.len()), (1, 44, 23));
        assert_eq!(claim.point.len(), 22);
        assert_eq!((grouped.group_count, grouped.baseline_term_callbacks), (1, 1_586_244));
        assert_eq!((boolean_u.boolean_checked_loads, boolean_u.boolean_checked_fields), (100, 100 * WIDTH));
        let proof_bytes = gkr::encode_proof(&proof).unwrap();
        let open_started = Instant::now();
        let opening = packed::open_native(&source, context.committed(), &setup, &claim.point, &mut prover).unwrap();
        let open_ms = open_started.elapsed().as_millis();
        let opening_bytes = pcs::encode_proof(&opening).unwrap();
        assert_eq!((proof_bytes.len(), opening_bytes.len()), (5_024, 29_421));
        assert_eq!(source.pass_count_for_test(), 2);
        println!("C564_PUBLIC_HEADER_STAGE|proof_ready");
        (root, total, commitment_bytes, proof_bytes, opening_bytes, claim, prover,
            producer_bound, producer_construct_ms, setup_commit_ms, prove_ms, open_ms)
    };
    println!("C564_PUBLIC_HEADER_STAGE|source_dropped");

    let construct_started = Instant::now();
    let parent = WorkTreeHistoryPlan::compile(3, 2, root, total).unwrap();
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    let statement = NativeHeaderPublicStatement::new(root, total, &key, &commitment_bytes).unwrap();
    let public = NativeHeaderPublicVerifier::new(&parent, statement.clone(), &key).unwrap();
    let public_construct_ms = construct_started.elapsed().as_millis();
    let mut public_bound = Transcript::new(C563_DOMAIN);
    public.bind(&mut public_bound).unwrap();
    c563_same_transcript(&public_bound, &producer_bound);
    let encoded_started = Instant::now();
    let mut encoded_final = Transcript::new(C563_DOMAIN);
    assert_eq!(public.verify_encoded_on(&proof_bytes, &opening_bytes, &mut encoded_final).unwrap(), expected_claim);
    c563_same_transcript(&encoded_final, &prover_final);
    let encoded_verify_ms = encoded_started.elapsed().as_millis();
    let proof = gkr::decode_dimensions(&[22], &proof_bytes).unwrap();
    let opening = pcs::decode_proof(&opening_bytes, 22).unwrap();
    let commitment = pcs::decode_commitment(&commitment_bytes).unwrap();
    let typed_started = Instant::now();
    let mut typed_final = Transcript::new(C563_DOMAIN);
    assert_eq!(public.verify_on(&proof, &opening, &mut typed_final).unwrap(), expected_claim);
    c563_same_transcript(&typed_final, &prover_final);
    let typed_verify_ms = typed_started.elapsed().as_millis();
    println!("C564_PUBLIC_HEADER_STAGE|public_verified");

    let negative_started = Instant::now();
    let verify_gkr = |candidate: &gkr::GkrProof| {
        let mut continuation = Transcript::new(C563_DOMAIN);
        let result = gkr::verify_with_wiring(&[22], 1 << 21, candidate, &mut continuation,
            |bound| *bound = public_bound.clone(),
            |_layer, r, u, v| public.coefficients(r, u, v).map_err(|_| gkr::GkrError::TerminalExpression));
        (result, continuation)
    };
    let (original_claim, gkr_continuation) = verify_gkr(&proof);
    assert_eq!(original_claim.unwrap(), expected_claim);
    // Establish nonzero sensitivity at the ORIGINAL pre-terminal challenges.
    let mut terminal = public_bound.clone();
    let r = gkr::output_point(1 << 21, &mut terminal);
    gkr::append_usize(&mut terminal, b"gkr-layer-index", 0);
    let challenges: Vec<_> = proof.layers[0].rounds.iter().map(|polynomial| {
        gkr::append_polynomial(&mut terminal, b"gkr-sumcheck-polynomial", polynomial);
        terminal.challenge_scalar(b"gkr-sumcheck-challenge")
    }).collect();
    let (u, v) = challenges.split_at(22);
    let coefficients = public.coefficients(&r, u, v).unwrap();
    assert!(!(coefficients[1] + coefficients[3] * proof.layers[0].right_value).is_zero());
    assert!(!(coefficients[2] + coefficients[3] * proof.layers[0].left_value).is_zero());
    let reject_gkr = |candidate: &gkr::GkrProof, expected: gkr::GkrError| {
        let mut transcript = Transcript::new(C563_DOMAIN);
        let before = transcript.clone();
        assert_eq!(public.verify_on(candidate, &opening, &mut transcript), Err(Error::Gkr(expected)));
        c563_same_transcript(&transcript, &before);
    };
    let mut left = proof.clone();
    left.layers[0].left_value += Fr::one();
    reject_gkr(&left, gkr::GkrError::TerminalExpression);
    let mut right = proof.clone();
    right.layers[0].right_value += Fr::one();
    reject_gkr(&right, gkr::GkrError::TerminalExpression);
    let mut endpoint = proof.clone();
    endpoint.layers[0].line_coefficients[0] += Fr::one();
    reject_gkr(&endpoint, gkr::GkrError::LineEndpoints);
    for fault in 0..4 {
        let mut malformed = proof.clone();
        let expected = match fault {
            0 => { malformed.layers.clear(); gkr::GkrError::ProofLayerCount }
            1 => { malformed.layers[0].rounds.pop(); gkr::GkrError::SumcheckRoundCount }
            2 => { malformed.layers[0].rounds[0].pop(); gkr::GkrError::SumcheckDegree }
            3 => { malformed.layers[0].line_coefficients.pop(); gkr::GkrError::LineDegree }
            _ => unreachable!(),
        };
        reject_gkr(&malformed, expected);
    }

    let mut interior = proof.clone();
    interior.layers[0].line_coefficients[1] += Fr::one();
    interior.layers[0].line_coefficients[2] -= Fr::one();
    assert_eq!(interior.layers[0].line_coefficients[0], proof.layers[0].line_coefficients[0]);
    assert_eq!(gkr::eval_polynomial(&interior.layers[0].line_coefficients, Fr::one()), proof.layers[0].right_value);
    let (interior_claim, mut interior_continuation) = verify_gkr(&interior);
    let interior_claim = interior_claim.expect("endpoint-preserving interior line must pass GKR");
    assert_ne!(interior_claim.point, expected_claim.point);
    assert_ne!(interior_claim.value, expected_claim.value);
    assert!(pcs::verify_admitted(commitment, interior_claim.value, &interior_claim.point,
        &opening, &key, &mut interior_continuation).is_err());
    let mut interior_joined = Transcript::new(C563_DOMAIN);
    let before = interior_joined.clone();
    assert!(matches!(public.verify_on(&interior, &opening, &mut interior_joined), Err(Error::Pcs(_))));
    c563_same_transcript(&interior_joined, &before);
    let interior_bytes = gkr::encode_proof(&interior).unwrap();
    assert!(matches!(public.verify_encoded_on(&interior_bytes, &opening_bytes, &mut interior_joined), Err(Error::Pcs(_))));
    c563_same_transcript(&interior_joined, &before);
    // Valid-length query corruption is a primitive PCS control. The joined API
    // derives q and has no caller query override.
    let mut wrong_point = expected_claim.point.clone();
    wrong_point[20] += Fr::one();
    assert_eq!(wrong_point.len(), 22);
    assert!(pcs::verify_admitted(commitment, expected_claim.value, &wrong_point,
        &opening, &key, &mut gkr_continuation.clone()).is_err());

    // Coherent replacement statements must reach GKR/PCS, rather than fail an
    // unchanged-parent mismatch. Doubled C is valid canonical GT encoding.
    for fault in 0..3 {
        let mut changed_root = root;
        let mut changed_total = total;
        let mut changed_c = commitment_bytes.clone();
        match fault {
            0 => changed_root[0] ^= 1,
            1 => changed_total[27] ^= 1,
            2 => {
                changed_c = pcs::encode_commitment(&(commitment + commitment)).unwrap();
                assert_ne!(changed_c, commitment_bytes);
                assert_eq!(pcs::encode_commitment(&pcs::decode_commitment(&changed_c).unwrap()).unwrap(), changed_c);
            }
            _ => unreachable!(),
        }
        let changed_parent = WorkTreeHistoryPlan::compile(3, 2, changed_root, changed_total).unwrap();
        let changed_statement = NativeHeaderPublicStatement::new(changed_root, changed_total, &key, &changed_c).unwrap();
        let changed_public = NativeHeaderPublicVerifier::new(&changed_parent, changed_statement, &key).unwrap();
        let mut transcript = Transcript::new(C563_DOMAIN);
        let before = transcript.clone();
        assert!(matches!(changed_public.verify_encoded_on(&proof_bytes, &opening_bytes, &mut transcript),
            Err(Error::Gkr(_)) | Err(Error::Pcs(_))), "coherent public field {fault}");
        c563_same_transcript(&transcript, &before);
    }
    let key18 = verifier_key::admit(18, include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert!(NativeHeaderPublicStatement::new(root, total, &key18, &commitment_bytes).is_err());
    assert!(matches!(NativeHeaderPublicVerifier::new(&parent, statement.clone(), &key18), Err(Error::Statement(_))));
    let parent4 = WorkTreeHistoryPlan::compile(4, 2, root, total).unwrap();
    assert!(matches!(NativeHeaderPublicVerifier::new(&parent4, statement.clone(), &key), Err(Error::Statement(_))));
    assert!(NativePcsSource::public_binding(&parent4).is_err());
    for fault in 0..4 {
        let mut malformed = statement.clone();
        match fault {
            0 => malformed.root[0] ^= 1,
            1 => malformed.total[27] ^= 1,
            2 => malformed.key_id[0] ^= 1,
            3 => malformed.commitment_bytes.fill(0xff),
            _ => unreachable!(),
        }
        assert!(matches!(NativeHeaderPublicVerifier::new(&parent, malformed, &key), Err(Error::Statement(_))));
    }
    assert!(NativeHeaderPublicStatement::new(root, total, &key, &commitment_bytes[..commitment_bytes.len() - 1]).is_err());
    assert!(NativeHeaderPublicStatement::new(root, total, &key, &vec![0xff; commitment_bytes.len()]).is_err());
    for fault in 0..4 {
        let mut bad_gkr = proof_bytes.clone();
        let mut bad_pcs = opening_bytes.clone();
        match fault {
            0 => { bad_gkr.pop(); }
            1 => bad_gkr[..32].fill(0xff),
            2 => { bad_pcs.pop(); }
            3 => bad_pcs[..32].fill(0xff),
            _ => unreachable!(),
        }
        let mut transcript = Transcript::new(C563_DOMAIN);
        let before = transcript.clone();
        let error = public.verify_encoded_on(&bad_gkr, &bad_pcs, &mut transcript).unwrap_err();
        if fault < 2 {
            assert!(gkr::decode_dimensions(&[22], &bad_gkr).is_err());
            assert!(matches!(error, Error::GkrEncoding(_)));
        } else {
            assert!(pcs::decode_proof(&bad_pcs, 22).is_err());
            assert!(matches!(error, Error::PcsEncoding(_)));
        }
        c563_same_transcript(&transcript, &before);
    }
    let mut challenged = Transcript::new(C563_DOMAIN);
    challenged.try_challenge_scalar(b"before-public-header").unwrap();
    let before = challenged.clone();
    assert!(matches!(public.bind(&mut challenged), Err(Error::Statement(_))));
    c563_same_transcript(&challenged, &before);
    assert!(matches!(public.verify_on(&proof, &opening, &mut challenged), Err(Error::Statement(_))));
    c563_same_transcript(&challenged, &before);
    assert!(matches!(public.verify_encoded_on(&proof_bytes, &opening_bytes, &mut challenged), Err(Error::Statement(_))));
    c563_same_transcript(&challenged, &before);
    let negative_ms = negative_started.elapsed().as_millis();
    println!("C564_PUBLIC_HEADER_STAGE|negative_controls");
    println!("C564_PUBLIC_HEADER_METRICS|producer_construct_ms={producer_construct_ms}|setup_commit_ms={setup_commit_ms}|prove_ms={prove_ms}|open_ms={open_ms}|public_construct_ms={public_construct_ms}|encoded_verify_ms={encoded_verify_ms}|typed_verify_ms={typed_verify_ms}|negative_ms={negative_ms}|total_ms={}|gkr_bytes={}|pcs_bytes={}|same_process_source_drop=1|cold_process_measured=0",
        started.elapsed().as_millis(), proof_bytes.len(), opening_bytes.len());
    println!("C564_PUBLIC_HEADER_STAGE|PASS");
}

const EQ_CACHE_CHUNK_BITS: usize = 8;

struct EqIndexCache {
    domain: usize,
    chunks: Vec<Vec<Fr>>,
}

impl EqIndexCache {
    fn new(point: &[Fr]) -> Result<Self, String> {
        let domain = power_of_two(point.len())?;
        let chunks = point
            .chunks(EQ_CACHE_CHUNK_BITS)
            .map(|chunk| {
                let size = power_of_two(chunk.len())?;
                let mut weights = Vec::with_capacity(size);
                for index in 0..size {
                    weights.push(eq_index(chunk, index));
                }
                Ok(weights)
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(Self { domain, chunks })
    }

    fn evaluate(&self, index: usize) -> Result<Fr, String> {
        if index >= self.domain {
            return Err("equality-cache index outside point domain".into());
        }
        let mut remaining = index;
        let mut weight = Fr::one();
        for chunk in &self.chunks {
            let bits = chunk.len().trailing_zeros() as usize;
            weight *= chunk[remaining & (chunk.len() - 1)];
            remaining >>= bits;
        }
        if remaining != 0 {
            return Err("equality-cache index has unused high bits".into());
        }
        Ok(weight)
    }
}

struct CoefficientWeights {
    row: EqIndexCache,
    left: EqIndexCache,
    right: EqIndexCache,
}

impl CoefficientWeights {
    fn new(r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<Self, String> {
        Ok(Self {
            row: EqIndexCache::new(r)?,
            left: EqIndexCache::new(u)?,
            right: EqIndexCache::new(v)?,
        })
    }

    fn weight(&self, edge: &EdgeTerm) -> Result<Fr, String> {
        Ok(self.row.evaluate(edge.term.row)?
            * self.left.evaluate(edge.term.gate.left)?
            * self.right.evaluate(edge.term.gate.right)?)
    }
}

fn field_key(value: Fr) -> [u8; 32] {
    let bytes = value.into_bigint().to_bytes_le();
    assert!(bytes.len() <= 32);
    let mut out = [0u8; 32];
    out[..bytes.len()].copy_from_slice(&bytes);
    out
}

fn key(edge: &EdgeTerm) -> ExactTermKey {
    ExactTermKey {
        source_slot: edge.source_slot,
        family_row: edge.family_row,
        row: edge.term.row,
        left: edge.term.gate.left,
        right: edge.term.gate.right,
        coefficients: [
            field_key(edge.term.gate.c0),
            field_key(edge.term.gate.c1),
            field_key(edge.term.gate.c2),
            field_key(edge.term.gate.c3),
        ],
    }
}

fn add(multiset: &mut Multiset, edge: &EdgeTerm) -> Result<(), String> {
    let entry = multiset.entry(key(edge)).or_insert(0);
    *entry = entry
        .checked_add(1)
        .ok_or("endpoint multiset multiplicity overflow")?;
    Ok(())
}

fn add_one(multiset: &mut Multiset, term_key: ExactTermKey) -> Result<(), String> {
    let count = multiset.entry(term_key).or_insert(0);
    *count = count.checked_add(1).ok_or("test occurrence count overflow")?;
    Ok(())
}

fn remove_one(multiset: &mut Multiset, term_key: &ExactTermKey) -> Result<(), String> {
    let remove = match multiset.get(term_key) {
        Some(count) if *count == 1 => true,
        Some(_) => false,
        None => return Err("mutant source occurrence missing from complete partition".into()),
    };
    if remove {
        multiset.remove(term_key);
    } else {
        let count = multiset
            .get_mut(term_key)
            .ok_or("mutant source occurrence missing from complete partition")?;
        *count -= 1;
    }
    Ok(())
}

fn occurrence_delta(left: &Multiset, right: &Multiset) -> Result<u128, String> {
    let keys = left.keys().chain(right.keys()).collect::<BTreeSet<_>>();
    keys.into_iter().try_fold(0u128, |sum, term_key| {
        let a = left.get(term_key).copied().unwrap_or(0);
        let b = right.get(term_key).copied().unwrap_or(0);
        let delta = if a >= b { a - b } else { b - a };
        sum.checked_add(delta)
            .ok_or_else(|| "complete-partition delta overflow".to_owned())
    })
}

fn zero_coefficients() -> [Fr; 4] {
    [Fr::zero(); 4]
}

fn add_coefficients(
    out: &mut [Fr; 4],
    edge: &EdgeTerm,
    weights: &CoefficientWeights,
) -> Result<(), String> {
    let gate = &edge.term.gate;
    let weight = weights.weight(edge)?;
    for (sum, coefficient) in out.iter_mut().zip([gate.c0, gate.c1, gate.c2, gate.c3]) {
        *sum += weight * coefficient;
    }
    Ok(())
}

fn asymmetric_points(shape: &ProducerEndpointShape) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    let r = (0..shape.row_log)
        .map(|bit| Fr::from(7 + 2 * bit as u64))
        .collect();
    let u = (0..shape.input_log)
        .map(|bit| Fr::from(101 + 6 * bit as u64))
        .collect();
    let v = (0..shape.input_log)
        .map(|bit| Fr::from(313 + 10 * bit as u64))
        .collect();
    (r, u, v)
}

fn verify_weight_cache_against_eq_index(shape: &ProducerEndpointShape) -> Result<(), String> {
    let (r, u, v) = asymmetric_points(shape);
    for point in [&r[..], &u[..], &v[..]] {
        let cache = EqIndexCache::new(point)?;
        let domain = power_of_two(point.len())?;
        let mut indices = BTreeSet::new();
        indices.insert(0usize);
        indices.insert(domain - 1);
        for bit in 0..point.len() {
            let basis = power_of_two(bit)?;
            indices.insert(basis);
            indices.insert((domain - 1) ^ basis);
        }
        for boundary_bit in [8usize, 16, 24, 32] {
            if boundary_bit < point.len() {
                let boundary = power_of_two(boundary_bit)?;
                indices.insert(boundary - 1);
                indices.insert(boundary);
                if boundary + 1 < domain {
                    indices.insert(boundary + 1);
                }
            }
        }
        indices.insert(
            power_of_two(point.len().min(8))?
                .saturating_sub(1),
        );
        for index in indices {
            if cache.evaluate(index)? != eq_index(point, index) {
                return Err("chunked equality cache differs from eq_index".into());
            }
        }
    }
    Ok(())
}

fn endpoint_owner(edge: &EdgeTerm, side: EndpointSide) -> usize {
    let wire = if side == EndpointSide::Left {
        edge.term.gate.left
    } else {
        edge.term.gate.right
    };
    wire / WIDTH
}

fn add_expected_edge(
    role: GlobalProducerRole,
    side: EndpointSide,
    owner: usize,
    shape: &ProducerEndpointShape,
    weights: &CoefficientWeights,
    edge: EdgeTerm,
    multiset: &mut Multiset,
    coefficients: &mut [Fr; 4],
    row_owner_differs: &mut bool,
) -> Result<(), String> {
    if endpoint_owner(&edge, side) != owner {
        return Err("canonical source edge entered the wrong endpoint partition".into());
    }
    if edge.source_slot != owner {
        *row_owner_differs = true;
    }
    add(multiset, &edge)?;
    add_coefficients(coefficients, &edge, weights)?;
    if edge.term.row >= power_of_two(shape.row_log)? {
        return Err("canonical edge exceeds the selected row shape".into());
    }
    Ok(())
}

fn expected_for_endpoint(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    side: EndpointSide,
    owner: usize,
    shape: &ProducerEndpointShape,
    weights: &CoefficientWeights,
) -> Result<(Multiset, [Fr; 4], bool), String> {
    let mut multiset = Multiset::new();
    let mut coefficients = zero_coefficients();
    let mut row_owner_differs = false;
    match role {
        GlobalProducerRole::Work => {
            let source_shape = plan.shape(role)?;
            plan.test_work_relation().visit_terms(|term| {
                let edge = GlobalProducerEndpointPlan::canonical_work_edge(&source_shape, term)?;
                if endpoint_owner(&edge, side) == owner {
                    add_expected_edge(
                        role,
                        side,
                        owner,
                        shape,
                        weights,
                        edge,
                        &mut multiset,
                        &mut coefficients,
                        &mut row_owner_differs,
                    )?;
                }
                Ok(())
            })?;
        }
        GlobalProducerRole::DaaRoster => {
            for source_owner in 0..shape.slots {
                plan.roster.visit_owner_terms(source_owner as u64, |term| {
                    let edge = GlobalProducerEndpointPlan::canonical_roster_edge(shape, term)?;
                    if endpoint_owner(&edge, side) == owner {
                        add_expected_edge(
                            role,
                            side,
                            owner,
                            shape,
                            weights,
                            edge,
                            &mut multiset,
                            &mut coefficients,
                            &mut row_owner_differs,
                        )?;
                    }
                    Ok(())
                })?;
            }
        }
        GlobalProducerRole::ReleasedHeader => {
            plan.roster.visit_header_terms(owner as u64, |term| {
                let edge = GlobalProducerEndpointPlan::canonical_roster_edge(shape, term)?;
                if edge.source_slot != owner
                    || edge.term.gate.left / WIDTH != owner
                    || edge.term.gate.right / WIDTH != owner
                {
                    return Err("canonical released HEADER term is not owner-local".into());
                }
                if endpoint_owner(&edge, side) == owner {
                    add_expected_edge(
                        role,
                        side,
                        owner,
                        shape,
                        weights,
                        edge,
                        &mut multiset,
                        &mut coefficients,
                        &mut row_owner_differs,
                    )?;
                }
                Ok(())
            })?;
        }
    }
    Ok((multiset, coefficients, row_owner_differs))
}

fn actual_for_endpoint(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    side: EndpointSide,
    owner: usize,
    weights: &CoefficientWeights,
) -> Result<(Multiset, [Fr; 4], bool), String> {
    let mut multiset = Multiset::new();
    let mut coefficients = zero_coefficients();
    let mut row_owner_differs = false;
    plan.visit_endpoint(role, side, owner, |edge| {
        if edge.source_slot != owner {
            row_owner_differs = true;
        }
        add(&mut multiset, &edge)?;
        add_coefficients(&mut coefficients, &edge, weights)?;
        Ok(())
    })?;
    Ok((multiset, coefficients, row_owner_differs))
}

fn direct_source_coefficients(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    shape: &ProducerEndpointShape,
    weights: &CoefficientWeights,
) -> Result<(u128, [Fr; 4]), String> {
    let mut count = 0u128;
    let mut coefficients = zero_coefficients();
    let mut add_term = |edge: EdgeTerm| -> Result<(), String> {
        add_coefficients(&mut coefficients, &edge, weights)?;
        count = count.checked_add(1).ok_or("direct source count overflow")?;
        Ok(())
    };
    match role {
        GlobalProducerRole::Work => {
            let source_shape = plan.shape(role)?;
            plan.test_work_relation().visit_terms(|term| {
                add_term(GlobalProducerEndpointPlan::canonical_work_edge(&source_shape, term)?)
            })?;
        }
        GlobalProducerRole::DaaRoster => {
            for owner in 0..shape.slots {
                plan.roster.visit_owner_terms(owner as u64, |term| {
                    add_term(GlobalProducerEndpointPlan::canonical_roster_edge(shape, term)?)
                })?;
            }
        }
        GlobalProducerRole::ReleasedHeader => {
            for owner in 0..shape.slots {
                plan.roster.visit_header_terms(owner as u64, |term| {
                    add_term(GlobalProducerEndpointPlan::canonical_roster_edge(shape, term)?)
                })?;
            }
        }
    }
    drop(add_term);
    Ok((count, coefficients))
}

fn relation_coefficients(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> Result<[Fr; 4], String> {
    match role {
        GlobalProducerRole::Work => plan.work.coefficients(r, u, v),
        GlobalProducerRole::DaaRoster => plan.roster.coefficients(r, u, v),
        GlobalProducerRole::ReleasedHeader => plan.roster.header_coefficients(r, u, v),
    }
}

fn compare_small_shape(
    plan: &GlobalProducerEndpointPlan<'_>,
) -> Result<(), String> {
    for role in [
        GlobalProducerRole::Work,
        GlobalProducerRole::DaaRoster,
        GlobalProducerRole::ReleasedHeader,
    ] {
        let shape = plan.shape(role)?;
        let (r, u, v) = asymmetric_points(&shape);
        let weights = CoefficientWeights::new(&r, &u, &v)?;
        let (source_count, source_coefficients) =
            direct_source_coefficients(plan, role, &shape, &weights)?;
        if source_count != plan.global_census(role)?.terms {
            return Err("tiny source multiset count differs from its checked census".into());
        }
        if source_coefficients != relation_coefficients(plan, role, &r, &u, &v)? {
            return Err("asymmetric non-Boolean coefficient reference differs from its source".into());
        }
        for side in [EndpointSide::Left, EndpointSide::Right] {
            let mut expected_total = zero_coefficients();
            let mut actual_total = zero_coefficients();
            let mut endpoint_total = 0u128;
            let mut row_owner_differs = false;
            for owner in 0..shape.slots {
                let (expected, expected_coefficients, expected_row_owner_differs) =
                    expected_for_endpoint(plan, role, side, owner, &shape, &weights)?;
                let (actual, actual_coefficients, actual_row_owner_differs) =
                    actual_for_endpoint(plan, role, side, owner, &weights)?;
                if expected != actual {
                    return Err(format!(
                        "{:?} {:?} endpoint multiset differs at owner {}",
                        role, side, owner
                    ));
                }
                expected_total
                    .iter_mut()
                    .zip(expected_coefficients)
                    .for_each(|(sum, value)| *sum += value);
                actual_total
                    .iter_mut()
                    .zip(actual_coefficients)
                    .for_each(|(sum, value)| *sum += value);
                endpoint_total = endpoint_total
                    .checked_add(expected.values().try_fold(0u128, |sum, n| {
                        sum.checked_add(*n).ok_or("endpoint total overflow")
                    })?)
                    .ok_or("endpoint total overflow")?;
                row_owner_differs |= expected_row_owner_differs || actual_row_owner_differs;
            }
            if endpoint_total != source_count
                || expected_total != source_coefficients
                || actual_total != source_coefficients
            {
                return Err("complete endpoint partitions differ from full source".into());
            }
            if matches!(role, GlobalProducerRole::Work | GlobalProducerRole::DaaRoster)
                && !row_owner_differs
            {
                return Err("source row owner was never distinct from endpoint owner".into());
            }
        }
    }
    Ok(())
}

fn valid_repacked(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    mut edge: EdgeTerm,
) -> Result<EdgeTerm, String> {
    let shape = plan.shape(role)?;
    edge.term.row = crate::sparse_stream_roster::global_edge_row(
        edge.source_slot,
        edge.family_row,
        shape.slot_log,
        shape.base_row_bits,
        shape.family_bits,
        &shape.member_row_bits,
    )?;
    plan.validate_edge(role, &edge)?;
    Ok(edge)
}

fn contribution(
    edge: &EdgeTerm,
    weights: &CoefficientWeights,
) -> Result<[Fr; 4], String> {
    let mut out = zero_coefficients();
    add_coefficients(&mut out, edge, weights)?;
    Ok(out)
}

fn add_coefficient_vectors(left: [Fr; 4], right: [Fr; 4]) -> [Fr; 4] {
    std::array::from_fn(|index| left[index] + right[index])
}

fn subtract_coefficient_vectors(left: [Fr; 4], right: [Fr; 4]) -> [Fr; 4] {
    std::array::from_fn(|index| left[index] - right[index])
}

fn work_tag_mutants(plan: &GlobalProducerEndpointPlan<'_>) -> Result<(), String> {
    let shape = plan.shape(GlobalProducerRole::Work)?;
    let mut samples: Vec<Option<EdgeTerm>> = (0..6).map(|_| None).collect();
    plan.test_work_relation().visit_terms(|term| {
        let edge = GlobalProducerEndpointPlan::canonical_work_edge(&shape, term)?;
        let tag = edge.family_row >> super::WORK_BASE_ROW_BITS;
        if samples[tag].is_none() {
            samples[tag] = Some(edge);
        }
        Ok(())
    })?;
    let samples = samples
        .into_iter()
        .map(|edge| edge.ok_or_else(|| "tiny Work source omitted a tagged family".to_owned()))
        .collect::<Result<Vec<_>, _>>()?;
    let (r, u, v) = asymmetric_points(&shape);
    let weights = CoefficientWeights::new(&r, &u, &v)?;

    let tag_two = samples[2].clone();
    let mut unused_local_bit = samples[0].clone();
    let original_tag = unused_local_bit.family_row >> super::WORK_BASE_ROW_BITS;
    unused_local_bit.family_row ^= 1;
    if unused_local_bit.family_row >> super::WORK_BASE_ROW_BITS != original_tag
        || unused_local_bit.source_slot != samples[0].source_slot
        || unused_local_bit.term != samples[0].term
    {
        return Err("Work zero-extension mutant changed more than one local bit".into());
    }
    if plan
        .validate_edge(GlobalProducerRole::Work, &unused_local_bit)
        .err()
        .as_deref()
        != Some("edge term row outside family/slot allocation")
    {
        return Err("unused Work local bit did not fail at the narrow member extent".into());
    }

    let mut bad_tag = tag_two.clone();
    bad_tag.family_row ^= 1 << super::WORK_BASE_ROW_BITS;
    if plan.validate_edge(GlobalProducerRole::Work, &bad_tag).is_ok() {
        return Err("tag-only mutant was not rejected".into());
    }
    let mut changed_tag = tag_two.clone();
    changed_tag.family_row ^= 1 << super::WORK_BASE_ROW_BITS;
    let changed_tag = valid_repacked(plan, GlobalProducerRole::Work, changed_tag)?;
    if contribution(&tag_two, &weights)? == contribution(&changed_tag, &weights)? {
        return Err("non-Boolean Work family tag weight did not change".into());
    }

    let mut row_only = tag_two.clone();
    row_only.term.row ^= 1;
    if plan.validate_edge(GlobalProducerRole::Work, &row_only).is_ok() {
        return Err("isolated Work Term.row-only mutant was not rejected".into());
    }

    let mut bad_owner = tag_two.clone();
    bad_owner.source_slot ^= 1;
    if plan.validate_edge(GlobalProducerRole::Work, &bad_owner).is_ok() {
        return Err("Work row-owner-only mutant was not rejected".into());
    }
    let mut changed_owner = tag_two.clone();
    changed_owner.source_slot ^= 1;
    let changed_owner = valid_repacked(plan, GlobalProducerRole::Work, changed_owner)?;
    if contribution(&tag_two, &weights)? == contribution(&changed_owner, &weights)? {
        return Err("non-Boolean Work row-owner weight did not change".into());
    }

    let mut bad_wire = tag_two.clone();
    bad_wire.term.gate.left = power_of_two(shape.input_log)?;
    if plan.validate_edge(GlobalProducerRole::Work, &bad_wire).is_ok() {
        return Err("Work endpoint-wire range mutant was not rejected".into());
    }

    let (baseline, baseline_coefficients, _) = expected_for_endpoint(
        plan,
        GlobalProducerRole::Work,
        EndpointSide::Left,
        0,
        &shape,
        &weights,
    )?;
    let (actual, actual_coefficients, _) = actual_for_endpoint(
        plan,
        GlobalProducerRole::Work,
        EndpointSide::Left,
        0,
        &weights,
    )?;
    if baseline != actual || baseline_coefficients != actual_coefficients {
        return Err("complete canonical Work partition differs from actual endpoint output".into());
    }
    let original_key = key(&tag_two);
    if !baseline.contains_key(&original_key) || tag_two.term.gate.c1.is_zero() {
        return Err("Work control occurrence is absent or has a zero sign coefficient".into());
    }
    let original_contribution = contribution(&tag_two, &weights)?;

    let mut missing = baseline.clone();
    remove_one(&mut missing, &original_key)?;
    let missing_coefficients =
        subtract_coefficient_vectors(baseline_coefficients, original_contribution);
    if occurrence_delta(&baseline, &missing)? != 1
        || missing_coefficients == baseline_coefficients
    {
        return Err("single missing-occurrence control was not distinguished".into());
    }

    let mut duplicate = baseline.clone();
    add_one(&mut duplicate, original_key.clone())?;
    let duplicate_coefficients =
        add_coefficient_vectors(baseline_coefficients, original_contribution);
    if occurrence_delta(&baseline, &duplicate)? != 1
        || duplicate_coefficients == baseline_coefficients
    {
        return Err("single duplicate-occurrence control was not distinguished".into());
    }

    let mut changed_sign = tag_two.clone();
    changed_sign.term.gate.c1 = -changed_sign.term.gate.c1;
    let changed_sign_key = key(&changed_sign);
    let mut signed = baseline.clone();
    remove_one(&mut signed, &original_key)?;
    add_one(&mut signed, changed_sign_key)?;
    let signed_coefficients = add_coefficient_vectors(
        subtract_coefficient_vectors(baseline_coefficients, original_contribution),
        contribution(&changed_sign, &weights)?,
    );
    if occurrence_delta(&baseline, &signed)? != 2
        || signed_coefficients == baseline_coefficients
    {
        return Err("single sign-occurrence control was not distinguished".into());
    }
    if plan
        .visit_endpoint(
            GlobalProducerRole::Work,
            EndpointSide::Left,
            shape.slots,
            |_| Ok(()),
        )
        .is_ok()
    {
        return Err("Work endpoint owner range mutant was not rejected".into());
    }

    let mut callbacks = 0usize;
    if plan
        .visit_work_boundary_endpoint(
            &shape,
            EndpointSide::Left,
            0,
            &mut |_| {
                callbacks += 1;
                Err("bounded boundary sink stop".into())
            },
        )
        .is_ok()
        || callbacks != 1
    {
        return Err("Work infallible boundary emitter did not latch and suppress after sink error".into());
    }
    Ok(())
}

fn daa_row_mutants(plan: &GlobalProducerEndpointPlan<'_>) -> Result<(), String> {
    let daa_shape = plan.shape(GlobalProducerRole::DaaRoster)?;
    let mut lane_sample = None;
    for owner in 0..daa_shape.slots {
        plan.roster.visit_owner_terms(owner as u64, |term| {
            let edge = GlobalProducerEndpointPlan::canonical_roster_edge(&daa_shape, term)?;
            if edge.family_row >> 17 != 0 && lane_sample.is_none() {
                lane_sample = Some(edge);
            }
            Ok(())
        })?;
        if lane_sample.is_some() {
            break;
        }
    }
    let lane_sample = lane_sample.ok_or("tiny DAA source has no nonzero lane row")?;
    let (r, u, v) = asymmetric_points(&daa_shape);
    let weights = CoefficientWeights::new(&r, &u, &v)?;
    let mut bad_lane = lane_sample.clone();
    bad_lane.family_row ^= 1 << 17;
    if plan.validate_edge(GlobalProducerRole::DaaRoster, &bad_lane).is_ok() {
        return Err("DAA lane-only mutant was not rejected".into());
    }
    let mut changed_lane = lane_sample.clone();
    changed_lane.family_row ^= 1 << 17;
    let changed_lane = valid_repacked(plan, GlobalProducerRole::DaaRoster, changed_lane)?;
    if contribution(&lane_sample, &weights)? == contribution(&changed_lane, &weights)? {
        return Err("non-Boolean DAA lane weight did not change".into());
    }

    let mut bad_owner = lane_sample.clone();
    bad_owner.source_slot ^= 1;
    if plan.validate_edge(GlobalProducerRole::DaaRoster, &bad_owner).is_ok() {
        return Err("DAA row-owner-only mutant was not rejected".into());
    }
    let mut changed_owner = lane_sample.clone();
    changed_owner.source_slot ^= 1;
    let changed_owner = valid_repacked(plan, GlobalProducerRole::DaaRoster, changed_owner)?;
    if contribution(&lane_sample, &weights)? == contribution(&changed_owner, &weights)? {
        return Err("non-Boolean DAA row-owner weight did not change".into());
    }

    let header_shape = plan.shape(GlobalProducerRole::ReleasedHeader)?;
    let mut header_sample = None;
    plan.roster.visit_header_terms(0, |term| {
        if header_sample.is_none() {
            header_sample = Some(GlobalProducerEndpointPlan::canonical_roster_edge(
                &header_shape,
                term,
            )?);
        }
        Ok(())
    })?;
    let header_sample = header_sample.ok_or("tiny released HEADER owner has no terms")?;
    plan.validate_edge(GlobalProducerRole::ReleasedHeader, &header_sample)?;

    endpoint_sink_failures(plan)?;

    if crate::sparse_stream_roster::global_edge_row(
        0,
        0,
        usize::BITS as usize,
        super::WORK_BASE_ROW_BITS,
        super::WORK_FAMILY_BITS,
        &WORK_MEMBER_ROW_BITS,
    )
    .is_ok()
    {
        return Err("edge row shift overflow mutant was not rejected".into());
    }
    if super::checked_shift(usize::MAX, 1).is_ok() {
        return Err("left-shifted high bits were not rejected".into());
    }
    Ok(())
}

fn endpoint_sink_failures(plan: &GlobalProducerEndpointPlan<'_>) -> Result<(), String> {
    for role in [
        GlobalProducerRole::Work,
        GlobalProducerRole::DaaRoster,
        GlobalProducerRole::ReleasedHeader,
    ] {
        let mut calls = 0usize;
        let result = plan.visit_endpoint(role, EndpointSide::Left, 0, |_| {
            calls = calls.checked_add(1).ok_or("sink-fault call count overflow")?;
            Err("isolated first sink failure".into())
        });
        if result.is_ok() || calls != 1 {
            return Err(format!(
                "{:?} endpoint did not stop after its first sink error",
                role
            ));
        }
    }
    Ok(())
}

#[derive(Default)]
struct EndpointAudit {
    multiset: Multiset,
    source_row_owner_matches: bool,
    high_owner_bit_joined: bool,
}

fn record_endpoint_edge(
    role: GlobalProducerRole,
    side: EndpointSide,
    owner: usize,
    shape: &ProducerEndpointShape,
    edge: EdgeTerm,
    audit: &mut EndpointAudit,
) -> Result<(), String> {
    GlobalProducerEndpointPlan::validate_edge_shape(shape, &edge)?;
    record_validated_endpoint_edge(role, side, owner, shape, edge, audit)
}

fn record_validated_endpoint_edge(
    role: GlobalProducerRole,
    side: EndpointSide,
    owner: usize,
    shape: &ProducerEndpointShape,
    edge: EdgeTerm,
    audit: &mut EndpointAudit,
) -> Result<(), String> {
    if endpoint_owner(&edge, side) != owner {
        return Err("bounded source edge entered the wrong endpoint owner".into());
    }
    audit.source_row_owner_matches |= edge.source_slot == owner;
    let owner_bit = power_of_two(20)?;
    if owner & owner_bit != 0 {
        let member_bits = match role {
            GlobalProducerRole::Work => {
                let tag = edge.family_row >> super::WORK_BASE_ROW_BITS;
                *WORK_MEMBER_ROW_BITS.get(tag).ok_or("high-owner Work tag outside roster")?
            }
            GlobalProducerRole::DaaRoster | GlobalProducerRole::ReleasedHeader => 19,
        };
        let row_owner_bit = power_of_two(
            member_bits.checked_add(20).ok_or("high-owner row bit overflow")?,
        )?;
        let high_wire_bit = power_of_two(40)?;
        let wire = if side == EndpointSide::Left {
            edge.term.gate.left
        } else {
            edge.term.gate.right
        };
        if edge.source_slot & owner_bit != 0
            && edge.term.row & row_owner_bit != 0
            && wire & high_wire_bit != 0
        {
            audit.high_owner_bit_joined = true;
        }
    }
    add(&mut audit.multiset, &edge)
}

fn reference_work_edge(
    shape: &ProducerEndpointShape,
    tag: usize,
    source_slot: usize,
    local_row: usize,
    mut term: Term,
) -> Result<EdgeTerm, String> {
    let member_bits = *WORK_MEMBER_ROW_BITS.get(tag).ok_or("reference Work tag outside roster")?;
    let member_rows = power_of_two(member_bits)?;
    if local_row >= member_rows {
        return Err("reference Work row outside its ragged member".into());
    }
    let untagged = source_slot
        .checked_mul(member_rows)
        .and_then(|row| row.checked_add(local_row))
        .ok_or("reference Work source row overflow")?;
    if term.row != untagged {
        return Err("reference Work source row metadata mismatch".into());
    }
    let family_row = tag
        .checked_mul(power_of_two(super::WORK_BASE_ROW_BITS)?)
        .and_then(|row| row.checked_add(local_row))
        .ok_or("reference Work family row overflow")?;
    let tag_span = power_of_two(
        super::WORK_BASE_ROW_BITS
            .checked_add(shape.slot_log)
            .ok_or("reference Work family shift overflow")?,
    )?;
    term.row = untagged
        .checked_add(tag.checked_mul(tag_span).ok_or("reference Work tag overflow")?)
        .ok_or("reference Work tagged row overflow")?;
    let reconstructed = global_edge_row(
        source_slot,
        family_row,
        shape.slot_log,
        super::WORK_BASE_ROW_BITS,
        super::WORK_FAMILY_BITS,
        &WORK_MEMBER_ROW_BITS,
    )?;
    if reconstructed != term.row {
        return Err("reference Work row differs from global_edge_row".into());
    }
    let edge = EdgeTerm {
        source_slot,
        family_row,
        term,
    };
    Ok(edge)
}

fn reference_roster_edge(
    shape: &ProducerEndpointShape,
    term: Term,
) -> Result<EdgeTerm, String> {
    let mask = power_of_two(19)?
        .checked_sub(1)
        .ok_or("reference roster row mask underflow")?;
    let edge = EdgeTerm {
        source_slot: term.row >> 19,
        family_row: term.row & mask,
        term,
    };
    let reconstructed = global_edge_row(
        edge.source_slot,
        edge.family_row,
        shape.slot_log,
        19,
        0,
        &[19],
    )?;
    if reconstructed != edge.term.row {
        return Err("reference roster row differs from global_edge_row".into());
    }
    Ok(edge)
}

fn reference_bounded_endpoint(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    side: EndpointSide,
    owner: usize,
    shape: &ProducerEndpointShape,
) -> Result<EndpointAudit, String> {
    let mut audit = EndpointAudit::default();
    match role {
        GlobalProducerRole::Work => {
            let mut numeric_count = 0usize;
            let reported = plan.numeric.visit_endpoint_terms(side == EndpointSide::Left, owner, |term| {
                let source_slot = term.row;
                let edge = reference_work_edge(shape, 0, source_slot, 0, term)?;
                record_endpoint_edge(role, side, owner, shape, edge, &mut audit)?;
                numeric_count = numeric_count.checked_add(1).ok_or("reference numeric count overflow")?;
                Ok(())
            })?;
            if reported != numeric_count {
                return Err("reference numeric endpoint count changed".into());
            }

            let row_base = owner
                .checked_mul(crate::work_tree_work::LOCAL_ROW_WIDTH)
                .ok_or("reference Work boundary row base overflow")?;
            let mut boundary_error = None;
            let mut boundary_count = 0usize;
            let boundary_result = plan.parent.work_boundary().emit_slot(owner, |term| {
                if boundary_error.is_some() {
                    return;
                }
                let attempt = (|| -> Result<(), String> {
                    let local_row = term
                        .row
                        .checked_sub(row_base)
                        .ok_or("reference Work boundary row precedes owner")?;
                    let edge = reference_work_edge(shape, 1, owner, local_row, term)?;
                    record_endpoint_edge(role, side, owner, shape, edge, &mut audit)?;
                    boundary_count = boundary_count
                        .checked_add(1)
                        .ok_or("reference Work boundary count overflow")?;
                    Ok(())
                })();
                if let Err(error) = attempt {
                    boundary_error = Some(error);
                }
            });
            boundary_result?;
            if let Some(error) = boundary_error {
                return Err(error);
            }

            for tag in 2..=5 {
                let family = plan.work_family(tag)?;
                family.emit_endpoint_terms(
                    plan.parent.descriptor(),
                    side == EndpointSide::Left,
                    owner,
                    |source_slot, local_row, term| {
                        let edge = reference_work_edge(shape, tag, source_slot, local_row, term)?;
                        record_endpoint_edge(role, side, owner, shape, edge, &mut audit)
                    },
                )?;
            }
        }
        GlobalProducerRole::DaaRoster => {
            let mut count = 0usize;
            let reported = plan.roster.visit_history_endpoint_terms(
                side == EndpointSide::Left,
                owner,
                |term| {
                    let edge = reference_roster_edge(shape, term)?;
                    record_endpoint_edge(role, side, owner, shape, edge, &mut audit)?;
                    count = count.checked_add(1).ok_or("reference DAA count overflow")?;
                    Ok(())
                },
            )?;
            let reported_total = reported.lanes.iter().try_fold(0usize, |sum, lane| {
                sum.checked_add(*lane)
                    .ok_or_else(|| "reference DAA lane total overflow".to_owned())
            })?;
            if count != reported_total {
                return Err("reference DAA endpoint count changed".into());
            }
        }
        GlobalProducerRole::ReleasedHeader => {
            let source_owner = u64::try_from(owner).map_err(|_| "reference HEADER owner width")?;
            let mut count = 0usize;
            let reported = plan.roster.visit_header_terms(source_owner, |term| {
                let edge = reference_roster_edge(shape, term)?;
                if edge.source_slot != owner
                    || edge.term.gate.left / WIDTH != owner
                    || edge.term.gate.right / WIDTH != owner
                {
                    return Err("reference HEADER source is not owner-local".into());
                }
                record_endpoint_edge(role, side, owner, shape, edge, &mut audit)?;
                count = count.checked_add(1).ok_or("reference HEADER count overflow")?;
                Ok(())
            })?;
            if count != reported.emitted {
                return Err("reference HEADER endpoint count changed".into());
            }
        }
    }
    Ok(audit)
}

fn actual_bounded_endpoint(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    side: EndpointSide,
    owner: usize,
    shape: &ProducerEndpointShape,
) -> Result<EndpointAudit, String> {
    let mut audit = EndpointAudit::default();
    let mut count = 0u128;
    let reported = plan.visit_endpoint(role, side, owner, |edge| {
        record_validated_endpoint_edge(role, side, owner, shape, edge, &mut audit)?;
        count = count.checked_add(1).ok_or("actual bounded endpoint count overflow")?;
        Ok(())
    })?;
    if count != reported.emitted {
        return Err("actual bounded endpoint count differs from emitted terms".into());
    }
    Ok(audit)
}

fn compare_bounded_endpoint(
    plan: &GlobalProducerEndpointPlan<'_>,
    role: GlobalProducerRole,
    owner: usize,
    require_high_owner_bit: bool,
    require_source_row_owner: bool,
) -> Result<(), String> {
    let shape = plan.shape(role)?;
    let expected = reference_bounded_endpoint(plan, role, EndpointSide::Left, owner, &shape)?;
    let actual = actual_bounded_endpoint(plan, role, EndpointSide::Left, owner, &shape)?;
    if expected.multiset != actual.multiset {
        return Err(format!("{:?} LEFT source pack differs at owner {}", role, owner));
    }
    if require_high_owner_bit && owner & power_of_two(20)? == 0 {
        return Err("high-owner control did not select owner bit20".into());
    }
    if expected.source_row_owner_matches != actual.source_row_owner_matches
        || expected.high_owner_bit_joined != actual.high_owner_bit_joined
    {
        return Err("source and endpoint owner packing flags differ".into());
    }
    if require_high_owner_bit && !expected.high_owner_bit_joined {
        return Err("owner bit20 was not preserved in source row and global address".into());
    }
    if require_source_row_owner && !expected.source_row_owner_matches {
        return Err("selected active source owner did not occur as a row owner".into());
    }
    Ok(())
}

fn h21_census_and_bounded_packing(
    plan: &GlobalProducerEndpointPlan<'_>,
) -> Result<(), String> {
    for role in [
        GlobalProducerRole::Work,
        GlobalProducerRole::DaaRoster,
        GlobalProducerRole::ReleasedHeader,
    ] {
        let census = plan.global_census(role)?;
        if census.slot_count != (1u128 << 21)
            || census.terms == 0
            || census.input_log != 41
            || census.row_log == 0
            || (role != GlobalProducerRole::ReleasedHeader && census.numeric_terms == 0)
        {
            return Err("H21 scalar census shape or source count rejected".into());
        }
        compare_bounded_endpoint(plan, role, 844_672, false, false)?;
        compare_bounded_endpoint(plan, role, 1usize << 20, true, false)?;
    }
    if plan.roster.owner_class(2048)? != OwnerClass::M1
        || plan.roster.owner_class(3072)? != OwnerClass::Short(Profile::M2)
    {
        return Err("H21 M1 or short M2 owner class changed".into());
    }
    compare_bounded_endpoint(plan, GlobalProducerRole::DaaRoster, 2048, false, true)?;
    compare_bounded_endpoint(plan, GlobalProducerRole::DaaRoster, 3072, false, true)?;
    Ok(())
}

#[test]
#[ignore = "C562 source incidence and accounting oracle; no proof or execution admission"]
fn global_endpoint_plan_incidence_and_accounting() {
    println!("C562_ENDPOINT_PLAN_STAGE|start");
    for (headers, slot_log, stage) in [
        (3u64, 2usize, "shape_n3"),
        (4u64, 2usize, "shape_n4"),
        (5u64, 3usize, "shape_n5"),
    ] {
        let history = WorkTreeHistoryPlan::compile(headers, slot_log, [0x35; 32], [0x35; 28])
            .unwrap();
        let plan = GlobalProducerEndpointPlan::new(&history).unwrap();
        compare_small_shape(&plan).unwrap();
        println!("C562_ENDPOINT_PLAN_STAGE|{}", stage);
        if headers == 5 {
            work_tag_mutants(&plan).unwrap();
            println!("C562_ENDPOINT_PLAN_STAGE|work_tag_mutants");
            daa_row_mutants(&plan).unwrap();
            println!("C562_ENDPOINT_PLAN_STAGE|daa_row_mutants");
        }
    }
    let h21_history =
        WorkTreeHistoryPlan::compile(1_827_840, 21, [0x35; 32], [0x35; 28]).unwrap();
    let h21_plan = GlobalProducerEndpointPlan::new(&h21_history).unwrap();
    let cache_shape = h21_plan.shape(GlobalProducerRole::DaaRoster).unwrap();
    verify_weight_cache_against_eq_index(&cache_shape).unwrap();
    h21_census_and_bounded_packing(&h21_plan).unwrap();
    println!("C562_ENDPOINT_PLAN_STAGE|h21_census");
    for role in [
        GlobalProducerRole::Work,
        GlobalProducerRole::DaaRoster,
        GlobalProducerRole::ReleasedHeader,
    ] {
        let report = h21_plan.fallback_accounting(role, 32).unwrap();
        let census = h21_plan.global_census(role).unwrap();
        let expected_census =
            checked_mul_u128(report.terms, 2, "expected census callback overflow").unwrap();
        let expected_u =
            checked_mul_u128(report.terms, 21, "expected U replay callback overflow").unwrap();
        let expected_v =
            checked_mul_u128(report.terms, 21, "expected V replay callback overflow").unwrap();
        let expected_numeric_right0 = checked_mul_u128(
            census.numeric_terms,
            21,
            "expected numeric RIGHT0 read overflow",
        )
        .unwrap();
        let expected_replays = expected_u.checked_add(expected_v).unwrap();
        let expected_fields = checked_mul_u128(
            report.full_owner_vector_expansions,
            WIDTH as u128,
            "expected field expansion overflow",
        )
        .unwrap();
        let expected_bytes =
            checked_mul_u128(expected_fields, 32, "expected expansion byte overflow").unwrap();
        if report.census_callbacks != expected_census
            || report.u_replay_callbacks != expected_u
            || report.u_scalar_right_reads != expected_u
            || report.v_replay_callbacks != expected_v
            || report.replay_callbacks != expected_replays
            || report.full_owner_vector_expansions != 90_177_536
            || report.expanded_field_elements != expected_fields
            || report.cumulative_expansion_bytes != expected_bytes
            || report.line_owner_requests != 1u128 << 21
            || report.numeric_right0_u_scalar_reads != expected_numeric_right0
            || report.numeric_right0_u_scalar_reads > report.u_scalar_right_reads
        {
            panic!("fallback lower-bound accounting changed for {:?}", role);
        }
    }
    if checked_mul_u128(u128::MAX, 2, "expected overflow").is_ok()
        || h21_plan
            .fallback_accounting(GlobalProducerRole::Work, 0)
            .is_ok()
    {
        panic!("fallback checked-arithmetic negative did not fail closed");
    }
    println!("C562_ENDPOINT_PLAN_STAGE|accounting");
    println!("C562_ENDPOINT_PLAN_STAGE|PASS");
}

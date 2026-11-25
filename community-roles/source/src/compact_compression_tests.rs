//! Bounded source tests for compact compression gates and their GKR/PCS joins.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::mem::{align_of, size_of};
use std::io::{self, Write};
use std::time::Instant;

use crate::circuit::{blake2b256_initial_state, CompressionInput};
use crate::compact_compression::{self as compact, CompactGate};
use crate::gkr::{self, Layer};
use crate::transcript::Transcript;

fn gate(left: u32, right: u32, kind: u8, expectedbit: u8) -> CompactGate {
    CompactGate { left, right, kind, expectedbit }
}

fn scalar(value: u64) -> Fr { Fr::from(value) }

fn hex_upper(bytes: &[u8]) -> String {
    bytes.iter().map(|value| format!("{value:02X}")).collect()
}

/// Includes all seven opcodes, both constant bits and both public bits. The
/// second layer makes each first-layer value observable in a zero output.
fn tiny_fixture() -> (Vec<Fr>, compact::Compiled, Vec<Layer>) {
    let input = vec![Fr::one(), Fr::zero(), Fr::one(), Fr::zero()];
    let first = vec![
        gate(0, 0, 0, 1), gate(0, 0, 0, 0), gate(0, 0, 1, 0),
        gate(0, 1, 2, 0), gate(0, 1, 3, 0), gate(0, 1, 4, 0),
        gate(0, 0, 5, 0), gate(0, 0, 6, 1),
    ];
    let expected = [1, 0, 1, 1, 0, 1, 0, 0];
    let final_layer = expected.iter().enumerate().map(|(index, bit)| {
        gate(index as u32, index as u32, 6, *bit)
    }).collect();
    let compact = compact::tiny(4, vec![first, final_layer]).unwrap();
    let mut previous_width = 4;
    let legacy = compact.layers().iter().map(|layer| {
        let expanded = layer.iter().map(|candidate| {
            compact::decode_gate(*candidate, previous_width).unwrap()
        }).collect::<Layer>();
        previous_width = layer.len();
        expanded
    }).collect();
    (input, compact, legacy)
}

#[test]
fn compact_gate_layout_and_literal_non_boolean_coefficients() {
    assert_eq!(size_of::<CompactGate>(), 12);
    assert_eq!(align_of::<CompactGate>(), 4);
    let two = scalar(2);
    let three = scalar(3);
    let cases = [
        (gate(0, 1, 0, 0), [Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero()]),
        (gate(0, 1, 0, 1), [Fr::one(), Fr::zero(), Fr::zero(), Fr::zero()]),
        (gate(0, 1, 1, 0), [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]),
        (gate(0, 1, 2, 0), [Fr::zero(), Fr::one(), Fr::one(), -two]),
        (gate(0, 1, 3, 0), [Fr::zero(), Fr::zero(), Fr::zero(), Fr::one()]),
        (gate(0, 1, 4, 0), [Fr::zero(), Fr::one(), Fr::one(), Fr::zero()]),
        (gate(0, 0, 5, 0), [Fr::zero(), -Fr::one(), Fr::zero(), Fr::one()]),
        (gate(0, 1, 6, 0), [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]),
        (gate(0, 1, 6, 1), [-Fr::one(), Fr::one(), Fr::zero(), Fr::zero()]),
    ];
    for (candidate, coefficients) in cases {
        let decoded = compact::decode_gate(candidate, 2).unwrap();
        assert_eq!([decoded.c0, decoded.c1, decoded.c2, decoded.c3], coefficients);
        let left = [two, three][candidate.left as usize];
        let right = [two, three][candidate.right as usize];
        let expected = coefficients[0] + coefficients[1] * left + coefficients[2] * right
            + coefficients[3] * left * right;
        assert_eq!(decoded.evaluate(&[two, three]), expected,
            "kind {} at non-Boolean point", candidate.kind);
    }
}

#[test]
fn compact_gate_admission_rejects_one_fault_at_a_time() {
    for candidate in [
        gate(0, 0, 7, 0), gate(0, 0, 255, 0),
        gate(0, 0, 0, 2), gate(0, 0, 6, 2),
        gate(0, 0, 1, 1), gate(0, 0, 2, 1), gate(0, 0, 3, 1),
        gate(0, 0, 4, 1), gate(0, 0, 5, 1),
        gate(2, 0, 2, 0), gate(0, 2, 2, 0),
        gate(0, 1, 5, 0),
    ] {
        assert!(compact::decode_gate(candidate, 2).is_err(),
            "malformed gate was admitted: {candidate:?}");
    }
    let (_, compiled, _) = tiny_fixture();
    let original = compiled.layers()[0][0];
    for candidate in [
        gate(original.left + 1, original.right, original.kind, original.expectedbit),
        gate(original.left, original.right + 1, original.kind, original.expectedbit),
        gate(original.left, original.right, 6, original.expectedbit),
        gate(original.left, original.right, original.kind, 0),
    ] {
        assert!(compiled.validate_candidate_gate(0, 0, candidate).is_err(),
            "stored gate field drift was admitted");
    }
    assert!(compiled.validate_candidate_gate(0, 0, original).is_ok());
}

#[test]
fn tiny_all_opcode_legacy_bytes_claim_and_continuation_match() {
    let (input, compact, legacy) = tiny_fixture();
    let values = compact.evaluate(&input).unwrap();
    assert_eq!(values.layer(0), input.as_slice());
    assert!(values.layer(2).iter().all(Fr::is_zero));
    let domain = b"compact-compression-tiny-legacy-differential";
    let mut old_prover = Transcript::new(domain);
    let (old_proof, old_claim) = gkr::prove(&input, &legacy, &mut old_prover).unwrap();
    let mut new_prover = Transcript::new(domain);
    let (new_proof, new_claim) = compact.prove_evaluated(&values, &mut new_prover).unwrap();
    assert_eq!(gkr::encode_proof(&new_proof).unwrap(), gkr::encode_proof(&old_proof).unwrap());
    assert_eq!(new_claim, old_claim);
    assert_eq!(new_prover.challenges(), old_prover.challenges());
    assert_eq!(new_prover.bytes_absorbed(), old_prover.bytes_absorbed());
    assert_eq!(new_prover.challenge_scalar(b"after-gkr"), old_prover.challenge_scalar(b"after-gkr"));

    let wire = gkr::encode_proof(&new_proof).unwrap();
    let decoded = gkr::decode_dimensions(compact.dimensions(), &wire).unwrap();
    assert_eq!(decoded, new_proof);
    let mut old_verifier = Transcript::new(domain);
    let old_verified = gkr::verify(input.len(), &legacy, &decoded, &mut old_verifier).unwrap();
    let mut new_verifier = Transcript::new(domain);
    let new_verified = compact.verify(&decoded, &mut new_verifier).unwrap();
    assert_eq!(new_verified, old_verified);
    assert_eq!(new_verified, new_claim);
    assert_eq!(new_verified.value, gkr::mle(&input, &new_verified.point).unwrap());
    assert_eq!(new_verifier.challenge_scalar(b"after-gkr"), old_verifier.challenge_scalar(b"after-gkr"));
}

#[test]
fn tiny_phase_codec_and_binding_mutants_fail_closed() {
    let (input, compiled, _) = tiny_fixture();
    let domain = b"compact-compression-tiny-mutants";
    let (proof, _) = compiled.prove(&input, &mut Transcript::new(domain)).unwrap();
    let wire = gkr::encode_proof(&proof).unwrap();
    for malformed in [
        wire[..wire.len() - 1].to_vec(),
        { let mut value = wire.clone(); value.push(0); value },
        { let mut value = wire.clone(); value[..32].fill(255); value },
    ] {
        assert!(gkr::decode_dimensions(compiled.dimensions(), &malformed).is_err());
    }
    let mut changes = Vec::new();
    let mut round = proof.clone(); round.layers[0].rounds[0][0] += Fr::one(); changes.push(round);
    let mut right = proof.clone(); right.layers[0].right_value += Fr::one(); changes.push(right);
    let mut line = proof.clone(); line.layers[0].line_coefficients[0] += Fr::one(); changes.push(line);
    for altered in changes {
        assert!(compiled.verify(&altered, &mut Transcript::new(domain)).is_err());
    }
    let mut bound = Transcript::new(domain);
    compiled.bind(&mut bound);
    let mut control = Transcript::new(domain);
    // The legacy verifier's initial binding is checked by the proof differential
    // above; an extra or changed prefix must alter the first challenge.
    control.append_bytes(b"wrong-statement", b"one-byte-difference");
    compiled.bind(&mut control);
    assert_ne!(bound.challenge_scalar(b"after-binding"), control.challenge_scalar(b"after-binding"));

    let words = [0u64; 8];
    let key_id = [7u8; 32];
    let commitment = [9u8; 32];
    let mut baseline = Transcript::new(domain);
    bind_public(&mut baseline, &words, &key_id, &commitment);
    compiled.bind(&mut baseline);
    let mut changed_words = words;
    changed_words[0] = 1;
    let mut changed_output = Transcript::new(domain);
    bind_public(&mut changed_output, &changed_words, &key_id, &commitment);
    compiled.bind(&mut changed_output);
    assert_ne!(baseline.clone().challenge_scalar(b"after-binding"),
        changed_output.challenge_scalar(b"after-binding"));
    let mut changed_commitment = commitment;
    changed_commitment[0] ^= 1;
    let mut changed_commit = Transcript::new(domain);
    bind_public(&mut changed_commit, &words, &key_id, &changed_commitment);
    compiled.bind(&mut changed_commit);
    assert_ne!(baseline.challenge_scalar(b"after-binding"),
        changed_commit.challenge_scalar(b"after-binding"));
}

#[test]
fn subcube_lsb_non_boolean_basis_and_arbitrary_tail() {
    let mut input = vec![Fr::zero(); 2048];
    input[0] = scalar(5);
    input[1] = scalar(7);
    input[2] = scalar(11);
    input[2047] = scalar(13);
    let point11: Vec<Fr> = [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        .into_iter().map(scalar).collect();
    let point18 = compact::subcube_point(&point11).unwrap();
    assert_eq!(point18.len(), 18);
    assert_eq!(&point18[..11], point11.as_slice());
    assert!(point18[11..].iter().all(Fr::is_zero));
    let mut extended = compact::pcs_input18(&input).unwrap();
    assert_eq!(extended.len(), 1 << 18);
    assert_eq!(gkr::mle(&input, &point11).unwrap(), gkr::mle(&extended, &point18).unwrap());
    extended[2048] = scalar(37); // An external unused tail need not be constrained to zero.
    assert_eq!(gkr::mle(&input, &point11).unwrap(), gkr::mle(&extended, &point18).unwrap());
    let mut wrong_high = point18.clone(); wrong_high[11] = scalar(2);
    assert_ne!(gkr::mle(&input, &point11).unwrap(), gkr::mle(&extended, &wrong_high).unwrap());
    let mut wrong_order = point18; wrong_order.reverse();
    assert_ne!(gkr::mle(&input, &point11).unwrap(), gkr::mle(&extended, &wrong_order).unwrap());
    assert!(compact::subcube_point(&point11[..10]).is_err());
    assert!(compact::pcs_input18(&input[..2047]).is_err());
}

fn native_case() -> CompressionInput {
    CompressionInput {
        state: std::array::from_fn(|index| blake2b256_initial_state()[index]
            ^ (0x9e37_79b9_7f4a_7c15u64.rotate_left(index as u32))),
        block: std::array::from_fn(|index| (index as u8).wrapping_mul(197).wrapping_add(37)),
        counter: 0x8000_0000_0000_0080,
        final_flag: true,
    }
}

/// A separate old-circuit assignment supplies all 512 native output bits. It
/// uses the fixed old width and is dropped before any large proof allocation.
#[test]
fn native_primary_shape_all_output_bits_and_local_faults() {
    let case = native_case();
    let reference = compact::native_reference(&case).unwrap();
    let input = compact::input_from_compression(&case);
    assert_eq!(reference.output.len(), 8);
    assert_eq!(input.len(), 2048);
    assert_eq!(&input[..1602], &reference.input[..1602]);
    assert!(input[1602..].iter().all(Fr::is_zero));
    let output = reference.output;
    drop(reference);

    let compiled = compact::compile(output).unwrap();
    let resources = compiled.resources();
    assert_eq!(resources.used_input, 1602);
    assert_eq!(resources.input_width, 2048);
    assert_eq!(resources.layers, 1853);
    assert_eq!(resources.primitive_nodes, 693_569);
    assert_eq!(resources.forwarding_gates, 9_646_972);
    assert_eq!(resources.logical_gates, 10_343_101);
    assert_eq!(resources.padding_gates, 4_795_715);
    assert_eq!(resources.padded_gates, 15_138_816);
    assert_eq!(resources.max_width, 8192);
    assert_eq!(resources.dependency_depth, 1852);
    assert_eq!(resources.proof_scalars, 174_105);
    assert_eq!(resources.proof_bytes, 5_571_360);
    assert_eq!(resources.challenges, 50_021);
    let audit = compiled.audit();
    assert_eq!(hex_upper(&audit.graph_blake),
        "9C7B85DA31C5375FF8915C640AC13F254BCFAEEC70E4033E4EA44FAF33788EFD60D3733FF09B7B5819EAD4313CADBD4B723931089C9791B5E60D2C151D1D7111");
    assert_eq!(hex_upper(&audit.widths_blake),
        "CC1D29348944A8E14FCF3D10A3E3249EAB2A8C0FD84D414898ACE93DDB78B2772D1967B2DDB9BA294C6258B3B173180A9CC1359CFB2D0CA34D23535B634A1863");

    let evaluation = compiled.evaluate(&input).unwrap();
    assert_native_controls(&compiled, &input, &output, &evaluation);
}

fn assert_native_controls(compiled: &compact::Compiled, input: &[Fr],
                          output: &[u64; 8], evaluation: &compact::Evaluation<'_>) {
    assert!(evaluation.layer(compiled.layers().len()).iter().all(Fr::is_zero));
    let layers = compiled.layers();
    assert_eq!(layers.iter().flatten().filter(|gate| gate.kind == 6).count(), 512);
    let final_layer = layers.last().unwrap();
    let final_previous = evaluation.layer(layers.len() - 1);
    for index in 0..512 {
        let native_bit = ((output[index / 64] >> (index % 64)) & 1) as u8;
        let residual = final_layer[2048 + index];
        assert_eq!(residual.kind, 1);
        assert_eq!(residual.left, residual.right);
        let decoded = compact::decode_gate(residual, final_previous.len()).unwrap();
        assert!(decoded.evaluate(final_previous).is_zero());
        let changed = final_previous[residual.left as usize] + Fr::one();
        let local_fault = decoded.c0 + decoded.c1 * changed + decoded.c2 * changed
            + decoded.c3 * changed * changed;
        assert_eq!(local_fault, Fr::one(), "output bit {index} final residual");

        // The final residuals retain source order; depth-bucket gate positions
        // do not. Follow forwarding copies to the originating comparison.
        let mut layer_index = layers.len() - 2;
        let mut gate_index = residual.left as usize;
        loop {
            let candidate = layers[layer_index][gate_index];
            let previous = evaluation.layer(layer_index);
            let value = evaluation.layer(layer_index + 1)[gate_index];
            let decoded = compact::decode_gate(candidate, previous.len()).unwrap();
            assert_eq!(decoded.evaluate(previous), value);
            assert!(value.is_zero(), "output bit {index} forwarded residual");
            match candidate.kind {
                1 => {
                    assert_eq!(candidate.left, candidate.right);
                    assert!(layer_index > 0, "output bit {index} lacks comparison");
                    gate_index = candidate.left as usize;
                    layer_index -= 1;
                }
                6 => {
                    assert_eq!(candidate.expectedbit, native_bit, "native output bit {index}");
                    assert_eq!(previous[candidate.left as usize], scalar(native_bit as u64));
                    let mut flipped = candidate;
                    flipped.expectedbit ^= 1;
                    let changed_value = compact::decode_gate(flipped, previous.len())
                        .unwrap().evaluate(previous);
                    assert!(changed_value == Fr::one() || changed_value == -Fr::one(),
                        "output bit {index} isolated comparison fault");
                    assert!(compiled.validate_candidate_gate(layer_index, gate_index, flipped)
                        .is_err(), "output bit {index} location binding");
                    break;
                }
                _ => panic!("output bit {index} trace reached a non-comparison gate"),
            }
        }
    }

    // Each input residual has a canonical final row. Follow its forwarded
    // value to the exact first-layer bitness or zero constraint.
    let layout = compact::native_layout();
    let faults = [
        ("zero", 0usize, Fr::one(), 1u8),
        ("state", layout.state[0][0], scalar(2), 5),
        ("block", layout.message[3][7], scalar(2), 5),
        ("counter", layout.counter[63], scalar(2), 5),
        ("flag", layout.final_flag, scalar(2), 5),
        ("padding-first", 1602, Fr::one(), 1),
        ("padding-last", 2047, Fr::one(), 1),
    ];
    for (name, wire, value, kind) in faults {
        let final_residual = final_layer[wire];
        assert_eq!(final_residual.kind, 1, "{name} final residual copy");
        assert_eq!(final_residual.left, final_residual.right);
        let mut gate_index = final_residual.left as usize;
        for layer_index in (1..layers.len() - 1).rev() {
            let copy = layers[layer_index][gate_index];
            assert_eq!(copy.kind, 1, "{name} forwarding kind");
            assert_eq!(copy.left, copy.right);
            assert_eq!(evaluation.layer(layer_index + 1)[gate_index],
                evaluation.layer(layer_index)[copy.left as usize]);
            gate_index = copy.left as usize;
        }
        let constraint = layers[0][gate_index];
        assert_eq!(constraint.kind, kind, "{name} source residual kind");
        assert_eq!(constraint.left as usize, wire, "{name} source wire");
        assert_eq!(constraint.right, constraint.left);
        let decoded = compact::decode_gate(constraint, input.len()).unwrap();
        assert!(decoded.evaluate(input).is_zero(), "{name} honest residual");
        let mut changed = input.to_vec();
        changed[wire] = value;
        assert!(!decoded.evaluate(&changed).is_zero(), "{name} violated residual");
        let mut dropped = constraint;
        dropped.kind = 0;
        assert!(compiled.validate_candidate_gate(0, gate_index, dropped).is_err(),
            "{name} dropped constraint");
        let mut rerouted = constraint;
        rerouted.left = ((wire + 1) % input.len()) as u32;
        rerouted.right = rerouted.left;
        assert!(compiled.validate_candidate_gate(0, gate_index, rerouted).is_err(),
            "{name} rerouted constraint");
    }
}

fn phase<T>(name: &'static str, action: impl FnOnce() -> T) -> (T, u64) {
    println!("COMPACT_STAGE_BEGIN_V1 {name}");
    io::stdout().flush().unwrap();
    let start = Instant::now();
    let result = action();
    let elapsed = u64::try_from(start.elapsed().as_nanos()).unwrap();
    println!("COMPACT_STAGE_END_V1 {name} {elapsed}");
    io::stdout().flush().unwrap();
    (result, elapsed)
}

fn output_bytes(words: &[u64; 8]) -> [u8; 64] {
    let mut bytes = [0u8; 64];
    for (word, chunk) in words.iter().zip(bytes.chunks_exact_mut(8)) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    bytes
}

fn bind_public(transcript: &mut Transcript, words: &[u64; 8], key_id: &[u8; 32],
               commitment: &[u8]) {
    transcript.append_bytes(b"compression-profile", b"primary-localops-blake2b-v1");
    transcript.append_bytes(b"compression-public-512", &output_bytes(words));
    transcript.append_bytes(b"compression-setup-id", key_id);
    transcript.append_bytes(b"compression-input-commitment", commitment);
}

/// This is deliberately ignored: the parent runs it under an independent hard
/// 2 GiB / 120 s Job. Stage starts are flushed before costly allocations; a
/// timeout has no successful final diagnostic line.
#[test]
#[ignore = "supervised 2 GiB / 120 s primary diagnostic only"]
fn aggregate_primary_compact_gkr_pcs_diagnostic() {
    use std::collections::BTreeMap;
    use crate::{pcs, verifier_key};
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;

    let mut phase_ns = BTreeMap::new();
    let (_, elapsed) = phase("tiny", || {
        compact_gate_layout_and_literal_non_boolean_coefficients();
        compact_gate_admission_rejects_one_fault_at_a_time();
        tiny_all_opcode_legacy_bytes_claim_and_continuation_match();
        tiny_phase_codec_and_binding_mutants_fail_closed();
        subcube_lsb_non_boolean_basis_and_arbitrary_tail();
    });
    phase_ns.insert("tiny", elapsed);

    let case = native_case();
    let ((input, output), elapsed) = phase("native_oracle", || {
        let native = compact::native_reference(&case).unwrap();
        let primary = compact::input_from_compression(&case);
        assert_eq!(primary.len(), 2048);
        assert_eq!(&primary[..1602], &native.input[..1602]);
        assert_eq!(native.input.len(), 65536);
        let output = native.output;
        drop(native);
        (primary, output)
    });
    phase_ns.insert("native_oracle", elapsed);

    let (compiled, elapsed) = phase("compile", || compact::compile(output).unwrap());
    phase_ns.insert("compile", elapsed);
    let resources = compiled.resources();
    let audit = compiled.audit();
    assert_eq!(resources.used_input, 1602);
    assert_eq!(resources.input_width, 2048);
    assert_eq!(resources.layers, 1853);
    assert_eq!(resources.padded_gates, 15_138_816);
    assert_eq!(resources.gate_capacity_bytes, 181_665_792);
    assert!(resources.node_capacity_bytes <= 218_103_808);
    assert!(resources.map_peak_bytes <= 27_824_680);
    assert!(resources.layer_header_bytes <= 65_536);
    assert!(resources.phase_peak_bytes <= 1_310_720);
    assert_eq!(hex_upper(&audit.graph_blake),
        "9C7B85DA31C5375FF8915C640AC13F254BCFAEEC70E4033E4EA44FAF33788EFD60D3733FF09B7B5819EAD4313CADBD4B723931089C9791B5E60D2C151D1D7111");
    assert_eq!(hex_upper(&audit.widths_blake),
        "CC1D29348944A8E14FCF3D10A3E3249EAB2A8C0FD84D414898ACE93DDB78B2772D1967B2DDB9BA294C6258B3B173180A9CC1359CFB2D0CA34D23535B634A1863");

    let (evaluation, elapsed) = phase("evaluate", || {
        let evaluation = compiled.evaluate(&input).unwrap();
        assert_native_controls(&compiled, &input, &output, &evaluation);
        evaluation
    });
    phase_ns.insert("evaluate", elapsed);
    let evaluation_resources = evaluation.resources();

    let key_bytes = include_bytes!("../fixtures/verifier-keys-v1/log18.vk");
    let ((setup, key, prepared_coeff_capacity_bytes), elapsed) = phase("setup", || {
        use ark_ec::CurveGroup;
        let key = verifier_key::admit(18, key_bytes).unwrap();
        let setup = pcs::generate_setup(18).unwrap();
        assert_eq!(&setup.id, key.id());
        assert_eq!(pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap(), key_bytes);
        assert_eq!(size_of::<Fr>(), 32);
        assert_eq!(size_of::<ark_bn254::G1Projective>(), 96);
        assert_eq!(size_of::<ark_bn254::G2Projective>(), 192);
        assert_eq!(setup.prover.g1_vec.len(), 512);
        assert_eq!(setup.prover.g2_vec.len(), 512);
        let prepared = <ark_bn254::Bn254 as ark_ec::pairing::Pairing>::G2Prepared::from(
            setup.prover.g2_vec[0].0.clone().into_affine());
        assert_eq!(prepared.ell_coeffs.len(), 87);
        assert!(prepared.ell_coeffs.capacity() <= 128);
        assert_eq!(std::mem::size_of_val(&prepared.ell_coeffs[0]), 192);
        let prepared_coeff_capacity_bytes = prepared.ell_coeffs.capacity() * 192;
        drop(prepared);
        (setup, key, prepared_coeff_capacity_bytes)
    });
    phase_ns.insert("setup", elapsed);

    let ((committed, commitment_bytes, pcs_vector_capacity_bytes), elapsed) = phase("commit", || {
        let extended = compact::pcs_input18(&input).unwrap();
        assert_eq!(&extended[..2048], input.as_slice());
        assert!(extended[2048..].iter().all(Fr::is_zero));
        let pcs_vector_capacity_bytes = extended.capacity() * size_of::<Fr>();
        let committed = pcs::commit(&extended, &setup).unwrap();
        let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap();
        drop(extended);
        (committed, commitment_bytes, pcs_vector_capacity_bytes)
    });
    phase_ns.insert("commit", elapsed);

    let domain = b"nipopow-primary-compact-gkr-pcs-v1";
    let mut producer = Transcript::new(domain);
    bind_public(&mut producer, &output, key.id(), &commitment_bytes);
    let ((proof, claim), elapsed) = phase("gkr_prove", || {
        compiled.prove_evaluated(&evaluation, &mut producer).unwrap()
    });
    phase_ns.insert("gkr_prove", elapsed);
    let gkr_challenges = producer.challenges();
    assert_eq!(gkr_challenges, resources.challenges as u64);

    let ((wire, decoded), elapsed) = phase("gkr_codec", || {
        let wire = gkr::encode_proof(&proof).unwrap();
        assert_eq!(wire.len(), resources.proof_bytes);
        assert!(wire.capacity() <= 8_388_608);
        drop(proof);
        assert!(gkr::decode_dimensions(compiled.dimensions(), &wire[..wire.len()-1]).is_err());
        let mut trailing = wire.clone(); trailing.push(0);
        assert!(gkr::decode_dimensions(compiled.dimensions(), &trailing).is_err());
        drop(trailing);
        let decoded = gkr::decode_dimensions(compiled.dimensions(), &wire).unwrap();
        (wire, decoded)
    });
    phase_ns.insert("gkr_codec", elapsed);
    assert_eq!(wire.len(), 5_571_360);

    let mut consumer = Transcript::new(domain);
    bind_public(&mut consumer, &output, key.id(), &commitment_bytes);
    let (verified, elapsed) = phase("gkr_verify", || {
        let verified = compiled.verify(&decoded, &mut consumer).unwrap();
        assert_eq!(verified, claim);
        assert_eq!(verified.value, gkr::mle(&input, &verified.point).unwrap());
        assert_eq!(consumer.challenges(), gkr_challenges);
        assert_eq!(consumer.clone().challenge_scalar(b"after-gkr"),
                   producer.clone().challenge_scalar(b"after-gkr"));
        verified
    });
    phase_ns.insert("gkr_verify", elapsed);

    let point18 = compact::subcube_point(&verified.point).unwrap();
    let (opening, elapsed) = phase("pcs_open", || {
        pcs::open(&committed, &point18, &setup, &mut producer).unwrap()
    });
    phase_ns.insert("pcs_open", elapsed);
    let ((), elapsed) = phase("pcs_verify", || {
        let encoded = pcs::encode_proof(&opening).unwrap();
        let decoded_opening = pcs::decode_proof(&encoded, 18).unwrap();
        let before = consumer.clone();
        pcs::verify_admitted(committed.commitment.clone(), verified.value, &point18,
            &decoded_opening, &key, &mut consumer).unwrap();
        assert_eq!(producer.clone().challenge_scalar(b"after-pcs"),
                   consumer.clone().challenge_scalar(b"after-pcs"));
        assert!(pcs::verify_admitted(committed.commitment.clone(), verified.value + Fr::one(),
            &point18, &decoded_opening, &key, &mut before.clone()).is_err());
        let mut wrong_point = point18.clone(); wrong_point[0] += Fr::one();
        assert!(pcs::verify_admitted(committed.commitment.clone(), verified.value,
            &wrong_point, &decoded_opening, &key, &mut before.clone()).is_err());
    });
    phase_ns.insert("pcs_verify", elapsed);

    // This is a live-vector payload estimate, not process RSS. The supervised
    // Job measures the actual hard cap. PCS/setup scratch is only a proposed
    // ceiling until separately measured.
    let setup_pcs_scratch_ceiling_bytes = 32usize << 20;
    let setup_pcs_scratch_model_bytes = 512usize * 128 * 192
        + 2 * (1usize << 18) * size_of::<Fr>() + (4usize << 20);
    assert!(setup_pcs_scratch_model_bytes <= setup_pcs_scratch_ceiling_bytes);
    let logical_payload_model_bytes = resources.gate_capacity_bytes
        + evaluation_resources.values_capacity_bytes + resources.phase_peak_bytes
        + resources.proof_bytes + wire.capacity() + pcs_vector_capacity_bytes
        + setup_pcs_scratch_ceiling_bytes;
    assert!(logical_payload_model_bytes <= 1usize << 30);
    let report = serde_json::json!({
        "schema": "nipopow-compact-compression-diagnostic-v1",
        "status": "completed",
        "phase_ns": phase_ns,
        "counts": {
            "used_input": resources.used_input,
            "input_width": resources.input_width,
            "layers": resources.layers,
            "primitive_nodes": resources.primitive_nodes,
            "forwarding_gates": resources.forwarding_gates,
            "logical_gates": resources.logical_gates,
            "padding_gates": resources.padding_gates,
            "padded_gates": resources.padded_gates,
            "max_width": resources.max_width,
            "dependency_depth": resources.dependency_depth,
            "proof_scalars": resources.proof_scalars,
            "proof_bytes": resources.proof_bytes,
            "gkr_challenges": gkr_challenges,
            "post_pcs_challenges": consumer.challenges(),
            "producer_transcript_bytes": producer.bytes_absorbed(),
            "consumer_transcript_bytes": consumer.bytes_absorbed(),
        },
        "capacities": {
            "gate_bytes": resources.gate_capacity_bytes,
            "node_bytes": resources.node_capacity_bytes,
            "map_peak_bytes": resources.map_peak_bytes,
            "layer_header_bytes": resources.layer_header_bytes,
            "compiler_peak_bytes": resources.compiler_peak_bytes,
            "values_bytes": resources.values_bytes,
            "values_capacity_bytes": evaluation_resources.values_capacity_bytes,
            "phase_peak_bytes": resources.phase_peak_bytes,
            "proof_wire_capacity_bytes": wire.capacity(),
            "pcs_vector_capacity_bytes": pcs_vector_capacity_bytes,
            "prepared_coeff_capacity_bytes": prepared_coeff_capacity_bytes,
            "setup_pcs_scratch_model_bytes": setup_pcs_scratch_model_bytes,
            "setup_pcs_scratch_ceiling_bytes": setup_pcs_scratch_ceiling_bytes,
            "logical_payload_model_bytes": logical_payload_model_bytes,
        },
        "checks": {
            "audit_blake": true,
            "native512": true,
            "final_zero": true,
            "setup18_id": true,
            "key_bytes": true,
            "pcs_prepared_sample": true,
            "setup_executed": true,
            "gkr_proof_executed": true,
            "pcs_open_executed": true,
            "gkr_codec": true,
            "gkr_claim": true,
            "subcube": true,
            "pcs_admitted": true,
            "continuation": true,
            "setup_pcs_scratch_measured": false,
        },
        "global_claim_closed": false,
    });
    println!("COMPACT_DIAG_V1 {report}");
    io::stdout().flush().unwrap();
}

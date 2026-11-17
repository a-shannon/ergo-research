use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ergo_header_core::Header;

use crate::{
    daa_count,
    daa_integer::{self, Inputs},
    daa_one_ratio_finish::{self, CompiledOne},
    gkr::Gate,
    header_hash,
    mapped_one_daa::{MappedM1, IMAGE_START},
    one_daa_layout::OneDaaLayout,
    serializer,
    sparse::Term,
    transcript::Transcript,
};

const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");
const SLOT_LEN: usize = 1 << 20;
const CHILD_SLOT: usize = 2048;

fn raw_at(height: u32) -> Vec<u8> {
    let value: serde_json::Value = serde_json::from_str(FIXTURE).unwrap();
    value["headers"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["height"].as_u64() == Some(height as u64))
        .map(|entry| {
            entry["raw_hex"]
                .as_str()
                .unwrap()
                .as_bytes()
                .chunks_exact(2)
                .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                .collect()
        })
        .unwrap_or_else(|| panic!("fixture height {height} missing"))
}

fn header_at(height: u32) -> Header {
    Header::decode(&raw_at(height), None).unwrap()
}

fn fixture_producer() -> CompiledOne {
    let start = header_at(1024);
    let end = header_at(2048);
    let child = header_at(2049);
    daa_one_ratio_finish::compile(
        &daa_count::q(),
        Inputs {
            nbits: end.n_bits,
            start_timestamp: start.timestamp,
            end_timestamp: end.timestamp,
        },
        child.n_bits,
        true,
    )
    .unwrap()
}

fn native_residual_rows(compiled: &daa_integer::Compiled) -> Vec<usize> {
    daa_integer::residuals(compiled)
        .unwrap()
        .iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect()
}

fn mapped_residual_rows(mapped: &MappedM1) -> Vec<usize> {
    let mut rows = vec![Fr::zero(); mapped.circuit().row_count];
    for term in &mapped.circuit().terms {
        rows[term.row] += term.gate.evaluate(mapped.witness());
    }
    rows.iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect()
}

fn owner_assignments() -> Vec<(usize, serializer::Compiled)> {
    [1024u32, 2048, 2049]
        .into_iter()
        .map(|height| {
            let header = header_at(height);
            let fields = serializer::Fields::from_header(&header).unwrap();
            (
                height as usize - 1,
                serializer::build(Some(&fields)).unwrap(),
            )
        })
        .collect()
}

fn eq_at(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, value)| {
            weight
                * if (index >> bit) & 1 == 1 {
                    *value
                } else {
                    Fr::one() - value
                }
        })
}

fn dense_point(log: usize, salt: u64) -> Vec<Fr> {
    (0..log)
        .map(|index| Fr::from(((index as u64 * 17 + salt * 13 + 5) % 97) + 2))
        .collect()
}

fn boolean_point(log: usize, index: usize) -> Vec<Fr> {
    (0..log)
        .map(|bit| Fr::from(((index >> bit) & 1) as u64))
        .collect()
}

fn finite_arithmetic_coefficients(
    terms: &[Term],
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
    row_slot: usize,
    left_slot: usize,
    right_slot: usize,
    dummy_global_zero: bool,
) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for term in terms {
        let row = row_slot * (1 << 14) + term.row;
        let left = left_slot * SLOT_LEN + IMAGE_START + term.gate.left;
        let right = if dummy_global_zero && term.gate.right == 0 {
            0
        } else {
            right_slot * SLOT_LEN + IMAGE_START + term.gate.right
        };
        let weight = eq_at(r, row) * eq_at(u, left) * eq_at(v, right);
        out[0] += weight * term.gate.c0;
        out[1] += weight * term.gate.c1;
        out[2] += weight * term.gate.c2;
        out[3] += weight * term.gate.c3;
    }
    out
}

fn expected_alias_terms(producer: &CompiledOne) -> Vec<Term> {
    let serializer = serializer::build(None).unwrap();
    let fields = &serializer.layout.fields;
    let external = &producer.arithmetic.external;
    let child = &producer.output.child_nbits;
    let mut ports = Vec::with_capacity(192);
    let mut append = |slot: usize, serializer_field: usize, native_wire: usize| {
        let row = (CHILD_SLOT << 8) + ports.len();
        ports.push(Term {
            row,
            gate: Gate {
                left: slot * SLOT_LEN + header_hash::SERIALIZER_OFFSET + serializer_field,
                right: CHILD_SLOT * SLOT_LEN + IMAGE_START + native_wire,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: -Fr::one(),
                c3: Fr::zero(),
            },
        });
    };
    for bit in 0..64 {
        append(1023, fields.timestamp[bit], external.start_timestamp[bit]);
    }
    for bit in 0..64 {
        append(2047, fields.timestamp[bit], external.end_timestamp[bit]);
    }
    for bit in 0..32 {
        append(2047, fields.n_bits[bit], external.nbits[bit]);
    }
    for bit in 0..32 {
        append(2048, fields.n_bits[bit], child[bit]);
    }
    ports
}

fn finite_alias_coefficients(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for term in terms {
        let weight = eq_at(r, term.row) * eq_at(u, term.gate.left) * eq_at(v, term.gate.right);
        out[0] += weight * term.gate.c0;
        out[1] += weight * term.gate.c1;
        out[2] += weight * term.gate.c2;
        out[3] += weight * term.gate.c3;
    }
    out
}

#[test]
fn raw_2049_admits_and_all_192_canonical_serializer_imports_resolve() {
    let layout = OneDaaLayout::compile(2049, 12).unwrap();
    let producer = fixture_producer();
    let mapped = layout.admit(&producer).unwrap();
    assert!(native_residual_rows(&producer.arithmetic).is_empty());
    assert!(mapped_residual_rows(&mapped).is_empty());

    let owners = owner_assignments();
    let mut terms = Vec::new();
    assert_eq!(
        layout
            .visit_alias_terms(|term| {
                terms.push(term);
                Ok(())
            })
            .unwrap(),
        192
    );
    assert_eq!(terms.len(), 192);
    let fields = [
        &owners[0].1.layout.fields,
        &owners[1].1.layout.fields,
        &owners[2].1.layout.fields,
    ];
    let expected_targets = expected_alias_terms(&producer);
    assert_eq!(terms, expected_targets, "full physical alias gate tuples");
    let mut expected_sources = Vec::with_capacity(192);
    expected_sources.extend(fields[0].timestamp.iter().map(|wire| (1023usize, *wire)));
    expected_sources.extend(fields[1].timestamp.iter().map(|wire| (2047usize, *wire)));
    expected_sources.extend(fields[1].n_bits.iter().map(|wire| (2047usize, *wire)));
    expected_sources.extend(fields[2].n_bits.iter().map(|wire| (2048usize, *wire)));

    let mut residual_nonzero = 0usize;
    for (index, term) in terms.iter().enumerate() {
        let (source_slot, serializer_wire) = expected_sources[index];
        let expected_left =
            source_slot * SLOT_LEN + header_hash::SERIALIZER_OFFSET + serializer_wire;
        let expected_right = expected_targets[index].gate.right;
        assert_eq!(term.row, (CHILD_SLOT << 8) + index);
        assert_eq!(
            term.gate.left, expected_left,
            "source owner/wire at port {index}"
        );
        assert_eq!(
            term.gate.right, expected_right,
            "target owner/wire at port {index}"
        );
        assert_eq!(term.gate.c1, Fr::one());
        assert_eq!(term.gate.c2, -Fr::one());

        let assignment = owners
            .iter()
            .find(|(slot, _)| *slot == source_slot)
            .unwrap();
        let local = term.gate.left % SLOT_LEN - header_hash::SERIALIZER_OFFSET;
        let input = assignment.1.input.as_ref().unwrap();
        let source = input[local];
        let target = mapped.witness()[term.gate.right % SLOT_LEN];
        if source != target {
            residual_nonzero += 1;
        }
    }
    assert_eq!(residual_nonzero, 0);
    assert_eq!(
        layout
            .visit_alias_terms(|_| Err("stop at sink".into()))
            .err()
            .as_deref(),
        Some("stop at sink")
    );
    assert_eq!(
        layout
            .alias_coefficients(
                &vec![Fr::zero(); 19],
                &vec![Fr::zero(); 32],
                &vec![Fr::zero(); 32]
            )
            .err()
            .as_deref(),
        Some("M1 alias point dimensions rejected")
    );
    for (u_len, v_len) in [(31, 32), (32, 31)] {
        assert_eq!(
            layout
                .alias_coefficients(
                    &vec![Fr::zero(); 20],
                    &vec![Fr::zero(); u_len],
                    &vec![Fr::zero(); v_len]
                )
                .err()
                .as_deref(),
            Some("M1 alias point dimensions rejected")
        );
    }
    assert_eq!(
        layout
            .arithmetic_coefficients(
                &vec![Fr::zero(); 25],
                &vec![Fr::zero(); 32],
                &vec![Fr::zero(); 32]
            )
            .err()
            .as_deref(),
        Some("M1 arithmetic point dimensions rejected")
    );
    for (u_len, v_len) in [(31, 32), (32, 31)] {
        assert_eq!(
            layout
                .arithmetic_coefficients(
                    &vec![Fr::zero(); 26],
                    &vec![Fr::zero(); u_len],
                    &vec![Fr::zero(); v_len]
                )
                .err()
                .as_deref(),
            Some("M1 arithmetic point dimensions rejected")
        );
    }
}

#[test]
fn consumer_template_rejects_each_native_count_checkpoint_and_handle_change() {
    let layout = OneDaaLayout::compile(2049, 12).unwrap();
    let mut producer = fixture_producer();
    macro_rules! reject_field {
        ($target:expr, $error:expr) => {{
            let previous = $target;
            $target = previous + 1;
            assert_eq!(layout.admit(&producer).err().as_deref(), Some($error));
            $target = previous;
        }};
    }

    const COUNT_ERROR: &str = "M1 native semantic count or witness shape mismatch";
    const HANDLE_ERROR: &str = "M1 native external, A1, finish, or checkpoint handles mismatch";
    const CIRCUIT_ERROR: &str = "M1 native circuit differs from consumer template";
    reject_field!(producer.arithmetic.count.live_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.input_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.padded_input_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.residual_rows, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.padded_rows, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.terms, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.boolean_rows, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.linear_rows, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.bilinear_rows, COUNT_ERROR);
    reject_field!(
        producer.arithmetic.count.maximum_column_signed_abs_bits,
        COUNT_ERROR
    );
    reject_field!(producer.arithmetic.count.maximum_degree, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.source_nbits_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.source_timestamp_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.decoded_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.wrapped_delta_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.denominator_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.numerator_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.quotient_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.remainder_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.quotient_sign_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.remainder_sign_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.auxiliary_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.padding_bits, COUNT_ERROR);
    reject_field!(producer.arithmetic.count.peak_row_terms, COUNT_ERROR);
    let old_topology = producer.arithmetic.count.topology_blake2b256;
    producer.arithmetic.count.topology_blake2b256[0] ^= 1;
    assert_eq!(layout.admit(&producer).err().as_deref(), Some(COUNT_ERROR));
    producer.arithmetic.count.topology_blake2b256 = old_topology;

    let saved_circuit = producer.arithmetic.circuit.take();
    assert_eq!(
        layout.admit(&producer).err().as_deref(),
        Some("M1 producer circuit was not materialized")
    );
    producer.arithmetic.circuit = saved_circuit;

    let removed = producer.arithmetic.witness.pop().unwrap();
    assert_eq!(layout.admit(&producer).err().as_deref(), Some(COUNT_ERROR));
    producer.arithmetic.witness.push(removed);

    let padding_wire = producer.arithmetic.count.live_bits;
    let previous_padding = producer.arithmetic.witness[padding_wire];
    producer.arithmetic.witness[padding_wire] = Fr::one();
    assert_eq!(
        layout.admit(&producer).err().as_deref(),
        Some("M1 producer native padding is nonzero")
    );
    producer.arithmetic.witness[padding_wire] = previous_padding;

    for index in 0..producer.output.timestamp_rows.len() {
        reject_field!(producer.output.timestamp_rows[index], HANDLE_ERROR);
    }
    reject_field!(producer.output.delta_nonzero, HANDLE_ERROR);
    reject_field!(producer.output.use_quotient, HANDLE_ERROR);
    reject_field!(producer.output.selected[0], HANDLE_ERROR);
    reject_field!(producer.output.numeric_result[0], HANDLE_ERROR);
    for index in 0..producer.output.child_nbits.len() {
        reject_field!(producer.output.child_nbits[index], HANDLE_ERROR);
    }
    reject_field!(producer.output.before.live_bits, HANDLE_ERROR);
    reject_field!(producer.output.before.rows, HANDLE_ERROR);
    reject_field!(producer.output.before.terms, HANDLE_ERROR);
    reject_field!(producer.output.after_profile.live_bits, HANDLE_ERROR);
    reject_field!(producer.output.after_profile.rows, HANDLE_ERROR);
    reject_field!(producer.output.after_profile.terms, HANDLE_ERROR);
    reject_field!(producer.output.after_fallback.live_bits, HANDLE_ERROR);
    reject_field!(producer.output.after_fallback.rows, HANDLE_ERROR);
    reject_field!(producer.output.after_fallback.terms, HANDLE_ERROR);
    reject_field!(producer.output.before_child.live_bits, HANDLE_ERROR);
    reject_field!(producer.output.before_child.rows, HANDLE_ERROR);
    reject_field!(producer.output.before_child.terms, HANDLE_ERROR);
    reject_field!(producer.output.increment.before.live_bits, HANDLE_ERROR);
    reject_field!(producer.output.increment.before.rows, HANDLE_ERROR);
    reject_field!(producer.output.increment.before.terms, HANDLE_ERROR);
    reject_field!(producer.output.increment.after.live_bits, HANDLE_ERROR);
    reject_field!(producer.output.increment.after.rows, HANDLE_ERROR);
    reject_field!(producer.output.increment.after.terms, HANDLE_ERROR);
    reject_field!(producer.output.increment.added_live_bits, HANDLE_ERROR);
    reject_field!(producer.output.increment.added_rows, HANDLE_ERROR);
    reject_field!(producer.output.increment.added_terms, HANDLE_ERROR);
    reject_field!(producer.arithmetic.external.nbits[0], HANDLE_ERROR);
    reject_field!(
        producer.arithmetic.external.start_timestamp[0],
        HANDLE_ERROR
    );
    reject_field!(producer.arithmetic.external.end_timestamp[0], HANDLE_ERROR);
    reject_field!(
        producer.arithmetic.output.decoded_difficulty[0],
        HANDLE_ERROR
    );
    reject_field!(producer.arithmetic.output.wrapped_delta[0], HANDLE_ERROR);
    reject_field!(
        producer.arithmetic.output.denominator_magnitude[0],
        HANDLE_ERROR
    );
    reject_field!(producer.arithmetic.output.numerator[0], HANDLE_ERROR);
    reject_field!(
        producer.arithmetic.output.quotient_magnitude[0],
        HANDLE_ERROR
    );
    reject_field!(producer.arithmetic.output.quotient_negative, HANDLE_ERROR);
    reject_field!(
        producer.arithmetic.output.remainder_magnitude[0],
        HANDLE_ERROR
    );
    reject_field!(producer.arithmetic.output.remainder_negative, HANDLE_ERROR);

    let old = {
        let term = &mut producer.arithmetic.circuit.as_mut().unwrap().terms[0];
        let old = term.gate.c0;
        term.gate.c0 += Fr::one();
        old
    };
    assert_eq!(
        layout.admit(&producer).err().as_deref(),
        Some(CIRCUIT_ERROR)
    );
    producer.arithmetic.circuit.as_mut().unwrap().terms[0]
        .gate
        .c0 = old;
    assert!(layout.admit(&producer).is_ok());
}

#[test]
fn domain_and_analytic_coefficients_are_checked_against_independent_global_terms() {
    for (headers, slot_log, error) in [
        (2048, 11, "M1 history count or slot domain rejected"),
        (
            2049,
            11,
            "M1 history count does not match its minimal slot domain",
        ),
        (
            2049,
            13,
            "M1 history count does not match its minimal slot domain",
        ),
        (2_097_153, 22, "M1 history count or slot domain rejected"),
        (u64::MAX, 64, "M1 history count or slot domain rejected"),
    ] {
        assert_eq!(
            OneDaaLayout::compile(headers, slot_log).err().as_deref(),
            Some(error)
        );
    }
    let layout = OneDaaLayout::compile(2049, 12).unwrap();
    let native_producer = fixture_producer();
    let native = native_producer.arithmetic.circuit.as_ref().unwrap();
    let r = dense_point(26, 1);
    let u = dense_point(32, 2);
    let v = dense_point(32, 3);
    let actual = layout.arithmetic_coefficients(&r, &u, &v).unwrap();
    let expected = finite_arithmetic_coefficients(
        native.terms.as_slice(),
        &r,
        &u,
        &v,
        CHILD_SLOT,
        CHILD_SLOT,
        CHILD_SLOT,
        false,
    );
    assert_eq!(actual, expected);

    for (row_slot, left_slot, right_slot, dummy) in [
        (CHILD_SLOT - 1, CHILD_SLOT, CHILD_SLOT, false),
        (CHILD_SLOT, CHILD_SLOT - 1, CHILD_SLOT, false),
        (CHILD_SLOT, CHILD_SLOT, CHILD_SLOT - 1, false),
        (CHILD_SLOT, CHILD_SLOT, CHILD_SLOT, true),
    ] {
        let mutant = finite_arithmetic_coefficients(
            native.terms.as_slice(),
            &r,
            &u,
            &v,
            row_slot,
            left_slot,
            right_slot,
            dummy,
        );
        assert_ne!(mutant, expected);
    }

    let sample = native
        .terms
        .iter()
        .find(|term| term.gate.right == 0)
        .unwrap();
    let br = boolean_point(26, CHILD_SLOT * (1 << 14) + sample.row);
    let bu = boolean_point(32, CHILD_SLOT * SLOT_LEN + IMAGE_START + sample.gate.left);
    let bv = boolean_point(32, CHILD_SLOT * SLOT_LEN + IMAGE_START + sample.gate.right);
    assert_eq!(
        layout.arithmetic_coefficients(&br, &bu, &bv).unwrap(),
        finite_arithmetic_coefficients(
            native.terms.as_slice(),
            &br,
            &bu,
            &bv,
            CHILD_SLOT,
            CHILD_SLOT,
            CHILD_SLOT,
            false
        )
    );

    let alias_r = dense_point(20, 4);
    let alias_u = dense_point(32, 5);
    let alias_v = dense_point(32, 6);
    let alias = layout
        .alias_coefficients(&alias_r, &alias_u, &alias_v)
        .unwrap();
    let expected_terms = expected_alias_terms(&native_producer);
    let expected_alias = finite_alias_coefficients(&expected_terms, &alias_r, &alias_u, &alias_v);
    assert_eq!(alias, expected_alias);
    for (mutate, affected) in [(0usize, 0usize), (1, 64), (2, 1), (3, 0), (4, 0), (5, 160)] {
        let mut mutant = expected_terms.clone();
        match mutate {
            0 => mutant[0].gate.left += SLOT_LEN,
            1 => mutant[64].gate.left = mutant[96].gate.left,
            2 => mutant[1].gate.left = mutant[0].gate.left,
            3 => mutant[0].row += 1 << 8,
            4 => mutant[0].gate.right += SLOT_LEN,
            _ => mutant[160].gate.right += 1,
        }
        let point_r = boolean_point(20, expected_terms[affected].row);
        let point_u = boolean_point(32, expected_terms[affected].gate.left);
        let point_v = boolean_point(32, expected_terms[affected].gate.right);
        assert_ne!(
            finite_alias_coefficients(&mutant, &point_r, &point_u, &point_v),
            finite_alias_coefficients(&expected_terms, &point_r, &point_u, &point_v)
        );
    }
}

#[test]
fn descriptor_binds_history_count_without_changing_native_map_identity() {
    let first = OneDaaLayout::compile(2049, 12).unwrap();
    let repeat = OneDaaLayout::compile(2049, 12).unwrap();
    let next_count = OneDaaLayout::compile(2050, 12).unwrap();
    assert_eq!(first.descriptor(), repeat.descriptor());
    assert_ne!(first.descriptor(), next_count.descriptor());
    assert_eq!(first.mapped_relation(), repeat.mapped_relation());
    assert_eq!(first.mapped_relation(), next_count.mapped_relation());

    let producer = fixture_producer();
    let first_map = first.admit(&producer).unwrap();
    let next_map = next_count.admit(&producer).unwrap();
    assert_eq!(first_map.identity(), next_map.identity());
    assert_eq!(first_map.circuit(), next_map.circuit());

    let challenge = |layout: &OneDaaLayout| {
        let mut transcript = Transcript::new(b"one-daa-descriptor-test-v1");
        layout.bind(&mut transcript);
        transcript.challenge_scalar(b"history-domain")
    };
    assert_eq!(challenge(&first), challenge(&repeat));
    assert_ne!(challenge(&first), challenge(&next_count));
}

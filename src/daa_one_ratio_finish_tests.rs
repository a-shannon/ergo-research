//! Direct native M1 finish checks. These fixtures validate a local arithmetic
//! relation; they do not authenticate historical membership or proof-of-work.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ergo_header_core::Header;
use num_bigint::BigUint;

use crate::{daa_count, daa_finish, daa_integer, daa_one_ratio_finish};

const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");

fn raw_at(height: u32) -> Vec<u8> {
    let value: serde_json::Value = serde_json::from_str(FIXTURE).unwrap();
    value["headers"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["height"].as_u64() == Some(height as u64))
        .map(|entry| {
            let hex = entry["raw_hex"].as_str().unwrap();
            hex.as_bytes()
                .chunks_exact(2)
                .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                .collect()
        })
        .unwrap_or_else(|| panic!("fixture header {height} missing"))
}

fn header_at(height: u32) -> Header {
    Header::decode(&raw_at(height), None).unwrap()
}

fn read_bits(witness: &[Fr], bits: &[usize]) -> BigUint {
    let mut bytes = vec![0u8; bits.len().div_ceil(8)];
    for (index, &wire) in bits.iter().enumerate() {
        assert!(witness[wire].is_zero() || witness[wire] == Fr::one());
        if witness[wire] == Fr::one() {
            bytes[index / 8] |= 1 << (index % 8);
        }
    }
    BigUint::from_bytes_le(&bytes)
}

fn residual_rows(compiled: &daa_integer::Compiled) -> Vec<usize> {
    daa_integer::residuals(compiled)
        .unwrap()
        .iter()
        .enumerate()
        .filter_map(|(row, residual)| (!residual.is_zero()).then_some(row))
        .collect()
}

fn compile_relation(
    input: daa_integer::Inputs,
    child_nbits: u32,
) -> Result<daa_one_ratio_finish::CompiledOne, String> {
    let q = daa_count::q();
    let (arithmetic, output) = daa_integer::compile_extended(
        daa_integer::Epoch::Legacy,
        &q,
        input,
        true,
        |builder, external, a1| {
            daa_one_ratio_finish::append(builder, external, a1, &q, child_nbits)
        },
    )?;
    Ok(daa_one_ratio_finish::CompiledOne { arithmetic, output })
}

fn fallback_value() -> BigUint {
    BigUint::parse_bytes(daa_finish::INITIAL_DIFFICULTY_HEX.as_bytes(), 16).unwrap()
}

fn fallback_compact() -> u32 {
    daa_finish::native_positive_compact_roundtrip(&fallback_value()).0
}

#[test]
fn native_2049_finish_matches_raw_arithmetic_compact_and_count_census() {
    let start = header_at(1_024);
    let end = header_at(2_048);
    let child = header_at(2_049);
    assert_eq!(start.height, 1_024);
    assert_eq!(end.height, 2_048);
    assert_eq!(child.height, 2_049);
    assert_eq!(start.n_bits, 0x0601_1765);
    assert_eq!(end.n_bits, 0x0601_1765);
    assert_eq!(start.timestamp, 1_561_986_131_991);
    assert_eq!(end.timestamp, 1_561_993_105_670);
    let delta = end.timestamp - start.timestamp;
    assert_eq!(delta, 6_973_679);

    let compiled = daa_one_ratio_finish::compile(
        &daa_count::q(),
        daa_integer::Inputs {
            nbits: end.n_bits,
            start_timestamp: start.timestamp,
            end_timestamp: end.timestamp,
        },
        child.n_bits,
        true,
    )
    .unwrap();
    let arithmetic = &compiled.arithmetic;
    let output = &compiled.output;
    assert_eq!(
        read_bits(&arithmetic.witness, &arithmetic.output.decoded_difficulty),
        BigUint::from(1_199_990_374_400u64)
    );
    assert_eq!(
        read_bits(&arithmetic.witness, &arithmetic.output.numerator),
        BigUint::from(147_454_817_206_272_000_000u128)
    );
    assert_eq!(
        read_bits(
            &arithmetic.witness,
            &arithmetic.output.denominator_magnitude
        ),
        BigUint::from(delta as u64)
    );
    let quotient = read_bits(&arithmetic.witness, &arithmetic.output.quotient_magnitude);
    assert_eq!(quotient, BigUint::from(21_144_480_152_624u64));
    assert_eq!(
        read_bits(&arithmetic.witness, &arithmetic.output.remainder_magnitude),
        BigUint::from(1_216_304u64)
    );
    let (compact, rounded) = daa_finish::native_positive_compact_roundtrip(&quotient);
    assert_eq!(compact, 0x0613_3b15);
    assert_eq!(rounded, BigUint::from(21_144_476_319_744u64));
    assert_eq!(child.n_bits, compact);
    assert_eq!(read_bits(&arithmetic.witness, &output.selected), quotient);
    assert_eq!(
        read_bits(&arithmetic.witness, &output.numeric_result),
        rounded
    );
    assert_eq!(
        read_bits(&arithmetic.witness, &output.child_nbits),
        BigUint::from(compact)
    );
    assert!(residual_rows(arithmetic).is_empty());

    assert_eq!(output.timestamp_rows[1], output.timestamp_rows[0] + 1);
    assert_eq!(output.timestamp_rows[2], output.timestamp_rows[1] + 1);
    assert!(output.timestamp_rows[3] > output.timestamp_rows[2]);
    assert!(output.before.rows < output.after_profile.rows);
    assert!(output.after_profile.rows < output.after_fallback.rows);
    assert!(output.after_fallback.rows < output.before_child.rows);
    assert!(output.before_child.rows < output.increment.after.rows);
    let circuit = arithmetic.circuit.as_ref().unwrap();
    assert_eq!(arithmetic.count.padded_rows, circuit.row_count);
    assert!(arithmetic.count.residual_rows <= circuit.row_count);
    assert_eq!(arithmetic.count.terms, circuit.terms.len());
    assert_eq!(arithmetic.count.source_nbits_bits, 64);
    assert_eq!(arithmetic.count.source_timestamp_bits, 128);
    assert_eq!(output.increment.after.live_bits, arithmetic.count.live_bits);
    let count_only = daa_one_ratio_finish::compile(
        &daa_count::q(),
        daa_integer::Inputs {
            nbits: end.n_bits,
            start_timestamp: start.timestamp,
            end_timestamp: end.timestamp,
        },
        child.n_bits,
        false,
    )
    .unwrap();
    assert!(count_only.arithmetic.circuit.is_none());
    assert_eq!(count_only.arithmetic.witness, arithmetic.witness);
    assert_eq!(
        count_only.arithmetic.count.topology_blake2b256,
        arithmetic.count.topology_blake2b256
    );
    assert_eq!(
        count_only.arithmetic.count.live_bits,
        arithmetic.count.live_bits
    );
    assert_eq!(
        count_only.arithmetic.count.padded_input_bits,
        arithmetic.count.padded_input_bits
    );
    assert_eq!(
        count_only.arithmetic.count.residual_rows,
        arithmetic.count.residual_rows
    );
    assert_eq!(
        count_only.arithmetic.count.padded_rows,
        arithmetic.count.padded_rows
    );
    assert_eq!(count_only.arithmetic.count.terms, arithmetic.count.terms);
    println!("M1 COUNT {:?}", arithmetic.count);
    println!(
        "M1 STAGES A1={:?} profile={:?} fallback={:?} compact={:?} child={:?}",
        output.before,
        output.after_profile,
        output.after_fallback,
        output.before_child,
        output.increment.after
    );
    println!(
        "M1 one-bank fit={} capacity=32768 image={} child_start={} timestamp_rows={:?}",
        arithmetic.count.padded_input_bits <= 32768,
        arithmetic.count.padded_input_bits,
        output.child_nbits[0],
        output.timestamp_rows
    );
}

#[test]
fn fallback_quotient_boundary_and_equivalent_child_compacts_are_constrained() {
    let q = daa_count::q();
    let cases = [
        (122_880_001i64, false, fallback_compact()),
        (122_880_000i64, true, 0x0300_0001u32),
    ];
    let mut topology = None;
    for (delta, use_quotient, child_nbits) in cases {
        let compiled = daa_one_ratio_finish::compile(
            &q,
            daa_integer::Inputs {
                nbits: 0x0300_0001,
                start_timestamp: 10,
                end_timestamp: 10 + delta,
            },
            child_nbits,
            true,
        )
        .unwrap();
        let arithmetic = &compiled.arithmetic;
        let output = &compiled.output;
        assert_eq!(
            arithmetic.witness[output.use_quotient],
            Fr::from(use_quotient as u64)
        );
        let selected = read_bits(&arithmetic.witness, &output.selected);
        let expected = if use_quotient {
            BigUint::one()
        } else {
            fallback_value()
        };
        assert_eq!(selected, expected);
        let (_, expected_compact_value) = daa_finish::native_positive_compact_roundtrip(&expected);
        assert_eq!(
            read_bits(&arithmetic.witness, &output.numeric_result),
            expected_compact_value
        );
        assert!(residual_rows(arithmetic).is_empty());
        if let Some(previous) = topology {
            assert_eq!(arithmetic.count.topology_blake2b256, previous);
        }
        topology = Some(arithmetic.count.topology_blake2b256);
    }

    assert_eq!(
        daa_finish::native_positive_compact_roundtrip(&BigUint::one()).0,
        0x0101_0000
    );
    // One canonical encoding and two aliases decode to the same work1.
    for equivalent in [0x0101_0000, 0x0300_0001, 0x0200_0100] {
        let compiled = daa_one_ratio_finish::compile(
            &q,
            daa_integer::Inputs {
                nbits: 0x0300_0001,
                start_timestamp: 0,
                end_timestamp: 122_880_000,
            },
            equivalent,
            true,
        )
        .unwrap();
        assert!(residual_rows(&compiled.arithmetic).is_empty());
    }
    for invalid in [0x0300_0002, 0x0300_0000, 0x0380_0001] {
        let invalid = daa_one_ratio_finish::compile(
            &q,
            daa_integer::Inputs {
                nbits: 0x0300_0001,
                start_timestamp: 0,
                end_timestamp: 122_880_000,
            },
            invalid,
            true,
        )
        .unwrap();
        let failures = residual_rows(&invalid.arithmetic);
        assert!(!failures.is_empty());
        assert!(failures
            .iter()
            .all(|&row| row >= invalid.output.before_child.rows
                && row < invalid.output.increment.after.rows));
        if read_bits(&invalid.arithmetic.witness, &invalid.output.child_nbits)
            == BigUint::from(0x0380_0001u32)
        {
            // Only the child sign assertion changes: exponent/mantissa and work
            // decoder auxiliaries still encode the same positive value1.
            assert_eq!(failures, vec![invalid.output.before_child.rows + 32]);
        }
    }
}

#[test]
fn signed_timestamp_profile_guards_reject_wrap_and_descending_relations() {
    let q = daa_count::q();
    let positive = daa_integer::Inputs {
        nbits: 0x0300_0001,
        start_timestamp: 1,
        end_timestamp: 2,
    };
    assert!(daa_one_ratio_finish::compile(
        &q,
        daa_integer::Inputs {
            start_timestamp: -1,
            end_timestamp: 0,
            ..positive
        },
        fallback_compact(),
        true
    )
    .is_err());
    assert!(daa_one_ratio_finish::compile(
        &q,
        daa_integer::Inputs {
            start_timestamp: i64::MAX,
            end_timestamp: i64::MIN,
            ..positive
        },
        fallback_compact(),
        true
    )
    .is_err());
    assert!(daa_one_ratio_finish::compile(
        &q,
        daa_integer::Inputs {
            start_timestamp: 1,
            end_timestamp: 0,
            ..positive
        },
        fallback_compact(),
        true
    )
    .is_err());
    assert!(daa_one_ratio_finish::compile(
        &q,
        daa_integer::Inputs {
            start_timestamp: 1,
            end_timestamp: 1,
            ..positive
        },
        fallback_compact(),
        true
    )
    .is_err());

    // Bypass compile's host admission and check each committed profile row.
    let wrapped_positive_quotient =
        daa_finish::native_positive_compact_roundtrip(&BigUint::from(122_880_000u64)).0;
    let adversaries = [
        (
            daa_integer::Inputs {
                start_timestamp: i64::MAX,
                end_timestamp: i64::MIN,
                ..positive
            },
            1usize,
            wrapped_positive_quotient,
        ),
        (
            daa_integer::Inputs {
                start_timestamp: -1,
                end_timestamp: 0,
                ..positive
            },
            0usize,
            wrapped_positive_quotient,
        ),
        (
            daa_integer::Inputs {
                start_timestamp: 1,
                end_timestamp: 0,
                ..positive
            },
            2usize,
            fallback_compact(),
        ),
    ];
    for (input, failed_guard, child_nbits) in adversaries {
        let compiled = compile_relation(input, child_nbits).unwrap();
        let expected = compiled.output.timestamp_rows[failed_guard];
        assert_eq!(residual_rows(&compiled.arithmetic), vec![expected]);
    }
    let equal = compile_relation(
        daa_integer::Inputs {
            start_timestamp: 1,
            end_timestamp: 1,
            ..positive
        },
        fallback_compact(),
    )
    .unwrap();
    let failures = residual_rows(&equal.arithmetic);
    assert!(failures.contains(&equal.output.timestamp_rows[3]));
    assert!(failures.iter().any(|&row| row < equal.output.before.rows));
    // Division by zero cannot otherwise satisfy A1; additional failures are
    // confined to that upstream relation, not the valid fallback/child suffix.
    assert!(failures
        .iter()
        .all(|&row| row < equal.output.before.rows || row == equal.output.timestamp_rows[3]));
}

#[test]
fn coordinated_wrong_selector_recomputes_fallback_and_child_auxiliaries() {
    let q = daa_count::q();
    let fallback = daa_one_ratio_finish::compile(
        &q,
        daa_integer::Inputs {
            nbits: 0x0300_0001,
            start_timestamp: 10,
            end_timestamp: 10 + 122_880_001,
        },
        fallback_compact(),
        true,
    )
    .unwrap();
    let quotient = daa_one_ratio_finish::compile(
        &q,
        daa_integer::Inputs {
            nbits: 0x0300_0001,
            start_timestamp: 10,
            end_timestamp: 10 + 122_880_000,
        },
        0x0300_0001,
        true,
    )
    .unwrap();
    let output = &quotient.output;
    let source = &fallback.arithmetic;
    let mut mutant = quotient.arithmetic;
    assert_eq!(
        source.count.topology_blake2b256,
        mutant.count.topology_blake2b256
    );
    assert_eq!(source.witness.len(), mutant.witness.len());
    assert_eq!(output.use_quotient, fallback.output.use_quotient);
    assert_eq!(mutant.witness[output.use_quotient], Fr::one());

    // Copying the complete suffix reselects fallback and carries its freshly
    // computed compact encoding and child-work decoder auxiliaries with it.
    mutant.witness[output.use_quotient..].copy_from_slice(&source.witness[output.use_quotient..]);
    assert_eq!(mutant.witness[output.use_quotient], Fr::zero());
    assert_eq!(
        read_bits(&mutant.witness, &output.selected),
        fallback_value()
    );
    let (_, fallback_numeric) = daa_finish::native_positive_compact_roundtrip(&fallback_value());
    assert_eq!(
        read_bits(&mutant.witness, &output.numeric_result),
        fallback_numeric
    );

    let circuit = mutant.circuit.as_ref().unwrap();
    let selector_relation_rows: Vec<usize> = circuit
        .terms
        .iter()
        .filter(|term| {
            term.gate.left == output.use_quotient
                && term.gate.c1 == Fr::one()
                && term.gate.c3.is_zero()
                && circuit.terms.iter().any(|product| {
                    product.row == term.row
                        && product.gate.c3 == -Fr::one()
                        && product.gate.left != output.use_quotient
                        && product.gate.right != output.use_quotient
                })
        })
        .map(|term| term.row)
        .collect();
    assert_eq!(selector_relation_rows.len(), 1);
    assert_eq!(residual_rows(&mutant), selector_relation_rows);
}

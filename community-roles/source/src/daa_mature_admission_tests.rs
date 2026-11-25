use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ergo_header_core::Header;
use serde::Deserialize;
use std::collections::HashMap;

use crate::{
    daa_finish,
    daa_header_window::{self, SelectedWindow},
    daa_history_layout::DaaHistoryLayout,
    daa_integer::Epoch,
};

const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");

#[derive(Deserialize)]
struct Fixture {
    cases: Vec<FixtureCase>,
    headers: Vec<FixtureHeader>,
}

#[derive(Deserialize)]
struct FixtureCase {
    child: u32,
    parent: u32,
    samples: Vec<u32>,
}

#[derive(Deserialize)]
struct FixtureHeader {
    height: u32,
    raw_hex: String,
}

fn fixture() -> (Fixture, HashMap<u32, Vec<u8>>) {
    let fixture: Fixture = serde_json::from_str(FIXTURE).unwrap();
    let headers = fixture
        .headers
        .iter()
        .map(|header| {
            let bytes = header
                .raw_hex
                .as_bytes()
                .chunks_exact(2)
                .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(Header::decode(&bytes, None).unwrap().height, header.height);
            (header.height, bytes)
        })
        .collect();
    (fixture, headers)
}

fn selected(child: u32, fixture: &Fixture, headers: &HashMap<u32, Vec<u8>>) -> SelectedWindow {
    let case = fixture
        .cases
        .iter()
        .find(|case| case.child == child)
        .unwrap();
    let samples = case
        .samples
        .iter()
        .map(|height| headers.get(height).unwrap().as_slice())
        .collect::<Vec<_>>();
    let samples: [&[u8]; 9] = samples.try_into().unwrap();
    daa_header_window::select_window(
        headers.get(&case.parent).unwrap(),
        headers.get(&child).unwrap(),
        &samples,
    )
    .unwrap()
}

fn layout(epoch: Epoch, history_slots: u64) -> DaaHistoryLayout {
    let slot_log = history_slots.next_power_of_two().trailing_zeros() as usize;
    DaaHistoryLayout::compile(epoch, history_slots, slot_log).unwrap()
}

fn assert_error(
    layout: &DaaHistoryLayout,
    selected: &SelectedWindow,
    compiled: &daa_finish::CompiledFinish,
    expected: &str,
) {
    let error = match layout.admit_selected(selected, compiled) {
        Ok(_) => panic!("admission unexpectedly succeeded; expected {expected}"),
        Err(error) => error,
    };
    assert_eq!(error, expected);
}

#[test]
fn mature_admission_rejects_wrong_epoch_and_truncated_history() {
    let (fixture, headers) = fixture();
    let selected = selected(9_217, &fixture, &headers);
    let compiled = daa_header_window::compile_selected_window(&selected).unwrap();

    let wrong_epoch = layout(Epoch::Eip, 9_217);
    assert_error(
        &wrong_epoch,
        &selected,
        &compiled,
        "mature selected epoch mismatch",
    );

    let truncated = layout(Epoch::Legacy, 9_216);
    assert_error(
        &truncated,
        &selected,
        &compiled,
        "mature selected child outside consumer schedule",
    );
}

#[test]
fn mature_admission_rejects_native_program_shape_and_padding_faults() {
    let (fixture, headers) = fixture();
    let selected = selected(9_217, &fixture, &headers);
    let mut compiled = daa_header_window::compile_selected_window(&selected).unwrap();
    let consumer = layout(Epoch::Legacy, 9_217);

    let circuit = compiled.joined.joined.joined.circuit.take();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature producer circuit was not materialized",
    );
    compiled.joined.joined.joined.circuit = circuit;

    let popped = compiled.joined.joined.joined.witness.pop().unwrap();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature native semantic count or witness shape mismatch",
    );
    compiled.joined.joined.joined.witness.push(popped);

    let old_gate = compiled
        .joined
        .joined
        .joined
        .circuit
        .as_ref()
        .unwrap()
        .terms[0]
        .gate
        .clone();
    compiled
        .joined
        .joined
        .joined
        .circuit
        .as_mut()
        .unwrap()
        .terms[0]
        .gate
        .c0 += Fr::one();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature native circuit differs from consumer template",
    );
    compiled
        .joined
        .joined
        .joined
        .circuit
        .as_mut()
        .unwrap()
        .terms[0]
        .gate = old_gate;

    let padding_wire = compiled.joined.joined.joined.count.live_bits;
    assert!(padding_wire < compiled.joined.joined.joined.witness.len());
    let old_value = compiled.joined.joined.joined.witness[padding_wire];
    compiled.joined.joined.joined.witness[padding_wire] = Fr::one();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature producer native padding is nonzero",
    );
    compiled.joined.joined.joined.witness[padding_wire] = old_value;
}

#[test]
fn mature_admission_rejects_each_semantic_count_checkpoint_and_handle_family() {
    let (fixture, headers) = fixture();
    let selected = selected(9_217, &fixture, &headers);
    let mut compiled = daa_header_window::compile_selected_window(&selected).unwrap();
    let consumer = layout(Epoch::Legacy, 9_217);
    assert!(consumer.admit_selected(&selected, &compiled).is_ok());

    macro_rules! count_fault {
        ($field:ident) => {{
            let value = compiled.joined.joined.joined.count.$field;
            compiled.joined.joined.joined.count.$field = value.wrapping_add(1);
            assert_error(
                &consumer,
                &selected,
                &compiled,
                "mature native semantic count or witness shape mismatch",
            );
            compiled.joined.joined.joined.count.$field = value;
        }};
    }

    count_fault!(live_bits);
    count_fault!(input_bits);
    count_fault!(padded_input_bits);
    count_fault!(residual_rows);
    count_fault!(padded_rows);
    count_fault!(terms);
    count_fault!(boolean_rows);
    count_fault!(linear_rows);
    count_fault!(bilinear_rows);
    count_fault!(maximum_column_signed_abs_bits);
    count_fault!(maximum_degree);
    count_fault!(source_nbits_bits);
    count_fault!(source_timestamp_bits);
    count_fault!(decoded_bits);
    count_fault!(wrapped_delta_bits);
    count_fault!(denominator_bits);
    count_fault!(numerator_bits);
    count_fault!(quotient_bits);
    count_fault!(remainder_bits);
    count_fault!(quotient_sign_bits);
    count_fault!(remainder_sign_bits);
    count_fault!(auxiliary_bits);
    count_fault!(padding_bits);
    count_fault!(peak_row_terms);

    let digest = compiled.joined.joined.joined.count.topology_blake2b256;
    compiled.joined.joined.joined.count.topology_blake2b256[0] ^= 1;
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature native semantic count or witness shape mismatch",
    );
    compiled.joined.joined.joined.count.topology_blake2b256 = digest;

    macro_rules! increment_component_fault {
        ($component:expr) => {{
            let value = $component;
            $component = value.wrapping_add(1);
            assert_error(
                &consumer,
                &selected,
                &compiled,
                "mature native consumed handles or checkpoint mismatch",
            );
            $component = value;
        }};
    }
    macro_rules! increment_ledger_faults {
        ($increment:expr) => {{
            increment_component_fault!($increment.before.live_bits);
            increment_component_fault!($increment.before.rows);
            increment_component_fault!($increment.before.terms);
            increment_component_fault!($increment.after.live_bits);
            increment_component_fault!($increment.after.rows);
            increment_component_fault!($increment.after.terms);
            increment_component_fault!($increment.added_live_bits);
            increment_component_fault!($increment.added_rows);
            increment_component_fault!($increment.added_terms);
        }};
    }
    increment_ledger_faults!(compiled.increment);
    increment_ledger_faults!(compiled.joined.increment);
    increment_ledger_faults!(compiled.joined.joined.increment);

    macro_rules! handle_fault {
        ($handle:expr) => {{
            let value = $handle;
            $handle = value ^ 1;
            assert_error(
                &consumer,
                &selected,
                &compiled,
                "mature native consumed handles or checkpoint mismatch",
            );
            $handle = value;
        }};
    }
    for owner in 0..8 {
        for bit in [0, 31] {
            handle_fault!(compiled.joined.joined.joined.external[owner].nbits[bit]);
        }
        for bit in [0, 63] {
            handle_fault!(compiled.joined.joined.joined.external[owner].start_timestamp[bit]);
            handle_fault!(compiled.joined.joined.joined.external[owner].end_timestamp[bit]);
        }
    }
    for bit in [0, compiled.joined.output.x0_bits.len() - 1] {
        handle_fault!(compiled.joined.output.x0_bits[bit]);
    }
    for bit in [0, compiled.output.numeric_result.len() - 1] {
        handle_fault!(compiled.output.numeric_result[bit]);
    }
    for bit in [0, 31] {
        handle_fault!(compiled.child_nbits.as_mut().unwrap()[bit]);
    }

    let external = compiled.joined.joined.joined.external.pop().unwrap();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature native consumed handles or checkpoint mismatch",
    );
    compiled.joined.joined.joined.external.push(external);

    let x0 = compiled.joined.output.x0_bits.pop().unwrap();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature native consumed handles or checkpoint mismatch",
    );
    compiled.joined.output.x0_bits.push(x0);

    let numeric = compiled.output.numeric_result.pop().unwrap();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature native consumed handles or checkpoint mismatch",
    );
    compiled.output.numeric_result.push(numeric);

    let child_nbits = compiled.child_nbits.take();
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature native consumed handles or checkpoint mismatch",
    );
    compiled.child_nbits = child_nbits;
    assert!(consumer.admit_selected(&selected, &compiled).is_ok());
}

#[test]
fn mature_admission_binds_every_imported_field_to_selected_source() {
    let (fixture, headers) = fixture();
    let selected = selected(9_217, &fixture, &headers);
    let mut compiled = daa_header_window::compile_selected_window(&selected).unwrap();
    let consumer = layout(Epoch::Legacy, 9_217);

    let mut imported_wires = std::collections::BTreeSet::new();
    for external in &compiled.joined.joined.joined.external {
        for bit in [0, 31] {
            imported_wires.insert(external.nbits[bit]);
        }
        for bit in [0, 63] {
            imported_wires.insert(external.start_timestamp[bit]);
            imported_wires.insert(external.end_timestamp[bit]);
        }
    }
    for bit in [0, compiled.joined.output.x0_bits.len() - 1] {
        imported_wires.insert(compiled.joined.output.x0_bits[bit]);
    }
    for bit in [0, 31] {
        imported_wires.insert(compiled.child_nbits.as_ref().unwrap()[bit]);
    }

    assert!(consumer.admit_selected(&selected, &compiled).is_ok());

    let first = *imported_wires.first().unwrap();
    let original = compiled.joined.joined.joined.witness[first];
    compiled.joined.joined.joined.witness[first] = Fr::one() - original;
    assert_error(
        &consumer,
        &selected,
        &compiled,
        "mature selected source bit assignment mismatch",
    );
    compiled.joined.joined.joined.witness[first] = original;

    for &wire in &imported_wires {
        let original = compiled.joined.joined.joined.witness[wire];
        compiled.joined.joined.joined.witness[wire] = Fr::one() - original;
        assert_error(
            &consumer,
            &selected,
            &compiled,
            "mature selected source bit assignment mismatch",
        );
        compiled.joined.joined.joined.witness[wire] = original;
    }

    for wire in imported_wires {
        let original = compiled.joined.joined.joined.witness[wire];
        compiled.joined.joined.joined.witness[wire] = Fr::from(2u64);
        assert_error(
            &consumer,
            &selected,
            &compiled,
            "mature selected source bit assignment mismatch",
        );
        compiled.joined.joined.joined.witness[wire] = original;
    }
    assert!(consumer.admit_selected(&selected, &compiled).is_ok());
}

#[test]
fn mature_admission_is_structural_and_native_residuals_remain_separate() {
    let (fixture, headers) = fixture();
    let selected = selected(9_217, &fixture, &headers);
    let mut compiled = daa_header_window::compile_selected_window(&selected).unwrap();
    let consumer = layout(Epoch::Legacy, 9_217);

    let selector = compiled.output.use_prediction;
    let original = compiled.joined.joined.joined.witness[selector];
    compiled.joined.joined.joined.witness[selector] = if original.is_zero() {
        Fr::one()
    } else {
        Fr::zero()
    };

    assert!(consumer.admit_selected(&selected, &compiled).is_ok());
    let residuals = daa_finish::finish_residuals(&compiled).unwrap();
    assert!(residuals.iter().any(|residual| !residual.is_zero()));
}

//! Selected M2 common-owner fixture checks. These checks establish the local
//! relation for the four selected headers; sample predecessor metadata is
//! diagnostic and does not authenticate ancestry.

use ark_bn254::Fr;
use ark_ff::Zero;

use crate::{
    daa_count, daa_finish, daa_history_layout,
    daa_integer::TwoRatioInputs,
    daa_two_ratio_join, header_compact_links, serializer,
    short_common_owner::{Plan, COPY_BITS, LOCAL_BITS, LOGICAL_SLOTS, ROW_BITS},
    sparse_stream_roster::{self, EdgeTerm},
};

const WIDTH: usize = 1 << LOCAL_BITS;
const LOCAL_MASK: usize = WIDTH - 1;
const TERMS: usize = 2_123_291;
const FAMILY_ROW_BITS: usize = 19;
const MEMBER_ROW_BITS: [usize; 3] = [19, 17, 10];

/// Materialize four physical copies of the actual fixture headers. The first
/// three have no predecessor headers in this roster, so their order metadata
/// is intentionally diagnostic only. The child uses sample 3072's timestamp.
pub(crate) fn materialize(plan: &Plan, changed_sample: bool) -> Vec<Vec<Fr>> {
    assert_eq!(LOGICAL_SLOTS, [1023, 2047, 3071, 3072]);
    let raws = daa_two_ratio_join::fixture_raws();
    let headers = raws
        .iter()
        .map(|raw| ergo_header_core::Header::decode(raw, None).unwrap())
        .collect::<Vec<_>>();
    let mut fields = headers
        .iter()
        .map(serializer::Fields::from_header)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    if changed_sample {
        fields[0].timestamp ^= 1;
    }

    // Keep child arithmetic tied to the original code-owned fixture bytes,
    // including for the changed-sample alias mutant.
    let compiled = daa_finish::compile_two_finish_with_child(
        &daa_count::q(),
        TwoRatioInputs {
            nbits: [headers[1].n_bits, headers[2].n_bits],
            timestamps: [
                headers[0].timestamp,
                headers[1].timestamp,
                headers[2].timestamp,
            ],
        },
        headers[3].n_bits,
        true,
    )
    .unwrap();
    let mapped = plan.header().short_layout().admit(&compiled).unwrap();

    let mut copies = Vec::with_capacity(1 << COPY_BITS);
    for copy in 0..(1 << COPY_BITS) {
        let mut boundary = daa_history_layout::full_header_boundary(Some(&fields[copy])).unwrap();
        let (previous_height, previous_time) = if copy == 3 {
            (3072, headers[2].timestamp)
        } else {
            // No preceding header for these selected samples is present here.
            ((fields[copy].height - 1), 0)
        };
        header_compact_links::assign_order(
            &mut boundary,
            &fields[copy],
            previous_height,
            previous_time,
            false,
        )
        .unwrap();
        let mut input = boundary.base.base.base.input.take().unwrap();
        if copy == 3 {
            for (start, end) in mapped.phase_bank_ranges() {
                input[start..end].copy_from_slice(&mapped.witness()[start..end]);
            }
        }
        assert_eq!(input.len(), WIDTH);
        copies.push(input);
    }
    copies
}

fn gate_value(edge: &EdgeTerm, copies: &[Vec<Fr>]) -> Fr {
    let left_wire = edge.term.gate.left;
    let right_wire = edge.term.gate.right;
    let left = copies[left_wire >> LOCAL_BITS][left_wire & LOCAL_MASK];
    let right = copies[right_wire >> LOCAL_BITS][right_wire & LOCAL_MASK];
    let gate = &edge.term.gate;
    gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right
}

fn global_row(edge: &EdgeTerm) -> usize {
    sparse_stream_roster::global_edge_row(
        edge.source_slot,
        edge.family_row,
        COPY_BITS,
        FAMILY_ROW_BITS,
        2,
        &MEMBER_ROW_BITS,
    )
    .unwrap()
}

fn relation_residuals(plan: &Plan, copies: &[Vec<Fr>]) -> (Vec<Fr>, usize, usize) {
    let mut residuals = vec![Fr::zero(); 1 << ROW_BITS];
    let mut left_count = 0usize;
    let mut right_count = 0usize;
    for copy in 0..(1 << COPY_BITS) {
        plan.visit_endpoint(true, copy, |edge| {
            let row = global_row(&edge);
            residuals[row] += gate_value(&edge, copies);
            left_count += 1;
            Ok(())
        })
        .unwrap();
        plan.visit_endpoint(false, copy, |edge| {
            let _ = global_row(&edge);
            right_count += 1;
            Ok(())
        })
        .unwrap();
    }
    (residuals, left_count, right_count)
}

#[test]
fn original_selected_m2_roster_satisfies_every_emitted_relation() {
    let plan = Plan::new().unwrap();
    let copies = materialize(&plan, false);
    let (mut residuals, left_count, right_count) = relation_residuals(&plan, &copies);

    assert_eq!(left_count, TERMS);
    assert_eq!(right_count, TERMS);
    assert!(
        residuals.iter().all(Zero::is_zero),
        "all emitted header, arithmetic, and alias rows must vanish"
    );

    let anchor = plan
        .header()
        .base()
        .canonical_circuit()
        .terms
        .iter()
        .find(|term| (348_440..356_632).contains(&term.row) && !copies[3][term.gate.left].is_zero())
        .expect("actual child M2 assignment has a nonzero released A4 anchor");
    assert_eq!(anchor.gate.evaluate(&copies[3]), Fr::from(1u64));
    let anchor_row = global_row(&EdgeTerm {
        source_slot: 3,
        family_row: anchor.row,
        term: anchor.clone(),
    });
    assert!(residuals[anchor_row].is_zero());
    residuals[anchor_row] += anchor.gate.evaluate(&copies[3]);
    let reinserted_rows = residuals
        .iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect::<Vec<_>>();
    assert_eq!(reinserted_rows, vec![anchor_row]);
}

#[test]
fn one_sample_timestamp_bit_fault_isolated_to_one_alias_row() {
    let plan = Plan::new().unwrap();
    let copies = materialize(&plan, true);
    let (residuals, left_count, right_count) = relation_residuals(&plan, &copies);

    assert_eq!(left_count, TERMS);
    assert_eq!(right_count, TERMS);
    let bad_rows = residuals
        .iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect::<Vec<_>>();
    assert_eq!(bad_rows, vec![(2 << 21) | (3 << 10)]);
    assert!(residuals
        .iter()
        .enumerate()
        .filter(|(row, _)| (*row >> (FAMILY_ROW_BITS + COPY_BITS)) < 2)
        .all(|(_, value)| value.is_zero()));
}

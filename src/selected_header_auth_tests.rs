//! Direct checks for the fixed four-role selected-header authentication map.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};

use crate::{
    daa_history_layout, daa_two_ratio_join, header_compact_links, point_membership, segment_points,
    segment_relation, selected_header_auth::Plan, short_common_owner,
    short_common_owner::LOGICAL_SLOTS, short_common_owner_fixture_tests, sparse::Circuit,
    sparse_stream_roster, work_tree_layout,
};

const WIDTH: usize = 1 << 20;

/// Derive the public statement directly from the code-owned RAW fixtures.
/// Production verification still receives these IDs from its caller.
pub(crate) fn expected_ids() -> [[u8; 32]; 4] {
    daa_two_ratio_join::fixture_raws().map(|raw| {
        let digest = Blake2b::<U32>::digest(raw);
        let mut id = [0u8; 32];
        id.copy_from_slice(&digest);
        id
    })
}

fn finite_core_expansion(core: &Circuit, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let row_weights = crate::gkr::eq_weights(r);
    let left_weights = crate::gkr::eq_weights(u);
    let right_weights = crate::gkr::eq_weights(v);
    let mut out = [Fr::zero(); 4];
    for copy in 0..4 {
        for bank in 0..8 {
            for term in &core.terms {
                let row = term.row + copy * (1 << 17) + bank * (1 << 19);
                let left = copy * WIDTH + bank * work_tree_layout::CORE + term.gate.left;
                let right = copy * WIDTH + bank * work_tree_layout::CORE + term.gate.right;
                let weight = row_weights[row] * left_weights[left] * right_weights[right];
                out[0] += weight * term.gate.c0;
                out[1] += weight * term.gate.c1;
                out[2] += weight * term.gate.c2;
                out[3] += weight * term.gate.c3;
            }
        }
    }
    out
}

fn finite_sparse_coefficients(circuit: &Circuit, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let row_weights = crate::gkr::eq_weights(r);
    let left_weights = crate::gkr::eq_weights(u);
    let right_weights = crate::gkr::eq_weights(v);
    let mut out = [Fr::zero(); 4];
    for term in &circuit.terms {
        let weight =
            row_weights[term.row] * left_weights[term.gate.left] * right_weights[term.gate.right];
        out[0] += weight * term.gate.c0;
        out[1] += weight * term.gate.c1;
        out[2] += weight * term.gate.c2;
        out[3] += weight * term.gate.c3;
    }
    out
}

fn point_residuals(circuit: &Circuit, witness: &[bool]) -> Vec<Fr> {
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        let left = Fr::from(witness[term.gate.left] as u64);
        let right = Fr::from(witness[term.gate.right] as u64);
        rows[term.row] +=
            term.gate.c0 + term.gate.c1 * left + term.gate.c2 * right + term.gate.c3 * left * right;
    }
    rows
}

fn id_residuals(circuit: &Circuit, copies: &[Vec<Fr>], mutate: Option<usize>) -> Vec<Fr> {
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for (index, term) in circuit.terms.iter().enumerate() {
        let copy = term.gate.left / WIDTH;
        let wire = term.gate.left % WIDTH;
        let bit = copies[copy][wire];
        let c0 = if mutate == Some(index) {
            term.gate.c0 + if bit.is_one() { Fr::one() } else { -Fr::one() }
        } else {
            term.gate.c0
        };
        rows[term.row] += c0 + term.gate.c1 * bit;
    }
    rows
}

fn core_residual_rows(circuit: &Circuit, assignment: &[Fr]) -> Vec<usize> {
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        rows[term.row] += term.gate.evaluate(assignment);
    }
    nonzero_rows(&rows)
}

fn common_residual_rows(plan: &short_common_owner::Plan, copies: &[Vec<Fr>]) -> Vec<usize> {
    let mut residuals = vec![Fr::zero(); 1 << short_common_owner::ROW_BITS];
    for copy in 0..4 {
        plan.visit_endpoint(true, copy, |edge| {
            let row = sparse_stream_roster::global_edge_row(
                edge.source_slot,
                edge.family_row,
                2,
                19,
                2,
                &[19, 17, 10],
            )
            .unwrap();
            let value = |wire: usize| copies[wire / WIDTH][wire % WIDTH];
            let gate = &edge.term.gate;
            residuals[row] += gate.c0
                + gate.c1 * value(gate.left)
                + gate.c2 * value(gate.right)
                + gate.c3 * value(gate.left) * value(gate.right);
            Ok(())
        })
        .unwrap();
    }
    nonzero_rows(&residuals)
}

fn serializer_bytes(fields: &crate::serializer::Fields) -> Vec<u8> {
    let serializer = crate::serializer::build(None).unwrap();
    let assignment = serializer.assign(fields);
    let length = serializer
        .layout
        .length
        .iter()
        .enumerate()
        .filter(|(_, wire)| assignment[**wire].is_one())
        .map(|(bit, _)| 1usize << bit)
        .sum::<usize>();
    (0..length)
        .map(|byte| {
            serializer.layout.bytes[byte]
                .iter()
                .enumerate()
                .fold(0u8, |value, (bit, wire)| {
                    value | ((assignment[*wire].is_one() as u8) << bit)
                })
        })
        .collect()
}

fn replace_first_copy_with_fields(
    original: &mut [Vec<Fr>],
    fields: &crate::serializer::Fields,
) -> Vec<Vec<Fr>> {
    let mut boundary = daa_history_layout::full_header_boundary(Some(fields)).unwrap();
    header_compact_links::assign_order(
        &mut boundary,
        fields,
        fields.height.saturating_sub(1),
        0,
        false,
    )
    .unwrap();
    let input = boundary.base.base.base.input.take().unwrap();
    assert_eq!(input.len(), WIDTH);
    original[0] = input;
    original.to_vec()
}

fn nonzero_rows(rows: &[Fr]) -> Vec<usize> {
    rows.iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect()
}

#[test]
fn core_wiring_matches_independent_eight_bank_four_copy_expansion() {
    let plan = Plan::new(expected_ids()).unwrap();
    let point = |salt: usize| {
        (0..22)
            .map(|i| Fr::from((salt + 3 * i + 1) as u64) / Fr::from((i + 2) as u64))
            .collect::<Vec<_>>()
    };
    let (r, u, v) = (point(7), point(19), point(41));
    assert_eq!(
        plan.core_coefficients(&r, &u, &v).unwrap(),
        finite_core_expansion(plan.core(), &r, &u, &v),
        "all four coefficient channels must include every bank and physical copy"
    );

    // The wire-side bank map has four bits, but only banks 0..7 are active.
    let mut padded_bank = vec![Fr::zero(); 22];
    padded_bank[16] = Fr::zero();
    padded_bank[17] = Fr::zero();
    padded_bank[18] = Fr::zero();
    padded_bank[19] = Fr::one(); // bank 8
    padded_bank[20] = Fr::zero();
    padded_bank[21] = Fr::zero();
    let mut family_zero = vec![Fr::zero(); 22];
    let mut copy_zero = vec![Fr::zero(); 22];
    assert_eq!(
        plan.core_coefficients(&family_zero, &padded_bank, &copy_zero)
            .unwrap(),
        [Fr::zero(); 4]
    );

    // An endpoint assigned to a different physical copy cannot select a term.
    let mut left_copy_one = vec![Fr::zero(); 22];
    left_copy_one[20] = Fr::one();
    assert_eq!(
        plan.core_coefficients(&family_zero, &left_copy_one, &copy_zero)
            .unwrap(),
        [Fr::zero(); 4]
    );
    for lengths in [(21, 22, 22), (22, 21, 22), (22, 22, 21)] {
        let args = (
            vec![Fr::zero(); lengths.0],
            vec![Fr::zero(); lengths.1],
            vec![Fr::zero(); lengths.2],
        );
        assert!(plan.core_coefficients(&args.0, &args.1, &args.2).is_err());
    }
}

#[test]
fn actual_core_fixture_passes_and_private_internal_bit_fails_core_rows_only() {
    let plan = Plan::new(expected_ids()).unwrap();
    let copies = short_common_owner_fixture_tests::materialize(plan.common(), false);
    let core = plan.core();
    let mut exported = std::collections::HashSet::new();
    let logical_base = LOGICAL_SLOTS[0] * WIDTH;
    plan.common()
        .header()
        .visit_slot_terms(LOGICAL_SLOTS[0] as u64, |term| {
            for wire in [term.gate.left, term.gate.right] {
                if let Some(local) = wire
                    .checked_sub(logical_base)
                    .filter(|local| *local < WIDTH)
                {
                    exported.insert(local);
                }
            }
            Ok(())
        })
        .unwrap();
    assert!(
        !exported.is_empty(),
        "selected slot must expose boundary handles"
    );

    for bank in 0..8 {
        let base = bank * work_tree_layout::CORE;
        assert!(
            core_residual_rows(core, &copies[0][base..base + work_tree_layout::CORE]).is_empty(),
            "actual fixture core bank {bank} must satisfy its own rows"
        );
    }

    let internal_wire = core
        .terms
        .iter()
        .flat_map(|term| {
            [
                (
                    term.gate.left,
                    !term.gate.c1.is_zero() || !term.gate.c3.is_zero(),
                ),
                (
                    term.gate.right,
                    !term.gate.c2.is_zero() || !term.gate.c3.is_zero(),
                ),
            ]
        })
        .filter_map(|(wire, active)| active.then_some(wire))
        .find(|wire| *wire < work_tree_layout::CORE && !exported.contains(wire))
        .expect("canonical compression has a private internal witness bit");
    let mut changed = copies[0][..work_tree_layout::CORE].to_vec();
    changed[internal_wire] = if changed[internal_wire].is_zero() {
        Fr::one()
    } else {
        Fr::zero()
    };
    assert!(
        !core_residual_rows(core, &changed).is_empty(),
        "private core witness mutation must fail the core relation"
    );
    let mut changed_copies = copies.clone();
    changed_copies[0][internal_wire] = changed[internal_wire];
    assert!(common_residual_rows(plan.common(), &changed_copies).is_empty());
}

#[test]
fn id_relation_matches_actual_fixture_and_each_expected_bit_owns_one_row() {
    let ids = expected_ids();
    let plan = Plan::new(ids).unwrap();
    let circuit = plan.ids();
    assert_eq!(
        (circuit.input_len, circuit.row_count, circuit.terms.len()),
        (1 << 22, 2048, 1152)
    );
    for (copy, id) in ids.iter().enumerate() {
        for bit in 0..256 {
            let term = &circuit.terms[256 * copy + bit];
            assert_eq!(term.row, 256 * copy + bit);
            assert_eq!(
                term.gate.left,
                WIDTH * copy + segment_relation::DIGEST_OFFSET + bit
            );
            assert_eq!(term.gate.right, 0);
            assert_eq!(
                term.gate.c0,
                -Fr::from(((id[bit / 8] >> (bit % 8)) & 1) as u64)
            );
            assert_eq!(term.gate.c1, Fr::one());
            assert!(term.gate.c2.is_zero() && term.gate.c3.is_zero());
        }
    }

    let copies = short_common_owner_fixture_tests::materialize(plan.common(), false);
    assert!(nonzero_rows(&id_residuals(circuit, &copies, None)).is_empty());
    for (index, term) in circuit.terms[..1024].iter().enumerate() {
        assert_eq!(
            nonzero_rows(&id_residuals(circuit, &copies, Some(index))),
            vec![term.row],
            "changing caller expected ID bit at row {} must fail only that row",
            term.row
        );
    }

    let heights = crate::header_height_layout::HeaderHeightLayout::compile(3073, 12).unwrap();
    for (copy, logical) in LOGICAL_SLOTS.iter().enumerate() {
        let mut emitted = Vec::new();
        assert_eq!(
            heights
                .visit_slot_terms(*logical as u64, |term| {
                    emitted.push(term);
                    Ok(())
                })
                .unwrap(),
            32
        );
        for bit in 0..32 {
            let term = &circuit.terms[1024 + copy * 32 + bit];
            assert_eq!(term.row, 1024 + copy * 32 + bit);
            assert_eq!(
                term.gate.left,
                copy * WIDTH + heights.height_wire(bit).unwrap()
            );
            assert_eq!(term.gate.right, copy * WIDTH);
            assert_eq!(term.gate.c0, -Fr::from(((*logical as u64 + 1) >> bit) & 1));
            assert_eq!(term.gate.c1, Fr::one());
            assert!(term.gate.c2.is_zero() && term.gate.c3.is_zero());
        }
        assert_eq!(emitted.len(), 32);
    }

    let point = |salt: usize, length: usize| {
        (0..length)
            .map(|i| Fr::from((salt + 7 * i + 1) as u64) / Fr::from((i + 3) as u64))
            .collect::<Vec<_>>()
    };
    let (r, u, v) = (point(5, 11), point(13, 22), point(29, 22));
    let shape = crate::sparse::validate(circuit, 0).unwrap();
    let expected = finite_sparse_coefficients(circuit, &r, &u, &v);
    assert_eq!(
        crate::sparse::wiring(circuit, &shape, &r, &u, &v).unwrap(),
        expected
    );
    let mut wrong_right = circuit.clone();
    for term in &mut wrong_right.terms[1024..] {
        term.gate.right = 0;
    }
    assert_ne!(
        crate::sparse::wiring(&wrong_right, &shape, &r, &u, &v).unwrap(),
        expected,
        "height terms must retain their copy-local global-zero selector"
    );
}

#[test]
fn changing_one_valid_fixture_height_fails_only_its_height_bit_row() {
    let raws = daa_two_ratio_join::fixture_raws();
    let headers = raws
        .iter()
        .map(|raw| ergo_header_core::Header::decode(raw, None).unwrap())
        .collect::<Vec<_>>();
    let mut fields = headers
        .iter()
        .map(crate::serializer::Fields::from_header)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    fields[0].height += 1;
    let changed_raw = serializer_bytes(&fields[0]);
    let changed_header = ergo_header_core::Header::decode(&changed_raw, None).unwrap();
    let changed_id = changed_header.id().unwrap();
    let mut ids = expected_ids();
    ids[0] = changed_id;

    let plan = Plan::new(ids).unwrap();
    let mut copies = short_common_owner_fixture_tests::materialize(plan.common(), false);
    let copies = replace_first_copy_with_fields(&mut copies, &fields[0]);
    assert!(common_residual_rows(plan.common(), &copies).is_empty());
    for bank in 0..8 {
        let base = bank * work_tree_layout::CORE;
        assert!(
            core_residual_rows(plan.core(), &copies[0][base..base + work_tree_layout::CORE])
                .is_empty()
        );
    }
    let point_witness = point_membership::witness(fields[0].pk, fields[0].w).unwrap();
    assert!(point_residuals(&plan.points().circuit, &point_witness)
        .iter()
        .all(Zero::is_zero));
    let id_rows = id_residuals(plan.ids(), &copies, None);
    assert!(id_rows[..1024].iter().all(Zero::is_zero));
    assert_eq!(nonzero_rows(&id_rows), vec![1024]);
}

#[test]
fn actual_point_witness_passes_and_an_internal_y_bit_fails_point_rows() {
    let plan = Plan::new(expected_ids()).unwrap();
    let raws = daa_two_ratio_join::fixture_raws();
    let headers = raws
        .iter()
        .map(|raw| ergo_header_core::Header::decode(raw, None).unwrap())
        .collect::<Vec<_>>();
    let fields = headers
        .iter()
        .map(crate::serializer::Fields::from_header)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    for header_fields in &fields {
        let mut witness = point_membership::witness(header_fields.pk, header_fields.w).unwrap();
        let rows = point_residuals(&plan.points().circuit, &witness);
        assert!(
            nonzero_rows(&rows).is_empty(),
            "fixture point relation must satisfy every row"
        );

        // The ordinate is a private arithmetic witness, separate from encoded bytes.
        let y_wire = plan.points().layout.points[0].y[0];
        witness[y_wire] = !witness[y_wire];
        assert!(
            !nonzero_rows(&point_residuals(&plan.points().circuit, &witness)).is_empty(),
            "an internal y witness mutation must fail the point circuit"
        );

        let mut joined = segment_points::build(Some(header_fields)).unwrap();
        let boundary = &joined.base.boundary;
        let input = joined.base.input.as_mut().unwrap();
        assert!(core_residual_rows(boundary, input).is_empty());
        let aliased_y = segment_points::POINT_OFFSET + y_wire;
        assert!(!boundary.terms.iter().any(|term| {
            (term.gate.left == aliased_y && (!term.gate.c1.is_zero() || !term.gate.c3.is_zero()))
                || (term.gate.right == aliased_y
                    && (!term.gate.c2.is_zero() || !term.gate.c3.is_zero()))
        }));
        input[aliased_y] = if input[aliased_y].is_zero() {
            Fr::one()
        } else {
            Fr::zero()
        };
        assert!(
            core_residual_rows(boundary, input).is_empty(),
            "private y mutation must leave the serialized-byte boundary valid"
        );
    }
    assert_eq!(segment_points::POINT_OFFSET, 786_432);
}

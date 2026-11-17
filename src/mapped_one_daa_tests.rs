use super::*;
use crate::{daa_count, daa_integer::Inputs, daa_one_ratio_finish, gkr::Gate};
use ark_ff::One;

fn native() -> CompiledOne {
    // Exact fields separately checked against pinned RAW1024/2048/2049 by
    // the native finish gate. This oracle fixes their numeric values directly.
    daa_one_ratio_finish::compile(
        &daa_count::q(),
        Inputs {
            nbits: 0x0601_1765,
            start_timestamp: 1_561_986_131_991,
            end_timestamp: 1_561_993_105_670,
        },
        0x0613_3b15,
        true,
    )
    .unwrap()
}
fn bad_rows(circuit: &Circuit, witness: &[Fr]) -> Vec<usize> {
    let mut residuals = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        residuals[term.row] += term.gate.evaluate(witness);
    }
    residuals
        .iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect()
}

#[test]
fn complete_native_image_terms_witness_padding_and_residuals_match() {
    let c = native();
    let m = MappedM1::compile(&c).unwrap();
    let old = c.arithmetic.circuit.as_ref().unwrap();
    assert_eq!(m.circuit().input_len, 1 << 20);
    assert_eq!(m.circuit().row_count, 16384);
    assert_eq!(m.circuit().terms.len(), old.terms.len());
    assert_eq!(old.terms.len(), 44729);
    let mut destinations = std::collections::BTreeSet::new();
    for index in 0..8192 {
        let expected = 819200 + index;
        assert_eq!(m.mapped_wire(index).unwrap(), expected);
        assert!(destinations.insert(expected));
        assert_eq!(m.witness()[expected], c.arithmetic.witness[index]);
    }
    assert_eq!(destinations.len(), 8192);
    for (original, mapped) in old.terms.iter().zip(&m.circuit().terms) {
        assert_eq!(mapped.row, original.row);
        assert_eq!(mapped.gate.left, 819200 + original.gate.left);
        assert_eq!(mapped.gate.right, 819200 + original.gate.right);
        assert_eq!(
            [
                mapped.gate.c0,
                mapped.gate.c1,
                mapped.gate.c2,
                mapped.gate.c3
            ],
            [
                original.gate.c0,
                original.gate.c1,
                original.gate.c2,
                original.gate.c3
            ]
        );
    }
    assert!(m.mapped_wire(8192).is_err());
    assert!(m.mapped_wire(usize::MAX).is_err());
    assert_eq!(bad_rows(old, &c.arithmetic.witness), Vec::<usize>::new());
    assert_eq!(bad_rows(m.circuit(), m.witness()), Vec::<usize>::new());
    // Original wire0 is a real nBits bit (1 here), not a global zero cell.
    assert_eq!(c.arithmetic.witness[0], Fr::one());
    assert_eq!(m.witness()[819200], Fr::one());
    assert!(old
        .terms
        .iter()
        .any(|t| t.gate.right == 0 && !t.gate.c1.is_zero()));
    for offset in 6414..8192 {
        assert!(m.witness()[819200 + offset].is_zero());
        let padding = &m.circuit().terms[42951 + offset - 6414];
        assert_eq!(padding.row, 10776 + offset - 6414);
        assert_eq!(
            (padding.gate.left, padding.gate.right),
            (819200 + offset, 819200)
        );
        assert_eq!(
            [
                padding.gate.c0,
                padding.gate.c1,
                padding.gate.c2,
                padding.gate.c3
            ],
            [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]
        );
    }
    let second = MappedM1::compile(&c).unwrap();
    assert_eq!(m.identity(), second.identity());
    println!("M1 exact image PASS8192 cells,44729 ordered terms,1778 native padding; no reserved outside-image slack or header release");
}

#[test]
fn mapper_geometry_source_coordinates_and_padding_fail_separately() {
    let mut c = native();
    macro_rules! count_fault {
        ($field:ident) => {{
            let old = c.arithmetic.count.$field;
            c.arithmetic.count.$field = old + 1;
            assert_eq!(
                MappedM1::compile(&c).err().as_deref(),
                Some("M1 source geometry mismatch")
            );
            c.arithmetic.count.$field = old;
        }};
    }
    count_fault!(live_bits);
    count_fault!(input_bits);
    count_fault!(padded_input_bits);
    count_fault!(padding_bits);
    count_fault!(residual_rows);
    count_fault!(padded_rows);
    count_fault!(terms);
    let old = c.arithmetic.circuit.take().unwrap();
    assert_eq!(
        MappedM1::compile(&c).err().as_deref(),
        Some("M1 source not materialized")
    );
    c.arithmetic.circuit = Some(old);
    for field in 0..5 {
        let old = c.arithmetic.circuit.as_ref().unwrap().clone();
        let circuit = c.arithmetic.circuit.as_mut().unwrap();
        match field {
            0 => circuit.input_len += 1,
            1 => circuit.row_count += 1,
            2 => circuit.terms[0].row = 12554,
            3 => circuit.terms[0].gate.left = 8192,
            _ => circuit.terms[0].gate.right = 8192,
        }
        let expected = if field < 2 {
            "M1 source geometry mismatch"
        } else {
            "M1 source term escapes owned domain"
        };
        assert_eq!(MappedM1::compile(&c).err().as_deref(), Some(expected));
        c.arithmetic.circuit = Some(old);
    }
    let last = c.arithmetic.witness.pop().unwrap();
    assert_eq!(
        MappedM1::compile(&c).err().as_deref(),
        Some("M1 source geometry mismatch")
    );
    c.arithmetic.witness.push(last);
    c.arithmetic.witness[6414] = Fr::one();
    assert_eq!(
        MappedM1::compile(&c).err().as_deref(),
        Some("M1 source padding is nonzero")
    );
    c.arithmetic.witness[6414] = Fr::zero();
    assert!(MappedM1::compile(&c).is_ok());
}

#[test]
fn image_freedom_checks_both_header_endpoints_and_half_open_boundaries() {
    assert!(require_free_image(&[(819200, 827392)]).is_ok());
    for free in [
        vec![],
        vec![(819201, 827392)],
        vec![(819200, 827391)],
        vec![(0, 819200)],
    ] {
        assert_eq!(
            require_free_image(&free).err().as_deref(),
            Some("M1 image is not in frozen free inventory")
        );
    }
    // Test the ownership predicate directly so a fingerprint rejection cannot
    // mask a missed endpoint. The production caller also pins the canonical program.
    let term = |left, right| Term {
        row: 0,
        gate: Gate {
            left,
            right,
            c0: Fr::one(),
            c1: Fr::zero(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    };
    assert!(require_no_header_use(&[term(819199, 827392)]).is_ok());
    for wire in [819200, 827391] {
        assert_eq!(
            require_no_header_use(&[term(wire, 0)]).err().as_deref(),
            Some("M1 image conflicts with canonical header ownership")
        );
        assert_eq!(
            require_no_header_use(&[term(0, wire)]).err().as_deref(),
            Some("M1 image conflicts with canonical header ownership")
        );
    }
    assert!(check_image_ownership().is_ok());
}

#[test]
fn structural_mapping_does_not_claim_native_residual_validity() {
    let mut c = native();
    c.arithmetic.witness[c.output.use_quotient] = Fr::zero();
    let m = MappedM1::compile(&c).unwrap();
    assert!(!bad_rows(m.circuit(), m.witness()).is_empty());
}

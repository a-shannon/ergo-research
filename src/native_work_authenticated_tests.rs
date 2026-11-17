use super::*;

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use num_bigint::BigUint;
use std::collections::BTreeMap;

use crate::{
    gkr::{self, GkrError, InputClaim},
    native_work_relation::NativeWorkRelation,
    pcs::{self, Committed, Setup},
    sparse::{self, Circuit, Term},
    transcript::Transcript,
    verifier_key::{self, AdmittedVerifierKey},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self, Endpoints, WIDTH},
    work_tree_work,
};

const INPUT_LOG: usize = 22;
const INPUT_LEN: usize = 1usize << INPUT_LOG;
const OUTPUT_LOG: usize = 18;
const ROW_COUNT: usize = 1usize << OUTPUT_LOG;
const SLOT_LOG: usize = 2;
const LOCAL_ROW_LOG: usize = 13 + SLOT_LOG;
const TAG_SHIFT: usize = LOCAL_ROW_LOG;
const TAG_STRIDE: usize = 1usize << TAG_SHIFT;
const EXPECTED_TERMS: usize = 25_522;
const EXPECTED_BY_TAG: [usize; 6] = [1_121, 10_947, 224, 448, 224, 12_558];
const ROOT: [u8; 32] = [7; 32];
const COMPACT_NBITS: u32 = 0x0601_1765;
const ENVELOPE_BYTES: usize = 514;

fn total_be28(value: &BigUint) -> [u8; 28] {
    let bytes = value.to_bytes_be();
    assert!(bytes.len() <= 28, "test total must fit U224");
    let mut encoded = [0u8; 28];
    encoded[28 - bytes.len()..].copy_from_slice(&bytes);
    encoded
}

fn compile_parent(total: &BigUint) -> WorkTreeHistoryPlan {
    WorkTreeHistoryPlan::compile(4, SLOT_LOG, ROOT, total_be28(total)).unwrap()
}

fn assign_consistent(
    assigned: &mut BTreeMap<usize, Fr>,
    wire: usize,
    value: Fr,
) -> Result<(), String> {
    if !value.is_zero() && !value.is_one() {
        return Err(format!("fixture bit is not Boolean at wire {wire}"));
    }
    if let Some(old) = assigned.get(&wire) {
        if old != &value {
            return Err(format!("fixture assignment conflict at wire {wire}"));
        }
    } else {
        assigned.insert(wire, value);
    }
    Ok(())
}

fn assign_integer(
    assigned: &mut BTreeMap<usize, Fr>,
    base: usize,
    wires: &[usize],
    value: &BigUint,
) -> Result<(), String> {
    for (bit, wire) in wires.iter().enumerate() {
        assign_consistent(
            assigned,
            base + *wire,
            Fr::from(value.bit(bit as u64) as u64),
        )?;
    }
    Ok(())
}

fn alias_envelope(nbits: u32, height: u32) -> Vec<Fr> {
    let raw = [0u8; ENVELOPE_BYTES];
    let length = ENVELOPE_BYTES as u64;
    let mut bits = Vec::with_capacity(4_186);
    for byte in raw {
        for bit in 0..8 {
            bits.push(Fr::from(((byte >> bit) & 1) as u64));
        }
    }
    for bit in 0..10 {
        bits.push(Fr::from(((length >> bit) & 1) as u64));
    }
    for bit in 0..32 {
        bits.push(Fr::from(((nbits >> bit) & 1) as u64));
    }
    for bit in 0..32 {
        bits.push(Fr::from(((height >> bit) & 1) as u64));
    }
    assert_eq!(bits.len(), 4_186);
    bits
}

fn source_assignment() -> Result<BTreeMap<usize, Fr>, String> {
    let baseline = work_tree_layout::shared_baseline().unwrap();
    let endpoints = &baseline.endpoints;
    assert_eq!(baseline.header_alias_wires.len(), 4_186);
    assert_eq!(endpoints.header_aliases().len(), 4_186);
    assert_eq!(endpoints.work.len(), 224);

    let decoded = work_tree_work::native_decode(COMPACT_NBITS).unwrap();
    let expected = BigUint::from(0x0117_6500_0000u64);
    assert_eq!(decoded, expected, "pinned test nBits must match native decode");
    let minus_one = &decoded - BigUint::from(1u8);
    let mut assigned = BTreeMap::new();

    // Three genuine leaf records correspond to header heights 2, 3, and 4.
    for slot in 0..3 {
        let lower = &decoded * BigUint::from(slot as u64);
        let upper = &lower + &decoded;
        let base = slot * WIDTH;
        assign_integer(
            &mut assigned,
            base,
            &endpoints.n_bits,
            &BigUint::from(COMPACT_NBITS),
        )?;
        assign_integer(
            &mut assigned,
            base,
            &endpoints.height,
            &BigUint::from((slot + 2) as u64),
        )?;
        assign_integer(&mut assigned, base, &endpoints.lower, &lower)?;
        assign_integer(&mut assigned, base, &endpoints.upper, &upper)?;
        assign_integer(&mut assigned, base, &endpoints.work, &decoded)?;
        assign_integer(&mut assigned, base, &endpoints.work_minus_one, &minus_one)?;
        for (selector, wire) in endpoints.exponent.iter().enumerate() {
            assign_consistent(
                &mut assigned,
                base + *wire,
                if selector == 6 { Fr::one() } else { Fr::zero() },
            )?;
        }
    }

    // Owner 3 is the arithmetic-padding slot. Assign its constrained banks,
    // including zero bits, from the source contract.
    let pad_base = 3 * WIDTH;
    for wires in [
        &endpoints.lower,
        &endpoints.upper,
        &endpoints.work,
        &endpoints.work_minus_one,
        &endpoints.exponent,
    ] {
        for wire in wires {
            assign_consistent(&mut assigned, pad_base + *wire, Fr::zero())?;
        }
    }

    // A controlled 514-byte envelope is copied through the source-owned
    // header/leaf alias map. It is deliberately not claimed to be a canonical
    // Ergo header or a canonical history.
    let destination_aliases = endpoints.header_aliases();
    for header_owner in 1..4 {
        let values = alias_envelope(COMPACT_NBITS, (header_owner + 1) as u32);
        let leaf_owner = header_owner - 1;
        for ((&source, &destination), value) in baseline
            .header_alias_wires
            .iter()
            .zip(destination_aliases.iter())
            .zip(values.iter())
        {
            assign_consistent(
                &mut assigned,
                header_owner * WIDTH + source,
                *value,
            )?;
            assign_consistent(
                &mut assigned,
                leaf_owner * WIDTH + destination,
                *value,
            )?;
        }
    }
    Ok(assigned)
}

fn dense_input(assigned: &BTreeMap<usize, Fr>) -> Vec<Fr> {
    let mut input = vec![Fr::zero(); INPUT_LEN];
    for (&wire, &value) in assigned {
        assert!(wire < INPUT_LEN);
        input[wire] = value;
    }
    input
}

fn set_integer(input: &mut [Fr], base: usize, wires: &[usize], value: &BigUint) {
    for (bit, wire) in wires.iter().enumerate() {
        input[base + *wire] = Fr::from(value.bit(bit as u64) as u64);
    }
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |acc, (bit, value)| {
            acc * if (index >> bit) & 1 == 1 {
                *value
            } else {
                Fr::one() - value
            }
        })
}

fn direct_terms(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for term in terms {
        let gate = &term.gate;
        let weight = eq_index(r, term.row) * eq_index(u, gate.left) * eq_index(v, gate.right);
        for (sum, coefficient) in out.iter_mut().zip([gate.c0, gate.c1, gate.c2, gate.c3]) {
            *sum += weight * coefficient;
        }
    }
    out
}

fn residuals_by_tag(terms: &[Term], input: &[Fr]) -> [BTreeMap<usize, Fr>; 6] {
    let mut out: [BTreeMap<usize, Fr>; 6] = std::array::from_fn(|_| BTreeMap::new());
    for term in terms {
        let tag = term.row >> TAG_SHIFT;
        assert!(tag < 6, "unexpected family tag {tag}");
        let row = term.row & (TAG_STRIDE - 1);
        let gate = &term.gate;
        let x = input[gate.left];
        let y = input[gate.right];
        let residual = gate.c0 + gate.c1 * x + gate.c2 * y + gate.c3 * x * y;
        *out[tag].entry(row).or_insert_with(Fr::zero) += residual;
    }
    out
}

fn nonzero_rows(residuals: &[BTreeMap<usize, Fr>; 6], tag: usize) -> Vec<usize> {
    residuals[tag]
        .iter()
        .filter_map(|(&row, value)| (!value.is_zero()).then_some(row))
        .collect()
}

fn assert_only_failed_tag(residuals: &[BTreeMap<usize, Fr>; 6], expected: usize) {
    let failed: Vec<_> = residuals
        .iter()
        .enumerate()
        .filter_map(|(tag, rows)| rows.values().any(|value| !value.is_zero()).then_some(tag))
        .collect();
    assert_eq!(failed, vec![expected]);
}

fn assert_exact_failed_rows(residuals: &[BTreeMap<usize, Fr>; 6], tag: usize, expected: &[usize]) {
    assert_only_failed_tag(residuals, tag);
    assert_eq!(nonzero_rows(residuals, tag), expected);
}

fn assert_row_omission_clears(
    terms: &[Term],
    input: &[Fr],
    tag: usize,
    rows: &[usize],
) {
    assert!(!rows.is_empty());
    let is_omitted = |term: &Term| {
        term.row >> TAG_SHIFT == tag && rows.contains(&(term.row & (TAG_STRIDE - 1)))
    };
    let removed = terms.iter().filter(|term| is_omitted(term)).count();
    assert!(removed > 0, "no Terms match family {tag}, rows {rows:?}");
    let retained: Vec<_> = terms.iter().filter(|term| !is_omitted(term)).cloned().collect();
    assert_eq!(terms.len() - retained.len(), removed);
    let residuals = residuals_by_tag(&retained, input);
    assert!(residuals.iter().all(|family| family.values().all(|value| value.is_zero())),
        "omitting only family {tag}, rows {rows:?} did not clear the isolated fault");
}

fn terms_for(relation: &NativeWorkRelation<'_>) -> Vec<Term> {
    let mut terms = Vec::new();
    let count = relation
        .visit_terms(|term| {
            terms.push(term);
            Ok(())
        })
        .unwrap();
    assert_eq!(count, terms.len());
    terms
}

fn field_point(bits: usize, seed: u64) -> Vec<Fr> {
    (0..bits)
        .map(|bit| Fr::from(seed + 19 * (bit as u64 + 1)))
        .collect()
}

fn family_counts(terms: &[Term]) -> [usize; 6] {
    let mut counts = [0usize; 6];
    for term in terms {
        let tag = term.row >> TAG_SHIFT;
        assert!(tag < counts.len());
        assert!(term.row < ROW_COUNT);
        counts[tag] += 1;
    }
    counts
}

fn assert_native_work_fixture(parent: &WorkTreeHistoryPlan, relation: &NativeWorkRelation<'_>, terms: &[Term]) -> Vec<Fr> {
    let d = work_tree_work::native_decode(COMPACT_NBITS).unwrap();
    assert_eq!(d, BigUint::from(0x0117_6500_0000u64));
    let total = &d * BigUint::from(3u8);
    assert_eq!((relation.input_log(), relation.row_log()), (INPUT_LOG, OUTPUT_LOG));
    let assigned = source_assignment().unwrap();
    assert!(!assigned.contains_key(&7), "wire 7 is not assigned by the fixture sources");
    for (&wire, &value) in &assigned {
        let mut conflict = assigned.get(&wire).copied().unwrap();
        conflict = Fr::one() - conflict;
        let mut one_entry = BTreeMap::new();
        one_entry.insert(wire, value);
        assert!(assign_consistent(&mut one_entry, wire, conflict).is_err(),
            "conflicting source assignment escaped at wire {wire}");
    }
    println!("C554_NATIVE_WORK_STAGE fixture_conflicts_checked bit_assignments={} conflicts_rejected={}", assigned.len(), assigned.len());

    let mut input = dense_input(&assigned);
    assert_eq!(terms.len(), EXPECTED_TERMS);
    assert_eq!(family_counts(&terms), EXPECTED_BY_TAG);
    assert!(terms.iter().all(|term| term.gate.left != 7 && term.gate.right != 7),
        "Fr(2) at wire 7 is outside all six selected families");
    input[7] = Fr::from(2u64);

    let endpoints = Endpoints::new();
    for (slot, lower, upper) in [
        (0usize, BigUint::from(0u8), d.clone()),
        (1usize, d.clone(), &d * BigUint::from(2u8)),
        (2usize, &d * BigUint::from(2u8), total.clone()),
    ] {
        assert_eq!(read_bits(&input, slot * WIDTH, &endpoints.work), d);
        assert_eq!(read_bits(&input, slot * WIDTH, &endpoints.lower), lower);
        assert_eq!(read_bits(&input, slot * WIDTH, &endpoints.upper), upper);
        assert_eq!(read_bits(&input, slot * WIDTH, &endpoints.n_bits), BigUint::from(COMPACT_NBITS));
    }
    assert_eq!(read_bits(&input, 0, &endpoints.height), BigUint::from(2u8));
    assert_eq!(read_bits(&input, WIDTH, &endpoints.height), BigUint::from(3u8));
    assert_eq!(read_bits(&input, 2 * WIDTH, &endpoints.height), BigUint::from(4u8));
    assert!(residuals_by_tag(terms, &input)
        .iter()
        .all(|rows| rows.values().all(|value| value.is_zero())));
    assert_eq!(parent.work_profile().total_be28, total_be28(&total));
    input
}

fn read_bits(input: &[Fr], base: usize, wires: &[usize]) -> BigUint {
    let mut value = BigUint::from(0u8);
    for (bit, wire) in wires.iter().enumerate() {
        let field = input[base + *wire];
        assert!(field.is_zero() || field.is_one(), "source bit is not Boolean");
        if field.is_one() {
            value |= BigUint::from(1u8) << bit;
        }
    }
    value
}

fn assert_six_family_coefficients(relation: &NativeWorkRelation<'_>, terms: &[Term]) {
    let source_logs = [SLOT_LOG, 11 + SLOT_LOG, 8 + SLOT_LOG, 8 + SLOT_LOG, 8 + SLOT_LOG, 13 + SLOT_LOG];
    let mut saw_tag_mutant = false;
    let mut saw_zero_extension_mutant = false;
    let mut saw_padded_row_mutant = false;

    for seed in [13u64, 71, 193] {
        let mut r = field_point(OUTPUT_LOG, seed);
        let u = field_point(INPUT_LOG, seed + 1001);
        let v = field_point(INPUT_LOG, seed + 2003);
        for (bit, value) in [(13usize, Fr::from(2u64)), (14, Fr::from(5u64)),
            (15, Fr::from(3u64)), (16, Fr::from(7u64)), (17, Fr::from(11u64))] {
            r[bit] = value;
        }
        let expected = direct_terms(terms, &r, &u, &v);
        assert_eq!(relation.coefficients(&r, &u, &v).unwrap(), expected);

        let mut split = [Fr::zero(); 4];
        let mut missing_zero_factors = [Fr::zero(); 4];
        for tag in 0..6 {
            let unembedded: Vec<_> = terms
                .iter()
                .filter(|term| term.row >> TAG_SHIFT == tag)
                .map(|term| {
                    let mut term = term.clone();
                    term.row &= TAG_STRIDE - 1;
                    term
                })
                .collect();
            let source = direct_terms(&unembedded, &r[..source_logs[tag]], &u, &v);
            let tag_weight = eq_index(&r[TAG_SHIFT..OUTPUT_LOG], tag);
            let zero_factor = r[source_logs[tag]..TAG_SHIFT]
                .iter()
                .fold(Fr::one(), |acc, value| acc * (Fr::one() - value));
            for index in 0..4 {
                split[index] += tag_weight * zero_factor * source[index];
                missing_zero_factors[index] += tag_weight * source[index];
            }
        }
        assert_eq!(split, expected, "finite tag/zero-extension formula");
        saw_zero_extension_mutant |= missing_zero_factors != expected;

        let mut wrong_tag = terms.to_vec();
        let index = wrong_tag.iter().position(|term| term.row >> TAG_SHIFT == 0)
            .expect("numeric family term");
        wrong_tag[index].row += 6 * TAG_STRIDE;
        saw_tag_mutant |= direct_terms(&wrong_tag, &r, &u, &v) != expected;

        let work_tag = 1usize;
        let source_width = 1usize << source_logs[work_tag];
        let last = terms.iter().enumerate()
            .filter(|(_, term)| term.row >> TAG_SHIFT == work_tag)
            .max_by_key(|(_, term)| term.row & (TAG_STRIDE - 1))
            .map(|(index, _)| index).unwrap();
        let mut padded = terms.to_vec();
        padded[last].row = work_tag * TAG_STRIDE + source_width;
        saw_padded_row_mutant |= direct_terms(&padded, &r, &u, &v) != expected;
    }
    assert!(saw_tag_mutant, "changing a family tag must change the direct MLE");
    assert!(saw_zero_extension_mutant, "omitting the row zero-extension factor must change the result");
    assert!(saw_padded_row_mutant, "moving a live term into the first padded row must change the result");
}

fn assert_native_work_faults(parent: &WorkTreeHistoryPlan, terms: &[Term], input: &[Fr]) {
    let d = work_tree_work::native_decode(COMPACT_NBITS).unwrap();
    let total = &d * BigUint::from(3u8);
    let endpoints = Endpoints::new();
    let decoded_group = parent.work_boundary().group("decoded_work").unwrap();
    let decoded_row = decoded_group.start + 24;

    // Decoder fault: nBits bit 0 changes on the header side and copied leaf
    // side of only the first genuine leaf, so alias equality remains satisfied
    // while exactly its decoded-work row disagrees.
    let decoded_bad = COMPACT_NBITS ^ 1;
    assert_ne!(work_tree_work::native_decode(decoded_bad).unwrap(), d);
    let baseline = work_tree_layout::shared_baseline().unwrap();
    let nbits_alias_index = 4_112 + 10;
    {
        let mut bad_decode = input.to_vec();
        let header_owner = 1;
        let source = header_owner * WIDTH + baseline.header_alias_wires[nbits_alias_index];
        let leaf = (header_owner - 1) * WIDTH + endpoints.n_bits[0];
        bad_decode[source] = Fr::one() - bad_decode[source];
        bad_decode[leaf] = Fr::one() - bad_decode[leaf];
        let decoded_rows = residuals_by_tag(terms, &bad_decode);
        assert_exact_failed_rows(&decoded_rows, 1, &[decoded_row]);
        assert_row_omission_clears(terms, &bad_decode, 1, &[decoded_row]);
    }

    // Reuse one changed public total/profile for the isolated first-lower,
    // continuity and public-total controls.
    let shifted_total = &total + BigUint::from(1u8);
    let shifted_parent = compile_parent(&shifted_total);
    let shifted_relation = NativeWorkRelation::new(&shifted_parent).unwrap();
    let shifted_terms = terms_for(&shifted_relation);
    let nbits_bit0 = 4_112 + 10;
    let first_lower_row = 0usize;
    let continuity_row = 256;
    let public_total_row = 512;

    {
        let mut shifted = input.to_vec();
        for slot in 0..3 {
            let base = slot * WIDTH;
            let lower = read_bits(input, base, &endpoints.lower) + BigUint::from(1u8);
            let upper = read_bits(input, base, &endpoints.upper) + BigUint::from(1u8);
            set_integer(&mut shifted, base, &endpoints.lower, &lower);
            set_integer(&mut shifted, base, &endpoints.upper, &upper);
        }
        let rows = residuals_by_tag(&shifted_terms, &shifted);
        assert_exact_failed_rows(&rows, 2, &[first_lower_row]);
        assert_row_omission_clears(&shifted_terms, &shifted, 2, &[first_lower_row]);
    }

    {
        let mut discontinuous = input.to_vec();
        let lower1 = &d + BigUint::from(1u8);
        let upper1 = &d * BigUint::from(2u8) + BigUint::from(1u8);
        let lower2 = upper1.clone();
        let upper2 = &total + BigUint::from(1u8);
        set_integer(&mut discontinuous, WIDTH, &endpoints.lower, &lower1);
        set_integer(&mut discontinuous, WIDTH, &endpoints.upper, &upper1);
        set_integer(&mut discontinuous, 2 * WIDTH, &endpoints.lower, &lower2);
        set_integer(&mut discontinuous, 2 * WIDTH, &endpoints.upper, &upper2);
        let rows = residuals_by_tag(&shifted_terms, &discontinuous);
        assert_exact_failed_rows(&rows, 3, &[continuity_row]);
        assert_row_omission_clears(&shifted_terms, &discontinuous, 3, &[continuity_row]);
    }

    let total_rows = residuals_by_tag(&shifted_terms, input);
    assert_exact_failed_rows(&total_rows, 4, &[public_total_row]);
    assert_row_omission_clears(&shifted_terms, input, 4, &[public_total_row]);

    {
        let source_wire = WIDTH + baseline.header_alias_wires[nbits_bit0];
        assert_eq!(input[source_wire], Fr::one());
        let mut alias_bad = input.to_vec();
        alias_bad[source_wire] = Fr::zero();
        let alias_row = (1usize << 13) + nbits_bit0;
        let rows = residuals_by_tag(terms, &alias_bad);
        assert_exact_failed_rows(&rows, 5, &[alias_row]);
        assert_row_omission_clears(terms, &alias_bad, 5, &[alias_row]);
    }

    // Preserve the weighted U224 values and link equality while violating
    // consumed endpoint bit Booleanity in upper_0 and matching lower_1.
    {
        let mut non_boolean = input.to_vec();
        for (slot, endpoint) in [(0usize, &endpoints.upper), (1, &endpoints.lower)] {
            non_boolean[slot * WIDTH + endpoint[0]] = Fr::from(2u64);
            non_boolean[slot * WIDTH + endpoint[1]] = -Fr::one();
        }
        let upper_rows = parent.work_boundary().group("upper_boolean").unwrap();
        let lower_rows = parent.work_boundary().group("lower_boolean").unwrap();
        let mut expected = vec![
            upper_rows.start,
            upper_rows.start + 1,
            work_tree_work::LOCAL_ROW_WIDTH + lower_rows.start,
            work_tree_work::LOCAL_ROW_WIDTH + lower_rows.start + 1,
        ];
        expected.sort_unstable();
        let rows = residuals_by_tag(terms, &non_boolean);
        assert_exact_failed_rows(&rows, 1, &expected);
        assert_row_omission_clears(terms, &non_boolean, 1, &expected);
    }

    // Arithmetic padding is explicitly zero at leaf owner 3; this fault does
    // not claim that other unused coordinates must be zero or Boolean.
    {
        let mut padding_bad = input.to_vec();
        padding_bad[3 * WIDTH + endpoints.lower[0]] = Fr::one();
        let padding_group = parent.work_boundary().group("padding_arithmetic_zero").unwrap();
        let padding_row = 3 * work_tree_work::LOCAL_ROW_WIDTH + padding_group.start;
        let rows = residuals_by_tag(terms, &padding_bad);
        assert_exact_failed_rows(&rows, 1, &[padding_row]);
        assert_row_omission_clears(terms, &padding_bad, 1, &[padding_row]);
    }
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

fn prove_and_open(
    verifier: &NativeWorkVerifier<'_>,
    circuit: &Circuit,
    input: &[Fr],
    committed: &Committed,
    setup: &Setup,
    phase: &str,
) -> (Vec<u8>, Vec<u8>, InputClaim) {
    println!("C554_NATIVE_WORK_STAGE {phase}_gkr_start");
    let mut transcript = Transcript::new(NATIVE_WORK_DOMAIN);
    verifier.bind_gkr(&mut transcript).unwrap();
    let (proof, claim) = sparse::prove_with_binding(circuit, input, 0, &mut transcript, |_| {}).unwrap();
    assert_eq!(gkr::mle(input, &claim.point).unwrap(), claim.value);
    println!("C554_NATIVE_WORK_STAGE {phase}_gkr_done");
    native_work_pcs_separator(&mut transcript);
    println!("C554_NATIVE_WORK_STAGE {phase}_pcs_start");
    let pcs_proof = pcs::open(committed, &claim.point, setup, &mut transcript).unwrap();
    println!("C554_NATIVE_WORK_STAGE {phase}_pcs_done");
    (gkr::encode_proof(&proof).unwrap(), pcs::encode_proof(&pcs_proof).unwrap(), claim)
}

fn replay_with_terms(
    verifier: &NativeWorkVerifier<'_>,
    terms: &[Term],
    proof_bytes: &[u8],
) -> Result<(InputClaim, Transcript), String> {
    let proof = gkr::decode_dimensions(&[INPUT_LOG], proof_bytes)?;
    if gkr::encode_proof(&proof)? != proof_bytes {
        return Err("mutant GKR canonical re-encoding mismatch".into());
    }
    let mut transcript = Transcript::new(NATIVE_WORK_DOMAIN);
    verifier.bind_gkr(&mut transcript)?;
    let claim = gkr::verify_with_wiring(
        &[INPUT_LOG],
        ROW_COUNT,
        &proof,
        &mut transcript,
        |_| {},
        |layer, r, u, v| {
            if layer != 0 {
                return Err(GkrError::ProofLayerCount);
            }
            Ok(direct_terms(terms, r, u, v))
        },
    )
    .map_err(|error| error.to_string())?;
    Ok((claim, transcript))
}

#[test]
#[ignore = "bounded authenticated native-work same-X diagnostic"]
fn authenticated_native_work_same_x_and_whole_alias_omission() {
    println!("C554_NATIVE_WORK_STAGE fixture_start");
    let decoded = work_tree_work::native_decode(COMPACT_NBITS).unwrap();
    let total = &decoded * BigUint::from(3u8);
    let parent = compile_parent(&total);
    let relation = NativeWorkRelation::new(&parent).unwrap();
    let terms = terms_for(&relation);
    assert_eq!((relation.input_log(), relation.row_log()), (INPUT_LOG, OUTPUT_LOG));
    assert_eq!(terms.len(), EXPECTED_TERMS);
    assert_eq!(family_counts(&terms), EXPECTED_BY_TAG);

    assert!(!terms.iter().any(|term| term.gate.left == 7 || term.gate.right == 7),
        "Fr(2) wire 7 must be unconsumed by all six families in this fixture");
    let input = assert_native_work_fixture(&parent, &relation, &terms);
    println!("C554_NATIVE_WORK_STAGE fixture_ready input_log=22 row_log=18 terms=25522 family_terms=1121,10947,224,448,224,12558 envelope_bytes=514 canonical_history=false");
    println!("C554_NATIVE_WORK_STAGE embedding_differential_start");
    assert_six_family_coefficients(&relation, &terms);
    println!("C554_NATIVE_WORK_STAGE embedding_differential_done");
    println!("C554_NATIVE_WORK_STAGE residual_controls_start");
    assert_native_work_faults(&parent, &terms, &input);
    println!("C554_NATIVE_WORK_STAGE residual_controls_done");
    let baseline = work_tree_layout::shared_baseline().unwrap();
    assert_eq!(baseline.header_alias_wires.len(), 4_186);

    println!("C554_NATIVE_WORK_STAGE setup22_start");
    let (setup, key) = setup_and_admitted_key();
    println!("C554_NATIVE_WORK_STAGE setup22_done");
    println!("C554_NATIVE_WORK_STAGE positive_commit_start");
    let committed = pcs::commit(&input, &setup).unwrap();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap();
    println!("C554_NATIVE_WORK_STAGE positive_commit_done");
    let verifier = NativeWorkVerifier::new(&parent, &key, &commitment_bytes).unwrap();
    let circuit = Circuit { input_len: INPUT_LEN, row_count: ROW_COUNT, terms: terms.clone() };
    let (gkr_bytes, pcs_bytes, claim) = prove_and_open(
        &verifier, &circuit, &input, &committed, &setup, "positive",
    );
    verifier.verify(&gkr_bytes, &pcs_bytes).unwrap();
    assert_eq!(claim.point.len(), INPUT_LOG);
    println!("C554_NATIVE_WORK_STAGE positive_verified gkr_bytes={} pcs_bytes={}", gkr_bytes.len(), pcs_bytes.len());
    drop(committed);

    // Rebuild X with one header-side nBits copy bit changed; keep the leaf
    // nBits, work intervals, all other bits, and public context fixed.
    println!("C554_NATIVE_WORK_STAGE alias_omission_mutant");
    let nbits_bit0 = 4_112 + 10;
    let source_wire = WIDTH + baseline.header_alias_wires[nbits_bit0];
    let destination_wire = Endpoints::new().n_bits[0];
    assert_eq!(input[source_wire], Fr::one());
    assert_eq!(input[destination_wire], Fr::one());
    let mut bad_input = input.to_vec();
    bad_input[source_wire] = Fr::zero();
    drop(input);
    let matches: Vec<_> = terms
        .iter()
        .enumerate()
        .filter(|(_, term)| {
            term.row >> TAG_SHIFT == 5
                && term.gate.left == source_wire
                && term.gate.right == destination_wire
                && term.gate.c0.is_zero()
                && term.gate.c1.is_one()
                && term.gate.c2 == -Fr::one()
                && term.gate.c3.is_zero()
        })
        .collect();
    assert_eq!(matches.len(), 1, "expected one complete header nBits alias Term");
    let mutant_index = matches[0].0;
    let removed = (*matches[0].1).clone();
    let mut mutant_terms = terms.clone();
    mutant_terms.remove(mutant_index);
    assert_eq!(terms.len() - mutant_terms.len(), 1);
    assert_eq!(removed.gate.left, source_wire);
    assert_eq!(removed.gate.right, destination_wire);
    let expected_alias_row = (5 << TAG_SHIFT) + (1 << 13) + nbits_bit0;
    assert_eq!(removed.row, expected_alias_row);
    assert_eq!([removed.gate.c0, removed.gate.c1, removed.gate.c2, removed.gate.c3],
        [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]);

    println!("C554_NATIVE_WORK_STAGE alias_mutant_commit_start");
    let committed_bad = pcs::commit(&bad_input, &setup).unwrap();
    let commitment_bad = pcs::encode_commitment(&committed_bad.commitment).unwrap();
    println!("C554_NATIVE_WORK_STAGE alias_mutant_commit_done");
    let verifier_bad = NativeWorkVerifier::new(&parent, &key, &commitment_bad).unwrap();
    let mutant_circuit = Circuit { input_len: INPUT_LEN, row_count: ROW_COUNT, terms: mutant_terms.clone() };
    let (mutant_gkr, mutant_pcs, mutant_claim) = prove_and_open(
        &verifier_bad, &mutant_circuit, &bad_input, &committed_bad, &setup, "alias_mutant",
    );
    assert_eq!(mutant_claim.point.len(), INPUT_LOG);
    let real_error = verifier_bad.verify(&mutant_gkr, &mutant_pcs).unwrap_err();
    assert!(real_error.contains("TerminalExpression"), "real relation did not reject at GKR terminal: {real_error}");
    println!("C554_NATIVE_WORK_STAGE alias_mutant_real_reject terminal_expression=true");

    // Isolated omitted-equation control: replay the same proof with exactly
    // the complete alias Term removed, then verify the same PCS bytes against
    // the same bad-X commitment.
    println!("C554_NATIVE_WORK_STAGE isolated_mutant_gkr_start");
    let (mutant_input_claim, mut mutant_transcript) =
        replay_with_terms(&verifier_bad, &mutant_terms, &mutant_gkr).unwrap();
    assert_eq!(mutant_input_claim, mutant_claim);
    println!("C554_NATIVE_WORK_STAGE isolated_mutant_gkr_done");
    native_work_pcs_separator(&mut mutant_transcript);
    let pcs_proof = pcs::decode_proof(&mutant_pcs, INPUT_LOG).unwrap();
    println!("C554_NATIVE_WORK_STAGE isolated_mutant_pcs_start");
    pcs::verify_admitted(
        committed_bad.commitment.clone(),
        mutant_input_claim.value,
        &mutant_input_claim.point,
        &pcs_proof,
        &key,
        &mut mutant_transcript,
    ).unwrap();
    println!("C554_NATIVE_WORK_STAGE isolated_mutant_pcs_done");
    println!("C554_NATIVE_WORK_ALIAS_OMISSION_PASS removed_complete_terms=1 real_terminal_rejects=true mutant_same_c_pcs_accepts=true");
    println!("C554_NATIVE_WORK_STAGE PASS input_log=22 row_log=18 terms=25522 alias_omissions=1");
    drop(committed_bad);
    drop(bad_input);
}

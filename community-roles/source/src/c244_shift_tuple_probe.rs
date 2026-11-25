//! Test-only differential of the Rust serializer Builder's 16 shift-stage
//! tuples against the independently generated, pinned c241 ordered stream.
//! This checks tuple grammar only; it makes no U, prover, or producer-cost claim.

use ark_bn254::Fr;
use ark_ff::Zero;
use serde_json::Value;
use std::collections::BTreeSet;
use std::fs;

const ATTACHED_ROW_OFFSET: usize = 12_836;
const ATTACHED_INPUT_OFFSET: usize = 524_288;
const EXPECTED_STAGE_COUNT: usize = 16;
const EXPECTED_TERM_COUNT: usize = 136_160;

#[derive(Clone)]
struct Tuple {
    row: usize,
    left: usize,
    right: usize,
    coefficients: [Fr; 4],
    // Diagnostic coordinate translations from the fixture; this is not an
    // attached-circuit build or an assertion about an attached producer.
    attached_row: usize,
    attached_left: usize,
    attached_right: usize,
}

type ReferenceTuple = [i64; 10];

fn env_path(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("required runner-pinned env var {name} is unset"))
}

fn required_usize(value: &Value, key: &str) -> usize {
    value[key]
        .as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .unwrap_or_else(|| panic!("receipt field {key} must be an unsigned integer"))
}

fn receipt_stage_rows(receipt: &Value) -> BTreeSet<usize> {
    let stages = receipt["stages"].as_array().expect("receipt stages must be an array");
    assert_eq!(stages.len(), EXPECTED_STAGE_COUNT, "receipt must declare all 16 stages");
    assert_eq!(required_usize(&receipt["counts"], "stages"), EXPECTED_STAGE_COUNT);
    assert_eq!(required_usize(&receipt["counts"], "ordered_terms"), EXPECTED_TERM_COUNT);

    let expected_families = [
        ("extension", 9usize),
        ("height", 3usize),
        ("timestamp", 4usize),
    ];
    let mut rows = BTreeSet::new();
    let mut previous_end = None;
    let mut previous_family = None;
    let mut family_bit = 0usize;
    let mut family_index = 0usize;
    for (stage_index, stage) in stages.iter().enumerate() {
        let name = stage["name"].as_str().expect("stage name must be a string");
        let (expected_name, family_size) = expected_families[family_index];
        assert_eq!(name, expected_name, "receipt stage family/order at index {stage_index}");
        assert_eq!(required_usize(stage, "bit"), family_bit, "receipt stage bit order at index {stage_index}");
        let keep = required_usize(stage, "source_keep_row");
        let first_mux = required_usize(stage, "source_mux_first_row");
        let mux_rows = required_usize(stage, "mux_rows");
        let distance = required_usize(stage, "distance");
        assert_eq!(first_mux, keep + 1 + distance, "stage keep/drop/mux boundaries disagree");
        if let Some(end) = previous_end {
            assert!(keep >= end, "receipt stage spans must not overlap");
            if previous_family == Some(name) {
                assert_eq!(keep, end, "rows must be contiguous within one shift family");
            } else {
                assert!(keep > end, "family transition must be ordered and non-overlapping");
                assert_eq!(family_index > 0, true, "unexpected initial family transition");
            }
        }
        let end = first_mux.checked_add(mux_rows).expect("stage end overflow");
        for row in keep..end {
            assert!(rows.insert(row), "overlapping stage row {row}");
        }
        previous_end = Some(end);
        previous_family = Some(name);
        family_bit += 1;
        if family_bit == family_size {
            family_index += 1;
            family_bit = 0;
        }
    }
    assert_eq!(family_index, expected_families.len(), "receipt must end after timestamp stages");
    rows
}

fn signed_fr(n: i64) -> Fr {
    if n < 0 { -Fr::from(n.unsigned_abs()) } else { Fr::from(n as u64) }
}

fn parse_reference(path: &str, stage_rows: &BTreeSet<usize>) -> Vec<ReferenceTuple> {
    let content = fs::read_to_string(path).unwrap_or_else(|e| panic!("read ordered tuple fixture: {e}"));
    let mut out = Vec::with_capacity(EXPECTED_TERM_COUNT);
    for (line_no, line) in content.lines().enumerate() {
        let tuple: Vec<i64> = serde_json::from_str(line)
            .unwrap_or_else(|e| panic!("invalid JSON tuple at line {}: {e}", line_no + 1));
        let tuple: ReferenceTuple = tuple.try_into().unwrap_or_else(|v: Vec<i64>| {
            panic!("line {} has {} fields; expected 10", line_no + 1, v.len())
        });
        let row = usize::try_from(tuple[0]).expect("tuple row must be nonnegative");
        if !stage_rows.contains(&row) {
            continue;
        }
        assert_eq!(tuple[7], tuple[0] + ATTACHED_ROW_OFFSET as i64, "attached row offset at line {}", line_no + 1);
        assert_eq!(tuple[8], tuple[1] + ATTACHED_INPUT_OFFSET as i64, "attached left offset at line {}", line_no + 1);
        assert_eq!(tuple[9], tuple[2] + ATTACHED_INPUT_OFFSET as i64, "attached right offset at line {}", line_no + 1);
        out.push(tuple);
    }
    out
}

fn candidate_tuples() -> Vec<Tuple> {
    let built = crate::serializer::build(None).expect("serializer::build(None) must succeed");
    built.circuit.terms.into_iter().map(|term| Tuple {
        row: term.row,
        left: term.gate.left,
        right: term.gate.right,
        coefficients: [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3],
        attached_row: term.row.checked_add(ATTACHED_ROW_OFFSET).expect("attached row overflow"),
        attached_left: term.gate.left.checked_add(ATTACHED_INPUT_OFFSET).expect("attached left overflow"),
        attached_right: term.gate.right.checked_add(ATTACHED_INPUT_OFFSET).expect("attached right overflow"),
    }).collect()
}

fn first_mismatch(expected: &[ReferenceTuple], actual: &[Tuple]) -> Option<(usize, usize)> {
    if expected.len() != actual.len() {
        return Some((expected.len().min(actual.len()), 10));
    }
    for (i, (e, a)) in expected.iter().zip(actual).enumerate() {
        let ordinary = [a.row, a.left, a.right, a.attached_row, a.attached_left, a.attached_right];
        let expected_ordinary = [e[0], e[1], e[2], e[7], e[8], e[9]];
        let fields = [0usize, 1, 2, 7, 8, 9];
        for (actual_value, (expected_value, field)) in ordinary.iter().zip(expected_ordinary.iter().zip(fields)) {
            if i64::try_from(*actual_value).ok() != Some(*expected_value) {
                return Some((i, field));
            }
        }
        for coefficient in 0..4 {
            if a.coefficients[coefficient] != signed_fr(e[3 + coefficient]) {
                return Some((i, 3 + coefficient));
            }
        }
    }
    None
}

fn field_name(field: usize) -> &'static str {
    match field {
        0 => "row",
        1 => "left",
        2 => "right",
        3 => "c0",
        4 => "c1",
        5 => "c2",
        6 => "c3",
        7 => "attached_row",
        8 => "attached_left",
        9 => "attached_right",
        _ => "tuple_count",
    }
}

fn assert_mismatch_at(expected: &[ReferenceTuple], actual: &[Tuple], index: usize, field: usize, fault: &str) {
    assert_eq!(first_mismatch(expected, actual), Some((index, field)), "{fault} must be isolated at tuple {index} field {}", field_name(field));
}

#[test]
fn c244_rust_builder_shift_tuples_match_pinned_ordered_fixture() {
    let receipt_path = env_path("C244_C241_RECEIPT");
    let tuples_path = env_path("C244_C241_ORDERED_TERMS");
    let receipt: Value = serde_json::from_str(&fs::read_to_string(&receipt_path).expect("read c241 receipt"))
        .expect("parse c241 receipt JSON");
    let stage_rows = receipt_stage_rows(&receipt);
    let expected = parse_reference(&tuples_path, &stage_rows);
    let mut actual: Vec<Tuple> = candidate_tuples().into_iter()
        .filter(|tuple| stage_rows.contains(&tuple.row))
        .collect();

    assert_eq!(expected.len(), EXPECTED_TERM_COUNT, "fixture stage filter must retain all ordered terms");
    assert_eq!(actual.len(), EXPECTED_TERM_COUNT, "Rust Builder stage filter term count");
    if let Some((index, field)) = first_mismatch(&expected, &actual) {
        panic!("Rust Builder tuple mismatch at ordered index {index}, field {}", field_name(field));
    }

    // Isolated comparator sensitivity controls. Each mutation preserves tuple
    // count and must be attributed to its single intentionally changed field.
    let mut wrong_row = actual.clone();
    wrong_row[0].row += 1;
    assert_mismatch_at(&expected, &wrong_row, 0, 0, "count-preserving wrong-row mutant");

    let mut wrong_attached_row = actual.clone();
    wrong_attached_row[0].attached_row += 1;
    assert_mismatch_at(&expected, &wrong_attached_row, 0, 7, "count-preserving attached-row mutant");

    let wrong_side_index = actual.iter().position(|t| t.attached_left != t.attached_right)
        .expect("fixture needs a left/right-distinct tuple for wrong-side mutant");
    let mut wrong_side = actual.clone();
    wrong_side[wrong_side_index].attached_right = wrong_side[wrong_side_index].attached_left;
    assert_mismatch_at(&expected, &wrong_side, wrong_side_index, 9, "wrong-side attached-right mutant");

    let source_zero_index = actual.iter().position(|t| t.right == 0)
        .expect("fixture needs a source-zero right wire");
    assert_eq!(expected[source_zero_index][9], ATTACHED_INPUT_OFFSET as i64,
        "X(o,524288) must remain distinct from X(o,0)");
    let mut source_zero_right = actual.clone();
    source_zero_right[source_zero_index].attached_right = source_zero_right[source_zero_index].right;
    assert_mismatch_at(&expected, &source_zero_right, source_zero_index, 9, "source-zero attached-right mutant");

    let (coefficient_index, coefficient_field) = actual.iter().enumerate().find_map(|(i, t)| {
        t.coefficients.iter().position(|c| !c.is_zero()).map(|c| (i, c))
    }).expect("fixture needs a nonzero coefficient");
    let mut wrong_sign = actual.clone();
    wrong_sign[coefficient_index].coefficients[coefficient_field] = -wrong_sign[coefficient_index].coefficients[coefficient_field];
    assert_mismatch_at(&expected, &wrong_sign, coefficient_index, 3 + coefficient_field, "coefficient-sign mutant");

}

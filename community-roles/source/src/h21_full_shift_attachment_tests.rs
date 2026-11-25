//! Full archived shift-family identity against adjacent H21 role-1 owners.
//! This checks callback attachment and owner census only; it is not a proof.

use crate::{
    daa_history_roster::{DaaHistoryRoster, HeaderCounts, OwnerClass},
    gkr::Gate,
    serializer,
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use ark_bn254::Fr;
use std::{collections::HashSet, convert::TryFrom, fs};

const H21_HEADERS: u64 = 1_827_840;
const SLOT_LOG: usize = 21;
const OWNER_ROWS: usize = 1 << 19;
const OWNER_WIDTH: usize = 1 << 20;
const LOCAL_ROWS: usize = 1 << 19;
const SOURCE_ROW_OFFSET: usize = 12_836;
const SOURCE_INPUT_OFFSET: usize = 524_288;
const EXPECTED_ARCHIVE_TERMS: usize = 136_160;
const EXPECTED_SERIALIZER_TERMS: usize = 315_546;
const EXPECTED_FULL_OWNER_TERMS: usize = 474_755;
const EXPECTED_EMITTED: usize = 396_561;
const EXPECTED_OMITTED_WORKTREE: usize = 78_194;
const ARCHIVE_SHA256: &str = "D9E73A442E992782481D78BCF8F2B40B972746150F309D8195E53CBC8CE19A49";

fn field_integer(value: i64) -> Fr {
    if value < 0 {
        -Fr::from(value.unsigned_abs())
    } else {
        Fr::from(value as u64)
    }
}

fn read_archive() -> (Vec<Term>, HashSet<usize>, HashSet<usize>) {
    let path = std::env::var("C260_C241_ORDERED_TERMS")
        .expect("runner must pin C260_C241_ORDERED_TERMS to the c241 archive");
    let bytes = fs::read(path).expect("read pinned c241 ordered-terms archive");
    let text = std::str::from_utf8(&bytes).expect("c241 archive must be UTF-8 JSONL");
    let mut expected = Vec::with_capacity(EXPECTED_ARCHIVE_TERMS);
    let mut rows = HashSet::new();
    let mut source_rows = HashSet::new();
    for (line_index, line) in text.lines().enumerate() {
        let values: [i64; 10] = serde_json::from_str(line)
            .unwrap_or_else(|error| panic!("archive line {}: {error}", line_index + 1));
        let row = usize::try_from(values[0]).expect("source row must be nonnegative");
        let left = usize::try_from(values[1]).expect("source left must be nonnegative");
        let right = usize::try_from(values[2]).expect("source right must be nonnegative");
        source_rows.insert(row);
        assert_eq!(row.checked_add(SOURCE_ROW_OFFSET), Some(values[7] as usize),
            "archive attached row at line {}", line_index + 1);
        assert_eq!(left.checked_add(SOURCE_INPUT_OFFSET), Some(values[8] as usize),
            "archive attached left at line {}", line_index + 1);
        assert_eq!(right.checked_add(SOURCE_INPUT_OFFSET), Some(values[9] as usize),
            "archive attached right at line {}", line_index + 1);
        let attached_row = usize::try_from(values[7]).expect("attached row must be nonnegative");
        let attached_left = usize::try_from(values[8]).expect("attached left must be nonnegative");
        let attached_right = usize::try_from(values[9]).expect("attached right must be nonnegative");
        rows.insert(attached_row);
        expected.push(Term {
            row: attached_row,
            gate: Gate {
                left: attached_left,
                right: attached_right,
                c0: field_integer(values[3]),
                c1: field_integer(values[4]),
                c2: field_integer(values[5]),
                c3: field_integer(values[6]),
            },
        });
    }
    assert_eq!(expected.len(), EXPECTED_ARCHIVE_TERMS, "complete ordered c241 archive");
    (expected, rows, source_rows)
}

fn normalized_callback_terms(
    roster: &DaaHistoryRoster<'_>,
    owner: usize,
    selected_rows: &HashSet<usize>,
) -> (HeaderCounts, usize, Vec<Term>) {
    let row_base = owner.checked_mul(OWNER_ROWS).expect("owner row base");
    let input_base = owner.checked_mul(OWNER_WIDTH).expect("owner input base");
    let row_end = row_base.checked_add(LOCAL_ROWS).expect("owner row end");
    let input_end = input_base.checked_add(OWNER_WIDTH).expect("owner input end");
    let mut observed = 0usize;
    let mut selected = Vec::with_capacity(EXPECTED_ARCHIVE_TERMS);
    let counts = roster.visit_header_terms(owner as u64, |mut term| {
        if !(input_base..input_end).contains(&term.gate.left)
            || !(input_base..input_end).contains(&term.gate.right)
            || !(row_base..row_end).contains(&term.row)
        {
            return Err("retained header term escapes physical owner".into());
        }
        term.row -= row_base;
        term.gate.left -= input_base;
        term.gate.right -= input_base;
        observed = observed.checked_add(1).ok_or("callback count overflow")?;
        if selected_rows.contains(&term.row) {
            selected.push(term);
        }
        Ok(())
    }).expect("H21 owner callback");
    (counts, observed, selected)
}

#[test]
fn adjacent_h21_owners_match_pinned_shift_family() {
    let plan = WorkTreeHistoryPlan::compile(H21_HEADERS, SLOT_LOG, [0x35; 32], [0x35; 28])
        .expect("pinned H21 fixture plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("H21 DAA roster");
    let (expected, archive_rows, source_rows) = read_archive();
    assert!(!archive_rows.is_empty(), "archive row-domain filter must be nonempty");
    let source = serializer::build(None).expect("source-zero canonical serializer");
    assert_eq!(source.circuit.terms.len(), EXPECTED_SERIALIZER_TERMS,
        "source-zero serializer term count");
    let source_attached: Vec<_> = source.circuit.terms.iter()
        .filter(|term| source_rows.contains(&term.row))
        .map(|term| Term {
            row: term.row + SOURCE_ROW_OFFSET,
            gate: Gate {
                left: term.gate.left + SOURCE_INPUT_OFFSET,
                right: term.gate.right + SOURCE_INPUT_OFFSET,
                c0: term.gate.c0,
                c1: term.gate.c1,
                c2: term.gate.c2,
                c3: term.gate.c3,
            },
        })
        .collect();
    assert_eq!(source_attached.len(), EXPECTED_ARCHIVE_TERMS,
        "all source-zero terms in the archive row domain");
    assert_eq!(source_attached, expected, "archive matches source-zero serializer terms");

    for owner in [9_214usize, 9_215usize] {
        assert_eq!(roster.owner_class(owner as u64).expect("owner class"), OwnerClass::Carry,
            "native schedule class for adjacent owner {owner}");
        let (counts, observed, actual) = normalized_callback_terms(&roster, owner, &archive_rows);
        assert_eq!(observed, counts.emitted, "observed callback census for owner {owner}");
        assert_eq!(counts.emitted, EXPECTED_EMITTED, "emitted owner terms for {owner}");
        assert_eq!(counts.omitted_worktree, EXPECTED_OMITTED_WORKTREE,
            "worktree omissions for owner {owner}");
        assert_eq!(counts.omitted_mature_a4, 0, "mature A4 omissions for owner {owner}");
        assert_eq!(counts.omitted_short_a4, 0, "short A4 releases for owner {owner}");
        assert_eq!(counts.emitted + counts.omitted_worktree + counts.omitted_mature_a4
            + counts.omitted_short_a4, EXPECTED_FULL_OWNER_TERMS,
            "complete owner partition for {owner}");
        assert_eq!(actual.len(), EXPECTED_ARCHIVE_TERMS,
            "no missing or extra callback terms in the archive row domain for {owner}");
        assert_eq!(actual, expected, "ordered attached shift tuples for owner {owner}");
    }
    println!("C260_H21_SHIFT_ATTACHMENT_PASS owners=9214,9215 tuples_per_owner={EXPECTED_ARCHIVE_TERMS} archive_sha256={ARCHIVE_SHA256} callback_terms_each={EXPECTED_EMITTED} full_proof=false");
}

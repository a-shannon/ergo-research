//! Narrow H21 role-1 callback identity and owner-census falsifier.
//!
//! Source fixture: c251-shift-bit8-u-source-20261021-1, with the H21 plan and
//! deterministic fixture inputs used by `daa_history_producer_tests`.
//! This replays only the role-1 owner callback's range checks and normalization;
//! it does not build a proof or a packed witness.

use crate::{
    daa_integer::Epoch,
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    gkr::Gate,
    header_hash,
    serializer,
    short_daa_layout::Profile,
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const H21_HEADERS: u64 = 1_827_840;
const SLOT_LOG: usize = 21;
const OWNER_ROWS: usize = 1 << 19;
const OWNER_WIDTH: usize = 1 << 20;
const SERIALIZER_ROW_BASE: usize = 12_836;
const SERIALIZER_ROWS: usize = 1 << 18;
const SERIALIZER_TERMS: usize = 315_546;
const OMITTED_WORKTREE: usize = 78_194;
const FULL_OWNER_TERMS: usize = 474_755;
const PROBE_ROWS: [usize; 2] = [22_133, 22_134];

fn mapped_serializer_terms(source: &serializer::Compiled) -> Vec<Term> {
    source
        .circuit
        .terms
        .iter()
        .filter(|term| {
            term.row >= PROBE_ROWS[0] - SERIALIZER_ROW_BASE
                && term.row < PROBE_ROWS[1] + 1 - SERIALIZER_ROW_BASE
        })
        .map(|term| Term {
            row: term.row + SERIALIZER_ROW_BASE,
            gate: Gate {
                left: term.gate.left + header_hash::SERIALIZER_OFFSET,
                right: term.gate.right + header_hash::SERIALIZER_OFFSET,
                c0: term.gate.c0,
                c1: term.gate.c1,
                c2: term.gate.c2,
                c3: term.gate.c3,
            },
        })
        .collect()
}

fn normalized_callback_terms(
    roster: &DaaHistoryRoster<'_>,
    owner: usize,
    selected_rows: &[usize],
) -> (crate::daa_history_roster::HeaderCounts, usize, Vec<Term>) {
    let row_base = owner * OWNER_ROWS;
    let input_base = owner * OWNER_WIDTH;
    let local_rows = 1 << 19;
    let mut callback_terms = 0usize;
    let mut selected = Vec::new();
    let counts = roster
        .visit_header_terms(owner as u64, |mut term| {
            if !(input_base..input_base + OWNER_WIDTH).contains(&term.gate.left)
                || !(input_base..input_base + OWNER_WIDTH).contains(&term.gate.right)
                || !(row_base..row_base + local_rows).contains(&term.row)
            {
                return Err("retained header escapes owner".into());
            }
            term.row -= row_base;
            term.gate.left -= input_base;
            term.gate.right -= input_base;
            callback_terms = callback_terms
                .checked_add(1)
                .ok_or("callback term count overflow")?;
            if selected_rows.contains(&term.row) {
                selected.push(term);
            }
            Ok(())
        })
        .expect("H21 role-1 owner callback should emit");
    (counts, callback_terms, selected)
}

#[test]
fn h21_role1_callback_matches_source_tuples_and_reports_owner_census() {
    let plan = WorkTreeHistoryPlan::compile(
        H21_HEADERS,
        SLOT_LOG,
        [0x35; 32],
        [0x35; 28],
    )
    .expect("pinned H21 fixture plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("H21 DAA roster");
    let source = serializer::build(None).expect("source-zero canonical serializer");
    assert_eq!(source.circuit.row_count, SERIALIZER_ROWS);
    assert_eq!(source.circuit.terms.len(), SERIALIZER_TERMS);

    let expected = mapped_serializer_terms(&source);
    assert_eq!(expected.len(), 48, "two complete mux-byte probe rows");
    assert!(expected.iter().all(|term| PROBE_ROWS.contains(&term.row)));
    for row in PROBE_ROWS {
        assert_eq!(
            expected.iter().filter(|term| term.row == row).count(),
            24,
            "complete mux-byte probe row {row}"
        );
    }

    let owners = [
        (9_215usize, 396_561usize, 0usize, 0usize),
        (844_672, 388_369, 8_192, 0),
        (3_072, 388_369, 0, 8_192),
    ];
    for (owner, expected_emitted, expected_mature_a4, expected_short_a4) in owners {
        let class = roster.owner_class(owner as u64).expect("owner class");
        match owner {
            9_215 => assert_eq!(class, OwnerClass::Carry),
            844_672 => assert_eq!(class, OwnerClass::Mature(Epoch::Eip)),
            3_072 => assert_eq!(class, OwnerClass::Short(Profile::M2)),
            _ => unreachable!(),
        }

        let (counts, callback_terms, actual) =
            normalized_callback_terms(&roster, owner, &PROBE_ROWS);
        assert_eq!(actual, expected, "attached serializer tuples for owner {owner}");
        assert_eq!(callback_terms, counts.emitted, "role-1 callback census for owner {owner}");
        assert_eq!(counts.emitted, expected_emitted, "emitted terms for owner {owner}");
        assert_eq!(counts.omitted_worktree, OMITTED_WORKTREE, "worktree omissions for owner {owner}");
        assert_eq!(counts.omitted_mature_a4, expected_mature_a4, "mature A4 omissions for owner {owner}");
        assert_eq!(counts.omitted_short_a4, expected_short_a4, "short A4 releases for owner {owner}");
        assert_eq!(
            counts.emitted
                + counts.omitted_worktree
                + counts.omitted_mature_a4
                + counts.omitted_short_a4,
            FULL_OWNER_TERMS,
            "complete owner census for owner {owner}"
        );

        // Comparator sensitivity: retaining all three owner bases cannot match
        // the callback's normalized local tuples.
        let mut wrong_owner_offset = expected.clone();
        for term in &mut wrong_owner_offset {
            term.row += OWNER_ROWS;
            term.gate.left += OWNER_WIDTH;
            term.gate.right += OWNER_WIDTH;
        }
        assert_ne!(actual, wrong_owner_offset, "owner-offset mutant for owner {owner}");
    }

    // Comparator sensitivity: shifting one expected source row breaks the
    // ordered tuple identity at the serializer-to-header boundary.
    let (_, _, actual) = normalized_callback_terms(&roster, 9_215, &PROBE_ROWS);
    let mut wrong_source_attachment = expected.clone();
    wrong_source_attachment[0].row -= 1;
    assert_ne!(actual, wrong_source_attachment);

    println!(
        "C254_H21_ROLE1_SHIFT_CALLBACK_PASS fixture=h21(n=1827840,slot_log=21,root=35x32,tag=35x28) serializer_terms={SERIALIZER_TERMS} probe_rows={:?} probe_terms={} ordinary=9215:396561/0/0 mature=844672:388369/8192/0 short=3072:388369/0/8192 full_owner_terms={FULL_OWNER_TERMS} full_proof=false",
        PROBE_ROWS,
        expected.len(),
    );
}

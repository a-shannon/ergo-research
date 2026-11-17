//! Direct tests for the fixed native DAA owner roster.
use crate::{
    daa_header_window::{self, Action},
    daa_history_roster::{
        validate_a4_identity, Counts, DaaHistoryRoster, OwnerClass, LOCAL_INPUT_LOG, LOCAL_ROW_LOG,
        SLOT_ROW_LOG, WIDTH,
    },
    daa_integer::Epoch,
    daa_one_ratio_finish,
    gkr::Gate,
    short_daa_layout::Profile,
    sparse::Term,
    transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};
use std::sync::OnceLock;

const OWNER_ROWS: usize = 1 << SLOT_ROW_LOG;

fn large_parent() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(844_801, 20, [0x35; 32], [0x35; 28]).unwrap())
}

fn large_roster() -> DaaHistoryRoster<'static> {
    DaaHistoryRoster::compile(large_parent()).unwrap()
}

fn field_point(bits: usize, seed: u64) -> Vec<Fr> {
    (0..bits)
        .map(|i| Fr::from(seed + 17 * (i as u64 + 1)))
        .collect()
}

fn set_index(point: &mut [Fr], start: usize, width: usize, index: usize) {
    for bit in 0..width {
        point[start + bit] = Fr::from(((index >> bit) & 1) as u64);
    }
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |acc, (bit, value)| {
            acc * if index >> bit & 1 == 1 {
                *value
            } else {
                Fr::one() - value
            }
        })
}

fn joint_owner_delta(r: &[Fr], u: &[Fr], v: &[Fr], slot: usize) -> Fr {
    eq_index(&r[SLOT_ROW_LOG..], slot)
        * eq_index(&u[LOCAL_INPUT_LOG..], slot)
        * eq_index(&v[LOCAL_INPUT_LOG..], slot)
}

fn all_joint_owner_delta(r: &[Fr], u: &[Fr], v: &[Fr]) -> Fr {
    (0..r.len() - SLOT_ROW_LOG).fold(Fr::one(), |acc, bit| {
        acc * ((Fr::one() - r[SLOT_ROW_LOG + bit])
            * (Fr::one() - u[LOCAL_INPUT_LOG + bit])
            * (Fr::one() - v[LOCAL_INPUT_LOG + bit])
            + r[SLOT_ROW_LOG + bit] * u[LOCAL_INPUT_LOG + bit] * v[LOCAL_INPUT_LOG + bit])
    })
}

fn direct_terms(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for term in terms {
        let gate = &term.gate;
        let weight = eq_index(r, term.row) * eq_index(u, gate.left) * eq_index(v, gate.right);
        out[0] += weight * gate.c0;
        out[1] += weight * gate.c1;
        out[2] += weight * gate.c2;
        out[3] += weight * gate.c3;
    }
    out
}

fn owner_terms(roster: &DaaHistoryRoster<'_>, slot: u64) -> (Counts, Vec<Term>) {
    let mut terms = Vec::new();
    let counts = roster
        .visit_owner_terms(slot, |term| {
            terms.push(term);
            Ok(())
        })
        .unwrap();
    (counts, terms)
}

fn fixture_input_values(
    headers: &std::collections::HashMap<u32, Vec<u8>>,
) -> std::collections::BTreeMap<usize, Fr> {
    let serializer = crate::serializer::build(None).unwrap();
    let mut values = std::collections::BTreeMap::new();
    for (height, raw) in headers {
        let header = ergo_header_core::Header::decode(raw, None).unwrap();
        let fields = crate::serializer::Fields::from_header(&header).unwrap();
        let assignment = serializer.assign(&fields);
        let wires = serializer
            .layout
            .fields
            .n_bits
            .iter()
            .chain(&serializer.layout.fields.timestamp)
            .chain(&serializer.layout.fields.height);
        for &wire in wires {
            values.insert(
                (*height as usize - 1) * WIDTH + crate::header_hash::SERIALIZER_OFFSET + wire,
                assignment[wire],
            );
        }
    }
    values
}

fn owner_residuals(
    roster: &DaaHistoryRoster<'_>,
    slot: u64,
    witness: &[Fr],
    external: &std::collections::BTreeMap<usize, Fr>,
) -> [std::collections::BTreeMap<usize, Fr>; 4] {
    let base = slot as usize * WIDTH;
    let mut residuals: [std::collections::BTreeMap<usize, Fr>; 4] =
        std::array::from_fn(|_| std::collections::BTreeMap::new());
    let (_, terms) = owner_terms(roster, slot);
    for term in terms {
        let lane = (term.row >> LOCAL_ROW_LOG) & 3;
        let row = term.row & ((1 << LOCAL_ROW_LOG) - 1);
        if lane == 1 {
            assert!(
                external.contains_key(&term.gate.left),
                "missing RAW alias source {}",
                term.gate.left
            );
        }
        let value = |wire: usize| {
            if let Some(value) = external.get(&wire) {
                *value
            } else if (base..base + witness.len()).contains(&wire) {
                witness[wire - base]
            } else {
                external.get(&wire).copied().unwrap_or_else(Fr::zero)
            }
        };
        let x = value(term.gate.left);
        let y = value(term.gate.right);
        *residuals[lane].entry(row).or_insert_with(Fr::zero) +=
            term.gate.c0 + term.gate.c1 * x + term.gate.c2 * y + term.gate.c3 * x * y;
    }
    residuals
}

fn assert_raw_alias_fault(
    roster: &DaaHistoryRoster<'_>,
    slot: u64,
    witness: &[Fr],
    external: &std::collections::BTreeMap<usize, Fr>,
) {
    let mut source = None;
    roster
        .visit_owner_terms(slot, |term| {
            if source.is_none() && ((term.row >> LOCAL_ROW_LOG) & 3) == 1 {
                assert!(external.contains_key(&term.gate.left));
                source = Some(term.gate.left);
            }
            Ok(())
        })
        .unwrap();
    let source = source.expect("real imported RAW bit");
    let mut fault = external.clone();
    fault.insert(source, Fr::one() - external[&source]);
    let rows = owner_residuals(roster, slot, witness, &fault);
    for (lane, residuals) in rows.iter().enumerate() {
        if lane == 1 {
            assert!(residuals.values().any(|value| !value.is_zero()));
        } else {
            assert!(
                residuals.values().all(|value| value.is_zero()),
                "alias fault escaped lane {lane}"
            );
        }
    }
}

#[test]
fn native_owner_frontiers_cover_all_roster_roles_and_padding() {
    let roster = large_roster();
    let cases = [
        (0, OwnerClass::Genesis),
        (1, OwnerClass::Initial),
        (2, OwnerClass::Carry),
        (1024, OwnerClass::Singleton),
        (1023, OwnerClass::Carry),
        (1025, OwnerClass::Carry),
        (2048, OwnerClass::M1),
        (2047, OwnerClass::Carry),
        (2049, OwnerClass::Carry),
        (3072, OwnerClass::Short(Profile::M2)),
        (3071, OwnerClass::Carry),
        (3073, OwnerClass::Carry),
        (4096, OwnerClass::Short(Profile::M3)),
        (5120, OwnerClass::Short(Profile::M4)),
        (6144, OwnerClass::Short(Profile::M5)),
        (7168, OwnerClass::Short(Profile::M6)),
        (8192, OwnerClass::Short(Profile::M7)),
        (9216, OwnerClass::Mature(Epoch::Legacy)),
        (417791, OwnerClass::FixedV2),
        (417792, OwnerClass::FixedV2),
        (417790, OwnerClass::Carry),
        (417793, OwnerClass::Carry),
        (844672, OwnerClass::Mature(Epoch::Eip)),
        (844671, OwnerClass::Carry),
        (844673, OwnerClass::Carry),
        (844800, OwnerClass::Mature(Epoch::Eip)),
        (844799, OwnerClass::Carry),
        (844801, OwnerClass::Padding),
        ((1 << 20) - 1, OwnerClass::Padding),
    ];
    for (slot, expected) in cases {
        assert_eq!(roster.owner_class(slot).unwrap(), expected, "slot {slot}");
    }
    assert!(roster
        .owner_class(1 << 20)
        .unwrap_err()
        .contains("outside slot domain"));
    let clipped = WorkTreeHistoryPlan::compile(3072, 12, [0x35; 32], [0x35; 28]).unwrap();
    let clipped_roster = DaaHistoryRoster::compile(&clipped).unwrap();
    assert_eq!(clipped_roster.owner_class(3071).unwrap(), OwnerClass::Carry);
    assert_eq!(
        clipped_roster.owner_class(3072).unwrap(),
        OwnerClass::Padding
    );
}

#[test]
fn fixed_lane_census_has_only_the_native_owner_and_preserves_padding_rows() {
    let roster = large_roster();
    for (slot, class) in [
        (2, OwnerClass::Carry),
        (1024, OwnerClass::Singleton),
        (2048, OwnerClass::M1),
        (3072, OwnerClass::Short(Profile::M2)),
        (9216, OwnerClass::Mature(Epoch::Legacy)),
        (844801, OwnerClass::Padding),
    ] {
        assert_eq!(roster.owner_class(slot).unwrap(), class);
        let (counts, terms) = owner_terms(&roster, slot);
        assert!(terms.iter().all(|t| t.row >> SLOT_ROW_LOG == slot as usize));
        assert!(terms
            .iter()
            .all(|t| t.gate.left < 1usize << roster.input_log()
                && t.gate.right < 1usize << roster.input_log()));
        if matches!(
            class,
            OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_)
        ) {
            assert!(counts.lanes[0] > 0, "native arithmetic lane at slot {slot}");
            assert!(counts.lanes[1] > 0, "native alias lane at slot {slot}");
            if slot == 2048 {
                assert_eq!(counts.lanes[3], 73728);
            } else {
                assert_eq!(counts.lanes[3], 0);
            }
        } else {
            assert_eq!(counts.lanes[0..2], [0, 0]);
            assert_eq!(counts.lanes[3], 81920, "full unused union at slot {slot}");
        }
    }
    for (slot, expected) in [
        (0u64, 0usize),
        (1, 225),
        (2, 448),
        (1024, 448),
        (417791, 225),
        (844801, 0),
    ] {
        assert_eq!(
            owner_terms(&roster, slot).0.lanes[2],
            expected,
            "numeric lane at {slot}"
        );
    }
    assert_eq!(owner_terms(&roster, 3072).0.lanes[2], 0);
}

#[test]
fn analytic_four_lane_coefficients_match_emitted_sparse_terms_at_asymmetric_points() {
    // M1 is the only active alias family in this clipped history. Distinct
    // non-Boolean owner axes exercise the full extension, not its endpoints.
    let clipped = WorkTreeHistoryPlan::compile(2049, 12, [0x35; 32], [0x35; 28]).unwrap();
    let m1 = DaaHistoryRoster::compile(&clipped).unwrap();
    let mut r = field_point(m1.row_log(), 1201);
    let u = field_point(m1.input_log(), 1301);
    let v = field_point(m1.input_log(), 1409);
    set_index(&mut r, LOCAL_ROW_LOG, 2, 1);
    let aliases: Vec<_> = owner_terms(&m1, 2048)
        .1
        .into_iter()
        .filter(|t| ((t.row >> LOCAL_ROW_LOG) & 3) == 1)
        .collect();
    assert_eq!(aliases.len(), 192);
    let expected = direct_terms(&aliases, &r, &u, &v);
    assert!(expected.iter().any(|value| !value.is_zero()));
    assert_eq!(m1.coefficients(&r, &u, &v).unwrap(), expected);

    let roster = large_roster();
    let cases = [
        (2u64, 2usize),
        (1024, 2),
        (2048, 0),
        (3072, 0),
        (9216, 0),
        (844801, 3),
    ];
    for (case_index, (slot, lane)) in cases.into_iter().enumerate() {
        let (_, terms) = owner_terms(&roster, slot);
        let mut r = field_point(roster.row_log(), 3 + case_index as u64);
        let mut u = field_point(roster.input_log(), 19 + case_index as u64);
        let mut v = field_point(roster.input_log(), 71 + case_index as u64);
        set_index(&mut r, LOCAL_ROW_LOG, 2, lane);
        set_index(&mut r, SLOT_ROW_LOG, roster.slot_log(), slot as usize);
        set_index(&mut u, LOCAL_INPUT_LOG, roster.slot_log(), slot as usize);
        set_index(&mut v, LOCAL_INPUT_LOG, roster.slot_log(), slot as usize);
        let owner_lane: Vec<_> = terms
            .into_iter()
            .filter(|t| ((t.row >> LOCAL_ROW_LOG) & 3) == lane)
            .collect();
        let expected = direct_terms(&owner_lane, &r, &u, &v);
        assert_eq!(
            roster.coefficients(&r, &u, &v).unwrap(),
            expected,
            "slot {slot}, lane {lane}"
        );
    }

    // Lane 1 aliases bind each imported source owner to the owning slot.
    // Evaluate each source-owner slice independently so the high axes differ.
    for (case_index, slot) in [2048u64, 3072, 9216, 844672].into_iter().enumerate() {
        let (_, terms) = owner_terms(&roster, slot);
        let aliases: Vec<_> = terms
            .into_iter()
            .filter(|t| ((t.row >> LOCAL_ROW_LOG) & 3) == 1)
            .collect();
        let mut sources = std::collections::BTreeSet::new();
        for term in &aliases {
            sources.insert(term.gate.left / WIDTH);
        }
        for source in sources {
            let selected: Vec<_> = aliases
                .iter()
                .filter(|t| t.gate.left / WIDTH == source)
                .cloned()
                .collect();
            if selected.is_empty() {
                continue;
            }
            let mut r = field_point(roster.row_log(), 101 + case_index as u64);
            let mut u = field_point(roster.input_log(), 151 + case_index as u64);
            let mut v = field_point(roster.input_log(), 211 + case_index as u64);
            set_index(&mut r, LOCAL_ROW_LOG, 2, 1);
            set_index(&mut r, SLOT_ROW_LOG, roster.slot_log(), slot as usize);
            set_index(&mut u, LOCAL_INPUT_LOG, roster.slot_log(), source);
            set_index(&mut v, LOCAL_INPUT_LOG, roster.slot_log(), slot as usize);
            assert_eq!(
                roster.coefficients(&r, &u, &v).unwrap(),
                direct_terms(&selected, &r, &u, &v),
                "alias source owner {source}, target {slot}"
            );
        }
    }
}

#[test]
fn h21_mature_eip_alias_coefficients_match_unplaced_terms_for_each_source_owner() {
    // This is the H21/S21 history geometry, without a frame or a placed ROW19
    // adapter. The coefficient oracle is the roster's own unplaced DAA stream.
    const OWNER: usize = 844_672;
    const FOREIGN_SOURCE: usize = 843_647;
    let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x35; 32], [0x35; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&parent).unwrap();
    assert_eq!(
        roster.owner_class(OWNER as u64).unwrap(),
        OwnerClass::Mature(Epoch::Eip)
    );
    assert_eq!((roster.row_log(), roster.input_log()), (40, 41));

    let (counts, terms) = owner_terms(&roster, OWNER as u64);
    let aliases: Vec<_> = terms
        .into_iter()
        .filter(|term| ((term.row >> LOCAL_ROW_LOG) & 3) == 1)
        .collect();
    assert_eq!(counts.lanes[1], 896);
    assert_eq!(aliases.len(), counts.lanes[1]);
    let sources: std::collections::BTreeSet<_> =
        aliases.iter().map(|term| term.gate.left / WIDTH).collect();
    assert!(sources.contains(&FOREIGN_SOURCE));
    assert!(sources.len() > 1);
    assert!(aliases.iter().all(|term| {
        term.row >> SLOT_ROW_LOG == OWNER
            && term.gate.right / WIDTH == OWNER
            && term.gate.c0.is_zero()
            && term.gate.c1 == Fr::one()
            && term.gate.c2 == -Fr::one()
            && term.gate.c3.is_zero()
    }));

    // Fix only the lane and three owner axes. The local row and input axes
    // remain distinct, non-Boolean field points for a full MLE differential.
    for (case, source) in sources.iter().copied().enumerate() {
        let selected: Vec<_> = aliases
            .iter()
            .filter(|term| term.gate.left / WIDTH == source)
            .cloned()
            .collect();
        assert!(!selected.is_empty(), "source {source} has no emitted alias");
        let mut r = field_point(roster.row_log(), 1_901 + case as u64);
        let mut u = field_point(roster.input_log(), 2_303 + case as u64);
        let mut v = field_point(roster.input_log(), 2_909 + case as u64);
        set_index(&mut r, LOCAL_ROW_LOG, 2, 1);
        set_index(&mut r, SLOT_ROW_LOG, roster.slot_log(), OWNER);
        set_index(&mut u, LOCAL_INPUT_LOG, roster.slot_log(), source);
        set_index(&mut v, LOCAL_INPUT_LOG, roster.slot_log(), OWNER);
        let emitted = direct_terms(&selected, &r, &u, &v);
        assert!(!emitted[1].is_zero(), "source {source} oracle is vacuous");
        assert_eq!(emitted, direct_terms(&aliases, &r, &u, &v));
        assert_eq!(
            roster.coefficients(&r, &u, &v).unwrap(),
            emitted,
            "H21 mature EIP alias source {source} to owner {OWNER}"
        );
    }

    // A Boolean point selects exactly one foreign-source alias occurrence.
    // Single-fault changes to its source, destination, local wire, row,
    // coefficient, or presence must disagree with the analytic coefficient.
    let index = aliases
        .iter()
        .position(|term| term.gate.left / WIDTH == FOREIGN_SOURCE)
        .unwrap();
    let first = &aliases[index];
    let mut r = vec![Fr::zero(); roster.row_log()];
    let mut u = vec![Fr::zero(); roster.input_log()];
    let mut v = vec![Fr::zero(); roster.input_log()];
    set_index(&mut r, 0, roster.row_log(), first.row);
    set_index(&mut u, 0, roster.input_log(), first.gate.left);
    set_index(&mut v, 0, roster.input_log(), first.gate.right);
    let expected = [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()];
    assert_eq!(direct_terms(&aliases, &r, &u, &v), expected);
    assert_eq!(roster.coefficients(&r, &u, &v).unwrap(), expected);

    let loses_selected_term = |name: &str, mutate: fn(&mut Term)| {
        let mut changed = aliases.clone();
        mutate(&mut changed[index]);
        assert_eq!(
            direct_terms(&changed, &r, &u, &v),
            [Fr::zero(); 4],
            "{name} mutant retained its selected alias"
        );
    };
    loses_selected_term("source owner", |term| term.gate.left += WIDTH);
    loses_selected_term("destination owner", |term| term.gate.right += WIDTH);
    loses_selected_term("destination alias wire", |term| term.gate.right ^= 1);
    loses_selected_term("alias row", |term| term.row ^= 1);

    let mut changed = aliases.clone();
    changed[index].gate.c2 = Fr::one();
    assert_eq!(
        direct_terms(&changed, &r, &u, &v),
        [Fr::zero(), Fr::one(), Fr::one(), Fr::zero()],
        "alias sign mutant must change one coefficient"
    );
    let mut omitted = aliases;
    omitted.remove(index);
    assert_eq!(direct_terms(&omitted, &r, &u, &v), [Fr::zero(); 4]);
}

#[test]
fn inactive_joint_mask_matches_finite_nonboolean_owner_enumeration() {
    let parent = WorkTreeHistoryPlan::compile(3, 2, [7; 32], [0x35; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&parent).unwrap();
    let mut r = field_point(roster.row_log(), 5);
    let mut u = field_point(roster.input_log(), 31);
    let mut v = field_point(roster.input_log(), 89);
    set_index(&mut r, LOCAL_ROW_LOG, 2, 3);
    // Distinct non-Boolean high axes force the same-owner three-way product.
    for (bit, values) in [
        (0usize, [Fr::from(2u64), Fr::from(3u64), Fr::from(5u64)]),
        (1, [Fr::from(7u64), Fr::from(11u64), Fr::from(13u64)]),
    ] {
        r[SLOT_ROW_LOG + bit] = values[0];
        u[LOCAL_INPUT_LOG + bit] = values[1];
        v[LOCAL_INPUT_LOG + bit] = values[2];
    }
    let mut emitted = Vec::new();
    for slot in 0..4 {
        let (_, terms) = owner_terms(&roster, slot);
        emitted.extend(
            terms
                .into_iter()
                .filter(|t| ((t.row >> LOCAL_ROW_LOG) & 3) == 3),
        );
    }
    assert_eq!(
        roster.coefficients(&r, &u, &v).unwrap(),
        direct_terms(&emitted, &r, &u, &v)
    );

    // At production N, enumerate actual Retarget owners and subtract their
    // deltas from the complete owner partition. The remaining full-zero
    // template and M1-complement template are evaluated independently.
    let roster = large_roster();
    let mut r = field_point(roster.row_log(), 313);
    let mut u = field_point(roster.input_log(), 419);
    let mut v = field_point(roster.input_log(), 523);
    set_index(&mut r, LOCAL_ROW_LOG, 2, 3);
    for bit in 0..roster.slot_log() {
        r[SLOT_ROW_LOG + bit] = Fr::from((2 + bit as u64 * 3) as u64);
        u[LOCAL_INPUT_LOG + bit] = Fr::from((5 + bit as u64 * 7) as u64);
        v[LOCAL_INPUT_LOG + bit] = Fr::from((11 + bit as u64 * 13) as u64);
    }
    let mut omitted = joint_owner_delta(&r, &u, &v, 2048);
    for short in [3072usize, 4096, 5120, 6144, 7168, 8192] {
        omitted += joint_owner_delta(&r, &u, &v, short);
    }
    let mut retargeted = Fr::zero();
    for slot in (9216usize..844672).step_by(1024) {
        if slot != 417792 {
            retargeted += joint_owner_delta(&r, &u, &v, slot);
        }
    }
    for slot in (844672usize..844801).step_by(128) {
        retargeted += joint_owner_delta(&r, &u, &v, slot);
    }
    omitted += retargeted;
    let full_mask = all_joint_owner_delta(&r, &u, &v) - omitted;
    let m1_delta = joint_owner_delta(&r, &u, &v, 2048);

    let (_, full_terms) = owner_terms(&roster, 0);
    let (_, m1_terms) = owner_terms(&roster, 2048);
    let bank_contains = |wire: usize| {
        [
            (663552, 671744),
            (688128, 720896),
            (819200, 851968),
            (991232, 999424),
        ]
        .iter()
        .any(|(start, end)| (*start..*end).contains(&wire))
    };
    assert!(full_terms
        .iter()
        .filter(|t| (t.row >> LOCAL_ROW_LOG) & 3 == 3)
        .all(|t| bank_contains(t.gate.left % WIDTH)
            && (t.gate.right % WIDTH == 0 || bank_contains(t.gate.right % WIDTH))));
    assert!(m1_terms
        .iter()
        .filter(|t| (t.row >> LOCAL_ROW_LOG) & 3 == 3)
        .all(|t| !(819200..827392).contains(&(t.gate.left % WIDTH))));
    let localize = |terms: Vec<Term>| {
        terms
            .into_iter()
            .filter(|t| ((t.row >> LOCAL_ROW_LOG) & 3) == 3)
            .map(|t| Term {
                row: t.row % (1 << LOCAL_ROW_LOG),
                gate: Gate {
                    left: t.gate.left % WIDTH,
                    right: t.gate.right % WIDTH,
                    ..t.gate
                },
            })
            .collect::<Vec<_>>()
    };
    let local_r = &r[..LOCAL_ROW_LOG];
    let local_u = &u[..LOCAL_INPUT_LOG];
    let local_v = &v[..LOCAL_INPUT_LOG];
    let full_local = direct_terms(&localize(full_terms), local_r, local_u, local_v)[1];
    let m1_complement_local = direct_terms(&localize(m1_terms), local_r, local_u, local_v)[1];
    let expected = full_local * full_mask + m1_complement_local * m1_delta;
    assert!(!expected.is_zero(), "inactive oracle must not be vacuous");
    assert_eq!(roster.coefficients(&r, &u, &v).unwrap()[1], expected);

    // Independent complete-domain oracle: numeric GLOBAL0/previous owners,
    // inactive padding, and all four tags mix at non-Boolean high points.
    for n in [3u64, 4] {
        let parent = WorkTreeHistoryPlan::compile(n, 2, [7; 32], [0x35; 28]).unwrap();
        let small = DaaHistoryRoster::compile(&parent).unwrap();
        let r = field_point(small.row_log(), 607);
        let u = field_point(small.input_log(), 701);
        let v = field_point(small.input_log(), 809);
        let mut terms = Vec::new();
        for slot in 0..4 {
            terms.extend(owner_terms(&small, slot).1);
        }
        let expected = direct_terms(&terms, &r, &u, &v);
        assert!(expected.iter().any(|value| !value.is_zero()));
        assert_eq!(
            small.coefficients(&r, &u, &v).unwrap(),
            expected,
            "whole N{n} relation"
        );
    }
}

#[test]
fn short_header_wrapper_removes_exactly_the_m2_to_m7_a4_anchors() {
    let roster = large_roster();
    let parent = large_parent();
    for slot in [
        2048u64, 3071, 3072, 3073, 4096, 5120, 6144, 7168, 8192, 9216, 417791, 417792, 844672,
        844801,
    ] {
        let base = slot as usize * (1usize << SLOT_ROW_LOG);
        let mut old = Vec::new();
        let old_counts = parent
            .visit_slot_terms(slot, |term| {
                old.push(term);
                Ok(())
            })
            .unwrap();
        let mut actual = Vec::new();
        let counts = roster
            .visit_header_terms(slot, |term| {
                actual.push(term);
                Ok(())
            })
            .unwrap();
        let is_short = (3072..=8192).contains(&slot) && slot % 1024 == 0;
        assert_eq!(counts.omitted_short_a4, if is_short { 8192 } else { 0 });
        assert_eq!(counts.omitted_mature_a4, old_counts.omitted_a4);
        let expected: Vec<_> = old
            .into_iter()
            .filter(|term| {
                let local = term.row - base;
                !(is_short
                    && (348440..356632).contains(&local)
                    && term.gate.left >= slot as usize * WIDTH + 991232
                    && term.gate.left < slot as usize * WIDTH + 999424
                    && term.gate.right == slot as usize * WIDTH)
            })
            .collect();
        assert_eq!(actual, expected, "header owner slot {slot}");
        assert_eq!(counts.emitted, actual.len());
    }
    let anchor = parent
        .header_boundary()
        .canonical_circuit()
        .terms
        .iter()
        .find(|t| t.row == 348440)
        .unwrap()
        .clone();
    validate_a4_identity(&anchor, 0, 0, 0).unwrap();
    for mutate in 0..7 {
        let mut bad = anchor.clone();
        match mutate {
            0 => bad.row += 1,
            1 => bad.gate.left += 1,
            2 => bad.gate.right += 1,
            3 => bad.gate.c0 = Fr::one(),
            4 => bad.gate.c1 = Fr::zero(),
            5 => bad.gate.c2 = Fr::one(),
            _ => bad.gate.c3 = Fr::one(),
        }
        assert!(
            validate_a4_identity(&bad, 0, 0, 0).is_err(),
            "A4 mutation {mutate}"
        );
    }
    assert!(validate_a4_identity(&anchor, 0, 0, 8192)
        .unwrap_err()
        .contains("outside range"));
    assert!(validate_a4_identity(&anchor, usize::MAX, 0, 0).is_err());
    assert!(validate_a4_identity(&anchor, 0, usize::MAX, 0).is_err());
}

#[test]
fn header_coefficients_match_the_direct_boolean_sparse_stream() {
    let roster = large_roster();
    for slot in [2048usize, 3072, 9216, 844801] {
        let mut terms = Vec::new();
        roster
            .visit_header_terms(slot as u64, |term| {
                terms.push(term);
                Ok(())
            })
            .unwrap();
        let r_index = slot * (1usize << SLOT_ROW_LOG) + 348441;
        let u_index = slot * WIDTH + 991233;
        let v_index = slot * WIDTH;
        let mut r = vec![Fr::zero(); SLOT_ROW_LOG + roster.slot_log()];
        let mut u = vec![Fr::zero(); roster.input_log()];
        let mut v = vec![Fr::zero(); roster.input_log()];
        let r_len = r.len();
        let u_len = u.len();
        let v_len = v.len();
        set_index(&mut r, 0, r_len, r_index);
        set_index(&mut u, 0, u_len, u_index);
        set_index(&mut v, 0, v_len, v_index);
        assert_eq!(
            roster.header_coefficients(&r, &u, &v).unwrap(),
            direct_terms(&terms, &r, &u, &v)
        );
    }
    let r = field_point(SLOT_ROW_LOG + roster.slot_log(), 907);
    let u = field_point(roster.input_log(), 1009);
    let v = field_point(roster.input_log(), 1103);
    let anchors: Vec<_> = (0..8192)
        .map(|i| Term {
            row: 348440 + i,
            gate: Gate {
                left: 991232 + i,
                right: 0,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        })
        .collect();
    let local = direct_terms(
        &anchors,
        &r[..SLOT_ROW_LOG],
        &u[..LOCAL_INPUT_LOG],
        &v[..LOCAL_INPUT_LOG],
    )[1];
    let owners =
        [3072usize, 4096, 5120, 6144, 7168, 8192]
            .into_iter()
            .fold(Fr::zero(), |sum, slot| {
                sum + eq_index(&r[SLOT_ROW_LOG..], slot)
                    * eq_index(&u[LOCAL_INPUT_LOG..], slot)
                    * eq_index(&v[LOCAL_INPUT_LOG..], slot)
            });
    let expected = local * owners;
    assert!(!expected.is_zero());
    let before = large_parent().coefficients(&r, &u, &v).unwrap();
    let after = roster.header_coefficients(&r, &u, &v).unwrap();
    for plane in 0..4 {
        assert_eq!(
            before[plane] - after[plane],
            if plane == 1 { expected } else { Fr::zero() }
        );
    }
}

#[test]
fn transcript_binding_changes_with_admitted_history_size() {
    let a = WorkTreeHistoryPlan::compile(2049, 12, [0x51; 32], [0x35; 28]).unwrap();
    let b = WorkTreeHistoryPlan::compile(2050, 12, [0x51; 32], [0x35; 28]).unwrap();
    let ra = DaaHistoryRoster::compile(&a).unwrap();
    let rb = DaaHistoryRoster::compile(&b).unwrap();
    let mut ta = Transcript::new(b"roster-binding-test");
    let mut tb = Transcript::new(b"roster-binding-test");
    ra.bind(&mut ta);
    rb.bind(&mut tb);
    assert_ne!(ta.challenge_scalar(b"join"), tb.challenge_scalar(b"join"));
    assert_eq!(ra.owner_class(2048).unwrap(), OwnerClass::M1);
    assert_eq!(rb.owner_class(2048).unwrap(), OwnerClass::M1);
    let changed = WorkTreeHistoryPlan::compile(2049, 12, [0x52; 32], [0x35; 28]).unwrap();
    let rc = DaaHistoryRoster::compile(&changed).unwrap();
    let mut unchanged = Transcript::new(b"roster-binding-test");
    let mut altered = Transcript::new(b"roster-binding-test");
    ra.bind(&mut unchanged);
    rc.bind(&mut altered);
    assert_ne!(
        unchanged.challenge_scalar(b"join"),
        altered.challenge_scalar(b"join")
    );
    // All three point dimensions and both streaming sinks fail closed.
    let bad_r = vec![Fr::zero(); ra.row_log() - 1];
    let good_u = vec![Fr::zero(); ra.input_log()];
    let good_v = vec![Fr::zero(); ra.input_log()];
    assert!(ra
        .coefficients(&bad_r, &good_u, &good_v)
        .unwrap_err()
        .contains("point dimensions"));
    let good_r = vec![Fr::zero(); ra.row_log()];
    assert!(ra
        .coefficients(&good_r, &good_u[..good_u.len() - 1], &good_v)
        .unwrap_err()
        .contains("point dimensions"));
    assert!(ra
        .coefficients(&good_r, &good_u, &good_v[..good_v.len() - 1])
        .unwrap_err()
        .contains("point dimensions"));
    assert!(ra
        .header_coefficients(&bad_r, &good_u, &good_v)
        .unwrap_err()
        .contains("header point dimensions"));
    assert!(ra.header_coefficients(&good_r, &good_u, &good_v).is_ok());
    assert!(ra
        .header_coefficients(&good_r, &good_u[..good_u.len() - 1], &good_v)
        .unwrap_err()
        .contains("header point dimensions"));
    assert!(ra
        .header_coefficients(&good_r, &good_u, &good_v[..good_v.len() - 1])
        .unwrap_err()
        .contains("header point dimensions"));
    let mut calls = 0;
    assert_eq!(
        ra.visit_owner_terms(2, |_| {
            calls += 1;
            Err("sink fault".into())
        })
        .unwrap_err(),
        "sink fault"
    );
    assert_eq!(calls, 1);
    let mut header_calls = 0;
    assert_eq!(
        ra.visit_header_terms(2, |_| {
            header_calls += 1;
            Err("header sink fault".into())
        })
        .unwrap_err(),
        "header sink fault"
    );
    assert_eq!(header_calls, 1);
    let mut bad_slot_calls = 0;
    assert!(ra
        .visit_owner_terms(4096, |_| {
            bad_slot_calls += 1;
            Ok(())
        })
        .is_err());
    assert_eq!(bad_slot_calls, 0);
}

fn decode_hex(s: &str) -> Vec<u8> {
    s.as_bytes()
        .chunks_exact(2)
        .map(|b| u8::from_str_radix(std::str::from_utf8(b).unwrap(), 16).unwrap())
        .collect()
}

fn fixture_headers() -> std::collections::HashMap<u32, Vec<u8>> {
    let value: serde_json::Value =
        serde_json::from_str(include_str!("../fixtures/mainnet-daa-windows-v1.json")).unwrap();
    assert_eq!(
        value["source_frame"]["sha256"].as_str(),
        Some("A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E")
    );
    value["headers"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| {
            (
                h["height"].as_u64().unwrap() as u32,
                decode_hex(h["raw_hex"].as_str().unwrap()),
            )
        })
        .collect()
}

fn actual_child_raw(height: u32) -> Option<Vec<u8>> {
    match height {
        3073 => {
            return Some(decode_hex(
                serde_json::from_str::<serde_json::Value>(include_str!(
                    "../fixtures/mainnet-daa-child-3073-v1.json"
                ))
                .unwrap()["raw_hex"]
                    .as_str()
                    .unwrap(),
            ))
        }
        4097 => Some(include_bytes!("../fixtures/mainnet-daa-child-4097-v1.raw.bin").to_vec()),
        5121 => Some(include_bytes!("../fixtures/mainnet-daa-child-5121-v1.raw.bin").to_vec()),
        6145 => Some(include_bytes!("../fixtures/mainnet-daa-child-6145-v1.raw.bin").to_vec()),
        7169 => Some(include_bytes!("../fixtures/mainnet-daa-child-7169-v1.raw.bin").to_vec()),
        _ => None,
    }
}
fn blake2b256(bytes: &[u8]) -> String {
    Blake2b::<U32>::digest(bytes)
        .iter()
        .map(|b| format!("{b:02X}"))
        .collect()
}

fn put_bits(
    values: &mut std::collections::BTreeMap<usize, Fr>,
    wires: &[usize],
    value: &num_bigint::BigUint,
) {
    for (bit, wire) in wires.iter().enumerate() {
        values.insert(*wire, Fr::from(value.bit(bit as u64) as u64));
    }
}

fn work_residuals(
    boundary: &crate::work_tree_work::Boundary,
    slot: usize,
    values: &std::collections::BTreeMap<usize, Fr>,
) -> Vec<usize> {
    let mut rows = vec![Fr::zero(); crate::work_tree_work::LOCAL_ROW_WIDTH];
    boundary
        .emit_slot(slot, |term| {
            let x = values
                .get(&(term.gate.left % WIDTH))
                .copied()
                .unwrap_or_else(Fr::zero);
            let y = values
                .get(&(term.gate.right % WIDTH))
                .copied()
                .unwrap_or_else(Fr::zero);
            rows[term.row % crate::work_tree_work::LOCAL_ROW_WIDTH] +=
                term.gate.c0 + term.gate.c1 * x + term.gate.c2 * y + term.gate.c3 * x * y;
        })
        .unwrap();
    rows.iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect()
}

#[test]
fn raw_child_producers_admit_only_at_their_fixed_short_m1_and_mature_owners() {
    use crate::{
        daa_count, daa_finish, daa_header_window,
        daa_integer::{self, Epoch},
        short_daa_layout::Profile as ShortProfile,
    };
    use ergo_header_core::Header;
    let roster = large_roster();
    let mut headers = fixture_headers();
    for height in [3073, 4097, 5121, 6145, 7169] {
        headers.insert(height, actual_child_raw(height).unwrap());
    }
    let fixture_values = fixture_input_values(&headers);
    let decode = |raw: &[u8]| Header::decode(raw, None).unwrap();

    // M1's two actual Legacy endpoints and the child are decoded from the pinned window fixture.
    let h0 = decode(headers.get(&1024).unwrap());
    let h1 = decode(headers.get(&2048).unwrap());
    let child = decode(headers.get(&2049).unwrap());
    let parent_id: [u8; 32] = Blake2b::<U32>::digest(headers.get(&2048).unwrap()).into();
    assert_eq!(child.parent_id, parent_id);
    let m1 = daa_one_ratio_finish::compile(
        &daa_count::q(),
        daa_integer::Inputs {
            nbits: h1.n_bits,
            start_timestamp: h0.timestamp,
            end_timestamp: h1.timestamp,
        },
        child.n_bits,
        true,
    )
    .unwrap();
    let mapped = roster.admit_one(&m1).unwrap();
    let (m1_counts, m1_terms) = owner_terms(&roster, 2048);
    assert_eq!(m1_counts.lanes[0], mapped.circuit().terms.len());
    assert_eq!(m1_counts.lanes[1], 192);
    assert_eq!(m1_counts.lanes[2], 0);
    assert_eq!(m1_counts.lanes[3], 73728);
    let m1_residuals = owner_residuals(&roster, 2048, mapped.witness(), &fixture_values);
    assert!(m1_residuals
        .iter()
        .all(|rows| rows.values().all(|value| value.is_zero())));
    let alias_source = m1_terms
        .iter()
        .filter(|t| (t.row >> LOCAL_ROW_LOG) & 3 == 1)
        .flat_map(|t| [t.gate.left, t.gate.right])
        .find(|wire| {
            *wire / WIDTH != 2048
                && fixture_values
                    .get(wire)
                    .is_some_and(|value| value.is_zero() || value.is_one())
        })
        .expect("M1 imports an authenticated RAW serializer bit");
    let mut bad_fixture_values = fixture_values.clone();
    let saved = bad_fixture_values[&alias_source];
    bad_fixture_values.insert(alias_source, Fr::one() - saved);
    let alias_fault = owner_residuals(&roster, 2048, mapped.witness(), &bad_fixture_values);
    assert!(alias_fault[0].values().all(|value| value.is_zero()));
    assert!(alias_fault[1].values().any(|value| !value.is_zero()));
    assert!(alias_fault[2].values().all(|value| value.is_zero()));
    assert!(alias_fault[3].values().all(|value| value.is_zero()));

    // Independently turn on one reserved zero-bank input at M1, carry, reset,
    // and padding owners; each fault is confined to the inactive lane.
    let mut inactive_cases = vec![(2048u64, mapped.witness().to_vec(), 827392..851968)];
    for slot in [2u64, 417791, 844801] {
        inactive_cases.push((slot, vec![Fr::zero(); WIDTH], 0..WIDTH));
    }
    for (slot, mut witness, allowed) in inactive_cases {
        let (_, terms) = owner_terms(&roster, slot);
        let base = slot as usize * WIDTH;
        let wire = terms
            .iter()
            .filter(|t| (t.row >> LOCAL_ROW_LOG) & 3 == 3)
            .map(|t| t.gate.left)
            .find(|wire| (base..base + WIDTH).contains(wire) && allowed.contains(&(wire - base)))
            .expect("inactive lane owns a local zero-bank input");
        let mut empty_external = std::collections::BTreeMap::new();
        if slot == 417791 {
            let endpoints = &crate::work_tree_layout::shared_baseline()
                .unwrap()
                .endpoints;
            for (bit, wire) in endpoints.work.iter().enumerate() {
                let value = if bit < 64 {
                    Fr::from((0x6f98d5000000u64 >> bit) & 1)
                } else {
                    Fr::zero()
                };
                empty_external.insert((slot as usize - 1) * WIDTH + wire, value);
            }
        }
        let external = if slot == 2048 {
            &fixture_values
        } else {
            &empty_external
        };
        let before = owner_residuals(&roster, slot, &witness, external);
        assert!(before
            .iter()
            .all(|rows| rows.values().all(|value| value.is_zero())));
        witness[wire - base] = Fr::one();
        let after = owner_residuals(&roster, slot, &witness, external);
        assert!(after[0].values().all(|value| value.is_zero()));
        assert!(after[1].values().all(|value| value.is_zero()));
        assert!(after[2].values().all(|value| value.is_zero()));
        assert!(
            after[3].values().any(|value| !value.is_zero()),
            "inactive owner {slot}"
        );
    }
    let mut bad_m1 = m1;
    let wire = bad_m1.arithmetic.external.nbits[0];
    bad_m1.arithmetic.external.nbits[0] = wire + 1;
    assert!(roster
        .admit_one(&bad_m1)
        .err()
        .unwrap()
        .contains("handles mismatch"));
    bad_m1.arithmetic.external.nbits[0] = wire;
    let (_, m1_terms) = owner_terms(&roster, 2048);
    let m1_base = 2048usize * WIDTH;
    let expected_m1: Vec<_> = mapped
        .circuit()
        .terms
        .iter()
        .map(|t| Term {
            row: 2048usize * OWNER_ROWS + t.row,
            gate: Gate {
                left: m1_base + t.gate.left,
                right: m1_base + t.gate.right,
                c0: t.gate.c0,
                c1: t.gate.c1,
                c2: t.gate.c2,
                c3: t.gate.c3,
            },
        })
        .collect();
    let actual_m1: Vec<_> = m1_terms
        .into_iter()
        .filter(|t| (t.row >> LOCAL_ROW_LOG) & 3 == 0)
        .collect();
    assert_eq!(
        actual_m1, expected_m1,
        "M1 arithmetic and endpoint translation"
    );

    // Native short children 3073, 4097, 5121, 6145 and 7169 have exact RAW fixtures.
    for (profile, child_height, count) in [
        (ShortProfile::M2, 3073u32, 2usize),
        (ShortProfile::M3, 4097, 3),
        (ShortProfile::M4, 5121, 4),
        (ShortProfile::M5, 6145, 5),
        (ShortProfile::M6, 7169, 6),
        (ShortProfile::M7, 8193, 7),
    ] {
        let child_raw = actual_child_raw(child_height)
            .or_else(|| headers.get(&child_height).cloned())
            .unwrap();
        let child = decode(&child_raw);
        assert_eq!(child.height, child_height);
        if matches!(child_height, 6145 | 7169) {
            assert_eq!(
                child.encode().unwrap(),
                child_raw,
                "RAW round-trip at {child_height}"
            );
        }
        let parent_id: [u8; 32] =
            Blake2b::<U32>::digest(headers.get(&(child_height - 1)).unwrap()).into();
        assert_eq!(
            child.parent_id, parent_id,
            "child parent linkage at {child_height}"
        );
        match child_height {
            6145 => assert_eq!(
                blake2b256(&child_raw),
                "c243f080a3fa16f0eb541c44cec6c49468233b9b49dd97d8d29a7b1d03f87459".to_uppercase()
            ),
            7169 => assert_eq!(
                blake2b256(&child_raw),
                "ac095a4e6936cd83504820274611bd700d327f6472f243b3443cdae9f32f6c9a".to_uppercase()
            ),
            _ => (),
        }
        let mut native = Vec::new();
        for i in 1..=count + 1 {
            native.push(decode(headers.get(&(i as u32 * 1024)).unwrap()));
        }
        let timestamps: Vec<i64> = native.iter().map(|h| h.timestamp).collect();
        let nbits: Vec<u32> = native.iter().skip(1).map(|h| h.n_bits).collect();
        let mut compiled = if profile == ShortProfile::M2 {
            daa_finish::compile_two_finish_with_child(
                &daa_count::q(),
                daa_integer::TwoRatioInputs {
                    nbits: nbits.try_into().unwrap(),
                    timestamps: timestamps.try_into().unwrap(),
                },
                child.n_bits,
                true,
            )
            .unwrap()
        } else {
            let native_profile = match profile {
                ShortProfile::M2 => unreachable!(),
                ShortProfile::M3 => daa_integer::ShortLegacyProfile::M3,
                ShortProfile::M4 => daa_integer::ShortLegacyProfile::M4,
                ShortProfile::M5 => daa_integer::ShortLegacyProfile::M5,
                ShortProfile::M6 => daa_integer::ShortLegacyProfile::M6,
                ShortProfile::M7 => daa_integer::ShortLegacyProfile::M7,
            };
            daa_finish::compile_short_legacy_with_child(
                &daa_count::q(),
                daa_integer::ShortLegacyInputs {
                    profile: native_profile,
                    nbits,
                    timestamps,
                },
                child.n_bits,
                true,
            )
            .unwrap()
        };
        let mapped = roster.admit_short(profile, &compiled).unwrap();
        let slot = u64::from(child_height - 1);
        let (counts, terms) = owner_terms(&roster, slot);
        assert_eq!(counts.lanes[0], mapped.circuit().terms.len());
        assert_eq!(counts.lanes[1], 96 * (count + 1));
        assert_eq!(counts.lanes[2], 0);
        assert_eq!(counts.lanes[3], 0);
        let residuals = owner_residuals(&roster, slot, mapped.witness(), &fixture_values);
        assert!(
            residuals.iter().all(|rows| rows.values().all(|value| value.is_zero())),
            "actual RAW arithmetic, alias, numeric, inactive residuals at {child_height}: {residuals:?}"
        );
        assert_raw_alias_fault(&roster, slot, mapped.witness(), &fixture_values);
        // The owned consumer rejects each directly consumed field-handle
        // mutation before the relation can enter the composed roster.
        let saved = {
            let w = &mut compiled.joined.joined.joined;
            let x = w.external[0].nbits[0];
            w.external[0].nbits[0] = x + 1;
            x
        };
        assert!(roster
            .admit_short(profile, &compiled)
            .err()
            .unwrap()
            .contains("field handle mismatch"));
        compiled.joined.joined.joined.external[0].nbits[0] = saved;
        let saved = {
            let w = &mut compiled.joined.joined.joined;
            let x = w.external[0].start_timestamp[0];
            w.external[0].start_timestamp[0] = x + 1;
            x
        };
        assert!(roster
            .admit_short(profile, &compiled)
            .err()
            .unwrap()
            .contains("field handle mismatch"));
        compiled.joined.joined.joined.external[0].start_timestamp[0] = saved;
        let saved = {
            let w = &mut compiled.joined.joined.joined;
            let i = w.external.len() - 1;
            let x = w.external[i].end_timestamp[63];
            w.external[i].end_timestamp[63] = x + 1;
            x
        };
        assert!(roster
            .admit_short(profile, &compiled)
            .err()
            .unwrap()
            .contains("field handle mismatch"));
        let last = compiled.joined.joined.joined.external.len() - 1;
        compiled.joined.joined.joined.external[last].end_timestamp[63] = saved;
        let saved = compiled.output.numeric_result[0];
        compiled.output.numeric_result[0] = saved + 1;
        assert!(roster
            .admit_short(profile, &compiled)
            .err()
            .unwrap()
            .contains("field handle mismatch"));
        compiled.output.numeric_result[0] = saved;
        let saved = {
            let bits = compiled.child_nbits.as_mut().unwrap();
            let x = bits[31];
            bits[31] = x + 1;
            x
        };
        assert!(roster
            .admit_short(profile, &compiled)
            .err()
            .unwrap()
            .contains("field handle mismatch"));
        compiled.child_nbits.as_mut().unwrap()[31] = saved;
        let expected: Vec<_> = mapped
            .circuit()
            .terms
            .iter()
            .map(|t| Term {
                row: slot as usize * OWNER_ROWS + t.row,
                gate: Gate {
                    left: slot as usize * WIDTH + t.gate.left,
                    right: slot as usize * WIDTH + t.gate.right,
                    c0: t.gate.c0,
                    c1: t.gate.c1,
                    c2: t.gate.c2,
                    c3: t.gate.c3,
                },
            })
            .collect();
        let arithmetic: Vec<_> = terms
            .into_iter()
            .filter(|t| t.row >> SLOT_ROW_LOG == slot as usize && (t.row >> LOCAL_ROW_LOG) & 3 == 0)
            .collect();
        assert_eq!(
            arithmetic, expected,
            "native short arithmetic owner {child_height}"
        );
    }

    // Both mature epochs and the late EIP boundary reuse their exact authenticated windows.
    for child_height in [9217u32, 844673, 844801] {
        let case: serde_json::Value =
            serde_json::from_str(include_str!("../fixtures/mainnet-daa-windows-v1.json")).unwrap();
        let samples: Vec<u32> = case["cases"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["child"].as_u64() == Some(child_height as u64))
            .unwrap()["samples"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u32)
            .collect();
        let parent_raw = headers.get(&(child_height - 1)).unwrap();
        let child_raw = headers.get(&child_height).unwrap();
        let sample_refs: Vec<_> = samples
            .iter()
            .map(|h| headers.get(h).unwrap().as_slice())
            .collect();
        let selected =
            daa_header_window::select_window(parent_raw, child_raw, &sample_refs).unwrap();
        let Action::Retarget(epoch) = selected.action() else {
            panic!("fixture branch")
        };
        let mut compiled = daa_finish::compile_finish_with_child(
            epoch,
            &daa_count::q(),
            selected.prediction(),
            selected.child_nbits(),
            true,
        )
        .unwrap();
        let mapped = roster.admit_mature(&selected, &compiled).unwrap();
        let slot = u64::from(child_height - 1);
        let (counts, terms) = owner_terms(&roster, slot);
        assert_eq!(counts.lanes[0], mapped.circuit().terms.len());
        assert_eq!(counts.lanes[1], 896);
        assert_eq!(counts.lanes[2], 0);
        assert_eq!(counts.lanes[3], 0);
        let residuals = owner_residuals(&roster, slot, mapped.witness(), &fixture_values);
        assert!(
            residuals.iter().all(|rows| rows.values().all(|value| value.is_zero())),
            "actual RAW arithmetic, alias, numeric, inactive residuals at {child_height}: {residuals:?}"
        );
        assert_raw_alias_fault(&roster, slot, mapped.witness(), &fixture_values);
        let wire = compiled.joined.joined.joined.external[0].nbits[0];
        compiled.joined.joined.joined.external[0].nbits[0] = wire + 1;
        assert!(roster
            .admit_mature(&selected, &compiled)
            .err()
            .unwrap()
            .contains("consumed handles"));
        compiled.joined.joined.joined.external[0].nbits[0] = wire;
        let mut source_wires = std::collections::BTreeSet::new();
        for external in &compiled.joined.joined.joined.external {
            for bits in [
                &external.nbits[..],
                &external.start_timestamp[..],
                &external.end_timestamp[..],
            ] {
                source_wires.insert(bits[0]);
                source_wires.insert(*bits.last().unwrap());
            }
        }
        source_wires.extend(compiled.joined.output.x0_bits.iter().copied());
        source_wires.extend(compiled.child_nbits.as_ref().unwrap().iter().copied());
        for source_wire in source_wires {
            let saved = compiled.joined.joined.joined.witness[source_wire];
            assert!(
                saved.is_zero() || saved.is_one(),
                "source witness must be Boolean"
            );
            compiled.joined.joined.joined.witness[source_wire] = Fr::one() - saved;
            assert!(
                roster
                    .admit_mature(&selected, &compiled)
                    .err()
                    .unwrap()
                    .contains("source bit assignment mismatch"),
                "imported wire {source_wire}"
            );
            compiled.joined.joined.joined.witness[source_wire] = saved;
        }
        let expected: Vec<_> = mapped
            .circuit()
            .terms
            .iter()
            .map(|t| Term {
                row: slot as usize * OWNER_ROWS + t.row,
                gate: Gate {
                    left: slot as usize * WIDTH + t.gate.left,
                    right: slot as usize * WIDTH + t.gate.right,
                    c0: t.gate.c0,
                    c1: t.gate.c1,
                    c2: t.gate.c2,
                    c3: t.gate.c3,
                },
            })
            .collect();
        let arithmetic: Vec<_> = terms
            .into_iter()
            .filter(|t| (t.row >> LOCAL_ROW_LOG) & 3 == 0)
            .collect();
        assert_eq!(
            arithmetic, expected,
            "mature arithmetic owner {child_height}"
        );
    }

    // Causal B1->B4 retarget join at child 9217, using only its imported
    // nBits and a sparse per-leaf assignment (never a historical witness).
    let work_child = decode(headers.get(&9217).unwrap());
    let header_slot = 9216usize;
    let leaf_slot = header_slot - 1;
    let base = crate::work_tree_layout::shared_baseline().unwrap();
    let endpoints = &base.endpoints;
    let serializer = crate::serializer::build(None).unwrap();
    let fields = crate::serializer::Fields::from_header(&work_child).unwrap();
    let serialized = serializer.assign(&fields);
    let family = large_parent()
        .topology()
        .families
        .iter()
        .find(|f| f.name == "header_to_leaf_raw_length_nbits_height")
        .unwrap();
    let mut nbits_edges = Vec::new();
    family
        .emit_endpoint_terms(
            &large_parent().topology().descriptor,
            true,
            header_slot,
            |row_slot, bit, term| {
                if (4122..4154).contains(&bit) {
                    let nbit = bit - 4122;
                    assert_eq!(
                        term.gate.left,
                        header_slot * WIDTH
                            + crate::header_hash::SERIALIZER_OFFSET
                            + serializer.layout.fields.n_bits[nbit]
                    );
                    assert_eq!(term.gate.right, leaf_slot * WIDTH + endpoints.n_bits[nbit]);
                    assert_eq!(row_slot, header_slot);
                    nbits_edges.push((nbit, term));
                }
                Ok(())
            },
        )
        .unwrap();
    assert_eq!(nbits_edges.len(), 32);
    for (bit, term) in &nbits_edges {
        let source = serialized[serializer.layout.fields.n_bits[*bit]];
        let target = Fr::from(((work_child.n_bits >> bit) & 1) as u64);
        assert_eq!(source, target);
        assert_eq!(term.gate.c1 * source + term.gate.c2 * target, Fr::zero());
        let flipped = Fr::one() - source;
        assert_ne!(
            term.gate.c1 * flipped + term.gate.c2 * target,
            Fr::zero(),
            "B1 source nBits bit {bit}"
        );
    }
    let nbits = num_bigint::BigUint::from(work_child.n_bits);
    let work = crate::work_tree_work::native_decode(work_child.n_bits).unwrap();
    let mut assignment = std::collections::BTreeMap::new();
    put_bits(&mut assignment, &endpoints.n_bits, &nbits);
    put_bits(
        &mut assignment,
        &endpoints.lower,
        &num_bigint::BigUint::zero(),
    );
    put_bits(&mut assignment, &endpoints.work, &work);
    put_bits(&mut assignment, &endpoints.upper, &work);
    put_bits(
        &mut assignment,
        &endpoints.work_minus_one,
        &(&work - num_bigint::BigUint::one()),
    );
    assignment.insert(
        endpoints.exponent[(work_child.n_bits >> 24) as usize],
        Fr::one(),
    );
    let good = work_residuals(large_parent().work_boundary(), leaf_slot, &assignment);
    assert!(
        good.is_empty(),
        "real child B4 assignment residual rows: {good:?}"
    );
    let wrong_work = &work + num_bigint::BigUint::one();
    let wrong_upper = wrong_work.clone();
    let wrong_minus_one = &wrong_work - num_bigint::BigUint::one();
    put_bits(&mut assignment, &endpoints.work, &wrong_work);
    put_bits(&mut assignment, &endpoints.upper, &wrong_upper);
    put_bits(&mut assignment, &endpoints.work_minus_one, &wrong_minus_one);
    let bad = work_residuals(large_parent().work_boundary(), leaf_slot, &assignment);
    let decoded = large_parent()
        .work_boundary()
        .group("decoded_work")
        .unwrap();
    assert!(
        !bad.is_empty() && bad.iter().all(|row| decoded.contains(row)),
        "coherent +1 work fault must isolate in B4 decoded_work: {bad:?}"
    );
    assert_ne!(wrong_work, work);
}

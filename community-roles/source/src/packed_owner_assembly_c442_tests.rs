//! Bounded test-only C442 differential for ordinary Map-only Slack authorship.
//! The fixture is structural; this module makes no authenticated Map, global
//! ROW, proof, frame, or production-H-claim assertion.
use super::*;
use crate::daa_history_roster::OwnerClass;
use ark_ff::Zero;

fn bank53_slice(bytes: &[u8]) -> &[u8] {
    let start = BANK53_BASE / 8;
    let end = (BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS) / 8;
    &bytes[start..end]
}

fn term_residual(term: &crate::sparse::Term, owner_values: &[Fr], owner: usize) -> Fr {
    let base = owner * WIDTH;
    let left = owner_values[term.gate.left.checked_sub(base).expect("owner-local left")];
    let right = if term.gate.c2.is_zero() && term.gate.c3.is_zero() {
        Fr::zero()
    } else {
        owner_values[term.gate.right.checked_sub(base).expect("owner-local right")]
    };
    term.gate.c0 + term.gate.c1 * left + term.gate.c2 * right
        + term.gate.c3 * left * right
}

fn require_ordered_slack_terms(
    actual: &[crate::sparse::Term],
    expected: &[crate::sparse::Term],
) -> Result<(), &'static str> {
    if actual.len() != expected.len() || actual != expected {
        return Err("Slack term count/order/tuple mismatch");
    }
    Ok(())
}

#[test]
fn c442_owner0_genesis_no_frame_slack_author_differential() {
    let owner = 0usize;
    let class = OwnerClass::Genesis;
    // Generate exactly once, then share the same binding and Map lease across
    // both routes and all independent fault cases.
    let (binding, bundle) = Eligible08MapSlackBundle::synthetic_for_test(owner, class)
        .expect("structural Map+Slack source fixture");
    let input = super::max_join_tests::bounded_input_n(3);
    let plan = WorkTreeHistoryPlan::compile(3, 2, input.root(), input.total_be28()).unwrap();
    let template = crate::daa_history_layout::HeaderAssignmentTemplate::new().unwrap();
    let genesis = input.header(1).unwrap();
    let genesis_fields = crate::serializer::Fields::from_header(&genesis).unwrap();
    let mut header_native = template.assign(&genesis_fields).unwrap();
    template.assign_order(&mut header_native, &genesis_fields, 0, 0, true).unwrap();
    assert_eq!(header_native.len(), WIDTH);
    let mask = plan.physical_assignment_replacement_mask(owner as u64).unwrap();
    assert_eq!(crate::daa_history_roster::DaaHistoryRoster::compile(&plan)
        .unwrap().owner_class(owner as u64).unwrap(), class);

    let d_reservation = preflight_map_slack_reservation(
        &bundle, &binding, owner, class, &mask, &header_native,
    ).expect("D reserves Map and retires HEADER from Slack");
    let h_reservation = preflight_map_pair_reservation(
        bundle.map_lease(), &binding, owner, class, &mask,
    ).expect("H reserves only Map");

    let mut d_rows = OwnedRows::new(OwnerSelection::Single { owner, class });
    d_rows.begin_author_census().unwrap();
    d_rows.set_author(NativePhysicalAuthor::Bank53).unwrap();
    claim_map_slack_live(&mut d_rows, &bundle, &binding, owner, class)
        .expect("production exclusive Map+Slack claim");
    let mut h_rows = OwnedRows::new(OwnerSelection::Single { owner, class });
    h_rows.begin_author_census().unwrap();
    h_rows.set_author(NativePhysicalAuthor::Bank53).unwrap();
    claim_map_pair_live(&mut h_rows, bundle.map_lease(), &binding, owner, class)
        .expect("production exclusive Map claim");

    d_rows.set_author(NativePhysicalAuthor::Header).unwrap();
    h_rows.set_author(NativePhysicalAuthor::Header).unwrap();
    let mut map_count = 0usize;
    let mut score_count = 0usize;
    let mut d_slack_count = 0usize;
    let mut h_slack_count = 0usize;
    for context in 0..BANK53_CONTEXTS {
        let start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
        let map_end = start + BANK53_MAP_LIVE_BITS;
        let slack_start = start + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT;
        let slack_end = slack_start + BANK53_SLACK_BITS;
        for local in start..map_end {
            assert!(d_reservation[local] && h_reservation[local]);
            assert!(d_rows.claimed[0][local] && h_rows.claimed[0][local]);
            assert_eq!(d_rows.author_census.as_ref().unwrap()[local],
                Some(NativePhysicalAuthor::Bank53));
            assert_eq!(h_rows.author_census.as_ref().unwrap()[local],
                Some(NativePhysicalAuthor::Bank53));
            map_count += 1;
        }
        for local in map_end..slack_start {
            assert!(!d_reservation[local] && !h_reservation[local]);
            assert!(!mask[local] && header_native[local].is_zero());
            d_rows.claim_exclusive(owner, local, Fr::zero())
                .expect("D keeps inactive Score as sole HEADER zero");
            h_rows.claim_exclusive(owner, local, Fr::zero())
                .expect("H keeps inactive Score as sole HEADER zero");
            assert_eq!(d_rows.author_census.as_ref().unwrap()[local],
                Some(NativePhysicalAuthor::Header));
            assert_eq!(h_rows.author_census.as_ref().unwrap()[local],
                Some(NativePhysicalAuthor::Header));
            score_count += 1;
        }
        for local in slack_start..slack_end {
            assert!(d_reservation[local]);
            assert!(!h_reservation[local], "H keeps Slack outside Map reservation");
            assert!(!mask[local], "owner0 Genesis HEADER replacement mask Slack");
            // In the canonical template assign/assign_order source audit,
            // both Slack intervals remain zero and are not replacement bits.
            assert!(header_native[local].is_zero());
            assert!(d_rows.claimed[0][local]);
            assert_eq!(d_rows.author_census.as_ref().unwrap()[local],
                Some(NativePhysicalAuthor::Bank53));
            h_rows.claim_exclusive(owner, local, Fr::zero())
                .expect("sole HEADER Slack zero claim");
            assert!(h_rows.claimed[0][local]);
            assert_eq!(h_rows.author_census.as_ref().unwrap()[local],
                Some(NativePhysicalAuthor::Header));
            d_slack_count += 1;
            h_slack_count += 1;
        }
    }
    assert_eq!(map_count, BANK53_CONTEXTS * BANK53_MAP_LIVE_BITS);
    assert_eq!(score_count, BANK53_CONTEXTS * crate::origin_score::INPUT);
    assert_eq!(d_slack_count, BANK53_CONTEXTS * BANK53_SLACK_BITS);
    assert_eq!(h_slack_count, BANK53_CONTEXTS * BANK53_SLACK_BITS);
    require_map_slack_claim_census(&d_rows, &bundle, &binding, owner, class)
        .expect("production D physical claim census");

    let d_bytes = d_rows.bytes(0).expect("D packed owner");
    let h_bytes = h_rows.bytes(0).expect("H packed owner");
    assert_eq!(bank53_slice(&d_bytes), bank53_slice(&h_bytes));
    assert_eq!(bundle.map_lease().binding(), &binding,
        "D/H structural routes share the same synthetic Map binding");
    assert_eq!(binding.owner, owner);

    let mut checked = 0usize;
    for context in 0..BANK53_CONTEXTS {
        let terms = bundle.checked_slack_terms(&binding, owner, class, context).unwrap();
        let expected = crate::bank53_slack::slack_zero_terms(owner, context).unwrap();
        require_ordered_slack_terms(terms, &expected)
            .expect("ordered Slack tuple identity and exact count");
        for term in terms {
            assert!(term_residual(term, &d_rows.values[0], owner).is_zero());
            assert!(term_residual(term, &h_rows.values[0], owner).is_zero());
            checked += 1;
        }
    }
    assert_eq!(checked, 774);

    let first_slack = BANK53_BASE + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT;
    d_rows.claimed[0][first_slack] = false;
    assert!(require_map_slack_claim_census(&d_rows, &bundle, &binding, owner, class)
        .unwrap_err().contains("missing or changed"),
        "one omitted physical zero claim must fail the production census");

    // Isolated source/value/context and term-count faults; each stops before
    // any PASS marker and reuses the existing fixture rather than regenerating.
    let mut one = bundle.clone();
    one.set_slack_bit_for_test(1, 386, true).unwrap();
    assert!(preflight_map_slack_reservation(
        &one, &binding, owner, class, &mask, &header_native,
    ).is_err(), "one Slack X bit set");

    let mut missing_term = bundle.clone();
    missing_term.remove_slack_term_for_test(1, 386).unwrap();
    assert!(missing_term.checked_slack_terms(&binding, owner, class, 1).is_err(),
        "one missing Slack equation must fail production source validation");

    let mut swapped_contexts = bundle.clone();
    swapped_contexts.swap_slack_contexts_for_test();
    assert!(swapped_contexts.checked_slack_terms(&binding, owner, class, 0).is_err(),
        "two valid Slack contexts exchanged must fail production validation");
    assert!(bundle.checked_slack_cells(&binding, owner + 1, class).is_err(),
        "wrong owner binding");
    let wrong_binding = binding.mutated_field_for_test(0);
    assert!(bundle.checked_slack_cells(&wrong_binding, owner, class).is_err(),
        "wrong parent binding");

    let mut duplicate = OwnedRows::new(OwnerSelection::Single { owner, class });
    duplicate.begin_author_census().unwrap();
    duplicate.set_author(NativePhysicalAuthor::Header).unwrap();
    duplicate.claim(owner, BANK53_BASE + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT,
        Fr::zero()).unwrap();
    duplicate.set_author(NativePhysicalAuthor::Bank53).unwrap();
    assert!(duplicate.claim(owner,
        BANK53_BASE + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT, Fr::zero())
        .unwrap_err().contains("cross-author duplicate"),
        "equal-zero duplicate writer rejected by the physical author census");

    let h21_plan = WorkTreeHistoryPlan::compile(
        1_827_840, 21, [0x51; 32], [0x52; 28],
    ).expect("fixed-H21 structural mask plan");
    let owner1 = 1usize;
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(&h21_plan).unwrap();
    assert_eq!(roster.owner_class(owner1 as u64).unwrap(), OwnerClass::Initial);
    let owner1_mask = h21_plan.physical_assignment_replacement_mask(owner1 as u64).unwrap();
    let header = input.header(owner1 + 1).unwrap();
    let previous = input.header(owner1).unwrap();
    let fields = crate::serializer::Fields::from_header(&header).unwrap();
    let mut owner1_header = template.assign(&fields).unwrap();
    template.assign_order(&mut owner1_header, &fields, previous.height,
        previous.timestamp, false).unwrap();
    assert_eq!(owner1_header.len(), WIDTH);
    let slack_start = BANK53_BASE + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT;
    let mut owner1_slack_cells = 0usize;
    for context in 0..BANK53_CONTEXTS {
        let start = BANK53_BASE + context * BANK53_CONTEXT_BITS
            + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT;
        for local in start..start + BANK53_SLACK_BITS {
            assert!(!owner1_mask[local], "owner1 Initial HEADER replacement mask Slack");
            assert!(owner1_header[local].is_zero(),
                "owner1 Initial canonical HEADER Slack value wire{local}");
            owner1_slack_cells += 1;
        }
    }
    assert_eq!(owner1_slack_cells, 774);
    assert!(!owner1_mask[slack_start]);

    // The parent replacement mask is owner-independent by construction;
    // sample each deciding owner class/boundary without claiming the later
    // special overlays leave HEADER as final author at those owners.
    for sample in [0usize, 1, 417_790, 845_758, 845_759, 845_887,
        1_827_839, 1_827_840, (1 << 21) - 1] {
        let sample_mask = h21_plan.physical_assignment_replacement_mask(sample as u64).unwrap();
        for context in 0..BANK53_CONTEXTS {
            let start = BANK53_BASE + context * BANK53_CONTEXT_BITS
                + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT;
            assert!(sample_mask[start..start + BANK53_SLACK_BITS].iter().all(|bit| !bit),
                "H21 parent Slack mask owner{sample} context{context}");
        }
    }

    // Diagnostic only: the raw owner1 Slack rows intersect DAA lane-3 rows.
    let row_lo = 393_216usize;
    let row_hi = 475_136usize;
    let owner1_terms = crate::bank53_slack::slack_zero_terms(owner1, 0).unwrap();
    let raw_collision = owner1_terms.iter()
        .filter(|term| (row_lo..row_hi).contains(&(term.row % crate::bank53_map::ROW_STRIDE)))
        .count();
    assert_eq!(raw_collision, BANK53_SLACK_BITS);
    println!("C442_RAW_ROW_COLLISION_DIAGNOSTIC owner=1 class=Initial context=0 slack=438496..438883 daa_lane3=393216..475136 overlap=387 global_row_pass=false");
    println!("C442_OWNER0_GENESIS_SLACK_AUTHOR_NO_FRAME_PASS owner=0 class=Genesis contexts=2 exact_slack_cells=774 exact_terms=774 zero_residuals_per_policy=774 bank53_bytes_equal=true D=dedicated_slack H=header_slack owner1_D_path=not_claimed global_row_pass=false frame=false proof=false client=false");
}

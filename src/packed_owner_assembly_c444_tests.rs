//! C444 no-frame checks for the pure Eligible08 regular Score owner classifier.
//!
//! These assertions establish scheduled membership and owner-local source
//! identities and isolated claim rejection only. They do not construct a
//! closed source join or complete physical row, authenticate header history,
//! or pass the producer.

use super::{
    claim_scored_owner_cells, scored_owner_cell_local, Eligible08RegularScoreOwner,
    H21EligibleMapStage, OwnedRows, ScoredOwnerPackedAuthor, WIDTH,
};
use super::h21_eligible_context::{ScoredOwnerPackedCell, ScoreReplayAuthor};
use crate::daa_history_roster::OwnerClass;

#[test]
fn c444_regular_score_owner_classifier_boundaries_no_frame() {
    // 846014 is immediately before the regular residue. 846015 is ordinal 1
    // and keeps both contexts active; its prior R and MAX sources are fixed by
    // the classifier's schedule, not supplied fixture values.
    assert!(Eligible08RegularScoreOwner::classify(846_014).is_err());
    let first = Eligible08RegularScoreOwner::classify(846_015)
        .expect("846015 is the first regular Score endpoint");
    assert_eq!(first.owner(), 846_015);
    assert_eq!(first.ordinal(), 1);
    assert_eq!(first.active(), [true, true]);
    assert_eq!(first.typed_cell_count(), 20_480);
    assert_eq!(first.previous_r_owner(), 845_887);
    assert_eq!(first.max_owner(), 844_926);

    // The Eligible08 context-0 tail has no context-1 Score/Cap producer.
    let last = Eligible08RegularScoreOwner::classify(1_810_879)
        .expect("1810879 is the last regular context-0 endpoint");
    assert_eq!(last.ordinal(), 7_539);
    assert_eq!(last.active(), [true, false]);
    assert_eq!(last.typed_cell_count(), 16_384);
    assert_eq!(last.previous_r_owner(), 1_810_751);
    assert_eq!(last.max_owner(), 1_809_790);

    // The two clipped guards are not members of the regular class.
    assert!(Eligible08RegularScoreOwner::classify(1_810_841).is_err());
    assert!(Eligible08RegularScoreOwner::classify(1_810_904).is_err());

    // First modern owner and historical anchors retain their distinct paths.
    for owner in [417_790, 845_758, 845_759] {
        assert!(Eligible08RegularScoreOwner::classify(owner).is_err());
    }
    // Existing first regular owner remains admitted without changing its
    // two-context typed-cell census.
    let retained = Eligible08RegularScoreOwner::classify(845_887)
        .expect("existing C443 regular owner remains classified");
    assert_eq!(retained.ordinal(), 0);
    assert_eq!(retained.active(), [true, true]);
    assert_eq!(retained.typed_cell_count(), 20_480);
    assert_eq!(retained.previous_r_owner(), 845_759);
    assert_eq!(retained.max_owner(), 844_798);

    // N and padded owners are outside the Eligible08 regular endpoint class.
    assert!(Eligible08RegularScoreOwner::classify(1_827_840).is_err());
    assert!(Eligible08RegularScoreOwner::classify((1usize << 21) - 1).is_err());

    println!("C444_NOFRAME_PURE_CLASSIFIER_PASS endpoints=846015,1810879 guards=1810841,1810904 padding=N,2097151 physical_producer=false authenticated_history=false frame=false pcs=false");
}

#[test]
fn c444_regular_score_pure_physical_cell_checker_no_frame() {
    fn score_cell(owner: usize, context: usize) -> ScoredOwnerPackedCell {
        let schedule = Eligible08RegularScoreOwner::classify(owner).unwrap();
        let local = H21EligibleMapStage::score_live(context).unwrap().start;
        ScoredOwnerPackedCell::synthetic_for_test(
            owner * WIDTH + local,
            ScoredOwnerPackedAuthor::Score(ScoreReplayAuthor {
                context,
                origin: owner + 1,
                previous_owner: schedule.previous_r_owner(),
                max_owner: schedule.max_owner(),
                cap_owner: owner,
            }),
            false,
        )
    }

    fn cap_cell(owner: usize, context: usize) -> ScoredOwnerPackedCell {
        let local = H21EligibleMapStage::cap_live(context).unwrap().start;
        ScoredOwnerPackedCell::synthetic_for_test(
            owner * WIDTH + local,
            ScoredOwnerPackedAuthor::Cap { context, origin: owner + 1 },
            false,
        )
    }

    for (owner, contexts) in [(846_015usize, [true, true]), (1_810_879, [true, false])] {
        for context in 0..2 {
            let score = score_cell(owner, context);
            let cap = cap_cell(owner, context);
            if contexts[context] {
                assert!(scored_owner_cell_local(owner, &score).is_ok());
                assert!(scored_owner_cell_local(owner, &cap).is_ok());
            } else {
                // Inactive authors are rejected even when the proposed bit is zero.
                assert!(scored_owner_cell_local(owner, &score).is_err());
                assert!(scored_owner_cell_local(owner, &cap).is_err());
            }
        }
    }

    let owner = 846_015usize;
    let local = H21EligibleMapStage::score_live(0).unwrap().start;
    let correct = score_cell(owner, 0);
    let bad_previous = ScoredOwnerPackedCell::synthetic_for_test(
        correct.wire(),
        ScoredOwnerPackedAuthor::Score(ScoreReplayAuthor {
            context: 0, origin: owner + 1, previous_owner: 845_759,
            max_owner: 844_926, cap_owner: owner,
        }), false,
    );
    let bad_max = ScoredOwnerPackedCell::synthetic_for_test(
        correct.wire(),
        ScoredOwnerPackedAuthor::Score(ScoreReplayAuthor {
            context: 0, origin: owner + 1, previous_owner: 845_887,
            max_owner: 844_798, cap_owner: owner,
        }), false,
    );
    assert!(scored_owner_cell_local(owner, &correct).is_ok());
    assert!(scored_owner_cell_local(owner, &bad_previous).is_err());
    assert!(scored_owner_cell_local(owner, &bad_max).is_err());

    // Equal-zero duplicate Score source claims remain exclusive; the checker
    // rejects both an intra-batch duplicate and a previously claimed wire.
    let mut duplicate = OwnedRows::new(crate::packed_owner_assembly::OwnerSelection::Single {
        owner, class: OwnerClass::Carry,
    });
    assert!(claim_scored_owner_cells(&mut duplicate, owner, &[correct, correct]).is_err());
    assert_eq!(duplicate.claimed[0].iter().filter(|claimed| **claimed).count(), 0);

    let mut prior = OwnedRows::new(crate::packed_owner_assembly::OwnerSelection::Single {
        owner, class: OwnerClass::Carry,
    });
    prior.claim(owner, local, ark_bn254::Fr::from(0u64)).unwrap();
    assert!(claim_scored_owner_cells(&mut prior, owner, &[correct]).is_err());
    assert_eq!(prior.claimed[0].iter().filter(|claimed| **claimed).count(), 1);

    println!("C444_NOFRAME_PURE_CELL_CHECKER_PASS owners=846015,1810879 inactive_zero_rejected=true prior_r_max_mutations_rejected=true duplicate_zero_claim_rejected=true physical_producer=false authenticated_history=false frame=false pcs=false");
}

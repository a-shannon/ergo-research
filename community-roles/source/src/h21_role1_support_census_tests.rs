//! Full-role1 H21 support census for the two adjacent Carry owners used by c262.
//! This is a callback support diagnostic, not a packed reader or GKR proof.

use crate::{
    daa_history_roster::{self, DaaHistoryRoster, OwnerClass},
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::collections::BTreeSet;

const HEADERS: u64 = 1_827_840;
const OWNERS: [usize; 2] = [9_214, 9_215];
const OWNER_ROWS: usize = 1 << daa_history_roster::SLOT_ROW_LOG;
const WIDTH: usize = 1 << daa_history_roster::LOCAL_INPUT_LOG;
const WINDOW: std::ops::Range<usize> = 524_288..589_824;
const BLOCK_BITS: usize = 65_536;

#[derive(Default)]
struct Support {
    occurrences: usize,
    window_occurrences: usize,
    by_region_occurrences: [usize; 3],
    by_region_coordinates: [BTreeSet<usize>; 3],
    coordinates: BTreeSet<usize>,
    blocks: BTreeSet<usize>,
    fold_buckets: BTreeSet<usize>,
}

impl Support {
    fn add(&mut self, local: usize) {
        assert!(
            local < WIDTH,
            "callback dependency escaped local input domain"
        );
        let region = if local < crate::header_hash::SERIALIZER_OFFSET {
            0
        } else if local < crate::header_hash::AUX_OFFSET {
            1
        } else {
            2
        };
        self.occurrences += 1;
        if WINDOW.contains(&local) {
            self.window_occurrences += 1;
        }
        self.by_region_occurrences[region] += 1;
        self.by_region_coordinates[region].insert(local);
        self.coordinates.insert(local);
        self.blocks.insert(local / BLOCK_BITS);
        self.fold_buckets.insert(local >> 16);
    }

    fn range(&self) -> (Option<usize>, Option<usize>) {
        (
            self.coordinates.first().copied(),
            self.coordinates.last().copied(),
        )
    }

    fn outside_window_occurrences(&self) -> usize {
        self.occurrences - self.window_occurrences
    }
}

#[derive(Default)]
struct OwnerCensus {
    terms: usize,
    omitted_worktree: usize,
    omitted_mature_a4: usize,
    omitted_short_a4: usize,
    left: Support,
    right: Support,
    constant_terms: usize,
    compact_alias_terms: usize,
    compact_alias_left: BTreeSet<usize>,
}

fn census_owner(roster: &DaaHistoryRoster<'_>, owner: usize) -> OwnerCensus {
    assert_eq!(
        roster.owner_class(owner as u64).expect("owner class"),
        OwnerClass::Carry
    );
    let row_base = owner * OWNER_ROWS;
    let input_base = owner * WIDTH;
    let mut census = OwnerCensus::default();
    let counts = roster
        .visit_header_terms(owner as u64, |term| {
            let local_row = term.row.checked_sub(row_base).ok_or("row before owner")?;
            let left = term
                .gate
                .left
                .checked_sub(input_base)
                .ok_or("left before owner")?;
            let right = term
                .gate
                .right
                .checked_sub(input_base)
                .ok_or("right before owner")?;
            if local_row >= OWNER_ROWS || left >= WIDTH || right >= WIDTH {
                return Err("role-1 callback term escapes physical owner".into());
            }
            census.terms += 1;
            if !term.gate.c0.is_zero() {
                census.constant_terms += 1;
            }
            // For c0+c1*X_l+c2*X_r+c3*X_l*X_r, these are the only
            // coordinates whose Boolean values can affect the gate value.
            if !term.gate.c1.is_zero() || !term.gate.c3.is_zero() {
                census.left.add(left);
            }
            if !term.gate.c2.is_zero() || !term.gate.c3.is_zero() {
                census.right.add(right);
            }
            if (405_894..406_406).contains(&local_row)
                && (crate::header_compact_links::HASH_OFFSET
                    ..crate::header_compact_links::HASH_OFFSET
                        + crate::header_compact_links::HASH_WIDTH)
                    .contains(&left)
                && term.gate.c0.is_zero()
                && term.gate.c1 == Fr::one()
                && term.gate.c2 == -Fr::one()
                && term.gate.c3.is_zero()
            {
                census.compact_alias_terms += 1;
                census.compact_alias_left.insert(left);
            }
            Ok(())
        })
        .expect("complete H21 role-1 callback");
    census.omitted_worktree = counts.omitted_worktree;
    census.omitted_mature_a4 = counts.omitted_mature_a4;
    census.omitted_short_a4 = counts.omitted_short_a4;
    census
}

fn region_unique(support: &Support) -> [usize; 3] {
    std::array::from_fn(|region| support.by_region_coordinates[region].len())
}

fn blocks(support: &Support) -> Vec<usize> {
    support.blocks.iter().copied().collect()
}

fn buckets(support: &Support) -> Vec<usize> {
    support.fold_buckets.iter().copied().collect()
}

#[test]
fn h21_two_carry_owners_full_role1_support_rejects_window_only_reader() {
    let plan = WorkTreeHistoryPlan::compile(HEADERS, 21, [0x35; 32], [0x35; 28])
        .expect("pinned H21 fixture plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("H21 DAA roster");
    let censuses = OWNERS.map(|owner| census_owner(&roster, owner));

    for (owner, census) in OWNERS.into_iter().zip(&censuses) {
        assert_eq!(
            census.terms, 396_561,
            "complete callback census for owner {owner}"
        );
        assert_eq!(
            census.omitted_worktree, 78_194,
            "work-tree omissions for owner {owner}"
        );
        assert_eq!(
            census.omitted_mature_a4, 0,
            "mature A4 omissions for Carry owner {owner}"
        );
        assert_eq!(
            census.omitted_short_a4, 0,
            "short A4 omissions for Carry owner {owner}"
        );
        assert_eq!(
            census.compact_alias_terms,
            crate::header_compact_links::HASH_WIDTH,
            "surviving compact-link aliases for Carry owner {owner}"
        );
        let expected_aliases: BTreeSet<_> = (crate::header_compact_links::HASH_OFFSET
            ..crate::header_compact_links::HASH_OFFSET + crate::header_compact_links::HASH_WIDTH)
            .collect();
        assert_eq!(
            census.compact_alias_left, expected_aliases,
            "compact-link alias left support for owner {owner}"
        );
        assert!(
            census
                .compact_alias_left
                .iter()
                .all(|wire| !WINDOW.contains(wire)),
            "the exact compact-link aliases falsify the proposed 8KiB-only window"
        );
        assert!(
            census.left.outside_window_occurrences() >= crate::header_compact_links::HASH_WIDTH,
            "full role-1 left-X dependencies outside the shift window for owner {owner}"
        );
        assert!(census.left.coordinates.iter().all(|wire| *wire < WIDTH));
        assert!(census.right.coordinates.iter().all(|wire| *wire < WIDTH));
    }

    let left_unique = censuses
        .iter()
        .map(|c| c.left.coordinates.len())
        .sum::<usize>();
    let right_unique = censuses
        .iter()
        .map(|c| c.right.coordinates.len())
        .sum::<usize>();
    let left_occ = censuses.iter().map(|c| c.left.occurrences).sum::<usize>();
    let right_occ = censuses.iter().map(|c| c.right.occurrences).sum::<usize>();
    let outside_left = censuses
        .iter()
        .map(|c| c.left.outside_window_occurrences())
        .sum::<usize>();
    let constants = censuses.iter().map(|c| c.constant_terms).sum::<usize>();
    let compact_aliases = censuses
        .iter()
        .map(|c| c.compact_alias_terms)
        .sum::<usize>();
    let left_regions = std::array::from_fn::<_, 3, _>(|r| {
        censuses
            .iter()
            .map(|c| c.left.by_region_occurrences[r])
            .sum::<usize>()
    });
    let right_regions = std::array::from_fn::<_, 3, _>(|r| {
        censuses
            .iter()
            .map(|c| c.right.by_region_occurrences[r])
            .sum::<usize>()
    });
    let left_region_unique = std::array::from_fn::<_, 3, _>(|r| {
        censuses
            .iter()
            .map(|c| c.left.by_region_coordinates[r].len())
            .sum::<usize>()
    });
    let right_region_unique = std::array::from_fn::<_, 3, _>(|r| {
        censuses
            .iter()
            .map(|c| c.right.by_region_coordinates[r].len())
            .sum::<usize>()
    });
    let left_ranges = censuses.iter().map(|c| c.left.range()).collect::<Vec<_>>();
    let right_ranges = censuses.iter().map(|c| c.right.range()).collect::<Vec<_>>();
    let left_blocks = censuses.iter().map(|c| blocks(&c.left)).collect::<Vec<_>>();
    let right_blocks = censuses
        .iter()
        .map(|c| blocks(&c.right))
        .collect::<Vec<_>>();
    let left_buckets = censuses
        .iter()
        .map(|c| buckets(&c.left))
        .collect::<Vec<_>>();
    let right_buckets = censuses
        .iter()
        .map(|c| buckets(&c.right))
        .collect::<Vec<_>>();
    let left_fold_closure_bits = censuses
        .iter()
        .map(|c| c.left.fold_buckets.len() * (1 << 16))
        .sum::<usize>();
    let right_fold_closure_bits = censuses
        .iter()
        .map(|c| c.right.fold_buckets.len() * (1 << 16))
        .sum::<usize>();
    let outside_alias_left = censuses
        .iter()
        .map(|c| c.compact_alias_left.len())
        .sum::<usize>();

    assert_eq!(left_regions.iter().sum::<usize>(), left_occ);
    assert_eq!(right_regions.iter().sum::<usize>(), right_occ);
    assert_eq!(left_region_unique.iter().sum::<usize>(), left_unique);
    assert_eq!(right_region_unique.iter().sum::<usize>(), right_unique);
    assert_eq!(
        outside_alias_left,
        2 * crate::header_compact_links::HASH_WIDTH
    );
    println!("C264_ROLE1_SUPPORT_CENSUS owners=9214,9215 terms_each=396561 omitted_worktree_each=78194 left_occ={left_occ} left_unique_owner_local_sum={left_unique} left_outside_window_occ={outside_left} left_region_occ={left_regions:?} left_region_unique_owner_local_sum={left_region_unique:?} left_range={left_ranges:?} left_blocks_8kiB={left_blocks:?} left_low16_buckets={left_buckets:?} left_low16_closure_bits={left_fold_closure_bits} right_occ={right_occ} right_unique_owner_local_sum={right_unique} right_region_occ={right_regions:?} right_region_unique_owner_local_sum={right_region_unique:?} right_range={right_ranges:?} right_blocks_8kiB={right_blocks:?} right_low16_buckets={right_buckets:?} right_low16_closure_bits={right_fold_closure_bits} constant_terms={constants} compact_alias_terms={compact_aliases} compact_alias_left_outside_window={outside_alias_left} window_only=false spatial_escape=false proof=false");
}

//! Pure required-author classifier for the fixed Eligible08 Bank53 identity.
//!
//! This selects the policy-required writer from the tuple alone. It does not
//! inspect producer routes, claims, packed values, or physical custody.

const N: usize = 1_827_840;
const S: usize = 1 << 21;
const CONTEXTS: usize = 2;
const BANK_BITS: usize = 8_192;
const MAP_END: usize = 5_757;
const SCORE_END: usize = 7_805;

const REGULAR_FIRST: usize = 845_887;
const REGULAR_STRIDE: usize = 128;
const REGULAR_LAST_J: [usize; CONTEXTS] = [7_539, 7_538];
const GUARDS: [usize; CONTEXTS] = [1_810_905, 1_810_842];
const CLIPPED_OWNERS: [usize; CONTEXTS] = [1_810_904, 1_810_841];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WriterRegion { Map, Score, Slack, HeaderZero }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Region { start: usize, end: usize, writer: WriterRegion }

fn writer_regions(owner: usize, context: usize) -> [Region; 3] {
    if owner >= N {
        return [
            Region { start: 0, end: MAP_END, writer: WriterRegion::HeaderZero },
            Region { start: MAP_END, end: SCORE_END, writer: WriterRegion::HeaderZero },
            Region { start: SCORE_END, end: BANK_BITS, writer: WriterRegion::HeaderZero },
        ];
    }
    [
        Region { start: 0, end: MAP_END, writer: WriterRegion::Map },
        Region { start: MAP_END, end: SCORE_END,
            writer: if owner < N && score_writer(owner, context).is_some() {
                WriterRegion::Score
            } else { WriterRegion::HeaderZero } },
        Region { start: SCORE_END, end: BANK_BITS,
            writer: if owner < N && is_dedicated_slack_owner(owner) {
                WriterRegion::Slack
            } else { WriterRegion::HeaderZero } },
    ]
}

/// The Score source family required at a scored Bank53 owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScoreEndpointKind {
    FirstModern,
    Regular,
    Clipped,
}

/// The policy-required Bank53 author. `HeaderZero` is an author requirement;
/// a zero packed bit without an exclusive HEADER claim does not satisfy it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RequiredWriter {
    Map { context: usize },
    ScoreAnchor { context: usize },
    ScoreReplay { context: usize, endpoint: ScoreEndpointKind },
    Slack { context: usize },
    HeaderZero,
}

/// Return the required writer for the frozen Eligible08 tuple.
///
/// Inputs are a logical owner, context index, and Bank53-relative bit offset.
/// Invalid coordinates fail closed. The function is deliberately independent
/// of observed source routes and claims.
pub(crate) fn required_bank53_writer(
    owner: usize,
    context: usize,
    offset: usize,
) -> Result<RequiredWriter, &'static str> {
    if owner >= S {
        return Err("Bank53 owner outside fixed slot domain");
    }
    if context >= CONTEXTS {
        return Err("Bank53 context outside fixed context domain");
    }
    if offset >= BANK_BITS {
        return Err("Bank53 offset outside fixed bank domain");
    }

    let region = writer_regions(owner, context).into_iter()
        .find(|region| region.start <= offset && offset < region.end)
        .expect("validated Bank53 offset belongs to a writer region");
    Ok(match region.writer {
        WriterRegion::Map => RequiredWriter::Map { context },
        WriterRegion::Score => score_writer(owner, context)
            .expect("Score region is created only for a Score owner"),
        WriterRegion::Slack => RequiredWriter::Slack { context },
        WriterRegion::HeaderZero => RequiredWriter::HeaderZero,
    })
}

pub(crate) fn require_ordinary_unscored_carry_map_header(
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    schedule: &crate::h21_scheduled_max_cap::Plan,
) -> Result<(), String> {
    if owner >= N { return Err("Map/HEADER owner outside active Bank53 domain".into()); }
    if class != crate::daa_history_roster::OwnerClass::Carry {
        return Err("Map/HEADER owner is not a Carry".into());
    }
    if schedule.descriptor() != crate::bank53_map::CutDescriptor::eligible08() {
        return Err("Map/HEADER schedule is not Eligible08".into());
    }
    if schedule.has_owner_writer(owner)? {
        return Err("Map/HEADER owner has scheduled MAX or Cap writer".into());
    }
    for context in 0..CONTEXTS {
        require_map_header_region_cut(owner, context)?;
    }
    Ok(())
}

pub(crate) fn require_map_header_region_cut(
    owner: usize,
    context: usize,
) -> Result<usize, String> {
    if owner >= N { return Err("Map/HEADER owner outside active Bank53 domain".into()); }
    if context >= CONTEXTS { return Err("Map/HEADER context outside Bank53 domain".into()); }
    let regions = writer_regions(owner, context);
    if regions[0].writer == WriterRegion::Map
        && regions[1].writer == WriterRegion::HeaderZero
        && regions[2].writer == WriterRegion::HeaderZero
        && regions[0].start == 0 && regions[0].end == MAP_END
        && regions[1].start == regions[0].end && regions[1].end == SCORE_END
        && regions[2].start == regions[1].end && regions[2].end == BANK_BITS
    {
        Ok(MAP_END)
    } else {
        Err("Map/HEADER owner has a non-Map or non-HEADER writer region".into())
    }
}

fn score_writer(owner: usize, context: usize) -> Option<RequiredWriter> {
    if matches!(owner, 417_790 | 845_758) {
        return Some(RequiredWriter::ScoreAnchor { context });
    }
    if owner == 845_759 {
        return Some(RequiredWriter::ScoreReplay {
            context,
            endpoint: ScoreEndpointKind::FirstModern,
        });
    }

    let regular = owner.checked_sub(REGULAR_FIRST).and_then(|delta| {
        if delta % REGULAR_STRIDE != 0 {
            return None;
        }
        let j = delta / REGULAR_STRIDE;
        (j <= REGULAR_LAST_J[context]
            && owner.checked_add(1).is_some_and(|origin| origin <= GUARDS[context]))
            .then_some(())
    }).is_some();
    if regular {
        return Some(RequiredWriter::ScoreReplay {
            context,
            endpoint: ScoreEndpointKind::Regular,
        });
    }

    if owner == CLIPPED_OWNERS[context] {
        return Some(RequiredWriter::ScoreReplay {
            context,
            endpoint: ScoreEndpointKind::Clipped,
        });
    }
    None
}

fn is_dedicated_slack_owner(owner: usize) -> bool {
    matches!(owner, 0 | 417_790 | 845_758 | 845_759)
        || owner >= REGULAR_FIRST
            && owner <= REGULAR_FIRST + REGULAR_STRIDE * REGULAR_LAST_J[0]
            && (owner - REGULAR_FIRST) % REGULAR_STRIDE == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn required(owner: usize, context: usize, offset: usize) -> RequiredWriter {
        required_bank53_writer(owner, context, offset).expect("valid Bank53 tuple")
    }

    #[test]
    fn rejects_coordinates_outside_fixed_identity() {
        assert!(required_bank53_writer(S, 0, 0).is_err());
        assert!(required_bank53_writer(0, CONTEXTS, 0).is_err());
        assert!(required_bank53_writer(0, 0, BANK_BITS).is_err());
    }

    #[test]
    fn frozen_classifier_geometry_matches_canonical_eligible08_sources() {
        let cut = crate::bank53_map::CutDescriptor::eligible08();
        assert_eq!(N as u64, crate::bank53_map::BANK53_N);
        assert_eq!(S, 1 << 21);
        assert_eq!(CONTEXTS, crate::bank53_map::CONTEXTS);
        assert_eq!(MAP_END, crate::bank53_map::MAP_LIVE);
        assert_eq!(cut.terminals(), [1_827_840, 1_810_842]);
        assert_eq!(cut.guards(), GUARDS);
        assert_eq!(cut.modern_start(), 845_760);
        assert_eq!(SCORE_END - MAP_END, crate::origin_score::INPUT);
        assert_eq!(SCORE_END, crate::bank53_slack::SLACK_INPUT_START);
        assert_eq!(SCORE_END, MAP_END + crate::origin_score::INPUT);
        assert_eq!(BANK_BITS, crate::bank53_slack::SLACK_INPUT_END);
        assert_eq!(crate::bank53_slack::SLACK_ZERO_COUNT,
            BANK_BITS - SCORE_END);
    }

    #[test]
    fn classifies_bank_boundaries_and_header_zero_distinctly() {
        assert_eq!(required(10, 0, 5_756), RequiredWriter::Map { context: 0 });
        assert_eq!(required(10, 1, 5_757), RequiredWriter::HeaderZero);
        assert_eq!(required(10, 0, 7_804), RequiredWriter::HeaderZero);
        assert_eq!(required(10, 1, 7_805), RequiredWriter::HeaderZero);
        assert_eq!(required(10, 0, 8_191), RequiredWriter::HeaderZero);
        assert_eq!(required(0, 0, 7_805), RequiredWriter::Slack { context: 0 });
        assert_eq!(required(845_887, 1, 7_805), RequiredWriter::Slack { context: 1 });
    }

    #[test]
    fn classifies_score_anchors_first_regular_and_clipped_endpoints() {
        for context in 0..CONTEXTS {
            for owner in [417_790, 845_758] {
                assert_eq!(required(owner, context, MAP_END),
                    RequiredWriter::ScoreAnchor { context });
            }
            assert_eq!(required(845_759, context, MAP_END), RequiredWriter::ScoreReplay {
                context, endpoint: ScoreEndpointKind::FirstModern,
            });
        }
        assert_eq!(required(845_887, 0, MAP_END), RequiredWriter::ScoreReplay {
            context: 0, endpoint: ScoreEndpointKind::Regular,
        });
        assert_eq!(required(1_810_879, 0, MAP_END), RequiredWriter::ScoreReplay {
            context: 0, endpoint: ScoreEndpointKind::Regular,
        });
        assert_eq!(required(1_810_751, 1, MAP_END), RequiredWriter::ScoreReplay {
            context: 1, endpoint: ScoreEndpointKind::Regular,
        });
        assert_eq!(required(1_810_904, 0, MAP_END), RequiredWriter::ScoreReplay {
            context: 0, endpoint: ScoreEndpointKind::Clipped,
        });
        assert_eq!(required(1_810_841, 1, MAP_END), RequiredWriter::ScoreReplay {
            context: 1, endpoint: ScoreEndpointKind::Clipped,
        });
    }

    #[test]
    fn score_and_slack_membership_are_context_independent_where_specified() {
        assert_eq!(required(1_810_879, 0, MAP_END), RequiredWriter::ScoreReplay {
            context: 0, endpoint: ScoreEndpointKind::Regular,
        });
        assert_eq!(required(1_810_879, 1, MAP_END), RequiredWriter::HeaderZero);
        for context in 0..CONTEXTS {
            assert_eq!(required(1_810_879, context, SCORE_END),
                RequiredWriter::Slack { context });
        }
        assert_eq!(required(1_810_904, 1, MAP_END), RequiredWriter::HeaderZero);
        assert_eq!(required(1_810_841, 0, MAP_END), RequiredWriter::HeaderZero);
    }

    #[test]
    fn dedicated_slack_set_has_exact_singleton_and_regular_edges() {
        for owner in [0, 417_790, 845_758, 845_759, 845_887, 1_810_879] {
            assert_eq!(required(owner, 0, SCORE_END), RequiredWriter::Slack { context: 0 });
        }
        for owner in [417_789, 417_791, 845_757, 845_760, 845_886, 1_810_880] {
            assert_eq!(required(owner, 0, SCORE_END), RequiredWriter::HeaderZero,
                "owner={owner} must be outside D");
        }
    }

    #[test]
    fn padding_uses_header_zero_at_every_offset_in_both_contexts() {
        for owner in [N, S - 1] {
            for context in 0..CONTEXTS {
                for offset in 0..BANK_BITS {
                    // Independent C520 oracle: assert the public classifier result
                    // directly, without deriving the expectation via `required`.
                    assert_eq!(required_bank53_writer(owner, context, offset),
                        Ok(RequiredWriter::HeaderZero),
                        "owner={owner} context={context} offset={offset}");
                }
            }
        }
        // The oracle distinguishes required HEADER custody from equal-zero
        // Map/Slack families; claim presence and physical authorship are tested
        // by the downstream typed reader, not by this pure classifier.
        assert_ne!(RequiredWriter::HeaderZero, RequiredWriter::Map { context: 0 });
        assert_ne!(RequiredWriter::HeaderZero, RequiredWriter::Slack { context: 0 });
    }

    #[test]
    fn shared_regions_cover_each_context_and_preserve_tuple_classification() {
        for owner in [2, 417_790, 845_758, 845_759, 845_887, 1_810_841, N] {
            for context in 0..CONTEXTS {
                let regions = writer_regions(owner, context);
                assert_eq!(regions[0].start, 0);
                for pair in regions.windows(2) { assert_eq!(pair[0].end, pair[1].start); }
                assert_eq!(regions[2].end, BANK_BITS);
                for offset in 0..BANK_BITS {
                    let region = regions.iter().find(|r| r.start <= offset && offset < r.end).unwrap();
                    let expected_family = match required(owner, context, offset) {
                        RequiredWriter::Map { .. } => WriterRegion::Map,
                        RequiredWriter::ScoreAnchor { .. } | RequiredWriter::ScoreReplay { .. } => WriterRegion::Score,
                        RequiredWriter::Slack { .. } => WriterRegion::Slack,
                        RequiredWriter::HeaderZero => WriterRegion::HeaderZero,
                    };
                    assert_eq!(region.writer, expected_family,
                        "owner={owner} context={context} offset={offset}");
                }
            }
        }
        let regions = writer_regions(2, 0);
        assert_eq!(regions.map(|r| (r.start, r.end, r.writer)), [
            (0, 5_757, WriterRegion::Map),
            (5_757, 7_805, WriterRegion::HeaderZero),
            (7_805, 8_192, WriterRegion::HeaderZero),
        ]);
    }

    #[test]
    fn ordinary_carry_policy_accepts_unscored_owners_and_rejects_other_shapes() {
        use crate::{daa_history_roster::OwnerClass, h21_scheduled_max_cap::Plan};
        let schedule = Plan::eligible08();
        for owner in [2, 844_673, 844_674, 845_760] {
            assert_eq!(schedule.has_owner_writer(owner).unwrap(), false);
            assert!(require_ordinary_unscored_carry_map_header(owner, OwnerClass::Carry, &schedule).is_ok(),
                "ordinary Carry owner {owner}");
        }
        for owner in [417_790, 845_758, 845_759, 0, N] {
            assert!(require_ordinary_unscored_carry_map_header(owner, OwnerClass::Carry, &schedule).is_err(),
                "Score/Slack/padding owner {owner}");
        }
        assert!(require_ordinary_unscored_carry_map_header(2, OwnerClass::Initial, &schedule).is_err());
        assert!(require_ordinary_unscored_carry_map_header(2, OwnerClass::Carry, &Plan::new()).is_err());
        for owner in [844_670, 845_759] {
            assert!(schedule.has_owner_writer(owner).unwrap(), "scheduled owner {owner}");
            assert!(require_ordinary_unscored_carry_map_header(owner, OwnerClass::Carry, &schedule).is_err());
        }
    }

    #[test]
    fn map_header_region_cut_is_exact_and_rejects_nonordinary_regions() {
        for context in 0..CONTEXTS {
            assert_eq!(require_map_header_region_cut(1, context).unwrap(), MAP_END);
            for owner in [2, 844_673, 844_674, 845_760] {
                assert_eq!(require_map_header_region_cut(owner, context).unwrap(), 5_757);
            }
            for owner in [417_790, 845_758, 845_759, 0, N, S - 1] {
                assert!(require_map_header_region_cut(owner, context).is_err(),
                    "owner={owner} context={context}");
            }
        }
        assert!(require_map_header_region_cut(N, 0).is_err());
        assert!(require_map_header_region_cut(2, CONTEXTS).is_err());
        // Region helper qualifies writer geometry; class policy remains stricter.
        let schedule = crate::h21_scheduled_max_cap::Plan::eligible08();
        assert!(require_ordinary_unscored_carry_map_header(
            1, crate::daa_history_roster::OwnerClass::Initial, &schedule).is_err());
    }
}

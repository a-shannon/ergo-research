use num_bigint::BigUint;
use crate::global_u_roster::{self as roster, CandidateSource, Schedule, SuppliedCandidate};

fn n(x: u64) -> BigUint { BigUint::from(x) }

fn q1_formula_bound() -> BigUint {
    n(roster::INITIAL_I) * crate::legacy_envelope_map::TE as u64
        / (1_000_000u64 + roster::K0 as u64)
}

fn candidates_1984(with_q1: bool) -> Vec<SuppliedCandidate> {
    Schedule::new(1984).unwrap().iter().filter_map(|source| match source {
        CandidateSource::HeaderDifficulty { .. } => Some(SuppliedCandidate { source, value: n(roster::INITIAL_I) }),
        CandidateSource::LegacyBound { q: 1, .. } if with_q1 => Some(SuppliedCandidate {
            source, value: q1_formula_bound(),
        }),
        CandidateSource::LegacyBound { .. } => None,
    }).collect()
}

#[test]
fn n1984_starts_with_work_owner_zero_then_first_legacy_q1() {
    let mut it = Schedule::new(1984).unwrap().iter();
    assert_eq!(it.next(), Some(CandidateSource::HeaderDifficulty { height: 2, work_owner: 0 }));
    assert_eq!(it.next(), Some(CandidateSource::HeaderDifficulty { height: 3, work_owner: 1 }));
    let mut last = None;
    for source in it { last = Some(source); }
    assert_eq!(last, Some(CandidateSource::LegacyBound {
        q: 1, endpoint: 2048, map_owner: 1983, ell: 1,
    }));
}

#[test]
fn q407_is_excluded_and_q408_resumes_with_exact_map_owner() {
    let schedule = Schedule::new(418_752).unwrap();
    let legacy = schedule.legacy_items().collect::<Vec<_>>();
    assert_eq!(legacy.last(), Some(&CandidateSource::LegacyBound {
        q: 408, endpoint: 418_816, map_owner: 418_751, ell: 8,
    }));
    assert!(legacy.iter().any(|x| *x == CandidateSource::LegacyBound {
        q: 406, endpoint: 416_768, map_owner: 416_703, ell: 8,
    }));
    assert!(!legacy.iter().any(|x| matches!(x, CandidateSource::LegacyBound { q: 407, .. })));
}

#[test]
fn capped_legacy_schedule_ends_at_q823() {
    let schedule = Schedule::new(843_712).unwrap();
    assert_eq!(schedule.legacy_items().last(), Some(CandidateSource::LegacyBound {
        q: 823, endpoint: 843_776, map_owner: 843_711, ell: 8,
    }));
}

#[test]
fn complete_n1984_roster_catches_omitted_cap_raising_q1() {
    // Formula-only q1 candidate at endpoint 2048 / owner 1983. This does not
    // construct a native-valid transcript or a physical Map row.
    let d = n(roster::INITIAL_I);
    let t1984 = 2_000_000u64;
    let t1024 = 1_000_000u64;
    let delta = t1984 - t1024 + roster::K0 as u64;
    let b2048 = &d * crate::legacy_envelope_map::TE as u64 / delta;
    assert_eq!(d, n(1_199_990_374_400));
    assert_eq!(t1984 - t1024, 1_000_000);
    assert_eq!(delta, 1_000_064);
    assert_eq!(b2048, n(147_445_380_701_907));

    let complete = roster::fold(1984, candidates_1984(true)).unwrap();
    assert_eq!(complete.max_difficulty, d);
    assert_eq!(complete.modern_floor, n(roster::INITIAL_I) * 3u8 / 2u8);
    assert_eq!(complete.maximum_candidate, b2048);
    assert_eq!(complete.exponent, 48);
    assert_eq!(complete.u, BigUint::from(1u8) << 48usize);
    assert_eq!((complete.header_count, complete.legacy_count), (1983, 1));
    let baseline_cap = BigUint::from(1u8) << 47usize;
    let baseline_max = n(roster::RESET_CHILD_417792).max(d.clone())
        .max(&d * 3u8 / 2u8);
    assert!(baseline_max > (BigUint::from(1u8) << 46usize));
    assert!(baseline_max <= baseline_cap);
    assert!(b2048 > baseline_cap);

    let missing = roster::fold(1984, candidates_1984(false));
    assert_eq!(missing.unwrap_err(), "global-U candidate sequence missing item");
    let mut without_q1 = candidates_1984(true);
    without_q1.pop();
    assert!(roster::fold(1984, without_q1).is_err());
    assert_eq!(BigUint::from(roster::RESET_CHILD_417792), BigUint::from(122_702_199_259_136u64));
    assert_eq!(BigUint::from(roster::RESET_CHILD_417793), BigUint::from(122_702_199_259_136u64));
    assert_eq!(n(roster::RESET_CHILD_417792).bits(), 47);
}

#[test]
fn wrong_owner_and_out_of_order_header_are_rejected() {
    let mut wrong_owner = candidates_1984(true);
    wrong_owner[0].source = CandidateSource::HeaderDifficulty { height: 2, work_owner: 1 };
    assert!(roster::fold(1984, wrong_owner).is_err());

    let mut order = candidates_1984(true);
    order.swap(0, 1);
    assert!(roster::fold(1984, order).is_err());
}

#[test]
fn extra_candidate_is_rejected() {
    let mut extra = candidates_1984(true);
    extra.push(SuppliedCandidate {
        source: CandidateSource::HeaderDifficulty { height: 1985, work_owner: 1983 },
        value: n(roster::INITIAL_I),
    });
    assert!(roster::fold(1984, extra).is_err());
}

#[test]
fn zero_difficulty_and_oversized_final_envelope_are_rejected() {
    let mut zero = candidates_1984(true);
    zero[0].value = BigUint::from(0u8);
    assert!(roster::fold(1984, zero).is_err());

    let mut oversized = candidates_1984(true);
    oversized[0].value = BigUint::from(1u8) << 64usize;
    assert_eq!(roster::fold(1984, oversized).unwrap_err(),
        "global-U final envelope exceeds 2^64");
}

#[test]
fn legacy_bound_below_initial_is_rejected() {
    let mut candidates = candidates_1984(true);
    candidates.last_mut().unwrap().value = n(roster::INITIAL_I - 1);
    assert_eq!(roster::fold(1984, candidates).unwrap_err(),
        "global-U legacy bound below initial");
}

fn reset_candidates(bad_height: Option<u64>) -> impl Iterator<Item = SuppliedCandidate> {
    Schedule::new(417_793).unwrap().iter().map(move |source| {
        let value = match source {
            CandidateSource::HeaderDifficulty { height, .. }
                if height == 417_792 || height == 417_793 => {
                    if Some(height) == bad_height { n(roster::INITIAL_I) }
                    else { n(roster::RESET_CHILD_417792) }
                }
            _ => n(roster::INITIAL_I),
        };
        SuppliedCandidate { source, value }
    })
}

#[test]
fn both_reset_child_difficulties_are_checked_when_present() {
    let complete = roster::fold(417_793, reset_candidates(None)).unwrap();
    assert_eq!(complete.max_difficulty, n(roster::RESET_CHILD_417792));
    for height in [417_792, 417_793] {
        assert_eq!(roster::fold(417_793, reset_candidates(Some(height))).unwrap_err(),
            "global-U reset child difficulty mismatch");
    }
}

#[test]
fn full_h21_global_u_schedule_has_exact_d_and_legacy_candidates() {
    const N: u64 = 1_827_840;
    let schedule = Schedule::new(N).unwrap();
    let mut joined = schedule.iter();
    let mut header_count = 0u64;

    for height in 2..=N {
        let expected = CandidateSource::HeaderDifficulty {
            height,
            work_owner: height - 2,
        };
        assert_eq!(joined.next(), Some(expected), "header height {height}");
        match height {
            417_792 => assert_eq!(expected, CandidateSource::HeaderDifficulty {
                height, work_owner: 417_790,
            }),
            417_793 => assert_eq!(expected, CandidateSource::HeaderDifficulty {
                height, work_owner: 417_791,
            }),
            841_729 => assert_eq!(expected, CandidateSource::HeaderDifficulty {
                height, work_owner: 841_727,
            }),
            _ => {}
        }
        header_count += 1;
    }
    assert_eq!(header_count, N - 1);

    let mut legacy_api = schedule.legacy_items();
    let mut legacy_count = 0u64;
    for q in 1..=823 {
        if q == 407 { continue; }
        let expected = CandidateSource::LegacyBound {
            q,
            endpoint: 1024 * (q + 1),
            map_owner: q * 1024 + 959,
            ell: q.min(8) as usize,
        };
        match q {
            1 => assert_eq!(expected, CandidateSource::LegacyBound {
                q: 1, endpoint: 2_048, map_owner: 1_983, ell: 1,
            }),
            9 => assert_eq!(expected, CandidateSource::LegacyBound {
                q: 9, endpoint: 10_240, map_owner: 10_175, ell: 8,
            }),
            _ => {}
        }
        assert_eq!(joined.next(), Some(expected), "legacy q {q}");
        assert_eq!(legacy_api.next(), Some(expected), "legacy API q {q}");
        legacy_count += 1;
    }
    assert_eq!(legacy_count, 822);
    assert_eq!(legacy_api.next(), None);
    assert_eq!(joined.next(), None);
}

#[test]
fn q9_tuple_mutation_and_q9_q10_permutation_are_rejected() {
    // This smaller cut contains q9 and q10; marker values isolate tuple
    // identity and are not D or B derivations.
    const N: u64 = 11_200;
    let sources = Schedule::new(N).unwrap().iter().collect::<Vec<_>>();
    let q9_index = sources.iter().position(|source| matches!(
        source, CandidateSource::LegacyBound { q: 9, .. }
    )).unwrap();
    let q10_index = sources.iter().position(|source| matches!(
        source, CandidateSource::LegacyBound { q: 10, .. }
    )).unwrap();
    assert_eq!(sources[q9_index], CandidateSource::LegacyBound {
        q: 9, endpoint: 10_240, map_owner: 10_175, ell: 8,
    });
    assert_eq!(sources[q10_index], CandidateSource::LegacyBound {
        q: 10, endpoint: 11_264, map_owner: 11_199, ell: 8,
    });
    let marker_candidates = |items: Vec<CandidateSource>| {
        items.into_iter().map(|source| SuppliedCandidate {
            source,
            value: n(roster::INITIAL_I),
        }).collect::<Vec<_>>()
    };

    let mut mutated = sources.clone();
    let CandidateSource::LegacyBound { q, endpoint, map_owner, ell } = mutated[q9_index] else {
        panic!("q9 source missing");
    };
    mutated[q9_index] = CandidateSource::LegacyBound {
        q, endpoint, map_owner: map_owner + 1, ell,
    };
    assert_eq!(roster::fold(N, marker_candidates(mutated)).unwrap_err(),
        "global-U candidate id/owner/order mismatch");

    let mut permuted = sources;
    permuted.swap(q9_index, q10_index);
    assert_eq!(roster::fold(N, marker_candidates(permuted)).unwrap_err(),
        "global-U candidate id/owner/order mismatch");
}

use super::*;
use num_bigint::BigUint;
use std::collections::BTreeMap;

fn plan(owner: usize) -> ClassEquationPlan {
    ClassEquationPlan::for_member(CutDescriptor::eligible08(), owner).unwrap()
}
fn terms(p: &ClassEquationPlan, context: usize) -> Vec<Term> {
    let mut out = Vec::new(); p.emit(context, |term| out.push(term)).unwrap(); out
}
fn point(n: usize, seed: u64) -> Vec<Fr> {
    (0..n).map(|i| Fr::from(seed + i as u64)).collect()
}
fn literal_spec(context: usize) -> score::Spec {
    score::Spec { active: true, origin_one: false, reducing: true, first: false,
        terminal: false, empty_terminal: false, maturity: [4995, 2090][context],
        guard_total: None, expected: BigUint::from(0u8) }
}

// Independent placement oracle: literal published addresses, no production
// emitter, plan author, plan placement helper, or coefficient routine. Native
// local arithmetic is deliberately shared; this tests the class compiler join.
fn literal_reference(owner: usize, context: usize, previous: usize) -> Vec<Term> {
    let base = 677_501 + context * 8192;
    let row_base = [487_421, 502_652][context];
    let mut out = Vec::new();
    score::emit_local(&literal_spec(context), |local| {
        let g = local.term.gate;
        out.push(Term { row: owner * 524_288 + row_base + local.term.row,
            gate: Gate { left: (if local.previous { previous } else { owner }) * 1_048_576 + base + g.left,
                right: owner * 1_048_576 + base + g.right,
                c0: g.c0, c1: g.c1, c2: g.c2, c3: g.c3 } });
    }).unwrap();
    for bit in 0..65 {
        out.push(Term { row: owner * 524_288 + [491_629, 506_860][context] + bit,
            gate: Gate { left: owner * 1_048_576 + base + 224 + bit,
                right: owner * 1_048_576 + [1_000_770, 1_002_818][context] + 740 + bit,
                c0: Fr::zero(), c1: Fr::one(), c2: -Fr::one(), c3: Fr::zero() } });
    }
    for bit in 0..224 {
        let row = owner * 524_288 + [491_694, 506_925][context] + bit;
        out.push(Term { row, gate: Gate { left: owner * 1_048_576 + base + bit, right: 0,
            c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
        out.push(Term { row, gate: Gate { left: (owner - 1) * 1_048_576 + 987_450 + bit, right: 0,
            c0: Fr::zero(), c1: -Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
    }
    out
}
fn reference_fold(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    // Separate equality implementation to avoid testing eq against itself.
    let weight = |point: &[Fr], index: usize| -> Fr {
        let mut product = Fr::one(); let mut index = index;
        for z in point { product *= if index % 2 == 0 { Fr::one() - z } else { *z }; index /= 2; }
        assert_eq!(index, 0); product
    };
    let mut out = [Fr::zero(); 4];
    for term in terms {
        let g = &term.gate;
        let w = weight(r, term.row) * weight(u, g.left) * weight(v, g.right);
        for (sum, c) in out.iter_mut().zip([g.c0, g.c1, g.c2, g.c3]) { *sum += w * c; }
    }
    out
}
fn source(p: &ClassEquationPlan) -> ([Vec<Term>; 2], Vec<(usize, ScoreRelationReadAuthor, Fr)>) {
    ([terms(p, 0), terms(p, 1)], p.reads().into_iter().map(|(w, a)| (w, a, Fr::zero())).collect())
}

#[test]
fn c567_class_boundaries_second_regular_and_both_clipped_routes() {
    for (owner, previous, maximum, active) in [
        (845_887, 845_759, 844_798, [true, true]),
        (846_015, 845_887, 844_926, [true, true]),
        (1_000_127, 999_999, 999_038, [true, true]),
        (1_810_751, 1_810_623, 1_809_662, [true, true]),
        (1_810_879, 1_810_751, 1_809_790, [true, false]),
        (1_810_904, 1_810_879, 1_809_918, [true, false]),
        (1_810_841, 1_810_751, 1_809_790, [false, true]),
    ] {
        let p = plan(owner); assert_eq!(p.owner(), owner); assert_eq!(p.active(), active);
        for context in 0..2 {
            if let Some(a) = p.authors()[context] {
                assert_eq!(a, ScoreReplayAuthor { context, origin: owner + 1,
                    previous_owner: previous, max_owner: maximum, cap_owner: owner });
                assert_eq!(terms(&p, context), literal_reference(owner, context, previous));
                assert_eq!(terms(&p, context).len(), 8545);
            } else { assert!(terms(&p, context).is_empty()); }
        }
    }
    assert_eq!(plan(1_810_904).kind(), MemberKind::Clipped { context: 0 });
    assert_eq!(plan(1_810_841).kind(), MemberKind::Clipped { context: 1 });
    let mut owners = std::collections::BTreeSet::new();
    for member in ClassEquationPlan::members() {
        let p = member.unwrap();
        assert!(owners.insert(p.owner()));
        for context in 0..2 {
            let writer = bank53_required_writer::required_bank53_writer(p.owner(), context, 5757).unwrap();
            assert_eq!(p.active()[context], matches!(writer, RequiredWriter::ScoreReplay { .. }));
        }
    }
    assert_eq!(owners.len(), 7542);
}

#[test]
fn c567_invalid_origin_residue_neighbours_padding_and_descriptor() {
    for owner in [0, 417_790, 845_758, 845_759, 845_886, 845_888, 846_014, 846_016,
        1_810_840, 1_810_842, 1_810_903, 1_810_905, 1_811_007, 1_827_840, (1 << 21) - 1, 1 << 21, usize::MAX] {
        assert!(ClassEquationPlan::for_member(CutDescriptor::eligible08(), owner).is_err(), "{owner}");
    }
    assert!(ClassEquationPlan::for_member(CutDescriptor::diagnostic08(), 846_015).is_err());
    let p = plan(846_015);
    assert!(p.emit(2, |_| {}).is_err());
    assert!(p.map_difficulty_reads(2).is_err());
}

#[test]
fn c567_map_d_import_endpoint_and_inactive_zero_role() {
    for (owner, context, count) in [(846_015, 0, 224), (846_015, 1, 224),
        (1_810_751, 1, 224),
        (1_810_841, 0, 224), (1_810_841, 1, 0),
        (1_810_879, 0, 224), (1_810_879, 1, 0), (1_810_904, 0, 224), (1_810_904, 1, 0)] {
        let p = plan(owner); let reads = p.map_difficulty_reads(context).unwrap();
        assert_eq!(reads.len(), count);
        let map = crate::legacy_envelope_map::Map::new(
            [1_827_840, 1_810_842][context], 21, 55).unwrap();
        let imported: Vec<_> = map.imports(owner as u64).unwrap().into_iter()
            .flat_map(|import| (0..import.width).map(move |bit| (import, bit)))
            .map(|(import, bit)| map.input_index(import, bit).unwrap()).collect();
        assert_eq!(reads, imported);
        for (bit, wire) in reads.into_iter().enumerate() { assert_eq!(wire, owner * 1_048_576 + 987_674 + bit); }
        assert!(p.required_predicates().contains(&RequiredPredicate::Map { context, owner }));
    }
    // The exact clipped Score remains active despite selecting no own D.
    assert!(plan(1_810_841).active()[1]);
}

#[test]
fn c567_all_dependency_metadata_missing_retag_duplicate_and_order() {
    for owner in [845_887, 846_015, 1_810_879, 1_810_904, 1_810_841] {
        let p = plan(owner); let required = p.required_predicates();
        p.require_dependency_metadata(&required).unwrap();
        for i in 0..required.len() {
            let mut missing = required.clone(); missing.remove(i);
            assert!(p.require_dependency_metadata(&missing).is_err());
            let mut duplicate = required.clone(); duplicate.insert(i, required[i]);
            assert!(p.require_dependency_metadata(&duplicate).is_err());
            let mut wrong = required.clone(); wrong[i] = RequiredPredicate::HeaderDaa { owner: usize::MAX };
            assert!(p.require_dependency_metadata(&wrong).is_err());
        }
        let a = p.authors().iter().flatten().next().unwrap();
        assert!(required.contains(&RequiredPredicate::PreviousScore { context: a.context, owner: a.previous_owner }));
        assert!(required.contains(&RequiredPredicate::PremodernAnchor { context: a.context, owner: 417_790 }));
        assert!(required.contains(&RequiredPredicate::PremodernAnchor { context: a.context, owner: 845_758 }));
        assert!(required.contains(&RequiredPredicate::WorkUpper { owner: owner - 1, height: owner + 1 }));
    }
}

#[test]
fn c567_writer_retirement_specialization_preserves_inactive_and_slack() {
    let scheduled = crate::h21_scheduled_max_cap::Plan::eligible08();
    for owner in [846_015, 1_810_879, 1_810_904, 1_810_841] {
        let p = plan(owner); p.require_writer_specialization().unwrap();
        let requests = p.retirement_requests();
        assert_eq!(requests.iter().filter(|r| matches!(r, RetirementRequest::ScheduledCapHeader { .. })).count(),
            p.active().iter().filter(|a| **a).count());
        for context in 0..2 {
            let mut cap_rows = 0;
            scheduled.visit_owner(owner, |writer, _| {
                if writer == (crate::h21_scheduled_max_cap::Writer::Cap { context, origin: owner + 1 }) {
                    cap_rows += 1;
                }
                Ok(())
            }).unwrap();
            assert_eq!(cap_rows, if p.active()[context] { 6419 } else { 0 });
            for bit in [0, 740, 804, 2047] {
                let old = Term { row: owner * 524_288 + [357_978, 360_026][context] + bit,
                    gate: Gate { left: owner * 1_048_576 + [1_000_770, 1_002_818][context] + bit,
                        right: owner * 1_048_576, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } };
                assert_eq!(p.require_cap_header_source(context, bit, &old).is_ok(), p.active()[context]);
                if p.active()[context] {
                    for field in 0..7 {
                        let mut wrong = old.clone();
                        match field { 0 => wrong.row += 1, 1 => wrong.gate.left += 1,
                            2 => wrong.gate.right += 1, 3 => wrong.gate.c0 = Fr::one(),
                            4 => wrong.gate.c1 = Fr::zero(), 5 => wrong.gate.c2 = Fr::one(),
                            _ => wrong.gate.c3 = Fr::one() }
                        assert!(p.require_cap_header_source(context, bit, &wrong).is_err());
                    }
                }
            }
            for local in [5757, 7804, 7805, 7897] {
                let old = Term { row: owner * 16384 + local,
                    gate: Gate { left: owner * 1_048_576 + 655654 + local,
                        right: owner * 1_048_576, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } };
                p.require_map_tail_source(context, local, &old).unwrap();
                for fault in 0..7 {
                    let mut wrong = old.clone();
                    match fault { 0 => wrong.row += 1, 1 => wrong.gate.left += 1,
                        2 => wrong.gate.right = 0, 3 => wrong.gate.c0 = Fr::one(),
                        4 => wrong.gate.c1 = Fr::from(2u8), 5 => wrong.gate.c2 = Fr::one(),
                        _ => wrong.gate.c3 = Fr::one() }
                    assert!(p.require_map_tail_source(context, local, &wrong).is_err());
                }
                assert_eq!(p.map_tail_replacement(context, local).unwrap(),
                    bank53_required_writer::required_bank53_writer(owner, context, local).unwrap());
            }
            assert!(p.require_map_tail_source(context, 7898, &Term { row: 0,
                gate: Gate { left: 0, right: 0, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } }).is_err());
            assert_eq!(crate::bank53_slack::SLACK_ZERO_COUNT, 387);
            if !p.active()[context] {
                assert_eq!(bank53_required_writer::required_bank53_writer(owner, context, 5757), Ok(RequiredWriter::HeaderZero));
            }
        }
    }
}

#[test]
fn c567_source_recipe_rejects_every_author_field_and_read_family() {
    for owner in [846_015, 1_810_879, 1_810_904, 1_810_841] {
        let p = plan(owner); let (rows, reads) = source(&p);
        p.require_source_recipe([&rows[0], &rows[1]], &reads, p.authors()).unwrap();
        for context in 0..2 {
            let Some(a) = p.authors()[context] else { continue; };
            for field in 0..5 {
                let mut wrong = *p.authors(); let mut changed = a;
                match field { 0 => changed.context = 1 - context, 1 => changed.origin += 1,
                    2 => changed.previous_owner += 1, 3 => changed.max_owner += 1, _ => changed.cap_owner += 1 }
                wrong[context] = Some(changed);
                assert!(p.require_source_recipe([&rows[0], &rows[1]], &reads, &wrong).is_err());
            }
        }
        // Isolate each field family at its first/interior/last bit, for every
        // active context, without replaying the same emitter per source bit.
        let indices: Vec<_> = (0..reads.len() / 514).flat_map(|context|
            [0, 112, 224, 225, 257, 289, 290, 401, 513].map(|i| context * 514 + i)).collect();
        for i in indices {
            let mut missing = reads.clone(); missing.remove(i);
            assert!(p.require_source_recipe([&rows[0], &rows[1]], &missing, p.authors()).is_err());
            let mut duplicate = reads.clone(); duplicate.insert(i, reads[i]);
            assert!(p.require_source_recipe([&rows[0], &rows[1]], &duplicate, p.authors()).is_err());
            let mut address = reads.clone(); address[i].0 += 1;
            assert!(p.require_source_recipe([&rows[0], &rows[1]], &address, p.authors()).is_err());
            let fields = if matches!(reads[i].1, ScoreRelationReadAuthor::Cap { .. }) { 4 } else { 2 };
            for field in 0..fields {
                let mut retagged = reads.clone();
                retagged[i].1 = match reads[i].1 {
                    ScoreRelationReadAuthor::PreviousR { context, owner } =>
                        ScoreRelationReadAuthor::PreviousR { context: if field == 0 { 2 } else { context },
                            owner: owner + usize::from(field == 1) },
                    ScoreRelationReadAuthor::WorkUpper { owner, height } =>
                        ScoreRelationReadAuthor::WorkUpper { owner: owner + usize::from(field == 0),
                            height: height + usize::from(field == 1) },
                    ScoreRelationReadAuthor::Cap { context, origin, max_owner, cap_owner } =>
                        ScoreRelationReadAuthor::Cap { context: if field == 0 { 2 } else { context },
                            origin: origin + usize::from(field == 1), max_owner: max_owner + usize::from(field == 2),
                            cap_owner: cap_owner + usize::from(field == 3) },
                };
                assert_ne!(retagged[i].1, reads[i].1);
                assert!(p.require_source_recipe([&rows[0], &rows[1]], &retagged, p.authors()).is_err());
            }
        }
        // Checking values remains the original source producer's obligation.
        let mut arbitrary_values = reads.clone(); arbitrary_values[0].2 = Fr::from(2u8);
        p.require_source_recipe([&rows[0], &rows[1]], &arbitrary_values, p.authors()).unwrap();
    }
}

#[test]
fn c567_alias_operands_dummy_right_multiplicity_and_row_faults() {
    for (owner, context) in [(846_015, 0), (846_015, 1), (1_810_904, 0), (1_810_841, 1)] {
        let p = plan(owner); let (rows, reads) = source(&p);
        let a = p.authors()[context].unwrap();
        let predecessor = owner * 524_288 + [487_421, 502_652][context] + score::group("predecessor").start;
        let pair: Vec<_> = rows[context].iter().filter(|t| t.row == predecessor).collect();
        assert_eq!(pair.len(), 2);
        assert_eq!(pair[0].gate.left, owner * 1_048_576 + 677_501 + 8192 * context + 1093);
        assert_eq!(pair[1].gate.left, a.previous_owner * 1_048_576 + 677_501 + 8192 * context + 1318);
        assert_eq!(pair[0].gate.right, owner * 1_048_576 + 677_501 + 8192 * context);
        assert_eq!(pair[1].gate.right, pair[0].gate.right);
        for row in [predecessor, owner * 524_288 + [491_629, 506_860][context],
            owner * 524_288 + [491_694, 506_925][context]] {
            let i = rows[context].iter().position(|t| t.row == row).unwrap();
            for fault in 0..6 {
                let mut wrong = rows.clone();
                match fault { 0 => wrong[context][i].row += 1,
                    1 => wrong[context][i].gate.left += 1, 2 => wrong[context][i].gate.right += 1,
                    3 => wrong[context][i].gate.c1 += Fr::one(),
                    4 => { wrong[context].remove(i); },
                    _ => { let t = wrong[context][i].clone(); wrong[context].insert(i, t); } }
                assert!(p.require_source_recipe([&wrong[0], &wrong[1]], &reads, p.authors()).is_err());
            }
        }
    }
}

#[test]
fn c567_arbitrary_field_coefficients_match_independent_literal_fold() {
    let (r, u, v) = (point(40, 2), point(41, 43), point(41, 97));
    for (owner, previous, active) in [(845_887, 845_759, [true, true]),
        (846_015, 845_887, [true, true]), (1_000_127, 999_999, [true, true]),
        (1_810_879, 1_810_751, [true, false]), (1_810_904, 1_810_879, [true, false]),
        (1_810_841, 1_810_751, [false, true])] {
        let p = plan(owner);
        for context in 0..2 {
            let expected = if active[context] {
                reference_fold(&literal_reference(owner, context, previous), &r, &u, &v)
            } else { [Fr::zero(); 4] };
            assert_eq!(p.coefficients(context, &r, &u, &v).unwrap(), expected);
            if active[context] {
                let reference = literal_reference(owner, context, previous);
                for row in [owner * 524_288 + [487_421, 502_652][context] + score::group("predecessor").start,
                    owner * 524_288 + [491_629, 506_860][context], owner * 524_288 + [491_694, 506_925][context]] {
                    let index = reference.iter().rposition(|t| t.row == row).unwrap();
                    let mut omitted = reference.clone(); omitted.remove(index);
                    assert_ne!(reference_fold(&omitted, &r, &u, &v), expected);
                    let mut right = reference.clone(); right[index].gate.right += 1;
                    assert_ne!(reference_fold(&right, &r, &u, &v), expected);
                }
            }
        }
    }
    assert!(plan(846_015).coefficients(0, &r[..39], &u, &v).is_err());
}

#[test]
fn c567_fr2_source_alias_omission_is_not_recurrence_ownership() {
    let p = plan(846_015); let t = terms(&p, 0);
    let row = 846_015 * 524_288 + 487_421 + score::group("predecessor").start;
    let pair: Vec<_> = t.iter().filter(|t| t.row == row).collect();
    let residual = |items: &[&Term]| items.iter().fold(Fr::zero(), |sum, t| {
        let value = if t.gate.left / 1_048_576 == 845_887 { Fr::from(2u8) } else { Fr::zero() };
        sum + t.gate.c0 + t.gate.c1 * value
    });
    assert_eq!(residual(&pair), -Fr::from(2u8));
    assert_eq!(residual(&pair[..1]), Fr::zero());
    assert_eq!(residual(&[pair[0], pair[1], pair[1]]), -Fr::from(4u8));
}

#[test]
fn c567_boolean_local_recurrence_can_import_wrong_previous_predicate() {
    let p = plan(846_015); let spec = literal_spec(0);
    let wrong_previous = BigUint::from(1u8) << 20usize;
    let values = score::produce(&spec, Some(&score::ConditionalInputs {
        w: BigUint::from(1u8), v: BigUint::from(1u8) }), &wrong_previous).unwrap();
    let layout = score::Layout::new();
    assert!(values.iter().all(|v| v.is_zero() || v.is_one()));
    let integer = |rail: std::ops::Range<usize>| rail.enumerate().fold(BigUint::from(0u8),
        |sum, (i, index)| sum + if values[index].is_one() { BigUint::from(1u8) << i } else { BigUint::from(0u8) });
    assert_eq!(integer(layout.a.clone()), BigUint::from(4996u64));
    assert_eq!(integer(layout.p.clone()), wrong_previous);
    assert_eq!(integer(layout.r.clone()), wrong_previous);
    let mut witness = BTreeMap::new();
    for (bit, value) in values.into_iter().enumerate() { witness.insert(846_015 * 1_048_576 + 677_501 + bit, value); }
    for bit in 0..225 { witness.insert(845_887 * 1_048_576 + 677_501 + 1318 + bit,
        Fr::from(wrong_previous.bit(bit as u64) as u64)); }
    for bit in 0..65 { witness.insert(846_015 * 1_048_576 + 1_000_770 + 740 + bit, Fr::from((bit == 0) as u64)); }
    for bit in 0..224 { witness.insert(846_014 * 1_048_576 + 987_450 + bit, Fr::from((bit == 0) as u64)); }
    let t = terms(&p, 0);
    let residuals = |x: &BTreeMap<usize, Fr>| {
        let mut rows = BTreeMap::<usize, Fr>::new();
        for t in &t { let g = &t.gate; let l = x.get(&g.left).copied().unwrap_or_else(Fr::zero);
            let r = x.get(&g.right).copied().unwrap_or_else(Fr::zero);
            *rows.entry(t.row).or_default() += g.c0 + g.c1 * l + g.c2 * r + g.c3 * l * r; }
        rows
    };
    assert!(residuals(&witness).values().all(Zero::is_zero));
    // An independently correct predecessor recurrence gives R=4996 here.
    // Installing that predicate conflicts with the wrong imported 2^20.
    let previous_values = score::produce(&spec, Some(&score::ConditionalInputs {
        w: BigUint::from(1u8), v: BigUint::from(1u8) }), &BigUint::from(0u8)).unwrap();
    let correct_previous = layout.r.clone().enumerate().fold(BigUint::from(0u8),
        |sum, (i, bit)| sum + if previous_values[bit].is_one() { BigUint::from(1u8) << i } else { BigUint::from(0u8) });
    assert_eq!(correct_previous, BigUint::from(4996u64));
    for bit in 0..225 { witness.insert(845_887 * 1_048_576 + 677_501 + 1318 + bit,
        Fr::from(correct_previous.bit(bit as u64) as u64)); }
    assert!(residuals(&witness).values().any(|r| !r.is_zero()));
    assert!(p.required_predicates().contains(&RequiredPredicate::PreviousScore { context: 0, owner: 845_887 }));
}

use super::*;
use crate::{
    native_w_loan::{NativeWLoan, NativeWLoanGroup, WLoanDestination, WSourceTag},
    packed_owner_assembly::{NativeOwnerProducer, NativePrefix},
};
use num_bigint::BigUint;

fn small_source() -> (NativePrefix, WorkTreeHistoryPlan) {
    let raws = read_prefix_raws();
    let prefix = NativePrefix::from_raw_iter(5, raws.into_iter().take(5).map(Ok)).unwrap();
    let plan = compile_plan(5, prefix.root(), prefix.total_be28());
    (prefix, plan)
}

fn source(owner: usize) -> WSourceTag { WSourceTag { height: owner + 2, local: 987_450 } }

fn small_group_fixture() -> (&'static NativePrefix, &'static WorkTreeHistoryPlan, &'static NativeWLoanGroup) {
    static FIXTURE: std::sync::OnceLock<(NativePrefix, WorkTreeHistoryPlan, NativeWLoanGroup)> = std::sync::OnceLock::new();
    let (prefix, plan, group) = FIXTURE.get_or_init(|| {
        let (prefix, plan) = small_source();
        let group = NativeWLoanGroup::issue_for_test(&plan, &prefix, &[1, 2, 3]).unwrap();
        (prefix, plan, group)
    });
    (prefix, plan, group)
}

#[test]
fn c146_w_loan_replays_small_canonical_prefix_for_both_contexts() {
    let (prefix, plan) = small_source();
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix).unwrap();
    let mut destination = WLoanDestination::default();
    for context in 0..2 {
        let owner = 1;
        let tag = source(owner);
        let row = producer.produce(owner).unwrap();
        let (_, upper) = prefix.interval(tag.height).unwrap();
        let expected = BigUint::from_bytes_be(&upper);
        let loan = NativeWLoan::issue(&plan, &prefix, context, owner, tag).unwrap();
        loan.consume(&plan, &prefix, context, owner, tag, &expected, &row,
            |source, consumer| { if source == consumer { Ok(()) } else { Err("W alias residual".into()) } },
            &mut destination).unwrap();
        assert_eq!(destination.get(context, owner), Some(&expected));
    }
}

#[test]
fn c146_w_loan_rejects_isolated_bit_owner_context_and_source_mutants_atomically() {
    let (prefix, plan) = small_source();
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix).unwrap();
    let owner = 1;
    let context = 0;
    let tag = source(owner);
    let row = producer.produce(owner).unwrap();
    let loan = NativeWLoan::issue(&plan, &prefix, context, owner, tag).unwrap();

    let mut destination = WLoanDestination::default();
    let before = destination.clone();
    let mut wrong_bit = loan.clone();
    wrong_bit.flip_value_bit_for_test(17);
    assert_eq!(wrong_bit.consume(&plan, &prefix, context, owner, tag, loan.value_for_test(), &row,
        |_, _| panic!("residual ran before W source replay"), &mut destination).unwrap_err(),
        "W loan immutable source replay mismatch");
    assert_eq!(destination, before);

    let mut packed = row.packed_bytes().to_vec();
    packed[987_450 / 8] ^= 1 << (987_450 % 8);
    let wrong_row = row.with_packed_bytes_for_test(&packed).unwrap();
    assert_eq!(loan.consume(&plan, &prefix, context, owner, tag, loan.value_for_test(), &wrong_row,
        |_, _| panic!("residual ran before W consumer source-row check"), &mut destination).unwrap_err(),
        "W consumer packed source row mismatch");
    assert_eq!(destination, before);

    let mut wrong_consumer = loan.value_for_test().clone();
    wrong_consumer.set_bit(19, !wrong_consumer.bit(19));
    assert_eq!(loan.consume(&plan, &prefix, context, owner, tag, &wrong_consumer, &row,
        |_, _| panic!("residual ran before W consumer alias check"), &mut destination).unwrap_err(),
        "W consumer alias value mismatch");
    assert_eq!(destination, before);

    for (bad_context, bad_owner, bad_source) in [
        (context, owner + 1, tag),
        (context + 1, owner, tag),
        (context, owner, WSourceTag { height: tag.height + 1, local: tag.local }),
        (context, owner, WSourceTag { height: tag.height, local: tag.local + 1 }),
    ] {
        assert_eq!(loan.consume(&plan, &prefix, bad_context, bad_owner, bad_source,
            loan.value_for_test(), &row, |_, _| panic!("residual ran on a mistagged W loan"),
            &mut destination).unwrap_err(), "W loan consumer context/owner/source mismatch");
        assert_eq!(destination, before);
    }
}

#[test]
fn c146_w_loan_rejects_coherent_consumer_substitution_before_residual() {
    let (prefix, plan) = small_source();
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix).unwrap();
    let owner = 1;
    let context = 0;
    let tag = source(owner);
    let row = producer.produce(owner).unwrap();
    let mut loan = NativeWLoan::issue(&plan, &prefix, context, owner, tag).unwrap();
    let mut substituted = loan.value_for_test().clone();
    substituted.set_bit(31, !substituted.bit(31));
    loan.replace_value_for_test(substituted.clone());
    let mut destination = WLoanDestination::default();
    let before = destination.clone();
    assert_eq!(loan.consume(&plan, &prefix, context, owner, tag, &substituted, &row,
        |_, _| panic!("coherent substitution reached consumer residual"), &mut destination).unwrap_err(),
        "W loan immutable source replay mismatch");
    assert_eq!(destination, before);
}

#[test]
fn c146_grouped_w_loan_replays_three_owners_for_both_contexts() {
    let (prefix, plan, group) = small_group_fixture();
    let owners = [1, 2, 3];
    assert_eq!(group.logical_loan_count_for_test(), 6);
    let mut destination = WLoanDestination::default();
    let mut count = 0;
    group.consume(&plan, &prefix, |context, owner, source, alias| {
        assert!(context < 2 && owners.contains(&owner));
        assert_eq!(source, alias);
        count += 1;
        Ok(())
    }, &mut destination).unwrap();
    assert_eq!(count, 6);
    for owner in owners { for context in 0..2 { assert!(destination.get(context, owner).is_some()); } }
}

#[test]
fn c146_grouped_w_loan_rejects_mistags_parents_and_equal_destination_atomically() {
    let (prefix, plan, baseline) = small_group_fixture();
    let owners = [1, 2, 3];
    let mut destination = WLoanDestination::default();
    let before = destination.clone();
    let mut bad = (*baseline).clone();
    bad.replace_context_for_test((0, 1), 1);
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("mistag reached residual"), &mut destination).unwrap_err(), "W group context/owner/source mismatch");
    assert_eq!(destination, before);
    let mut bad = (*baseline).clone();
    bad.replace_owner_for_test((0, 1), 2);
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("mistag reached residual"), &mut destination).unwrap_err(), "W group context/owner/source mismatch");
    let mut bad = (*baseline).clone();
    bad.replace_source_for_test((0, 1), source(2));
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("mistag reached residual"), &mut destination).unwrap_err(), "W group context/owner/source mismatch");
    let mut bad = (*baseline).clone();
    bad.corrupt_loan_parent_for_test((0, 1));
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("parent reached residual"), &mut destination).unwrap_err(), "W group loan parent mismatch");
    let mut bad = (*baseline).clone();
    bad.corrupt_group_parent_for_test();
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("parent reached residual"), &mut destination).unwrap_err(), "W group parent mismatch");
    let alternate = NativePrefix::from_raw_iter(4, read_prefix_raws().into_iter().take(4).map(Ok)).unwrap();
    let alternate_plan = compile_plan(4, alternate.root(), alternate.total_be28());
    assert_eq!(baseline.consume(&alternate_plan, &alternate, |_,_,_,_| panic!("alternate parent reached residual"), &mut destination).unwrap_err(), "W group parent mismatch");
    assert_eq!(destination, before);

    let expected = BigUint::from_bytes_be(&prefix.interval(source(1).height).unwrap().1);
    destination.insert_for_test(0, 1, expected.clone());
    assert_eq!(baseline.consume(&plan, &prefix, |_,_,_,_| panic!("duplicate reached residual"), &mut destination).unwrap_err(), "W group destination duplicate");
    assert_eq!(destination.get(0, 1), Some(&expected));
}

#[test]
fn c146_grouped_w_loan_rejects_packed_and_224_bit_alias_mutants_before_residual() {
    let (prefix, plan, baseline) = small_group_fixture();
    let mut destination = WLoanDestination::default();
    let before = destination.clone();
    let mut bad = (*baseline).clone();
    bad.corrupt_packed_source_for_test((0, 1));
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("packed mismatch reached residual"), &mut destination).unwrap_err(), "W group packed source row mismatch");
    assert_eq!(destination, before);
    let mut bad = (*baseline).clone();
    bad.corrupt_retained_row_for_test(1, 0);
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("row byte mutant reached residual"), &mut destination).unwrap_err(), "W group packed source row mismatch");
    assert_eq!(destination, before);
    let mut bad = (*baseline).clone();
    bad.flip_value_bit_for_test((0, 1), 19);
    assert_eq!(bad.consume(&plan, &prefix, |_,_,_,_| panic!("alias mismatch reached residual"), &mut destination).unwrap_err(), "W group 224-bit loan alias mismatch");
    assert_eq!(destination, before);
}

#[test]
fn c146_grouped_w_loan_residual_failure_does_not_publish_partial_group() {
    let (prefix, plan, group) = small_group_fixture();
    let mut destination = WLoanDestination::default();
    let before = destination.clone();
    assert_eq!(group.consume(&plan, &prefix, |context, owner, _, _| {
        if context == 1 && owner == 1 { Err("isolated grouped residual failure".into()) } else { Ok(()) }
    }, &mut destination).unwrap_err(), "isolated grouped residual failure");
    assert_eq!(destination, before);
}

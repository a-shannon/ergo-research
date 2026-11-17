use super::*;

const MAX_BASE: usize = 999_424;
const CAP_BASE: usize = 1_000_770;

fn number(cells: &OwnerCells, start: usize, bits: usize) -> BigUint {
    let mut out = BigUint::zero();
    for bit in 0..bits {
        if cells.read(start + bit).unwrap().is_one() {
            out += BigUint::from(1u8) << bit;
        }
    }
    out
}

#[test]
fn noframe_v_loan_binds_stream_and_first_max_cap_writers() {
    let source = SyntheticSource::canonical();
    let loan = NativeVLoan::issue_from(&source).unwrap();
    let consumer = loan.prepared_for_test();
    let mut destination = VLoanDestination::default();

    loan.consume_from(&source, 844_670, consumer, None, |patch| {
        assert_eq!(patch.writers(), expected_writer_tags(844_670));
        Ok(())
    }, &mut destination).unwrap();
    loan.consume_from(&source, 844_798, consumer, None, |patch| {
        assert_eq!(patch.writers(), expected_writer_tags(844_798));
        Ok(())
    }, &mut destination).unwrap();
    loan.consume_from(&source, 845_759, consumer, None, |patch| {
        assert_eq!(patch.writers(), expected_writer_tags(845_759));
        Ok(())
    }, &mut destination).unwrap();

    assert_eq!(destination.patches[&844_670].writers(), expected_writer_tags(844_670));
    assert_eq!(destination.patches[&844_798].writers(), expected_writer_tags(844_798));
    assert_eq!(destination.patches[&845_759].writers(), expected_writer_tags(845_759));

    let max_patch = loan.prepared.owner_patch(844_670).unwrap();
    let mut max_cells = OwnerCells::new(844_670).unwrap();
    max_patch.apply(&mut max_cells).unwrap();
    assert_eq!(number(&max_cells, MAX_BASE, 224), BigUint::from(1u8));

    let cap_patch = loan.prepared.owner_patch(845_759).unwrap();
    let mut cap_cells = OwnerCells::new(845_759).unwrap();
    cap_patch.apply(&mut cap_cells).unwrap();
    let r = number(&cap_cells, CAP_BASE + 1, 224);
    let target = (&r * 3u8) / 2u8;
    let mut rounded = BigUint::from(1u8);
    while rounded < target { rounded <<= 1usize; }
    assert_eq!(number(&cap_cells, CAP_BASE + 740, 65), rounded);
}

#[test]
fn noframe_v_group_replays_one_d_stream_and_returns_source_caps() {
    let source=SyntheticSource::canonical();
    let loan=NativeVLoan::issue_from(&source).unwrap();
    source.reads.set(0);
    let destination=VLoanDestination::default();
    let before=destination.clone();
    let group=loan.replay_group_from(&source).unwrap();
    assert_eq!(source.reads.get(),D_COUNT,"one compact-D replay, no per-owner replay");
    assert_eq!(group.first_d,crate::work_tree_work::native_decode(0x0101_0000).unwrap());
    for (index,owner) in [844_670,844_798,845_759].into_iter().enumerate() {
        assert_eq!(group.patches[index].writers(),expected_writer_tags(owner));
    }
    let mut cap_cells=OwnerCells::new(845_759).unwrap();
    group.patches[2].apply(&mut cap_cells).unwrap();
    assert_eq!(group.cap_values[0],number(&cap_cells,CAP_BASE+740,65));
    assert_eq!(group.cap_values[1],number(&cap_cells,CAP_BASE+2048+740,65));
    assert_eq!(destination,before,"group extraction does not publish patches");
}

#[test]
fn noframe_v_group_rejects_parent_and_drift_without_destination_changes() {
    let source=SyntheticSource::canonical();
    let loan=NativeVLoan::issue_from(&source).unwrap();
    let before=VLoanDestination::default();

    let changed_parent=SyntheticSource::changed_parent();
    let parent_destination=before.clone();
    assert_eq!(loan.replay_group_from(&changed_parent).unwrap_err(),
        "V loan immutable source replay mismatch");
    assert_eq!(changed_parent.reads.get(),0,"parent mismatch fails before D replay");
    assert_eq!(parent_destination,before);

    let changed_d=SyntheticSource::changed_d();
    let d_destination=before.clone();
    assert_eq!(loan.replay_group_from(&changed_d).unwrap_err(),
        "V loan immutable source replay mismatch");
    assert_eq!(changed_d.reads.get(),D_COUNT,"changed D is detected by one complete replay");
    assert_eq!(d_destination,before);
}

#[test]
fn noframe_v_group_rejects_owner_and_tag_mutants_before_destination_changes() {
    let source=SyntheticSource::canonical();
    let loan=NativeVLoan::issue_from(&source).unwrap();
    let group=loan.replay_group_from(&source).unwrap();
    let mut destination=VLoanDestination::default();
    let before=destination.clone();

    let mut wrong_owner=group.patches.clone();
    wrong_owner[0].set_owner_for_test(844_671);
    assert_eq!(validate_group_patches(&loan.prepared, &wrong_owner).unwrap_err(),
        "V group source patch owner/value mismatch");
    assert_eq!(destination,before);

    let mut wrong_tag=group.patches.clone();
    wrong_tag[0].set_writer_for_test(0,Writer::Max {context:0,end:844_673}).unwrap();
    assert_eq!(validate_group_patches(&loan.prepared, &wrong_tag).unwrap_err(),
        "V group writer/context/end/origin binding mismatch");
    assert_eq!(destination,before);
}

#[test]
fn noframe_v_loan_rejects_order_and_truncation_with_exact_stream_guards() {
    let mut destination = VLoanDestination::default();
    let before = destination.clone();
    let wrong_order = Prepared::from_d_iter(std::iter::once((FIRST_D + 1, BigUint::from(1u8))));
    assert_eq!(wrong_order.err().unwrap(), "scheduled D stream height/order");
    assert_eq!(destination, before);

    let missing = Prepared::from_d_iter(std::iter::empty());
    assert_eq!(missing.err().unwrap(), "scheduled D stream missing height");
    assert_eq!(destination, before);
}

#[test]
fn noframe_v_loan_rejects_mutated_d_and_coherent_consumer_before_residual() {
    let source = SyntheticSource::canonical();
    let substituted_source = SyntheticSource::changed_d();
    let substituted = NativeVLoan::issue_from(&substituted_source).unwrap();
    let coherent_consumer = substituted.prepared_for_test();
    let mut destination = VLoanDestination::default();
    let before = destination.clone();

    assert_eq!(substituted.consume_from(
        &source,
        844_670,
        coherent_consumer,
        None,
        |_| panic!("coherent V and consumer substitution reached residual"),
        &mut destination,
    ).unwrap_err(), "V loan immutable source replay mismatch");
    assert_eq!(destination, before);
}

#[test]
fn noframe_v_loan_rejects_max_cap_context_and_duplicate_writer_tags_atomically() {
    let source = SyntheticSource::canonical();
    let loan = NativeVLoan::issue_from(&source).unwrap();
    let consumer = loan.prepared_for_test();
    let mutants = [
        (844_670, vec![
            Writer::Max { context: 0, end: 844_673 },
            Writer::Max { context: 1, end: 844_672 },
        ]),
        (845_759, vec![
            Writer::Cap { context: 0, origin: 845_761 },
            Writer::Cap { context: 1, origin: 845_760 },
        ]),
        (845_759, vec![
            Writer::Cap { context: 1, origin: 845_760 },
            Writer::Cap { context: 1, origin: 845_760 },
        ]),
        (844_670, vec![
            Writer::Max { context: 1, end: 844_672 },
            Writer::Max { context: 0, end: 844_672 },
        ]),
        (844_670, vec![
            Writer::Max { context: 0, end: 844_672 },
            Writer::Max { context: 0, end: 844_672 },
        ]),
    ];

    for (owner, tags) in mutants {
        let mut destination = VLoanDestination::default();
        let before = destination.clone();
        assert_eq!(loan.consume_from(
            &source,
            owner,
            consumer,
            Some(&tags),
            |_| panic!("mistagged V writer reached residual"),
            &mut destination,
        ).unwrap_err(), "V writer/context/end/origin binding mismatch");
        assert_eq!(destination, before);
    }
}

#[test]
fn noframe_v_loan_keeps_equal_context_values_as_distinct_writers() {
    let source = SyntheticSource::canonical();
    let loan = NativeVLoan::issue_from(&source).unwrap();
    let patch = loan.prepared.owner_patch(844_670).unwrap();
    assert_eq!(patch.writers(), vec![
        Writer::Max { context: 0, end: 844_672 },
        Writer::Max { context: 1, end: 844_672 },
    ]);
    let mut cells = OwnerCells::new(844_670).unwrap();
    patch.apply(&mut cells).unwrap();
    assert_eq!(number(&cells, MAX_BASE, 224), number(&cells, MAX_BASE + 673, 224));
}

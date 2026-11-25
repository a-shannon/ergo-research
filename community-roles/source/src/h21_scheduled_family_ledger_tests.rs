use super::*;
use ark_ff::One;

fn profile()->[u8;32] {
    use blake2::{digest::consts::U32,Blake2b,Digest};
    let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
    bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    Blake2b::<U32>::digest(bytes).into()
}

#[test]
fn c194_full_first_cap_lease_q_mismatch_in_each_context_rejects_before_source_return() {
    let plan=WorkTreeHistoryPlan::compile(1_827_840,21,[17;32],[0;28]).unwrap();
    let snapshot=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile(),16).unwrap();
    let roster=DaaHistoryRoster::compile(&plan).unwrap();
    for context in 0..2 {
        let mut first=Eligible08NativeSnapshot::first_modern_constant_d_for_test(
            [17;32],[0;28],profile(),16).unwrap();
        first.flip_cap_q_bit_for_test(context,0).unwrap();
        assert_eq!(FirstModernCapPublication::stage(&plan,&snapshot,&roster,&first).err().unwrap(),
            "first Cap publication exact FirstModernCapLease source");
    }
}

fn reject(candidate:Candidate,destination:&mut Destination,expected:&str) {
    let before_rows=destination.rows.clone();let before_cells=destination.cells.clone();
    let before_imports=destination.imports.clone();let before_parent=destination.parent.clone();
    let before_external=destination.external_header_d.clone();
    assert_eq!(candidate.publish(destination).err().unwrap(),expected);
    assert_eq!(destination.rows,before_rows);assert_eq!(destination.cells,before_cells);
    assert_eq!(destination.imports,before_imports);assert_eq!(destination.parent,before_parent);
    assert_eq!(destination.external_header_d,before_external);
}

/// Real H21 symbolic WorkTree/DAA HEADER; D and parent custody are synthetic.
/// This never constructs NativePrefix or invokes native production admission.
#[test]
fn c183_synthetic_d_real_header_generic_family_atomic_source_orders() {
    let plan=WorkTreeHistoryPlan::compile(1827840,21,[17;32],[0;28]).unwrap();
    let snapshot=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile(),16).unwrap();
    let roster=DaaHistoryRoster::compile(&plan).unwrap();
    let first=Candidate::stage(&plan,&snapshot,&roster,&snapshot.owner_lease(844670).unwrap()).unwrap();
    let next=Candidate::stage(&plan,&snapshot,&roster,&snapshot.owner_lease(844798).unwrap()).unwrap();
    assert_eq!(first.retired,[673,673,0,0]);assert_eq!(first.cells.len(),1346);
    assert_eq!(first.imports.len(),448);assert_eq!(next.imports.len(),448);
    assert_eq!(first.external_header_d.len(),224);
    assert!(first.external_header_d.keys().all(|wire|wire/WIDTH==844670));
    assert!(first.imports.iter().all(|c|c.wire/WIDTH==844798));
    for context in 0..2 {
        assert_eq!(first.imports.iter().filter(|c|matches!(c.writer,Writer::Max{context:c,..} if c==context)).count(),224);
    }
    let mut forward=Destination::default();let joined=next.clone().publish(&mut forward).unwrap();
    assert_eq!(joined.owner,844798);assert_eq!(forward.pending_source_owners(),vec![844926]);
    first.clone().publish(&mut forward).unwrap();
    assert_eq!(forward.pending_source_owners(),vec![844926]);
    assert_eq!(forward.external_header_d.len(),448,"publishing MAX never discharges HEADER D authors");
    let mut reverse=Destination::default();first.clone().publish(&mut reverse).unwrap();
    assert_eq!(reverse.pending_source_owners(),vec![844798]);
    next.clone().publish(&mut reverse).unwrap();
    assert!(forward==reverse,"source and consumer order must produce identical ownership/obligations");
    reject(first.clone(),&mut forward,"scheduled ledger destination ROW overlap");

    let mut destination=Destination::default();destination.rows.insert(5,Author::Header);
    destination.cells.insert(7,(Author::Scheduled(Writer::Max{context:0,end:2}),Fr::zero()));
    let mut bit=first.clone();Arc::make_mut(&mut bit.cells)[0].value+=Fr::one();
    reject(bit,&mut destination,"scheduled ledger exact X source");
    let mut duplicate=first.clone();let zero=duplicate.cells.iter().find(|c|c.value.is_zero()).unwrap().clone();
    Arc::make_mut(&mut duplicate.cells).push(zero);
    reject(duplicate,&mut destination,"scheduled ledger duplicate X/parent transfer");
    let mut missing=first.clone();Arc::make_mut(&mut missing.cells).pop();
    reject(missing,&mut destination,"scheduled ledger exact X source");
    let mut row=first.clone();let rows=Arc::make_mut(&mut row.rows);
    rows.iter_mut().find(|r|r.author!=Author::Header).unwrap().term.gate.c0+=Fr::one();
    reject(row,&mut destination,"scheduled ledger exact ROW source");
    let mut row=first.clone();let duplicate=row.rows.last().unwrap().clone();
    Arc::make_mut(&mut row.rows).push(duplicate);
    reject(row,&mut destination,"scheduled ledger exact ROW source");
    let mut collision=first.clone();let mut header=collision.rows[0].clone();
    header.term.row=collision.rows.last().unwrap().term.row;
    Arc::make_mut(&mut collision.rows).push(header);
    reject(collision,&mut destination,"scheduled ledger ROW author collision");
    let mut imports=first.clone();Arc::make_mut(&mut imports.imports)[0].value+=Fr::one();
    reject(imports,&mut destination,"scheduled ledger exact import source");
    let mut external=first.clone();external.external_header_d.clear();
    reject(external,&mut destination,"scheduled ledger exact external HEADER D reads");
    let mut mask=first.clone();mask.replacement_mask[999424]^=true;
    reject(mask,&mut destination,"scheduled ledger exact transfer mask");

    let cell=&first.cells[0];let mut overlap=Destination::default();
    overlap.cells.insert(cell.wire,(Author::Scheduled(cell.writer),cell.value));
    reject(first.clone(),&mut overlap,"scheduled ledger destination X overlap");
    let imported=&first.imports[0];let mut wrong=Destination::default();
    wrong.cells.insert(imported.wire,(Author::Scheduled(imported.writer),imported.value+Fr::one()));
    reject(first.clone(),&mut wrong,"scheduled ledger published source mismatch");
    // Same zero/value with the wrong context/end is not a source author.
    let mut wrong=Destination::default();
    wrong.cells.insert(imported.wire,(Author::Scheduled(Writer::Max{context:1,end:844800}),imported.value));
    reject(first.clone(),&mut wrong,"scheduled ledger published source mismatch");
    let mut waiting=Destination::default();first.clone().publish(&mut waiting).unwrap();
    waiting.imports.get_mut(&imported.wire).unwrap().1+=Fr::one();
    reject(next.clone(),&mut waiting,"scheduled ledger incoming source mismatch");
    let mut other=first.clone();other.parent=Eligible08NativeSnapshot::constant_d_for_test(
        [17;32],[0;28],[4;32],16).unwrap().parent();
    reject(other,&mut forward,"scheduled ledger destination parent");
    assert_eq!(Candidate::stage(&plan,&snapshot,&roster,&snapshot.owner_lease(844671).unwrap()).err().unwrap(),
        "scheduled ledger inactive owner");
    assert!(snapshot.owner_lease(1<<21).is_err());
    let wrong_root=Eligible08NativeSnapshot::constant_d_for_test([18;32],[0;28],profile(),16).unwrap();
    assert_eq!(Candidate::stage(&plan,&wrong_root,&roster,&snapshot.owner_lease(844670).unwrap()).err().unwrap(),
        "scheduled ledger exact plan/root/total/cut");
    let wrong_profile=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],[4;32],16).unwrap();
    assert_eq!(Candidate::stage(&plan,&wrong_profile,&roster,&snapshot.owner_lease(844670).unwrap()).err().unwrap(),
        "scheduled ledger exact plan/root/total/cut");
    assert_eq!(Candidate::stage(&plan,&wrong_profile,&roster,&wrong_profile.owner_lease(844670).unwrap()).err().unwrap(),
        "scheduled ledger exact plan/root/total/cut");
    let admission=Admission{plan:&plan,snapshot:&snapshot,roster};
    let mut via_admission=Destination::default();
    admission.publish(844670,&mut via_admission).unwrap();
    assert_eq!(via_admission.pending_source_owners(),vec![844798]);
    assert_eq!(via_admission.external_header_d.len(),224);
    println!("C183_SYNTHETIC_D_REAL_HEADER first844670_next844798 both_orders atomic_negatives pending844926; native_H21=OPEN");
}

#[test]
fn c183_synthetic_d_real_header_terminal_clipped_and_cap_family() {
    let plan=WorkTreeHistoryPlan::compile(1827840,21,[17;32],[0;28]).unwrap();
    let snapshot=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile(),16).unwrap();
    let roster=DaaHistoryRoster::compile(&plan).unwrap();
    for (owner,retired,cells) in [(1827838,[673,0,0,0],673),
        (1810840,[0,673,0,0],673),(1810841,[0,0,0,2048],2048),
        (1810904,[0,0,2048,0],2048),
        (845759,[0,0,2048,2048],4096)] {
        let candidate=Candidate::stage(&plan,&snapshot,&roster,&snapshot.owner_lease(owner).unwrap()).unwrap();
        assert_eq!(candidate.retired,retired);assert_eq!(candidate.cells.len(),cells);
        if owner==1827838 || owner==1810840 {assert!(candidate.imports.is_empty(),"terminal has no successor");}
        if owner==845759 {
            assert_eq!(candidate.imports.len(),448);
            assert!(candidate.imports.iter().all(|c|c.wire/WIDTH==844670));
        }
        if owner==1810904 {
            assert_eq!(candidate.imports.len(),224);
            assert!(candidate.imports.iter().all(|c|c.wire/WIDTH==1809918));
        }
        if owner==1810841 {
            assert_eq!(candidate.imports.len(),224);
            assert!(candidate.imports.iter().all(|c|c.wire/WIDTH==1809790
                && matches!(c.writer,Writer::Max{context:1,..})));
        }
        let mut destination=Destination::default();candidate.publish(&mut destination).unwrap();
    }
    for owner in [1810841,1810903,1810905,1827837,1827839] {
        let lease=snapshot.owner_lease(owner).unwrap();
        if lease.cells().is_empty() {
            assert_eq!(Candidate::stage(&plan,&snapshot,&roster,&lease).err().unwrap(),"scheduled ledger inactive owner");
        }
    }
    println!("C183_SYNTHETIC_D_REAL_HEADER terminal0 terminal1 clippedCap firstCap; native_H21=OPEN");
}

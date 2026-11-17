//! No-frame structural fixture. Uses c135's reviewed scalar nBits value;
//! constant synthetic D across the schedule is not a native H21 execution.
use super::*;
use ark_ff::One;

fn profile()->[u8;32] {
    use blake2::{digest::consts::U32,Blake2b,Digest};
    let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
    bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    Blake2b::<U32>::digest(bytes).into()
}
fn reject(candidate:DSourceCandidate,destination:&mut Destination,expected:&str) {
    let parent=destination.parent.clone();let rows=destination.rows.clone();
    let cells=destination.cells.clone();let imports=destination.imports.clone();
    let external=destination.external_header_d.clone();
    assert_eq!(candidate.publish(destination).unwrap_err(),expected);
    assert_eq!(destination.parent,parent);assert_eq!(destination.rows,rows);
    assert_eq!(destination.cells,cells);assert_eq!(destination.imports,imports);
    assert_eq!(destination.external_header_d,external);
}

#[test]
fn c184_noframe_work_d_typed_author_both_orders_and_atomic_rejections() {
    let d=crate::work_tree_work::native_decode(0x073b033c).unwrap();
    assert!(d.bits()<=64);let scalar=d.to_u64_digits()[0];
    let plan=WorkTreeHistoryPlan::compile(1827840,21,[17;32],[0;28]).unwrap();
    let snapshot=Eligible08NativeSnapshot::constant_scalar_d_for_test([17;32],[0;28],profile(),d).unwrap();
    let consumer=snapshot.owner_lease(844670).unwrap();
    let source=NativeWorkDLease::synthetic_for_test(snapshot.parent(),844670,scalar);
    let roster=DaaHistoryRoster::compile(&plan).unwrap();
    let max=Candidate::stage(&plan,&snapshot,&roster,&consumer).unwrap();
    let native=DSourceCandidate::stage(&plan,&snapshot,&consumer,&source).unwrap();
    let mask=plan.physical_assignment_replacement_mask(844670).unwrap();
    assert!(mask[987674..987898].iter().all(|bit|*bit));
    assert_eq!(&max.replacement_mask[987674..987898],&mask[987674..987898]);
    assert_eq!(max.retired,[673,673,0,0],"D joins retire no extra HEADER anchors");

    let mut source_first=Destination::default();native.clone().publish(&mut source_first).unwrap();
    assert!(source_first.rows.is_empty(),"D author publication adds no HEADER ROW");
    assert_eq!(source_first.cells.len(),224);
    assert!(source_first.cells.values().all(|(author,_)|*author==Author::NativeWorkD{height:844672}));
    max.clone().publish(&mut source_first).unwrap();
    assert_eq!(source_first.pending_header_d(),0);
    assert_eq!(source_first.pending_source_owners(),vec![844798]);
    let mut consumer_first=Destination::default();max.clone().publish(&mut consumer_first).unwrap();
    assert_eq!(consumer_first.pending_header_d(),224);
    let other=Eligible08NativeSnapshot::constant_d_for_test([18;32],[0;28],profile(),16).unwrap();
    let mut wrong_parent=Destination{parent:Some(other.parent()),rows:consumer_first.rows.clone(),
        cells:consumer_first.cells.clone(),imports:consumer_first.imports.clone(),
        external_header_d:consumer_first.external_header_d.clone()};
    reject(native.clone(),&mut wrong_parent,"native Work-D destination parent");
    native.clone().publish(&mut consumer_first).unwrap();
    assert!(source_first==consumer_first);
    assert!(native.claims.iter().any(|(_,(_,value))|value.is_zero()));
    reject(native.clone(),&mut consumer_first,"native Work-D duplicate X author");

    let mut destination=Destination::default();destination.rows.insert(5,Author::Header);
    for kind in 0..9 {
        let mut wrong=source.clone();wrong.mutate_for_test(kind);
        let before=destination.rows.clone();
        let error=DSourceCandidate::stage(&plan,&snapshot,&consumer,&wrong).err().unwrap();
        let expected=match kind {0=>"native Work-D source differs from Prepared D",
            1|2=>"native Work-D parent/cut/owner/height",3|4=>"native Work-D exact 224-cell census",
            6=>"native Work-D nonboolean source",_=>"native Work-D exact ordered domain"};
        assert_eq!(error,expected,"source mutation {kind}");
        assert_eq!(destination.rows,before);assert!(destination.cells.is_empty());
    }
    // A coordinated copied expectation + source-bit substitution cannot alter
    // Prepared's original private D projection.
    let mut wrong_consumer=consumer.clone();wrong_consumer.flip_work_d_bit_for_test();
    let mut wrong_source=source.clone();wrong_source.mutate_for_test(0);
    assert_eq!(DSourceCandidate::stage(&plan,&snapshot,&wrong_consumer,&wrong_source).err().unwrap(),
        "Eligible08 MAX/Cap owner Work-D expectation source");
    assert!(destination.cells.is_empty());
    for owner in [844671usize,1827839,2000000] {
        let lease=snapshot.owner_lease(owner).unwrap();
        let source=NativeWorkDLease::synthetic_for_test(snapshot.parent(),owner,scalar);
        assert_eq!(DSourceCandidate::stage(&plan,&snapshot,&lease,&source).err().unwrap(),
            "native Work-D source requires active scheduled MAX owner");
        assert!(destination.cells.is_empty());
    }
    for (root,total,profile) in [([18;32],[0;28],profile()),([17;32],[1;28],profile()),([17;32],[0;28],[4;32])] {
        let other=Eligible08NativeSnapshot::constant_d_for_test(root,total,profile,16).unwrap();
        let wrong=NativeWorkDLease::synthetic_for_test(other.parent(),844670,scalar);
        assert_eq!(DSourceCandidate::stage(&plan,&snapshot,&consumer,&wrong).err().unwrap(),
            "native Work-D parent/cut/owner/height");
    }
    let wrong=NativeWorkDLease::synthetic_for_test(snapshot.parent().different_cut_for_test(),844670,scalar);
    assert_eq!(DSourceCandidate::stage(&plan,&snapshot,&consumer,&wrong).err().unwrap(),
        "native Work-D parent/cut/owner/height");

    let mut copied=native.clone();Arc::make_mut(&mut copied.claims)[0].1.1+=Fr::one();
    reject(copied,&mut destination,"native Work-D exact source claims");
    let mut copied=native.clone();Arc::make_mut(&mut copied.claims)[0].1.0=Author::Scheduled(Writer::Max{context:0,end:844672});
    reject(copied,&mut destination,"native Work-D exact source claims");
    let first=native.claims[0];
    for author in [Author::Scheduled(Writer::Max{context:0,end:844672}),Author::NativeWorkD{height:844673}] {
        let mut wrong=Destination::default();wrong.cells.insert(first.0,(author,first.1.1));
        let old=wrong.cells.clone();
        assert_eq!(max.clone().publish(&mut wrong).err().unwrap(),"scheduled ledger published Work-D source mismatch");
        assert_eq!(wrong.cells,old);assert!(wrong.rows.is_empty());
        let mut wrong=Destination::default();wrong.external_header_d.insert(first.0,(author,first.1.1));
        reject(native.clone(),&mut wrong,"native Work-D pending obligation mismatch");
    }
    let mut wrong=Destination::default();wrong.cells.insert(first.0,(first.1.0,first.1.1+Fr::one()));
    let old=wrong.cells.clone();
    assert_eq!(max.clone().publish(&mut wrong).err().unwrap(),"scheduled ledger published Work-D source mismatch");
    assert_eq!(wrong.cells,old);assert!(wrong.rows.is_empty());
    let mut wrong=Destination::default();wrong.external_header_d.insert(first.0,(first.1.0,first.1.1+Fr::one()));
    reject(native,&mut wrong,"native Work-D pending obligation mismatch");
    println!("C184_NOFRAME_C135_SCALAR both_orders typed_D_author 224_D_closed MAX844798_pending unchanged_HEADER_ROW_mask; native_H21=OPEN");
}

use super::*;
use crate::gkr::Gate;
use std::collections::BTreeSet;

fn anchor(owner: usize, offset: usize) -> Term {
    Term {row:owner*ROWS+ANCHOR+offset,gate:Gate {left:owner*WIDTH+BASE+offset,
        right:owner*WIDTH,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}
}
fn source() -> Circuit {
    Circuit {input_len:WIDTH,row_count:ROWS,terms:(0..END-BASE).map(|i|anchor(0,i)).collect()}
}

#[test]
fn schedule_anchor_census_isolates_every_gate_field_and_geometry() {
    let source=source();
    assert!(certify(&source).is_ok());
    for field in 0..7 {
        let mut bad=source.clone(); let term=&mut bad.terms[673];
        match field {0=>term.row+=1,1=>term.gate.left+=1,2=>term.gate.right=1,
            3=>term.gate.c0=Fr::one(),4=>term.gate.c1=Fr::zero(),
            5=>term.gate.c2=Fr::one(),_=>term.gate.c3=Fr::one()}
        assert!(certify(&bad).is_err(),"isolated gate field {field}");
    }
    let mut bad=source.clone(); bad.terms.remove(673); assert!(certify(&bad).is_err());
    let mut bad=source.clone(); bad.terms.push(bad.terms[673].clone()); assert!(certify(&bad).is_err());
    let mut bad=source.clone(); bad.terms[673]=bad.terms[672].clone(); assert!(certify(&bad).is_err());
    let mut bad=source.clone(); bad.input_len/=2; assert!(certify(&bad).is_err());
    let mut bad=source.clone(); bad.row_count/=2; assert!(certify(&bad).is_err());
    for right in [false,true] {
        let mut bad=source.clone();let mut extra=anchor(0,0);extra.row=ANCHOR-1;
        if right {extra.gate.left=0;extra.gate.right=BASE;extra.gate.c1=Fr::zero();extra.gate.c2=Fr::one();}
        bad.terms.push(extra);
        assert!(certify(&bad).unwrap_err().contains("additional HEADER consumer"));
    }
}

#[test]
fn schedule_h21_membership_matches_explicit_epoch_and_clipped_guard_rosters() {
    for context in 0..2 {
        let (terminal,guard)=Policy::H21.endpoints(context).unwrap();
        let mut max=BTreeSet::from([844_670]);
        let mut cap=BTreeSet::from([845_759]);
        // Build the reference partition in height space, including the singleton.
        for start in (844_673..=terminal).step_by(128) {
            let end=(start+127).min(terminal);
            max.insert(end-2);
            if start+1088 <= guard {cap.insert((end+1088).min(guard)-1);}
        }
        assert_eq!(max.len(),7682);
        assert_eq!(cap.len(),if context==0 {7674}else{7673});
        for owner in 0..1<<21 {
            assert_eq!(Policy::H21.active(owner,context,Relation::Max).unwrap(),max.contains(&owner),"MAX c{context} owner{owner}");
            assert_eq!(Policy::H21.active(owner,context,Relation::Cap).unwrap(),cap.contains(&owner),"Cap c{context} owner{owner}");
        }
        assert!(!Policy::H21.active(terminal-1,context,Relation::Max).unwrap());
        assert_eq!(Policy::H21.active(terminal-1,context,Relation::Cap).unwrap(),context==1);
        assert!(Policy::H21.active(guard-1,context,Relation::Cap).unwrap());
        assert!(!Policy::H21.active(guard,context,Relation::Cap).unwrap());
        for (role,before,after) in [(Relation::Max,(1<<20)-2,(1<<20)+126),
            (Relation::Cap,(1<<20)-65,(1<<20)+63)] {
            assert!(Policy::H21.active(before,context,role).unwrap());
            assert!(!Policy::H21.active(1<<20,context,role).unwrap());
            assert!(Policy::H21.active(after,context,role).unwrap());
        }
    }
    // Clipping is necessary: c0 final Cap owner has a nonstandard low residue.
    assert_ne!((1_827_838usize-1)%128,127);
    assert!(Policy::H21.endpoints(2).is_err());
    for owner in [(1<<20)-1,1<<20,(1<<20)+127,1_827_774,1_827_839] {
        for offset in [0,672,673,1345,1346,3393,3394,5441] {
            let term=anchor(owner,offset);
            assert_eq!(identity(&term,owner*ROWS,owner*WIDTH).unwrap(),offset);
            let mut wrong=term.clone();wrong.gate.right=0;
            assert!(identity(&wrong,owner*ROWS,owner*WIDTH).is_err());
            assert!(identity(&term,(owner-1)*ROWS,(owner-1)*WIDTH).is_err());
        }
    }
}

#[test]
fn schedule_h21_epoch_end_neighbors_and_cap_sources_match_height_partition() {
    for context in 0..2 {
        let (terminal,guard)=Policy::H21.endpoints(context).unwrap();
        let mut epochs=vec![(844_672usize,844_672usize)];
        epochs.extend((844_673..=terminal).step_by(128).map(|a|(a,(a+127).min(terminal))));
        assert_eq!(epochs.len(),7682);
        assert_eq!(epochs.last().copied(),Some((1_827_713,terminal)));
        assert_eq!(epochs.last().unwrap().1-epochs.last().unwrap().0+1,if context==0 {128}else{63});
        for (index,pair) in epochs.windows(2).enumerate() {
            let stride=pair[1].1-pair[0].1;
            let truncated_tail=context==1 && index==epochs.len()-2;
            assert_eq!(stride,if truncated_tail {63}else{128});
            if truncated_tail {
                // A fixed +128 successor would invent an owner past E1.
                let wrong_next=pair[0].1-2+128;
                assert_ne!(wrong_next,pair[1].1-2);
                assert!(!Policy::H21.active(wrong_next,context,Relation::Max).unwrap());
                assert!(Policy::H21.max_neighbors(wrong_next,context).is_err());
            }
        }
        let mut candidates=0;
        let mut clipped=0;
        for (index,&(a,b)) in epochs.iter().enumerate() {
            let owner=b-2;
            assert_eq!(epoch_at(terminal,a),Some(ScheduledEpoch{start:a,end:b}));
            assert_eq!(epoch_at(terminal,b),Some(ScheduledEpoch{start:a,end:b}));
            assert_eq!(Policy::H21.max_neighbors(owner,context).unwrap(),
                (index.checked_sub(1).map(|i|epochs[i].1-2),epochs.get(index+1).map(|e|e.1-2)));
            if a!=b {
                // Start-owner placement is independently rejected, including
                // the truncated terminal and the 2^20 owner crossing.
                assert!(!Policy::H21.active(a-2,context,Relation::Max).unwrap());
                assert!(Policy::H21.max_neighbors(a-2,context).is_err());
            }
            if a+1088>guard {continue;}
            candidates+=1;
            let i=(b+1088).min(guard);
            let source=Policy::H21.cap_max_source_owner(i-1,context).unwrap();
            assert_eq!(source,owner,"c{context} epoch [{a},{b}] origin {i}");
            assert!(Policy::H21.active(source,context,Relation::Max).unwrap());
            if b+1088<=guard {assert_eq!(source,i-1090);} else {
                clipped+=1;
                assert_ne!(source,i-1090);
                assert_eq!(source,if context==0 {1_826_814}else{1_826_686});
            }
        }
        assert_eq!(candidates,if context==0 {7674}else{7673});
        assert_eq!(clipped,1);
        assert_eq!(Policy::H21.cap_max_source_owner(845_759,context).unwrap(),844_670);
        assert_eq!(Policy::H21.max_neighbors(844_670,context).unwrap(),(None,Some(844_798)));
        assert_eq!(Policy::H21.max_neighbors(terminal-2,context).unwrap(),(Some(1_827_710),None));
        // Source and destination cross the owner bank independently.
        assert_eq!(Policy::H21.cap_max_source_owner((1<<20)+63,context).unwrap(),(1<<20)-1026);
        assert_eq!(Policy::H21.max_neighbors((1<<20)-2,context).unwrap(),
            (Some((1<<20)-130),Some((1<<20)+126)));
        for invalid in [0,844_669,844_671,terminal-1,1<<21,usize::MAX] {
            assert!(Policy::H21.max_neighbors(invalid,context).is_err());
        }
        for invalid in [0,845_758,845_760,guard,1<<21] {
            assert!(Policy::H21.cap_max_source_owner(invalid,context).is_err());
        }
        assert!(Policy::H21.cap_max_source_owner(usize::MAX,context).is_err());
        assert_eq!(epoch_at(terminal,844_671),None);
        assert_eq!(epoch_at(terminal,terminal+1),None);
    }
    assert_eq!(Policy::H21.cap_max_source_owner(1_827_837,0).unwrap(),1_826_814);
    assert_ne!(Policy::H21.cap_max_source_owner(1_827_837,0).unwrap(),1_826_748);
    assert_eq!(Policy::H21.cap_max_source_owner(1_827_774,1).unwrap(),1_826_686);
    assert_ne!(Policy::H21.cap_max_source_owner(1_827_774,1).unwrap(),1_826_685);
    assert!(Policy::H21.cap_max_source_owner(1_827_837,1).is_err());
    assert!(Policy::H21.cap_max_source_owner(1_827_774,0).is_err());
    assert!(Policy::H21.max_neighbors(844_670,2).is_err());
    assert!(Policy::H21.cap_max_source_owner(845_759,2).is_err());
    assert!(Policy::FixtureN3.max_neighbors(0,0).is_err());
    assert!(Policy::FixtureN3.cap_max_source_owner(0,0).is_err());
}

#[test]
fn schedule_fixture_only_native_mask_retirement_and_writer_binding() {
    let parent=WorkTreeHistoryPlan::compile(3,2,[7;32],[0x35;28]).unwrap();
    assert!(ScheduleAnchorAllocator::compile_h21(&parent).is_err());
    let allocator=ScheduleAnchorAllocator::compile(&parent,Policy::FixtureN3).unwrap();
    allocator.check_parent(&parent).unwrap();
    // Canonical source evidence is separate from the synthetic owner roster.
    assert_eq!(certify(parent.header_boundary().canonical_circuit()).unwrap(),certify(&source()).unwrap());
    let roles=[(0,Relation::Max),(1,Relation::Max),(0,Relation::Cap),(1,Relation::Cap)];
    let mut ranges=roles.iter().map(|&(c,r)|wires(c,r).unwrap()).collect::<Vec<_>>();
    ranges.sort_by_key(|r|r.start);
    assert!(ranges.windows(2).all(|r|r[0].end<=r[1].start));
    for owner in 0..4 {
        let parent_mask=parent.physical_assignment_replacement_mask(owner as u64).unwrap();
        let mask=allocator.replacement_mask(owner).unwrap();
        for wire in 0..WIDTH {
            let owned=roles.iter().any(|&(c,r)|allocator.active(owner,c,r).unwrap() && wires(c,r).unwrap().contains(&wire));
            assert_eq!(mask[wire],parent_mask[wire] || owned,"owner{owner} wire{wire}");
        }
        assert!(!mask[BASE-1]);assert!(!mask[END]);
        let mut original=Vec::new();
        parent.visit_slot_terms(owner as u64,|t|{original.push(t);Ok(())}).unwrap();
        let expected=original.iter().filter(|t| {
            let local=t.row-owner*ROWS;
            !(ANCHOR..ANCHOR+END-BASE).contains(&local) || !roles.iter().any(|&(c,r)|
                allocator.active(owner,c,r).unwrap() && wires(c,r).unwrap().contains(&(BASE+local-ANCHOR)))
        }).collect::<Vec<_>>();
        let mut index=0;
        let counts=allocator.visit_header_terms(owner,|t|{
            assert_eq!(Some(&t),expected.get(index).copied());index+=1;Ok(())
        }).unwrap();
        assert_eq!(index,expected.len());assert_eq!(counts.emitted,index);
        let wanted=if owner==0 {[673,673,2048,0]}else if owner==1 {[673,0,0,2048]}else{[0;4]};
        assert_eq!(counts.omitted,wanted);
        assert_eq!(counts.parent.emitted-counts.emitted,wanted.iter().sum::<usize>());
        for &(context,relation) in &roles {
            let range=wires(context,relation).unwrap();
            if allocator.active(owner,context,relation).unwrap() {
                let mut claimed=parent_mask.clone();
                allocator.claim_writer(owner,context,relation,range.clone(),&mut claimed).unwrap();
                assert!(allocator.claim_writer(owner,context,relation,range.clone(),&mut claimed).is_err());
                for other in 0..2 {
                    let mut cross=parent_mask.clone();
                    if other!=context {assert!(allocator.claim_writer(owner,other,relation,range.clone(),&mut cross).is_err());}
                }
                let mut overlap=parent_mask.clone();overlap[range.start]=true;
                assert!(allocator.claim_writer(owner,context,relation,range.clone(),&mut overlap).is_err());
                for bad in [range.start+1..range.end,range.start..range.end+1,BASE-1..END+1] {
                    assert!(allocator.claim_writer(owner,context,relation,bad,&mut parent_mask.clone()).is_err());
                }
                let other=if relation==Relation::Max {Relation::Cap}else{Relation::Max};
                assert!(allocator.claim_writer(owner,context,other,range,&mut parent_mask.clone()).is_err());
            } else {
                assert!(allocator.claim_writer(owner,context,relation,range,&mut parent_mask.clone()).is_err());
            }
        }
    }
    assert!(allocator.replacement_mask(4).is_err());
    assert!(allocator.claim_writer(0,2,Relation::Max,BASE..BASE+673,&mut vec![false;WIDTH]).is_err());
    assert!(allocator.claim_writer(0,0,Relation::Max,BASE..BASE+673,&mut []).is_err());
    let mut binding=Transcript::new(b"schedule-test");allocator.bind(&mut binding);
    let challenge=binding.challenge_scalar(b"binding");
    let mut repeated=Transcript::new(b"schedule-test");allocator.bind(&mut repeated);
    assert_eq!(challenge,repeated.challenge_scalar(b"binding"));
    let mut changed=Transcript::new(b"schedule-test");allocator.bind(&mut changed);
    changed.append_u64(b"schedule-context",1_827_839);
    assert_ne!(challenge,changed.challenge_scalar(b"binding"));
    // Read-only downstream census over every branch of the N3/N4 parent
    // fixtures, plus all local endpoint tables and all eleven core banks.
    let different=WorkTreeHistoryPlan::compile(4,2,[8;32],[0x35;28]).unwrap();
    assert!(allocator.check_parent(&different).is_err());
    assert!(ScheduleAnchorAllocator::compile(&different,Policy::FixtureN3).is_err());
    let engine=crate::work_tree_fixed_hash::engine().unwrap();
    for base in work_tree_layout::CORE_OFFSETS {assert!(base+engine.core.input_len<=BASE);}
    let mut consumers=0usize;
    for plan in [&parent,&different] {
        for family in plan.topology().families.iter().chain(plan.work_boundary().links()) {
            assert!(family.left_wires.iter().chain(&family.right_wires).all(|w| !(BASE..END).contains(w)));
        }
        for owner in 0..plan.slots() {
            let mut inspect=|t:Term| {
                assert!(!(BASE..END).contains(&(t.gate.left%WIDTH)));
                assert!(!(BASE..END).contains(&(t.gate.right%WIDTH)));
                consumers+=1;
            };
            crate::work_tree_fixed_hash::emit_slot(engine,plan.fixed_profile(),owner,&mut inspect).unwrap();
            plan.leaf_boundary().emit_slot(owner,&mut inspect).unwrap();
            plan.work_boundary().emit_slot(owner,&mut inspect).unwrap();
        }
    }
    println!("non-HEADER bounded native terms checked: {consumers}; helper consumers: 0");
    println!("canonical HEADER anchors certified: 5442; fixture owner omissions [3394,2721,0,0]; H21 full-plan mask pending");
}

//! Conditional no-frame tests. Synthetic native leases never establish H21
//! native production execution, HEADER retirement, global ROW or a proof.
use super::*;
use crate::packed_owner_assembly::NativeWorkDLease;

fn varied_snapshot()->Eligible08NativeSnapshot {
    // Independent difficulty epochs; the clipped context1 terminal belongs
    // to the same difficulty epoch as context0's later regular endpoint.
    let prepared=Prepared::from_d_iter_eligible08((FIRST..=LAST).map(|height| {
        let end=if height==FIRST {FIRST}else{FIRST+(height-FIRST).div_ceil(128)*128};
        let d=match end {1810688=>19,1810816=>3,1810944=>7,
            1827712=>23,1827840=>5,844672=>29,844800=>11,_=>13};
        (height,BigUint::from(d as u64))
    })).unwrap();
    Eligible08NativeSnapshot{parent:NativeParent{root:[17;32],total:[0;28],profile:[21;32],
        cut:CutDescriptor::eligible08()},prepared}
}
fn record(snapshot:&Eligible08NativeSnapshot,owner:usize)->MaxRecord {
    let mut out=MaxRecord{owner,d:[0;28],max:[None;2]};
    for (bit,&(_,value)) in snapshot.prepared.owner_work_d(owner).unwrap().unwrap().cells().iter().enumerate() {
        MaxRecord::set(&mut out.d,bit,value).unwrap();
    }
    for span in &snapshot.prepared.owner_patch(owner).unwrap().spans {if let Writer::Max{context,..}=span.writer {
        let mut bytes=[0;85];
        for (bit,&value) in span.values.iter().enumerate(){MaxRecord::set(&mut bytes,bit,value).unwrap();}
        out.max[context]=Some(bytes);
    }}out
}
// Position a conditional fixture at one calendar cut. It is intentionally
// incomplete: seeded successor records do not impersonate native execution.
fn at(snapshot:&Eligible08NativeSnapshot,owner:usize)->MaxStream<'_> {
    let mut stream=MaxStream::from_snapshot(snapshot).unwrap();
    stream.next=stream.calendar.iter().position(|(at,_)|*at==owner).unwrap();
    let steps=stream.calendar[stream.next].1;
    for context in 0..2 {if let Some(next)=steps[context].and_then(|step|step.next) {
        let index=stream.records.len();stream.records.push(record(snapshot,next));stream.frontier[context]=Some(index);
    }}stream
}
fn source(snapshot:&Eligible08NativeSnapshot,owner:usize)->NativeWorkDLease {
    let d=snapshot.prepared.owner_work_d(owner).unwrap().unwrap().cells().iter().enumerate()
        .filter(|(_,(_,value))|value.is_one()).fold(0u64,|sum,(bit,_)|sum|(1u64<<bit));
    NativeWorkDLease::synthetic_for_test(snapshot.parent(),owner,d)
}
fn reject(stream:&mut MaxStream<'_>,lease:&Eligible08OwnerLease,source:&NativeWorkDLease,expected:&str) {
    let before=(stream.parent.clone(),stream.next,stream.frontier,stream.records.clone());
    assert_eq!(stream.append(lease,source).unwrap_err(),expected);
    assert_eq!((stream.parent.clone(),stream.next,stream.frontier,stream.records.clone()),before);
}

#[test]
fn c185_independent_literal_full_calendar_and_retention_census() {
    let plan=Plan::eligible08();let actual=plan.max_calendar();
    let mut literal:BTreeMap<usize,[Option<MaxStep>;2]>=BTreeMap::new();
    let mut counts=[0;2];let mut edges=[0;2];
    for (context,terminal) in [(0,1827840usize),(1,1810842usize)] {
        let mut ends=vec![844672];
        let mut height=844673;
        while height<=terminal {ends.push((height+127).min(terminal));height+=128;}
        for (index,&end) in ends.iter().enumerate() {
            literal.entry(end-2).or_insert([None;2])[context]=Some(MaxStep{end,next:ends.get(index+1).map(|next|next-2)});
        }
        counts[context]=ends.len();edges[context]=ends.len()-1;
    }
    assert_eq!(actual,literal.into_iter().rev().collect::<Vec<_>>());
    assert_eq!(counts,[7682,7550]);assert_eq!(edges,[7681,7549]);assert_eq!(actual.len(),7683);
    assert_eq!(actual.iter().filter(|(_,steps)|steps.iter().all(Option::is_some)).count(),7549);
    for (owner,expected) in [(844670,[Some(844798),Some(844798)]),
        (1810814,[Some(1810942),Some(1810840)]),(1810840,[None,None]),
        (1827710,[Some(1827838),None]),(1827838,[None,None])] {
        let steps=actual.iter().find(|(at,_)|*at==owner).unwrap().1;
        assert_eq!(steps.map(|step|step.and_then(|step|step.next)),expected);
    }
    let snapshot=varied_snapshot();let stream=MaxStream::from_snapshot(&snapshot).unwrap();
    assert!(stream.retained_capacity_bytes()<2*1024*1024);
    assert_eq!(stream.remaining_owners(),7683);
    assert!(stream.closed_owner_cells(1827838).is_err());
    println!("C185_CALENDAR contexts={counts:?} edges={edges:?} union=7683 record_size={} calendar_size={} record_capacity={} calendar_capacity={} retained_capacity_bytes={} HEADER_rows=0; native_H21=OPEN",
        std::mem::size_of::<MaxRecord>(),std::mem::size_of::<(usize,[Option<MaxStep>;2])>(),
        stream.records.capacity(),stream.calendar.capacity(),stream.retained_capacity_bytes());
}

#[test]
fn c185_noframe_varied_d_edges_terminals_atomic_and_partial_state() {
    let snapshot=varied_snapshot();
    for owner in [844670,844798,1810686,1810814,1810840,1827710,1827838] {
        let lease=snapshot.owner_lease(owner).unwrap();let source=source(&snapshot,owner);
        let mut stream=at(&snapshot,owner);
        stream.append(&lease,&source).unwrap();
        assert_eq!(stream.records.last().unwrap(),&record(&snapshot,owner));
        let out=stream.records.last().unwrap();
        assert_eq!(out.d[0],match owner {844670=>29,844798=>11,1810686=>19,1810814=>3,1810840=>7,1827710=>23,1827838=>5,_=>unreachable!()});
        assert!(out.max.iter().flatten().all(|bytes|bytes[84]&0xfe==0));
        for span in &lease.patch.spans {if let Writer::Max{context,..}=span.writer {
            for (bit,&value) in span.values.iter().enumerate() {
                assert_eq!(MaxRecord::bit(out.max[context].as_ref().unwrap(),bit),value);
            }
        }}
        assert!(stream.closed_owner_cells(owner).is_err(),"partial fixture cannot export staged values");
    }
    // Real consecutive c1 tail transitions include both compare branches.
    let mut tail=at(&snapshot,1810840);
    let terminal=snapshot.owner_lease(1810840).unwrap();tail.append(&terminal,&source(&snapshot,1810840)).unwrap();
    assert_eq!(tail.calendar[tail.next].0,1810814);
    // c0's independently seeded frontier belongs to its next regular owner.
    tail.records.push(record(&snapshot,1810942));tail.frontier[0]=Some(tail.records.len()-1);
    for owner in [1810814,1810686] {
        tail.append(&snapshot.owner_lease(owner).unwrap(),&source(&snapshot,owner)).unwrap();
    }
    let owner=1810814;let lease=snapshot.owner_lease(owner).unwrap();let good=source(&snapshot,owner);
    for kind in 0..9 {
        let mut stream=at(&snapshot,owner);let mut wrong=good.clone();wrong.mutate_for_test(kind);
        let expected=match kind {0=>"streamed MAX exact native Work-D expectation",1|2=>"native Work-D parent/cut/owner/height",
            3|4=>"native Work-D exact 224-cell census",6=>"native Work-D nonboolean source",_=>"native Work-D exact ordered domain"};
        reject(&mut stream,&lease,&wrong,expected);
    }
    for field in 0..4 {
        let mut wrong=lease.clone();
        match field {0=>wrong.parent.root[0]^=1,1=>wrong.parent.total[0]^=1,
            2=>wrong.parent.profile[0]^=1,_=>wrong.parent.cut=CutDescriptor::diagnostic08()}
        reject(&mut at(&snapshot,owner),&wrong,&good,"Eligible08 MAX/Cap owner patch parent/source");
    }
    for kind in 0..4 {
        let mut wrong=lease.clone();
        match kind {
            0=>{wrong.patch.spans[0].writer=Writer::Max{context:1,end:owner+2};},
            1=>{wrong.patch.spans[0].writer=Writer::Max{context:0,end:owner+3};},
            2=>{wrong.patch.spans[0].values.pop();},
            _=>{wrong.patch.spans.push(wrong.patch.spans[0].clone());},
        }
        reject(&mut at(&snapshot,owner),&wrong,&good,"Eligible08 MAX/Cap owner patch parent/source");
    }
    let mut wrong=lease.clone();let zero=wrong.patch.spans[0].values.iter().position(Zero::is_zero).unwrap();
    wrong.patch.spans[0].values[zero]=Fr::one();
    reject(&mut at(&snapshot,owner),&wrong,&good,"Eligible08 MAX/Cap owner patch parent/source");
    for kind in 0..3 {
        let mut stream=at(&snapshot,owner);let index=stream.frontier[1].unwrap();
        match kind {0=>stream.records[index].owner+=1,1=>stream.records[index].max[1]=None,
            _=>stream.records[index].max[1].as_mut().unwrap()[0]^=1}
        reject(&mut stream,&lease,&good,if kind<2{"streamed MAX exact typed successor"}else{"streamed MAX successor value"});
    }
    let mut stream=at(&snapshot,owner);stream.frontier[1]=None;
    reject(&mut stream,&lease,&good,"streamed MAX successor/terminal census");
    let mut stream=at(&snapshot,owner);
    reject(&mut stream,&snapshot.owner_lease(1810686).unwrap(),&source(&snapshot,1810686),"streamed MAX exact descending owner");
    stream.append(&lease,&good).unwrap();
    reject(&mut stream,&lease,&good,"streamed MAX exact descending owner");
    // Producer mutants recompute the lease from the mutated snapshot, so the
    // named terminal/residual predicate must reject, not a stale copied lease.
    for context in 0..2 {
        let mut wrong=varied_snapshot();let owner=if context==0{1827838}else{1810840};
        wrong.prepared.max[context].last_mut().unwrap().t=BigUint::from(1u8);
        reject(&mut at(&wrong,owner),&wrong.owner_lease(owner).unwrap(),&source(&wrong,owner),"streamed MAX terminal T must be zero");
    }
    for field in 0..3 {
        let mut wrong=varied_snapshot();let index=wrong.prepared.plan.max_index(1,owner).unwrap();
        let witness=&mut wrong.prepared.max[1][index];
        match field {0=>witness.r+=BigUint::from(1u8),1=>witness.delta+=BigUint::from(1u8),_=>witness.less=!witness.less}
        reject(&mut at(&wrong,owner),&wrong.owner_lease(owner).unwrap(),&source(&wrong,owner),"streamed MAX exact residual census/value");
    }
    println!("C185_NOFRAME first_regular both_contexts c1_26_tail both_terminals varied_D both_branches atomic_faults; HEADER_Cap_PCS_proof=OPEN native_H21=OPEN");
}

#[test]
fn c185_conditional_closed_replay_is_staged_and_partial_rejects() {
    let snapshot=varied_snapshot();let mut stream=MaxStream::from_snapshot(&snapshot).unwrap();
    assert_eq!(stream.closed_owner_cells(844670).unwrap_err(),"streamed MAX incomplete closure");
    stream.next=stream.calendar.len();
    assert_eq!(stream.closed_owner_cells(844670).unwrap_err(),"streamed MAX incomplete closure");
    // Conditional replay fixture only: populate exact immutable Prepared bits.
    // This deliberately does not claim execution of every native source join.
    stream.records=stream.calendar.iter().map(|(owner,_)|record(&snapshot,*owner)).collect();
    for owner in [844670,1810814,1810840,1827838] {
        let cells=stream.closed_owner_cells(owner).unwrap();
        let mut expected:Vec<_>=snapshot.prepared.owner_work_d(owner).unwrap().unwrap().cells().iter()
            .map(|&(wire,value)|(wire,MaxReplayAuthor::NativeWorkD{height:owner+2},value)).collect();
        expected.extend(snapshot.owner_lease(owner).unwrap().cells().into_iter()
            .filter(|(_,writer,_)|matches!(writer,Writer::Max{..}))
            .map(|(wire,writer,value)|(wire,MaxReplayAuthor::Scheduled(writer),value)));
        assert_eq!(cells,expected);
        assert!(cells.len()==897 || cells.len()==1570);
        assert_eq!(cells.iter().map(|(wire,_,_)|*wire).collect::<std::collections::BTreeSet<_>>().len(),cells.len());
    }
    assert_eq!(stream.closed_owner_cells(844671).unwrap_err(),"streamed MAX replay inactive owner");
    assert!(stream.retained_capacity_bytes()<2*1024*1024);
    println!("C185_REPLAY exact_lossless_values staged_vec complete_vs_partial source_join_execution=NOT_CLAIMED native_H21=OPEN");
}

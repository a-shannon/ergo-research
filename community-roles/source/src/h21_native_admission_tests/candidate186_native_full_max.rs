//! One-use bounded native MAX-only diagnostic. No synthetic source seeds,
//! HEADER retirement, global X/ROW, PCS, proof or client are exercised here.
use super::*;
use ark_ff::One;
use crate::h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxReplayAuthor, MaxStep, MaxStream,
    Plan as MaxPlan, Writer};

fn phase(label:&str,started:Instant) {
    println!("C186_PHASE label={label} elapsed_s={:.6}",started.elapsed().as_secs_f64());
    std::io::stdout().flush().expect("flush c186 phase");
}

fn calendar()->Vec<(usize,[Option<MaxStep>;2])> {
    // Independent literal endpoint partition, including unequal terminal cuts.
    let mut literal:BTreeMap<usize,[Option<MaxStep>;2]>=BTreeMap::new();
    let mut counts=[0;2];let mut edges=[0;2];
    for (context,terminal) in [(0,1_827_840usize),(1,1_810_842usize)] {
        let mut ends=vec![844_672];
        for start in (844_673..=terminal).step_by(128) {ends.push((start+127).min(terminal));}
        counts[context]=ends.len();edges[context]=ends.len()-1;
        for (index,&end) in ends.iter().enumerate() {
            literal.entry(end-2).or_insert([None;2])[context]=Some(MaxStep {
                end,next:ends.get(index+1).map(|next|next-2)});
        }
    }
    assert_eq!(counts,[7682,7550]);assert_eq!(edges,[7681,7549]);
    let literal:Vec<_>=literal.into_iter().rev().collect();
    assert_eq!(literal.len(),7683);
    assert_eq!(literal.iter().filter(|(_,steps)|steps.iter().all(Option::is_some)).count(),7549);
    assert_eq!(literal,MaxPlan::eligible08().max_calendar());
    assert_eq!(literal.first().unwrap().0,1827838);assert_eq!(literal[1].0,1827710);
    assert_eq!(literal.last().unwrap().0,844670);
    assert_eq!(literal.iter().find(|(owner,_)|*owner==1810814).unwrap().1,
        [Some(MaxStep{end:1810816,next:Some(1810942)}),Some(MaxStep{end:1810816,next:Some(1810840)})]);
    literal
}

#[test]
fn c186_native_full_max_no_frame_preflight() {
    let owners=calendar();
    assert_eq!(owners.iter().filter(|(_,steps)|steps[0].is_some_and(|step|step.next.is_none())).count(),1);
    assert_eq!(owners.iter().filter(|(_,steps)|steps[1].is_some_and(|step|step.next.is_none())).count(),1);
    println!("C186_PREFLIGHT_PASS context0_owners=7682 context1_owners=7550 edges0=7681 edges1=7549 union=7683 shared=7549 native_execution=false");
}

#[test]
#[ignore = "one-use native frame run requires exact-source runner prelaunch review"]
fn c186_native_full_max_from_pinned_frame() {
    let started=Instant::now();let owners=calendar();phase("frame_start",started);
    let path=std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment");
    let path=Path::new(&path);assert!(path.is_absolute());
    let before=fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(),FRAME_BYTES);
    let file=File::open(path).expect("open existing pinned frame");
    assert_eq!(file.metadata().unwrap().len(),FRAME_BYTES);
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES).expect("frame SHA setup");
    preamble(&mut frame,1_827_839,N as u32).expect("pinned ERFV preamble");
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers).expect("single linked native H21 prefix");
        assert_eq!(headers.remaining,0);(prefix,headers.extensions)
    };
    assert_eq!(prefix.header_count(),N);assert_eq!(frame.offset,PREFIX_BYTES);assert_eq!(extensions,EXTENSIONS);
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256).expect("whole existing frame exact SHA");
    let after=fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(),before.len());assert_eq!(after.modified().unwrap(),before.modified().unwrap());
    phase("frame_verified",started);
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28()).expect("native H21 plan");
    validate_native_plan_input(&plan,&prefix).expect("native plan/prefix identity");
    phase("plan_verified",started);
    let snapshot=Eligible08NativeSnapshot::new(&plan,&prefix).expect("native immutable Eligible08 snapshot");
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix).expect("native producer");
    let mut stream=MaxStream::new(&plan,&prefix,&snapshot).expect("native MAX-only stream");
    assert_eq!(stream.remaining_owners(),7683);assert!(stream.retained_capacity_bytes()<2*1024*1024);
    phase("ready",started);
    println!("C186_CALENDAR context0_owners=7682 context1_owners=7550 edges0=7681 edges1=7549 union=7683 shared=7549 retained_capacity_bytes={}",stream.retained_capacity_bytes());
    assert_eq!(stream.push_native(&producer,owners[1].0).unwrap_err(),"streamed MAX exact descending owner");
    assert_eq!(stream.remaining_owners(),7683);
    assert_eq!(stream.closed_owner_cells(owners[0].0).unwrap_err(),"streamed MAX incomplete closure");
    println!("C186_ORDER_REJECT owner={} remaining=7683 replay_unavailable=true",owners[1].0);
    for (index,(owner,_)) in owners.iter().enumerate() {
        if index==owners.len()-1 {
            assert_eq!(stream.remaining_owners(),1);
            assert_eq!(stream.closed_owner_cells(owners[0].0).unwrap_err(),"streamed MAX incomplete closure");
            println!("C186_PARTIAL_REPLAY_REJECT owners=7682 remaining=1");
        }
        stream.push_native(&producer,*owner).expect("native MAX owner append");
        assert_eq!(stream.remaining_owners(),owners.len()-index-1);
        if [1,32,128,7683].contains(&(index+1)) {
            println!("C186_MAX_PROGRESS owners={} remaining={} elapsed_s={:.6}",index+1,stream.remaining_owners(),started.elapsed().as_secs_f64());
            std::io::stdout().flush().expect("flush c186 MAX progress");
        }
    }
    assert_eq!(stream.remaining_owners(),0);
    let exports=NativeExports::new_for_history(&plan,&prefix).expect("independent native scalar exports");
    for owner in [844670,844798,1810814,1810840,1827838] {
        let cells=stream.closed_owner_cells(owner).expect("complete MAX-only replay");
        let lease=producer.native_work_d_lease(owner).expect("native D sample lease");
        producer.require_work_d_lease(owner,&lease).expect("native D source replay");
        let d=lease.checked_cells(&snapshot.parent(),owner).expect("native D exact224");
        assert_eq!(d.len(),224);
        let expected_lease=snapshot.owner_lease(owner).expect("immutable scheduled sample");
        assert_eq!(d,expected_lease.work_d().unwrap().cells());
        let mut expected:Vec<_>=d.iter().map(|&(wire,value)| {
            assert_eq!(value,Fr::from(exports.bit(wire).expect("native export D")as u64));
            (wire,MaxReplayAuthor::NativeWorkD{height:owner+2},value)
        }).collect();
        expected.extend(expected_lease.cells().into_iter().filter(|(_,writer,_)|matches!(writer,Writer::Max{..}))
            .map(|(wire,writer,value)|(wire,MaxReplayAuthor::Scheduled(writer),value)));
        assert_eq!(cells,expected);
        assert!(cells.iter().all(|(_,_,value)|value.is_zero()||value.is_one()));
        assert_eq!(cells.iter().map(|(wire,_,_)|*wire).collect::<BTreeSet<_>>().len(),cells.len());
        println!("C186_REPLAY owner={owner} d_cells=224 max_cells={} total_cells={}",cells.len()-224,cells.len());
    }
    assert_eq!(stream.closed_owner_cells(844671).unwrap_err(),"streamed MAX replay inactive owner");
    phase("replay_verified",started);
    println!("C186_NATIVE_MAX_PASS owners=7683 context0_owners=7682 context1_owners=7550 edges0=7681 edges1=7549 shared=7549 samples=5 retained_capacity_bytes={} global_x_row=false pcs_proof_client=false",stream.retained_capacity_bytes());
}

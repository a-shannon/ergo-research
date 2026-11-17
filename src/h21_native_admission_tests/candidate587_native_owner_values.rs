//! One shared prefix/MAX/Score pass, then complete owner-value compositions.
use super::*;
use std::fs::OpenOptions;
use std::os::windows::fs::OpenOptionsExt;
use crate::{h21_scheduled_max_cap::{Eligible08NativeSnapshot,MaxStream,Plan as MaxPlan},
    packed_owner_assembly::{H21EligibleContext,h21_structural_roster::{H21StructuralRoster,PublicMapParameters}}};

#[test]
#[ignore = "pinned retained H21 frame; reviewed bounded native Job required"]
fn c587_native_complete_owner_values_and_literal_equations()->Result<(),String> {
    let frame_path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("C587 H21 frame path required")?;
    let path=Path::new(&frame_path);
    if !crate::preview_test_paths::absolute_outside_source(path) {return Err("C587 external absolute frame path".into());}
    let metadata=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !metadata.is_file()||metadata.file_type().is_symlink()||metadata.len()!=FRAME_BYTES {
        return Err("C587 pinned frame file/size".into());
    }
    // The existing Read1/Job preflight checks ancestors and exact provenance.
    // Keep this same handle write/delete-denying through the whole diagnostic.
    let mut file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {return Err("C587 opened frame size".into());}
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,&mut file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0 {return Err("C587 incomplete RAW source".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N||frame.offset!=PREFIX_BYTES||extensions!=EXTENSIONS {
        return Err("C587 prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    let context=H21EligibleContext::new(&plan,&prefix)?;
    let producer=context.native_owner_values_producer();
    let snapshot=Eligible08NativeSnapshot::new(&plan,&prefix)?;
    let mut max=MaxStream::new(&plan,&prefix,&snapshot)?;
    let calendar=MaxPlan::eligible08().max_calendar();
    if calendar.len()!=7_683 {return Err("C587 MAX calendar census".into());}
    for (owner,_) in calendar {max.push_native(producer,owner)?;}
    max.closed_native_snapshot(&plan,&prefix)?;
    let mut score=context.score_endpoint_stream(&max)?;
    let mut pushes=0usize;
    while let Some(owner)=score.next_owner() {
        if pushes>=7_542 {return Err("C587 Score calendar extent".into());}
        score.push_native(owner)?;pushes+=1;
    }
    if pushes!=7_542||!score.is_closed() {return Err("C587 Score calendar census".into());}
    score.terminal_r()?;
    let parameters=crate::bank53_map::CutDescriptor::eligible08().terminals()
        .map(|terminal|PublicMapParameters {terminal,exponent:55,
            lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},branch:LowerBranch::Pivot(54)}});
    let roster=H21StructuralRoster::from_public(&plan,parameters)?;
    let started=Instant::now();let mut rows=0usize;
    for owner in [0,844_672,844_798,417_790,845_758,845_759,846_014,846_015,
        1_810_840,1_810_841,1_810_904,N,(1<<21)-1] {
        let row=score.native_owner_values(owner)?;
        row.require_context(&context)?;
        if row.packed_bytes().len()!=131_072||row.owner()!=owner {return Err("C587 final owner bytes".into());}
        score.check_native_role1_values(&row,&roster)?;
        let c=row.census();
        println!("C587_NATIVE_OWNER_VALUES_PASS owner={owner} bytes=131072 map={:?} score={:?} slack={:?} max={:?} cap={:?} literal_role1=true global=false proof=false",c.map,c.score,c.slack,c.max,c.cap);
        std::io::stdout().flush().map_err(|e|e.to_string())?;rows+=1;
    }
    if rows!=13 {return Err("C587 selected owner class census".into());}
    println!("C587_NATIVE_VALUES_JOIN_PASS rows={rows} elapsed_us={} prefix_passes=1 max_passes=1 score_passes=1 global=false proof=false",started.elapsed().as_micros());
    Ok(())
}

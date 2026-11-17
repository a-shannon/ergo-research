use super::*;
use crate::{h21_scheduled_max_cap::{Eligible08NativeSnapshot,MaxStream,Plan as MaxPlan},
    packed_owner_assembly::H21EligibleContext,work_tree_history_plan::WorkTreeHistoryPlan};

#[test]
#[ignore="retained ERFV reader plus one native MAX/Score pass; project-local fresh fragment output required"]
fn c588_native_packed_prefix16_from_retained_history()->Result<(),String> {
    let output=std::env::var_os("NIPOPOW_C588_FRAGMENT_PATH").ok_or("C588 fragment output path required")?;
    let output=Path::new(&output);
    crate::h21_native_admission_tests::c574_with_pinned_prefix(|prefix| {
        let plan=WorkTreeHistoryPlan::compile(N as u64,21,prefix.root(),prefix.total_be28())?;
        let context=H21EligibleContext::new(&plan,prefix)?;
        let producer=context.native_owner_values_producer();
        let snapshot=Eligible08NativeSnapshot::new(&plan,prefix)?;
        let mut max=MaxStream::new(&plan,prefix,&snapshot)?;
        let calendar=MaxPlan::eligible08().max_calendar();
        if calendar.len()!=7_683 {return Err("C588 MAX calendar census".into());}
        for(owner,_)in calendar {max.push_native(producer,owner)?;}
        max.closed_native_snapshot(&plan,prefix)?;
        let mut stream=context.score_endpoint_stream(&max)?;let mut pushes=0usize;
        while let Some(owner)=stream.next_owner() {
            if pushes>=7_542 {return Err("C588 Score calendar extent".into());}
            stream.push_native(owner)?;pushes+=1;
        }
        if pushes!=7_542 || !stream.is_closed() {return Err("C588 Score calendar census".into());}
        stream.terminal_r()?;
        let export_started=std::time::Instant::now();
        let fragment=stream.write_h21_prefix(output,4)?;
        let generation_export_readback_us=export_started.elapsed().as_micros();
        if fragment.owners()!=16 || fragment.bytes()!=2_097_152
            || fragment.parent_binding()!=&HeaderSourceBinding::for_plan(&plan,0)? {
            return Err("C588 native fragment final extent/parent".into());
        }
        let digest=fragment.digest().iter().map(|b|format!("{b:02X}")).collect::<String>();
        println!("C588_NATIVE_PACKED_FRAGMENT_PASS owners=16 bytes=2097152 target_log_n=41 stored_log_n=24 contexts=2 digest={digest} generation_export_readback_us={generation_export_readback_us} prefix_passes=1 max_passes=1 score_passes=1 complete=false pcs=false proof=false source_qualified=false");
        Ok(())
    })
}

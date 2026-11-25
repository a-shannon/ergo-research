//! Genuine, selected N0 owners through the serial and indexed Rayon paths.
use super::*;
use ark_serialize::CanonicalSerialize;
use crate::packed_owner_assembly::h21_structural_roster::H21StructuralRoster;
use std::{path::Path,sync::atomic::{AtomicU64,Ordering},time::Instant};

type Load<'a>=dyn Fn(usize)->Result<Vec<u8>,String>+Sync+'a;
type Visit<'a>=dyn Fn(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>+Sync+'a;

#[link(name="kernel32")]
extern "system" { fn GetCurrentProcessorNumber()->u32; }

fn hash(data:&[u8])->Result<String,String>{
    Ok(crate::native_prefix_auth_plan::role0_sha256(data)?.iter().map(|b|format!("{b:02x}")).collect())
}
fn encode(values:&[Fr])->Result<Vec<u8>,String>{
    let mut out=Vec::with_capacity(values.len()*32);
    for v in values{v.serialize_compressed(&mut out).map_err(|e|e.to_string())?;}
    Ok(out)
}

fn reference(pass:Pass<'_>,load:&Load<'_>,mut visit:&Visit<'_>,stats:&mut EdgeFullStats,
    sink:&mut dyn FnMut(usize,[Fr;3])->Result<(),String>)->Result<(),String>{
    let mut input=h21_role1_input(load)?;
    let weight=|e:&EdgeTerm|Ok(pass.rows.at(e.term.row));
    for (offset,&count) in pass.counts.iter().enumerate(){
        let owner=pass.start+offset;
        let (state,high)=match pass.side{
            Side::U=>(edge_replay_u(&mut visit,&mut input,owner,WIDTH,OWNERS,19,&[19],
                count,&weight,pass.prefix,Some(pass.projection))?,None),
            Side::V{local,owners,value,zero}=>(edge_replay_v_with_zero(&mut visit,&mut input,owner,
                WIDTH,OWNERS,19,&[19],count,&weight,owners,local,value,pass.prefix,Some(pass.projection),zero)?,Some(owners)),
        };
        stats.state(&state,count,false,pass.prefix.len(),&input)?;
        let values=h21_weighted_header::combine(Some(pass.header),Some(pass.round),
            &mut input,owner,&state,high)?;
        let result=if pass.prefix.len()==20{[values[0],values[1],state.x[0]]}else{values};
        sink(owner,result)?;
    }
    Ok(())
}

fn shape(s:&EdgeFullStats)->[u64;8]{
    [s.term_callbacks,s.owner_requests,s.emitted_fields,s.sequential_x_folds,s.sequential_bank_folds,
        s.input_vector_clones,s.x as u64,s.banks as u64]
}

// Each selected triplet below was recorded before the parallel producer, on
// the same N0 witness. Terminals are the archived A, B and folded X fields.
// Fixture source: historical weighted-message measurement e59c2dd0…44df2.
const CASES:[(bool,usize,usize,usize,usize,&str);7]=[
    (true,0,600016,32,600023,"3a465ea27876ec22d3c82c083313cd285ea2d964fd7f373b8b5fec811e8208f0"),
    (false,3,600016,32,600023,"3c7c17e98fc397740ed2bba734cce08c20c92852f1b51222a6f0de5f49853fbe"),
    (false,0,0,4,0,"5d8ffed23e3bd073ad36be94f203975a66f17138f5ae38728841d2c63f7e4ad9"),
    (true,3,1804167,8,1804170,"13991e094ed8582f18b6094b85f5bcc5540059803fbd94d6fefb78ef01023404"),
    (true,20,1819600,65,1819648,"b415f8a6ae7ca93e7905204ee4a5dc58146ce1c4ee17e1cafa027b69c2142503"),
    (false,20,0,4,0,"25cde3835509a505f7096d2d5736f48c396d8b9b1b7d2df6b91e97533c4bf483"),
    (false,20,1804168,4,1804170,"0dfedec77c1c0c223a9749f1867266459bd40cb1f573dabfe792ac79a27c2e8e"),
];

pub(crate) fn check_h21_owner_batches(roster:&H21StructuralRoster<'_>,r:&[Fr],file:&Path)
    ->Result<(),String>{
    if r.len()!=40 || hash(&encode(r)?)?!="847f7f928eefffc0be797082fd41a03728ff2533d3799e028617f710dac91c55"{
        return Err("different historical N0 role-1 row point".into());
    }
    let mut witness=crate::packed::open_untrusted_held_regular(file,1<<38)?;
    let mut diagnostic=Transcript::new(b"nipopow/role1/partial-owner-cost/nonproduction-points/v1");
    for x in r{diagnostic.append_scalar(b"historical row point",x);}
    let u:Vec<_>=(0..41).map(|_|diagnostic.challenge_scalar(b"analysis u")).collect();
    let v:Vec<_>=(0..20).map(|_|diagnostic.challenge_scalar(b"analysis v")).collect();
    let lv=diagnostic.challenge_scalar(b"analysis left value");
    let ul=gkr::eq_weights(&u[..20]);let uh=gkr::eq_weights(&u[20..]);
    let d=roster.score_slack_right_zero_d(r,&u,lv)?;
    let header=h21_weighted_header::Header::new(roster,r)?;
    let weights=EqWeightLookup::new(r);
    let pool=|workers|rayon::ThreadPoolBuilder::new().num_threads(workers).stack_size(4<<20)
        .build().map_err(|e|e.to_string());
    let pool2=pool(2)?;let pool4=pool(4)?;
    let reads=AtomicU64::new(0);
    let bytes=AtomicU64::new(0);
    crate::packed::with_shared_h21_owner_rows(&mut witness,|size,status,_started|{
        if status.is_ok(){reads.fetch_add(1,Ordering::Relaxed);bytes.fetch_add(size as u64,Ordering::Relaxed);}
    },|load|{
        for (owner,pin) in [
            (0,"e4132d69ccb280d235bb818055febd9ca000b5c94dbf49a6225d2f9ba528fe58"),
            (600023,"07bd32a9a66037bb94837f0cf32be4ad3c4358e6ef725816f819ca2156283c65"),
            (1804170,"975e9f79703a3e4c0d1033f7f5703ac63327f2882232227425fc4864719779a8"),
            (1819648,"8398a2898c274d80b79e104091846583b5869644fa644adee60a35c0a7d76530")
        ]{if hash(&load(owner)?)?!=pin{return Err(format!("different original N0 owner {owner}"));}}
        let mut observations=Vec::new();
        for (index,&(left,k,start,n,known,pin)) in CASES.iter().enumerate(){
            let prefix=if left{&u[..k]}else{&v[..k]};
            let round=header.round(prefix,if left{None}else{Some((&ul,lv))})?;
            let projection=EdgeFullStats::default().plan(WIDTH,prefix,true)?;
            let literal=|side,slot,s:&mut dyn FnMut(EdgeTerm)->Result<(),String>|h21_u0::emit(roster,side,slot,s);
            let mut counts=Vec::with_capacity(n);
            for owner in start..start+n {
                counts.push(walk_edge_endpoint(&mut {&literal},left,owner,WIDTH,OWNERS,19,&[19],None,&mut |_|Ok(()))?);
            }
            let pass=Pass{side:if left{Side::U}else{Side::V{local:&ul,owners:&uh,value:lv,zero:Some(d)}},
                start,counts:&counts,prefix,projection:&projection,header:&header,round:&round,rows:&weights};
            let mut expected=None;
            let order:&[usize]=if index<2{&[1,2,4,4,2,1]}else{&[1,2,4]};
            for &workers in order{
                let worker_mask=AtomicU64::new(0);
                let processor_mask=AtomicU64::new(0);
                let visit=|side,slot,s:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{
                    if let Some(i)=rayon::current_thread_index(){worker_mask.fetch_or(1u64<<i,Ordering::Relaxed);}
                    let cpu=unsafe{GetCurrentProcessorNumber()};
                    if cpu>=64{return Err("unexpected processor group".into());}
                    processor_mask.fetch_or(1u64<<cpu,Ordering::Relaxed);
                    literal(side,slot,s)
                };
                let mut stats=EdgeFullStats::default();
                let mut outputs=Vec::with_capacity(n);
                let mut sink=|owner,row|{
                    if owner!=start+outputs.len(){return Err("test batch reordered owner".into());}
                    outputs.push(row);Ok(())
                };
                let before=reads.load(Ordering::Relaxed);
                let began=Instant::now();
                if workers==1{reference(pass,load,&visit,&mut stats,&mut sink)?;}
                else{
                    let lanes=Lanes{workers,load,visit:&visit};
                    let pool=if workers==2{&pool2}else{&pool4};
                    pool.install(||lanes.run(pass,&mut stats,&mut sink))?;
                }
                let elapsed=EdgeFullStats::ns(began)?;
                let observed=reads.load(Ordering::Relaxed)-before;
                let mask=worker_mask.load(Ordering::Relaxed);
                if index<2 && workers>1 && mask.count_ones() as usize!=workers {
                    return Err(format!("profile did not observe {workers} distinct Rayon workers"));
                }
                if outputs.len()!=n || stats.term_callbacks!=counts.iter().sum::<usize>() as u64 ||
                    stats.owner_requests!=n as u64 || hash(&encode(&outputs[known-start])?)?!=pin {
                    return Err("N0 historical owner or accounting differential".into());
                }
                let mut encoded=Vec::with_capacity(n*96);
                for row in &outputs{encoded.extend(encode(row)?);}
                let digest=hash(&encoded)?;
                let report=if let Some((reference_output,reference_stats))=&expected{
                    if *reference_output!=outputs || *reference_stats!=shape(&stats) {
                        return Err("serial and parallel owner sequences or statistics differ".into());
                    }
                    false
                }else{true};
                if report{expected=Some((outputs,shape(&stats)));}
                observations.push(serde_json::json!({"axis":if left{"U"}else{"V"},"k":k,"start":start,
                    "count":n,"workers":workers,"elapsed_ns":elapsed,"worker_mask":mask,
                    "processor_mask":processor_mask.load(Ordering::Relaxed),"physical_terms":stats.term_callbacks,
                    "read_calls":observed,"sha256":digest,"profiled":index<2}));
            }
            if index==2 {
                // Count fault on the last lane of this four-owner batch. No
                // result from the other successfully computed lanes is admitted.
                let mut wrong=counts.clone();wrong[n-1]+=1;
                let lanes=Lanes{workers:2,load,visit:&literal};
                let mut seen=0;
                let bad=Pass{counts:&wrong,..pass};
                let rejected=pool2.install(||lanes.run(bad,&mut EdgeFullStats::default(),&mut |_,_|{seen+=1;Ok(())}));
                if rejected.is_ok() || seen!=0{return Err("bad owner count escaped batch barrier".into());}
            }
        }
        println!("H21_OWNER_BATCH_MATCH {}",serde_json::json!({
            "snapshot":"N0","width_bits":20,"owner_bits":21,"workers":[1,2,4],"cases":CASES.len(),
            "profiles":12,"observations":observations,"witness_reads":reads.load(Ordering::Relaxed),
            "witness_bytes":bytes.load(Ordering::Relaxed),"checked_archived_triplets":CASES.len(),
            "subsequent_round_points":"diagnostic","proof_exported":false
        }));
        Ok(())
    })
}

//! Positive differential over complete owner messages, outside normal production.
use super::*;
use crate::packed_owner_assembly::h21_structural_roster::{Family,H21StructuralRoster};
use ark_serialize::CanonicalSerialize;
use std::{collections::{BTreeMap,BTreeSet},ffi::c_void,io::{Read,Seek,SeekFrom},path::Path,time::Instant};

const WIDTH:usize=1<<20;
const OWNERS:usize=1<<21;
const BYTES:usize=WIDTH/8;
const SAMPLE:[usize;6]=[0,600_023,844_672,845_887,1_804_170,1_819_648];
#[repr(C)]
#[derive(Default,Copy,Clone)]
struct FileTime{low:u32,high:u32}
impl FileTime{fn ticks(self)->u64{(u64::from(self.high)<<32)|u64::from(self.low)}}
#[link(name="kernel32")]
extern "system"{
    fn GetCurrentThread()->*mut c_void;
    fn GetThreadTimes(t:*mut c_void,c:*mut FileTime,e:*mut FileTime,k:*mut FileTime,u:*mut FileTime)->i32;
    fn QueryThreadCycleTime(t:*mut c_void,cycles:*mut u64)->i32;
}
fn clock()->Result<(u64,u64),String>{
    let [mut c,mut e,mut k,mut u]=[FileTime::default();4];let mut cycles=0;
    let t=unsafe{GetCurrentThread()};
    if unsafe{GetThreadTimes(t,&mut c,&mut e,&mut k,&mut u)}==0 || unsafe{QueryThreadCycleTime(t,&mut cycles)}==0{
        return Err(std::io::Error::last_os_error().to_string());}
    Ok(((k.ticks()+u.ticks())*100,cycles))
}
fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02x}")).collect()}
fn scalar_bytes(values:&[Fr])->Result<Vec<u8>,String>{
    let mut out=Vec::with_capacity(32*values.len());
    for v in values{v.serialize_compressed(&mut out).map_err(|e|e.to_string())?;}
    Ok(out)
}
fn sha(data:&[u8])->Result<String,String>{Ok(hex(&crate::native_prefix_auth_plan::role0_sha256(data)?))}

fn edges(roster:&H21StructuralRoster<'_>,weighted:bool,left:bool,owner:usize,
    sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
    let f=|_:Family,t:Term|{
        let (slot,local)=h21_role1_edge_metadata(t.row)?;
        if global_edge_row(slot,local,21,19,0,&[19])?!=t.row{return Err("noncanonical edge row".into());}
        sink(EdgeTerm{source_slot:slot,family_row:local,term:t})
    };
    if weighted{roster.role1_complement(left,owner,f)?;}else{roster.visit_role1_physical_endpoint(left,owner,f)?;}
    Ok(())
}

pub(crate) fn measure_weighted_n0_messages(roster:&H21StructuralRoster<'_>,r:&[Fr],path:&Path)->Result<(),String>{
    if r.len()!=40 || std::env::var("RAYON_NUM_THREADS").as_deref()!=Ok("1") ||
        std::env::var("RUST_TEST_THREADS").as_deref()!=Ok("1"){return Err("single-thread H21 real r required".into());}
    let census_start=Instant::now();
    let mut required=BTreeSet::new();let mut counts=BTreeMap::new();
    for &owner in &SAMPLE {
        required.insert(owner);
        for left in [true,false]{
            for fast in [false,true]{
                let mut emit=|side,o,s:&mut dyn FnMut(EdgeTerm)->Result<(),String>|edges(roster,fast,side,o,s);
                let count=walk_edge_endpoint(&mut emit,left,owner,WIDTH,OWNERS,19,&[19],None,&mut |t|{
                    if left{required.insert(t.term.gate.right/WIDTH);}
                    Ok(())
                })?;
                counts.insert((owner,left,fast),count);
            }
        }
    }
    if required.len()>128{return Err("spot check would exceed the retained-row read cap".into());}
    let census_ns=census_start.elapsed().as_nanos() as u64;
    let mut handle=crate::packed::open_untrusted_held_regular(path,1<<38)?;
    let mut data=BTreeMap::new();let mut witness_rows_sha256=BTreeMap::new();
    for owner in required{
        if owner>=OWNERS{return Err("row outside original source".into());}
        handle.seek(SeekFrom::Start((owner*BYTES) as u64)).map_err(|e|e.to_string())?;
        let mut row=vec![0u8;BYTES];handle.read_exact(&mut row).map_err(|e|e.to_string())?;
        witness_rows_sha256.insert(owner.to_string(),sha(&row)?);data.insert(owner,row);
    }
    let start=Instant::now();let header=h21_weighted_header::Header::new(roster,r)?;
    let table_ns=start.elapsed().as_nanos() as u64;
    let mut diagnostic=Transcript::new(b"nipopow/role1/partial-owner-cost/nonproduction-points/v1");
    for x in r{diagnostic.append_scalar(b"historical row point",x);}
    let u:Vec<_>=(0..41).map(|_|diagnostic.challenge_scalar(b"analysis u")).collect();
    let v:Vec<_>=(0..20).map(|_|diagnostic.challenge_scalar(b"analysis v")).collect();
    let lv=diagnostic.challenge_scalar(b"analysis left value");
    let ul=gkr::eq_weights(&u[..20]);let uh=gkr::eq_weights(&u[20..]);
    let right_zero=roster.score_slack_right_zero_d(r,&u,lv)?;
    let rw=EqWeightLookup::new(r);let weights=|e:&EdgeTerm|Ok(rw.at(e.term.row));
    let mut observations=Vec::new();
    for left in [true,false]{
        for k in [0usize,3,13,20]{
            let prefix=if left{&u[..k]}else{&v[..k]};
            let prep=Instant::now();
            let round=header.round(prefix,if left{None}else{Some((&ul,lv))})?;
            let mut metrics=EdgeFullStats::default();
            let projection=metrics.plan(WIDTH,prefix,true)?;
            let round_ns=prep.elapsed().as_nanos() as u64;
            for &owner in &SAMPLE{
                let mut expected=None;let mut samples=Vec::new();
                for mode in [false,true,true,false]{
                    let mut input=h21_role1_input(|row| data.get(&row).cloned().ok_or_else(||"non-retained witness row".into()))?;
                    let mut emit=|side,o,s:&mut dyn FnMut(EdgeTerm)->Result<(),String>|edges(roster,mode,side,o,s);
                    let count=counts[&(owner,left,mode)];
                    let before=clock()?;let timer=Instant::now();
                    let state=if left{
                        edge_replay_u(&mut emit,&mut input,owner,WIDTH,OWNERS,19,&[19],count,&weights,prefix,Some(&projection))?
                    }else{
                        edge_replay_v_with_zero(&mut emit,&mut input,owner,WIDTH,OWNERS,19,&[19],count,&weights,
                            &uh,&ul,lv,prefix,Some(&projection),Some(right_zero))?
                    };
                    let h=mode.then_some(&header);let hp=mode.then_some(&round);
                    let values=h21_weighted_header::combine(h,hp,&mut input,owner,&state,
                        if left{None}else{Some(&uh)})?;
                    let x_terminal=(k==20).then(||state.x[0]);
                    drop(state);drop(input);
                    let ns=timer.elapsed().as_nanos() as u64;let after=clock()?;
                    let output=(values,x_terminal);
                    if let Some(reference)=expected{if reference!=output{return Err(format!(
                        "role1 full {} contribution differs at owner {owner} prefix {k}",if left{"U"}else{"V"}));}}
                    else{expected=Some(output);}
                    samples.push(serde_json::json!({"mode":if mode{"weighted"}else{"reference"},
                        "physical_terms":count,"wall_ns":ns,"cpu_ns":after.0-before.0,"thread_cycles":after.1-before.1}));
                }
                let (values,x)=expected.ok_or("empty message sample")?;let mut fields=values.to_vec();
                if let Some(x)=x{fields.push(x);}
                observations.push(serde_json::json!({"axis":if left{"U"}else{"V"},"k":k,"owner":owner,
                    "kind":if k==20{"A_B_terminal_and_X"}else{"quadratic_coefficients"},"round_setup_ns":round_ns,
                    "coefficient_hex_le":hex(&scalar_bytes(&fields)?),"identical":true,"timings":samples}));
            }
        }
    }
    println!("ROLE1_WEIGHTED_N0_MESSAGES {}",serde_json::json!({"state":"ROLE1_WEIGHTED_N0_MESSAGES_MATCH",
        "snapshot":"N0","base_owners":SAMPLE,"witness_rows_sha256":witness_rows_sha256,"owner_bytes":BYTES,
        "canonical_r_sha256":sha(&scalar_bytes(r)?)?,"diagnostic_u_sha256":sha(&scalar_bytes(&u)?)?,
        "diagnostic_v_sha256":sha(&scalar_bytes(&v)?)?,"census_ns":census_ns,"header_setup_ns":table_ns,
        "global_right_zero_logical_terms":H21ScoreSlackRightZero::occurrences(),"observations":observations,
        "scope":"Actual committed N0 statement and role-1 output-point transcript. U0 uses no speculative preceding round. Later U/V points and left value are diagnostic; both paths consume identical original packed rows. Right(0) uses the separately checked analytic correction on both paths. Timings exclude cold storage reads, shared setup, global folds, line and PCS."}));
    Ok(())
}

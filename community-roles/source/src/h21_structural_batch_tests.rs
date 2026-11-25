//! Differential of the actual role-specific replay, including the cached endpoint lifecycle.
use super::*;
use super::{h21_owner_batches::Side,h21_structural_batches as sb};
use sb::Rounds;
use crate::daa_history_roster::DaaHistoryRoster;
use crate::historical_prefix_proof::H21StructuralDiagnosticContext;
use ark_serialize::CanonicalSerialize;
use std::{path::Path,sync::atomic::{AtomicU64,Ordering},time::Instant};

const WIDTH:usize=1<<20;
const OWNERS:usize=1<<21;
type Load<'a>=dyn Fn(usize)->Result<Vec<u8>,String>+Sync+'a;
type Visit<'a>=dyn Fn(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>+Sync+'a;

fn sha(bytes:&[u8])->Result<String,String>{
    Ok(crate::native_prefix_auth_plan::role0_sha256(bytes)?.iter().map(|v|format!("{v:02x}")).collect())
}
fn triple_hash(vals:&[[Fr;3]])->Result<String,String>{
    let mut bytes=Vec::with_capacity(96*vals.len());
    for values in vals{for value in values{value.serialize_compressed(&mut bytes).map_err(|e|e.to_string())?;}}
    sha(&bytes)
}
fn census(shape:&H21CandidateShape,mut visit:&Visit<'_>,left:bool,start:usize,n:usize)->Result<Vec<usize>,String>{
    (start..start+n).map(|owner|walk_edge_endpoint(&mut visit,left,owner,WIDTH,OWNERS,
        shape.base_row_bits, &shape.member_bits,None,&mut |_|Ok(()))).collect()
}

/// Use the original complete endpoint emitter and the serial arithmetic, including the literal zero rows.
fn reference(shape:&H21CandidateShape,load:&Load<'_>,mut visit:&Visit<'_>,pass:sb::Pass<'_>)
    ->Result<Vec<[Fr;3]>,String>{
    let mut input=h21_role_input(shape,load)?;
    let weight=|edge:&EdgeTerm|global_edge_row(edge.source_slot,edge.family_row,21,shape.base_row_bits,
        shape.family_bits,&shape.member_bits).map(|row|pass.rows.at(row));
    let mut outputs=Vec::with_capacity(pass.counts.len());
    for (i,&count) in pass.counts.iter().enumerate(){
        let owner=pass.start+i;
        let state=match pass.side {
            Side::U=>edge_replay_u(&mut visit,&mut input,owner,WIDTH,OWNERS,shape.base_row_bits,
                &shape.member_bits,count,&weight,pass.prefix,Some(pass.projection))?,
            Side::V{local,owners,value,..}=>edge_replay_v_with_zero(&mut visit,&mut input,owner,WIDTH,OWNERS,
                shape.base_row_bits,&shape.member_bits,count,&weight,owners,local,value,pass.prefix,Some(pass.projection),None)?,
        };
        let values=if pass.prefix.len()==20{
            let (a,b)=state.banks.terminal();[a,b,state.x[0]]
        }else{
            state.banks.message(&state.x).try_into().map_err(|_|"reference quadratic dimension")?
        };
        outputs.push(values);
    }
    Ok(outputs)
}

struct Points {
    u:Vec<Fr>,v:Vec<Fr>,local:Vec<Fr>,owners:Vec<Fr>,left_value:Fr,rows:EqWeightLookup,
}
impl Points {
    fn new(r:&[Fr])->Self{
        let mut t=Transcript::new(b"nipopow/H21/structural-owner-cost/nonproduction-points/v1");
        for z in r{t.append_scalar(b"actual-output-coordinate",z);}
        let u=(0..41).map(|_|t.challenge_scalar(b"u")).collect::<Vec<_>>();
        let v=(0..20).map(|_|t.challenge_scalar(b"v")).collect();
        Self{local:gkr::eq_weights(&u[..20]),owners:gkr::eq_weights(&u[20..]),u,v,
            left_value:t.challenge_scalar(b"left-value"),rows:EqWeightLookup::new(r)}
    }
    fn side(&self,left:bool)->Side<'_>{
        if left{Side::U}else{Side::V{local:&self.local,owners:&self.owners,value:self.left_value,zero:None}}
    }
    fn prefix(&self,left:bool,k:usize)->&[Fr]{if left{&self.u[..k]}else{&self.v[..k]}}
}

fn compare_case(config:&sb::Config<'_,'_>,prepared:&mut sb::Prepared<'_,'_>,points:&Points,
    literal:&Visit<'_>,left:bool,k:usize,start:usize,counts:&[usize],full_counts:&[usize])->Result<serde_json::Value,String>{
    let prefix=points.prefix(left,k);
    let projection=EdgeFullStats::default().plan(WIDTH,prefix,true)?;
    let base=|c|sb::Pass{side:points.side(left),start,counts:c,prefix,projection:&projection,rows:&points.rows};
    let clock=Instant::now();
    let expected=reference(config.shape,config.load,literal,base(full_counts))?;
    let reference_ns=clock.elapsed().as_nanos() as u64;
    let mut got=Vec::with_capacity(counts.len());
    let mut stats=EdgeFullStats::default();
    let clock=Instant::now();
    prepared.run(base(counts),&mut stats,&mut |owner,values|{
        if owner!=start+got.len(){return Err("structural owner order".into());}
        got.push(values);Ok(())
    })?;
    let candidate_ns=clock.elapsed().as_nanos() as u64;
    if got.len()!=counts.len() || expected!=got{
        return Err(format!("role {} owner message differs at {start}, left={left}, k={k}",config.shape.role.index()));
    }
    Ok(serde_json::json!({"axis":if left{"U"}else{"V"},"k":k,"start":start,"owners":counts.len(),
        "coefficients_sha256":triple_hash(&got)?,"reference_ns":reference_ns,
        "candidate_ns":candidate_ns,"physical_term_callbacks":stats.term_callbacks,
        "reference_terms":full_counts.iter().sum::<usize>()}))
}

fn scoped_hot(shape:&H21CandidateShape,daa:&DaaHistoryRoster<'_>,load:&Load<'_>,physical:&Visit<'_>,
    points:&Points,r:&[Fr],left:bool,owner:usize)->Result<serde_json::Value,String>{
    const STOP:&str="end of bounded structural test occurrences";
    let mut selected=Vec::new();
    let stop=physical(left,owner,&mut |e|{
        selected.push(e);
        if selected.len()==8{Err(STOP.into())}else{Ok(())}
    });
    if !matches!(stop,Err(ref e) if e==STOP) || selected.len()!=8{
        return Err("bounded exceptional endpoint did not reach requested sample".into());
    }
    let bounded=|side,id,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{
        if side!=left || id!=owner{return Err("wrong scoped hotspot".into());}
        for e in &selected{sink(e.clone())?;}Ok(())
    };
    let is_daa=shape.role==H21CandidateRole::HeightDaa;
    let literal=|side,id,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{
        bounded(side,id,sink)?;
        if is_daa{
            daa.visit_h21_zero_lane_owner(id,|mut t|{
                t.row=t.row.checked_add(1usize<<40).ok_or("DAA test ROW")?;
                let (source_slot,family_row)=shape.edge_metadata(t.row)?;
                sink(EdgeTerm{source_slot,family_row,term:t})
            })?;
        }
        Ok(())
    };
    let config=sb::Config {shape,daa:is_daa.then_some(daa),load,visit:&bounded,workers:4,retain_hot:true};
    let mut prepared=config.prepare(r)?;
    let counts=census(shape,&bounded,left,owner,1)?;
    let literal_counts=census(shape,&literal,left,owner,1)?;
    let mut checks=Vec::new();
    for k in 0..=20 {
        // Every intervening challenge reaches the retained state in production order.
        let check=compare_case(&config,&mut prepared,points,&literal,left,k,owner,&counts,&literal_counts)?;
        if k>0 && check["physical_term_callbacks"].as_u64()!=Some(0){
            return Err("exceptional folded state repeated a physical endpoint scan".into());
        }
        checks.push(check);
    }
    Ok(serde_json::json!({"owner":owner,"literal_physical_terms":selected.len(),"prefixes":checks}))
}

pub(crate) fn check(context:&H21StructuralDiagnosticContext<'_>,daa:&DaaHistoryRoster<'_>,
    shape:&H21CandidateShape,r:&[Fr],path:&Path)->Result<serde_json::Value,String>{
    if shape.input_log()!=41 || shape.row_log()!=r.len(){return Err("structural comparison dimensions".into());}
    let points=Points::new(r);
    let full=|left,owner,s:&mut dyn FnMut(EdgeTerm)->Result<(),String>|context.visit_remaining_endpoint(shape,left,owner,s);
    let physical=|left,owner,s:&mut dyn FnMut(EdgeTerm)->Result<(),String>|context.visit_remaining_physical_endpoint(shape,left,owner,s);
    let is_daa=shape.role==H21CandidateRole::HeightDaa;
    let component=if is_daa{crate::daa_history_roster::h21_zero::check_component(daa,r)?}else{0};
    if is_daa && component!=120{return Err("incomplete DAA zero-family differential".into());}
    let mut file=crate::packed::open_untrusted_held_regular(path,1<<38)?;
    let reads=AtomicU64::new(0);
    crate::packed::with_shared_h21_owner_rows(&mut file,|_,result,_|{
        if result.is_ok(){reads.fetch_add(1,Ordering::Relaxed);}
    },|load|{
        if sha(&load(600023)?)?!="07bd32a9a66037bb94837f0cf32be4ad3c4358e6ef725816f819ca2156283c65"{
            return Err("different retained N0 witness".into());
        }
        let config=sb::Config{shape,daa:is_daa.then_some(daa),load,visit:&physical,workers:8,
            retain_hot:matches!(shape.role,H21CandidateRole::Tree|H21CandidateRole::HeightDaa)};
        let started=Instant::now();
        let mut prepared=config.prepare(r)?;
        let prepare_ns=started.elapsed().as_nanos() as u64;
        let mut ordinary=Vec::new();
        for (left,k,start,n) in [(true,0,600016,16),(true,20,1819646,4),
                                (false,3,600016,16),(false,20,1804168,4)] {
            let counts=census(shape,&physical,left,start,n)?;
            let literal=census(shape,&full,left,start,n)?;
            ordinary.push(compare_case(&config,&mut prepared,&points,&full,left,k,start,&counts,&literal)?);
        }
        let mut hotspots=Vec::new();
        if shape.role==H21CandidateRole::Tree{
            hotspots.push(scoped_hot(shape,daa,load,&physical,&points,r,true,0)?);
            hotspots.push(scoped_hot(shape,daa,load,&physical,&points,r,false,OWNERS-1)?);
        }else if is_daa{
            hotspots.push(scoped_hot(shape,daa,load,&physical,&points,r,false,0)?);
        }
        let omitted=if is_daa{daa.h21_zero_logical_total()?}else{0};
        Ok(serde_json::json!({"role":shape.role.index(),"ordinary":ordinary,"scoped_hot":hotspots,
            "ordinary_workers":8,"scoped_workers":4,"shared_prepare_ns":prepare_ns,
            "logical_daa_terms_per_axis":omitted,"daa_linear_checks":component,
            "witness_reads":reads.load(Ordering::Relaxed)}))
    })
}

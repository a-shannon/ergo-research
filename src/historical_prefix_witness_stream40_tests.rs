//! New witness/PCS join; all seven GKR packets are retained and freshly verified.
use super::*;
use crate::historical_prefix_witness::stream40::{self,NativeSummary,WriterStats};
use std::{collections::BTreeMap,io::Write,path::PathBuf};

const JOIN_STAGES:&[(&str,&str)]=&[("admission","begin"),("admission","end"),("writer","begin"),("writer","end"),
    ("commit","begin"),("commit","end"),("roles","begin"),("roles","end"),("opening","begin"),("opening","end"),
    ("producer_drop","end"),("export","begin"),("export","end"),("consumer","begin"),("consumer","end"),
    ("custody","begin"),("custody","end"),("complete","end")];
const DIFF_STAGES:&[(&str,&str)]=&[("admission","begin"),("admission","end"),("n3_reference","begin"),("n3_reference","end"),
    ("n3_writer","begin"),("n3_writer","end"),("n3_readback","begin"),("n3_readback","end"),
    ("n4_reference","begin"),("n4_reference","end"),("n4_writer","begin"),("n4_writer","end"),
    ("n4_readback","begin"),("n4_readback","end"),("complete","end")];
struct Trace {case:&'static str,started:Instant,events:Vec<(&'static str,&'static str,u64)>}
impl Trace {
    fn stages(&self)->&'static [(&'static str,&'static str)] {if self.case=="differential"{DIFF_STAGES}else{JOIN_STAGES}}
    fn stamp(&self)->Result<u64,String>{u64::try_from(self.started.elapsed().as_nanos()).map_err(|_|"stream40 clock".into())}
    fn mark(&mut self,phase:&'static str,event:&'static str)->Result<(),String>{let now=self.stamp()?;self.at(phase,event,now)}
    fn at(&mut self,phase:&'static str,event:&'static str,now:u64)->Result<(),String>{
        if self.stages().get(self.events.len())!=Some(&(phase,event)) {return Err("stream40 marker order".into());}
        let cap=if self.case=="differential"{120}else{180};if now>cap*1_000_000_000 {return Err("stream40 deadline".into());}
        eprintln!("HISTORY_STREAM40_STAGE {} {phase} {event} {now}",self.case);self.events.push((phase,event,now));Ok(())
    }
    fn phases(&self)->BTreeMap<&str,u64>{self.events.windows(2).filter(|w|w[0].0==w[1].0&&w[0].1=="begin"&&w[1].1=="end")
        .map(|w|(w[0].0,w[1].2-w[0].2)).collect()}
}
fn hex(bytes:&[u8])->String {bytes.iter().map(|b|format!("{b:02x}")).collect()}
fn sha(bytes:&[u8])->Result<String,String>{Ok(hex(&crate::native_prefix_auth_plan::role0_sha256(bytes)?))}
fn native(summary:&NativeSummary)->serde_json::Value {serde_json::json!({"headers":summary.headers,
    "root":hex(&summary.root),"total":hex(&summary.total),"tip":hex(&summary.tip),"tip_time":summary.tip_time})}
fn private_path(case:&str)->PathBuf {std::env::temp_dir().join(format!("stream40-{case}-{}.bits",std::process::id()))}
fn packed_bytes(path:&Path)->Result<Vec<u8>,String>{generic37_read(path,524288)}
fn encode_report(value:&serde_json::Value)->Result<Vec<u8>,String>{
    let bytes=serde_json::to_vec(value).map_err(|e|e.to_string())?;
    if bytes.len()>4096{return Err("stream40 report capacity".into());}Ok(bytes)
}
fn record(summary:&NativeSummary,stats:&WriterStats,packed_sha:&str,faults:usize)->serde_json::Value{
    serde_json::json!({"public":native(summary),"packed_sha256":packed_sha,"writer":stats,"guard_faults":faults})
}
fn differential_report(records:Vec<serde_json::Value>)->serde_json::Value{
    serde_json::json!({"schema":"stream40-witness-v1","case":"differential","result":"PASS","records":records,
        "packed_bytes":524288,"owners":4,"gkr_regenerated":0,"gkr_reused":0,"exact_bytes_equal":true,"public_equal":true,
        "bit_faults_rejected":true,"owner_swap_rejected":true,"dense_dropped":true,"full_history":false,"production":false})
}
fn joined_report(case:&str,summary:&NativeSummary,stats:&WriterStats,packed_sha:&str,claims_sha:&str)->serde_json::Value{
    serde_json::json!({"schema":"stream40-witness-v1","case":case,"result":"PASS","public":native(summary),
        "writer":stats,"packed_sha256":packed_sha,"claims_sha256":claims_sha,"gkr_regenerated":0,"gkr_reused":7,
        "files":10,"public_bytes":66133,"opening_bytes":31581,"checks":{"commitment_equal":true,"canonical_opening":true,
            "opening_equal":true,"all_ten_equal":true,"fresh_claims_equal":true,"custody_equal":true,"producer_dropped":true},
        "full_history":false,"production":false})
}
fn serializer_controls()->Result<(),String>{
    let maximum=usize::MAX;
    let stats=WriterStats{sink_calls:maximum,written_bytes:maximum,finish_observed:true,output_capacity_peak:maximum,
        seen_capacity_peak:maximum,mask_capacity:maximum,header_capacity_peak:maximum,local_map_peak:maximum,
        frontier_peak:maximum,native_scans:maximum,scan_leaf_hashes:maximum,scan_node_hashes:maximum};
    let summary=NativeSummary{headers:4,root:[255;32],total:[255;28],tip:[255;32],tip_time:i64::MIN};
    for case in ["differential","n3","n4"]{
        let mut value=if case=="differential"{differential_report(vec![record(&summary,&stats,&"f".repeat(64),9);2])}
            else{joined_report(case,&summary,&stats,&"f".repeat(64),&"f".repeat(64))};
        let stages=if case=="differential"{DIFF_STAGES}else{JOIN_STAGES};
        let phases:BTreeMap<_,_>=stages.iter().filter(|(_,event)|*event=="begin").map(|(stage,_)|(*stage,u64::MAX)).collect();
        value["elapsed_ns"]=serde_json::json!(u64::MAX);value["phase_ns"]=serde_json::json!(phases);
        let bytes=encode_report(&value)?;
        let markers=stages.iter().map(|(p,e)|format!("HISTORY_STREAM40_STAGE {case} {p} {e} {}\n",u64::MAX)).collect::<String>();
        if bytes.len()+markers.len()+2048>65536{return Err("stream40 serializer aggregate".into());}
    }
    if encode_report(&serde_json::json!({"oversized":"x".repeat(4096)})).err().as_deref()!=Some("stream40 report capacity"){
        return Err("stream40 serializer oversize control".into());}Ok(())
}
fn emit(trace:&mut Trace,mut value:serde_json::Value)->Result<(),String>{
    let elapsed=trace.stamp()?;value["elapsed_ns"]=serde_json::json!(elapsed);value["phase_ns"]=serde_json::json!(trace.phases());
    let bytes=encode_report(&value)?;
    trace.at("complete","end",elapsed)?;
    let mut out=std::io::stdout().lock();out.write_all(b"\nHISTORY_STREAM40_REPORT ").map_err(|e|e.to_string())?;
    out.write_all(&bytes).map_err(|e|e.to_string())?;out.write_all(b"\n").map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())
}
fn execute(case:&'static str, operation:impl FnOnce(&mut Trace)->Result<(),String>){
    let mut trace=Trace{case,started:Instant::now(),events:Vec::with_capacity(18)};
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||operation(&mut trace)));
    let error=match result {Ok(Ok(()))=>return,Ok(Err(e))=>e,Err(_)=>"stream40 panic".into()};
    let error:String=error.chars().filter(|c|c.is_ascii_graphic()||*c==' ').take(200).collect();
    let stage=trace.events.last().map(|(p,e,_)|format!("{p}:{e}")).unwrap_or_else(||"entry".into());
    eprintln!("HISTORY_STREAM40_HOLD {case} {stage} {} {error}",trace.started.elapsed().as_nanos());panic!("stream40 HOLD");
}
#[test]
#[ignore="stream40 bounded dense-versus-owner witness differential"]
fn n3_n4_packed_public_differential(){execute("differential",|trace|{
    trace.mark("admission","begin")?;serializer_controls()?;
    let paths=[private_path("diff3"),private_path("diff4")];if paths.iter().any(|p|p.exists()){return Err("stream40 private target exists".into());}
    trace.mark("admission","end")?;let mut records=Vec::with_capacity(2);
    for (n,path) in [3usize,4].into_iter().zip(paths) {
        let phases=if n==3 {["n3_reference","n3_writer","n3_readback"]}else{["n4_reference","n4_writer","n4_readback"]};
        trace.mark(phases[0],"begin")?;
        let headers=witness::retained_headers_n(n)?;
        let (expected,summary)={let dense=witness::build(&headers)?;
            if dense.values.len()!=1<<22 {return Err("stream40 dense width".into());}
            let mut bytes=vec![0u8;524288];for (wire,value) in dense.values.iter().enumerate(){
                if !value.is_zero()&&!value.is_one(){return Err("stream40 dense non-Boolean".into());}
                if value.is_one(){bytes[wire/8]|=1<<(wire%8);}}
            (bytes,NativeSummary{headers:n,root:dense.root,total:dense.total,tip:dense.tip,tip_time:dense.tip_time})};
        let faults=stream40::differential_controls(&headers)?;
        trace.mark(phases[0],"end")?;trace.mark(phases[1],"begin")?;
        let (source,actual,stats)=stream40::write_packed(&headers,&path)?;
        trace.mark(phases[1],"end")?;trace.mark(phases[2],"begin")?;
        let actual_bytes=packed_bytes(&path)?;
        if actual!=summary||actual_bytes!=expected {return Err("stream40 exact packed/public differential".into());}
        for owner in 0..4 {let at=owner*131072;let mut changed=actual_bytes.clone();changed[at]^=1;
            if changed==expected{return Err("stream40 bit omission comparator".into());}}
        let mut swapped=actual_bytes.clone();for i in 0..131072 {swapped.swap(i,131072+i);}
        if swapped==expected{return Err("stream40 owner swap comparator".into());}
        if stats.sink_calls!=4||stats.written_bytes!=524288||!stats.finish_observed||stats.native_scans!=if n==3{2}else{3}{
            return Err("stream40 writer census".into());}
        records.push(record(&actual,&stats,&sha(&actual_bytes)?,faults));
        drop(source);std::fs::remove_file(&path).map_err(|e|e.to_string())?;trace.mark(phases[2],"end")?;
    }
    emit(trace,differential_report(records))
});}

fn join(n:usize){execute(if n==3{"n3"}else{"n4"},|trace|{
    trace.mark("admission","begin")?;serializer_controls()?;
    if !matches!(n,3|4){return Err("stream40 tiny profile".into());}
    let input=std::env::var_os("NIPOPOW_STREAM40_INPUT_DIR").map(PathBuf::from).ok_or("stream40 input directory")?;
    let output=artifact_directory()?;if input==output||!output.is_absolute(){return Err("stream40 output path".into());}
    generic37_metadata(&output,true)?;if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("stream40 nonempty output".into());}
    let pins=generic37_snapshot(&input)?;let (statement,reference)=generic37_load(&input,&pins)?;
    let decoded=crate::historical_prefix_public::decode_tiny_candidate(&statement)?;
    if decoded.headers!=n as u64{return Err("stream40 reference headers".into());}
    let private=private_path(trace.case);if private.exists(){return Err("stream40 private target exists".into());}
    trace.mark("admission","end")?;trace.mark("writer","begin")?;
    let headers=witness::retained_headers_n(n)?;
    let (source,summary,stats)=stream40::write_packed(&headers,&private)?;drop(headers);
    if (summary.root,summary.total,summary.tip,summary.tip_time)!=(decoded.root,decoded.total,decoded.tip,decoded.tip_time){
        return Err("stream40 writer/reference public".into());}
    let packed_sha=sha(&packed_bytes(&private)?)?;trace.mark("writer","end")?;
    let (artifact,claims)={
        trace.mark("commit","begin")?;let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
        let setup=pcs::generate_setup(22)?;if setup.id!=*key.id(){return Err("stream40 setup identity".into());}
        let committed=packed::commit(&source,&setup)?;
        if pcs::encode_commitment(&committed.commitment)?!=reference.commitment{return Err("stream40 mandatory C equality".into());}
        trace.mark("commit","end")?;trace.mark("roles","begin")?;
        let (claims,corpus)={let public=generic37_public(decoded);let consumer=Consumer::new(&public)?;
            let context=ProofContext::historical_tiny(&consumer,&statement)?;
            (context.verify_roles(&reference,&key).map_err(|e|format!("stream40 roles {e:?}"))?,context.corpus_id)};
        trace.mark("roles","end")?;trace.mark("opening","begin")?;
        let common=opening_batch::Statement{log_n:22,setup_id:setup.id,commitment:committed.commitment,corpus_id:Some(corpus),claims:claims.clone()};
        let (proof,_,_)=opening_batch::prove(&source,&committed,&setup,&common)?;
        let bytes=opening_batch::encode_proof(&proof,22)?;
        if bytes!=reference.batch||opening_batch::encode_proof(&opening_batch::decode_proof(&bytes,22)?,22)?!=bytes{
            return Err("stream40 common opening equality/codec".into());}
        trace.mark("opening","end")?;
        (Artifact{commitment:reference.commitment.clone(),roles:reference.roles.clone(),batch:bytes},claims)
    }; // Key/setup/rows/common graph and all writer state are gone.
    drop(source);drop(reference);trace.mark("producer_drop","end")?;
    trace.mark("export","begin")?;
    generic37_metadata(&output,true)?;if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("stream40 output drift".into());}
    for (name,bytes) in [("statement.bin",statement.as_slice()),("commitment.bin",artifact.commitment.as_slice()),("openings.bin",artifact.batch.as_slice())]{
        generic37_loaded_member(&pins,name,bytes)?;write_new(&output.join(name),bytes)?;}
    for role in &artifact.roles{let name=format!("role-{}.gkr",role.role);generic37_loaded_member(&pins,&name,&role.bytes)?;write_new(&output.join(name),&role.bytes)?;}
    if generic37_snapshot(&output)?!=pins{return Err("stream40 all ten export equality".into());}
    drop(artifact);drop(statement);trace.mark("export","end")?;trace.mark("consumer","begin")?;
    let (fresh_statement,fresh)=generic37_load(&output,&pins)?;let actual=verify_historical_tiny_bytes(&fresh_statement,&fresh)?;
    if actual!=claims{return Err("stream40 fresh claims".into());}
    trace.mark("consumer","end")?;trace.mark("custody","begin")?;
    if generic37_snapshot(&input)?!=pins||generic37_snapshot(&output)?!=pins{return Err("stream40 final custody".into());}
    let _=generic37_load(&input,&pins)?;let _=generic37_load(&output,&pins)?;
    std::fs::remove_file(&private).map_err(|e|e.to_string())?;trace.mark("custody","end")?;
    let mut claim_bytes=Vec::with_capacity(7*23*32);use ark_ff::{BigInteger,PrimeField};
    for claim in &actual {for value in claim.point.iter().chain(std::iter::once(&claim.value)){
        let mut bytes=value.into_bigint().to_bytes_le();bytes.resize(32,0);claim_bytes.extend_from_slice(&bytes);}}
    let value=joined_report(trace.case,&summary,&stats,&packed_sha,&sha(&claim_bytes)?);emit(trace,value)
});}
#[test]
#[ignore="stream40 new N3 PACK/common opening; seven retained GKR packets"]
fn n3_pcs_join(){join(3);}
#[test]
#[ignore="stream40 new N4 PACK/common opening; seven retained GKR packets"]
fn n4_pcs_join(){join(4);}

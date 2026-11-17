//! Closed two-route exact-packet experiment; producer defaults/verifier preserved.
use super::*;
use crate::sparse_stream_roster::{GroupedVAdmission,GroupedVStats,BooleanUPreweightStats,BooleanSubset4Stats,TestPhaseMark};
use std::cell::Cell;

const TERMS:usize=396561;
const KERNEL:[&str;13]=["baseline_start","baseline_done","u_cache_streamed","u_anchor_done",
    "u_local_done","u_handoff_done","v_cache_grouped","v_anchor_done","v_local_done",
    "v_handoff_done","terminal_wiring_done","line_start","line_done"];
const STAGES:[(&str,&str);22]=[("admission","begin"),("admission","end"),("writer","begin"),("writer","end"),
    ("commit","begin"),("commit","end"),("context","begin"),("context","end"),("reference","begin"),("reference","end"),
    ("baseline_boolean","begin"),("baseline_boolean","end"),("subset4","begin"),("subset4","end"),
    ("producer_drop","end"),("export","begin"),("export","end"),
    ("consumer","begin"),("consumer","end"),("custody","begin"),("custody","end"),("complete","end")];
// Fixture custody only. Derived from the accepted43 paired manifests and actual
// buffers; never passed as expected public/C to the cryptographic receiver.
const PINS5:[&str;10]=[
    "2be9b99327d50d808638ccbf2832dd87b0a846ad45b305c584aa37c94e1b85ca","4e86ccce00d726da94a6cb753841859f1ae77e4fa987ec5940577c73d7edec1d",
    "c6da9246eaa09107e6240007f388f7bdd69225e6fd2153eb0a12da2897fd4569","4bd92dfa1625f0fbd93eebc29b0a19fb7bbbc6d6cdfad32c9a17cb8c65a854e8",
    "4224d82a033e4f5a0573ac3a825529a536fd1efae7c9bfe5f747b12048d42359","79c4c09e5a06da79713446a34f369c29cb4a9c5f9a5887a897b3cc8d022b6b8c",
    "dd5b81aac1c1e41a5149e6663a5bc60744cb8b544c6e67218f225ff9790ac4de","4edf75af5b50c29ea59559df055fc9c8b07d3f3d664c080661ef25f113b62f89",
    "4a94b2a3f4a1e664bc8560c7dc671345bc7c258d5a169735713501b3346387b1","481955e5678c20dcb8ac3978ed1db5ecd9739f334e961a8c9f5f30810da62e5c"];
const PINS8:[&str;10]=[
    "639859c757704bb6204bf4893504fe3e1a0ba71970cb1889fb28867f4f70ac0c","9a9f4d68716d4a92eaec298cdb6684d3136854094d8fce0fa432210faa7c79b7",
    "b4b27cb486df68c30e32820c7373b8fb953557e7c82cc7957598d0357b52696c","1354ab3635d7764337076acf900f13151db78d24f208589ce5c2bbf2f00e2074",
    "e92f9a2a2f6cfe6fd44f89f046776a67e733a95fe8a9ac30225eacfd8f378583","8ca1083239a3ba8fe9e27ef147fffef7af26999aec7b5ced9b4e7d33a5f3c94b",
    "792666b66326e1e2b0ff8c44022ebb0c7e3b63cec0d18ca8a83685a65be3a1ec","4909df56bc13ca5b45d98275ec401e5e8931aa448596ecc754695224726d9f09",
    "861074ad036fe9d3b28e3321158c4d973c18ca20a66a4f539448e253b81193bb","0da81a4d0e74811ca3c86300bc14d50c22b2c2e460bef9429344fec313c56765"];
fn need(ok:bool,error:&str)->Result<(),String>{if ok{Ok(())}else{Err(error.into())}}
fn nanos(start:Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"boolean_fold45 clock".into())}
fn plus(cell:&Cell<u64>,n:u64)->Result<(),String>{cell.set(cell.get().checked_add(n).ok_or("boolean_fold45 counter overflow")?);Ok(())}
fn pins(n:u64)->Result<Vec<(String,String)>,String>{
    let p=match n{5=>PINS5,8=>PINS8,_=>return Err("boolean_fold45 headers".into())};
    Ok(H41_MEMBERS.iter().zip(p).map(|((name,_),pin)|(name.to_string(),pin.to_string())).collect())
}
fn binding(p:&[(String,String)])->Result<String,String>{h41_pins(p)?;h41_sha(&serde_json::to_vec(p).map_err(|e|e.to_string())?)}
#[derive(Clone)]
struct Admission{n:u64,h:usize,slots:usize,key_log:usize,input:usize,copies:usize,rows:usize,family:usize,
    members:[usize;1],groups:[usize;8],terms:usize,cache:Option<usize>}
impl Admission{
    fn closed(n:u64)->Self{Self{n,h:3,slots:8,key_log:23,input:20,copies:3,rows:19,family:0,
        members:[19],groups:[0;8],terms:TERMS,cache:Some(0)}}
    fn actual(c:&ProofContext<'_>,key:&verifier_key::AdmittedVerifierKey)->Self{
        let g=&c.geometry;Self{n:c.consumer.public.headers,h:g.slot_log,slots:g.slots,key_log:key.log_n(),
            input:g.input_bits[1]-g.slot_log,copies:g.slot_log,rows:g.row_bits[1]-g.slot_log,
            ..Self::closed(c.consumer.public.headers)}}
}
fn admitted<T>(a:&Admission,run:impl FnOnce(&GroupedVAdmission)->Result<T,String>)->Result<T,String>{
    need(matches!(a.n,5|8),"boolean_fold45 headers")?;
    need((a.h,a.slots,a.input,a.copies,a.rows,a.family,a.members)==(3,8,20,3,19,0,[19]),"boolean_fold45 geometry")?;
    need(a.key_log==23,"boolean_fold45 key dimension")?;
    need(a.groups==[0;8],"boolean_fold45 owner groups")?;need(a.terms==TERMS,"boolean_fold45 term admission")?;
    need(a.cache==Some(0),"boolean_fold45 cache budget")?;
    let groups=GroupedVAdmission::try_new(a.copies,&a.groups,&[a.terms])?;run(&groups)
}
// Literal canonical role1 callback semantics from source43 prove_role:1052.
fn owner_terms(context:&ProofContext<'_>,owner:usize,sink:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
    let counts=context.daa.visit_header_terms(owner as u64,|mut term|{
        let ib=owner*layout::WIDTH;let local_rows=Geometry::domain(context.geometry.row_bits[1]-context.geometry.slot_log)?;
        let rb=owner*local_rows;
        need((ib..ib+layout::WIDTH).contains(&term.gate.left)&&(ib..ib+layout::WIDTH).contains(&term.gate.right)
            &&(rb..rb+local_rows).contains(&term.row),"retained header escapes owner")?;
        term.row-=rb;term.gate.left-=ib;term.gate.right-=ib;sink(term)
    })?;
    need(counts.emitted==TERMS&&counts.omitted_mature_a4==0&&counts.omitted_short_a4==0&&counts.omitted_worktree==78194,
        "retained header count drift")
}
struct Produced{proof:GkrProof,claim:InputClaim,counters:[u64;3],continuation:Fr,stats:GroupedVStats,
    boolean:BooleanUPreweightStats,table:Option<BooleanSubset4Stats>,
    loads:u64,fields:u64,load_ns:u64,loader_capacity:usize,visits:u64,callbacks:u64,
    io:packed::PackedIoSnapshot,elapsed:u64,trace:Vec<TestPhaseMark>}
fn trace_valid(trace:&[TestPhaseMark],elapsed:u64)->Result<(),String>{
    need(trace.len()==KERNEL.len(),"boolean_fold45 kernel trace roster")?;
    let mut before=0;for(mark,name)in trace.iter().zip(KERNEL){
        need(mark.name==name&&mark.elapsed_ns>=before&&mark.elapsed_ns<=u128::from(elapsed),"boolean_fold45 kernel trace order/time")?;
        before=mark.elapsed_ns;}Ok(())
}
fn produce(context:&ProofContext<'_>,source:&PackedFile,key:&verifier_key::AdmittedVerifierKey,c:&[u8],subset:bool)->Result<Produced,String>{
    let spec=Admission::actual(context,key);
    admitted(&spec,|admission|{
        need(source.input_len()==1<<23,"boolean_fold45 source extent")?;
        need(context.height_binding==HeightBinding::HistoricalDiagnostic,"boolean_fold45 historical mode")?;
        let mut t=context.transcript(1,key,c);let loads=Cell::new(0);let fields=Cell::new(0);let load_ns=Cell::new(0);
        let capacity=Cell::new(0);let visits=Cell::new(0);let callbacks=Cell::new(0);
        source.reset_io_metrics();let start=Instant::now();crate::sparse_stream_roster::begin_phase_trace_for_test();
        let loader=|owner|{let at=Instant::now();let values=read_slot(source,owner,&context.geometry)?;
                plus(&loads,1)?;plus(&fields,values.len() as u64)?;plus(&load_ns,nanos(at)?)?;
                capacity.set(capacity.get().max(values.capacity()*std::mem::size_of::<Fr>()));Ok(values)};
        let visit=|owner,sink:&mut dyn FnMut(Term)->Result<(),String>|{plus(&visits,1)?;
            owner_terms(context,owner,&mut |term|{sink(term)?;plus(&callbacks,1)})};
        let result=if subset{crate::sparse_stream_roster::prove_historical_role1_subset4_for_test(
            spec.n,20,3,19,0,&[19],Some(0),admission,loader,&mut t,|t|context.bind_role(1,t),visit,
            |r,u,v|context.coefficients(1,r,u,v)).map(|(p,c,g,u,s)|(p,c,g,u,Some(s)))}
        else{crate::sparse_stream_roster::prove_with_boolean_u_grouped_v_for_test(20,3,19,0,&[19],Some(0),admission,
            loader,&mut t,|t|context.bind_role(1,t),visit,|r,u,v|context.coefficients(1,r,u,v))
            .map(|(p,c,g,u)|(p,c,g,u,None))};
        let trace=crate::sparse_stream_roster::take_phase_trace_for_test();let elapsed=nanos(start)?;
        let(proof,claim,stats,boolean,table)=result?;trace_valid(&trace,elapsed)?;
        need(stats.group_count==1&&stats.group_owner_counts.as_slice()==[8]&&stats.group_term_counts.as_slice()==[TERMS]
            &&stats.baseline_term_callbacks==8*TERMS&&stats.template_term_count==TERMS&&stats.bank_term_callbacks==TERMS
            &&stats.handoff_term_callbacks==0&&stats.local_rounds==20&&stats.owner_handoff_count==8,"boolean_fold45 grouped census")?;
        need(loads.get()==200&&visits.get()==8&&callbacks.get()==8*TERMS as u64
            &&boolean.prefix_builds==21&&boolean.shared_term_iterations==21*TERMS&&boolean.owner_term_selections==21*8*TERMS
            &&boolean.boolean_checked_loads==200&&boolean.boolean_checked_fields==200*(1<<20)
            &&boolean.zero_anchor_sweep_skipped&&boolean.preweight_entry_size_bytes==144,
            "boolean_fold45 Boolean census")?;
        if let Some(s)=&table{need(s.builds==20&&s.values_built==8388596&&s.build_additions==7864305
            &&s.apply_calls==168&&s.lookups==44040192&&s.apply_additions==35651592&&s.mask_bits==167772160
            &&s.table_payload_peak_bytes==134217728&&s.extra_reserved_bytes>134217728
            &&s.component_reserved_peak_bytes<=s.preflight_bound_bytes&&s.preflight_bound_bytes<=536870912,
            "boolean_fold45 subset census")?;}
        let io=source.io_metrics_snapshot();need(fields.get()==loads.get().checked_mul(1<<20).ok_or("boolean_fold45 fields overflow")?
            &&io.read_calls==loads.get().checked_mul(16).ok_or("boolean_fold45 IO overflow")?
            &&io.read_bytes==loads.get().checked_mul(131072).ok_or("boolean_fold45 IO overflow")?,"boolean_fold45 loader census")?;
        let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
        let continuation=t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
        Ok(Produced{proof,claim,counters,continuation,stats,boolean,table,loads:loads.get(),fields:fields.get(),load_ns:load_ns.get(),
            loader_capacity:capacity.get(),visits:visits.get(),callbacks:callbacks.get(),io,elapsed,trace})
    })
}
fn packet_equal(bytes:&[u8],expected:&[u8],claim:&Claim,reference:&Claim,counters:[u64;3],other:[u64;3],next:Fr,other_next:Fr)
    ->Result<(),String>{
    need(bytes.len()==5248&&bytes==expected,"boolean_fold45 exact role1 packet")?;
    need(claim.point.len()==23&&claim==reference,"boolean_fold45 role1 derived claim")?;
    need(counters==other,"boolean_fold45 role1 counters")?;need(next==other_next,"boolean_fold45 role1 continuation")
}
fn buffer<'a>(frame:&'a[u8],artifact:&'a Artifact,index:usize)->&'a[u8]{match index{
    0=>frame,1=>&artifact.commitment,2..=8=>&artifact.roles[index-2].bytes,_=>&artifact.batch}}
struct Trace{case:&'static str,start:Instant,events:Vec<(&'static str,&'static str,u64)>}
impl Trace{
    fn mark(&mut self,p:&'static str,e:&'static str)->Result<(),String>{
        self.at(p,e,nanos(self.start)?)
    }
    fn at(&mut self,p:&'static str,e:&'static str,ns:u64)->Result<(),String>{
        need(STAGES.get(self.events.len())==Some(&(p,e)),"boolean_fold45 stage order")?;
        need(ns<=360_000_000_000&&self.events.last().is_none_or(|x|x.2<=ns),"boolean_fold45 deadline/order")?;
        eprintln!("BOOLEAN_FOLD45_STAGE {} {p} {e} {ns}",self.case);self.events.push((p,e,ns));Ok(())
    }
    fn phases(&self)->std::collections::BTreeMap<&str,u64>{self.events.windows(2)
        .filter(|w|w[0].0==w[1].0&&w[0].1=="begin"&&w[1].1=="end").map(|w|(w[0].0,w[1].2-w[0].2)).collect()}
}
fn encode(v:&serde_json::Value)->Result<Vec<u8>,String>{let bytes=serde_json::to_vec(v).map_err(|e|e.to_string())?;
    need(bytes.len()<=16384,"boolean_fold45 report cap")?;Ok(bytes)}
fn route_report(name:&str,p:&Produced,proof_sha:&str)->serde_json::Value{
    let s=&p.stats;let u=&p.boolean;
    let table=p.table.as_ref().map(|x|serde_json::json!({"builds":x.builds,"values_built":x.values_built,
        "build_additions":x.build_additions,"apply_calls":x.apply_calls,"lookups":x.lookups,"apply_additions":x.apply_additions,
        "mask_bits":x.mask_bits,"table_payload_peak_bytes":x.table_payload_peak_bytes,"extra_reserved_bytes":x.extra_reserved_bytes,
        "component_reserved_peak_bytes":x.component_reserved_peak_bytes,"preflight_bound_bytes":x.preflight_bound_bytes,
        "build_ns":x.build_ns,"apply_ns":x.apply_ns}));
    serde_json::json!({"name":name,"proof_sha256":proof_sha,"sender":{"counters":p.counters,"continuation":h41_fr(p.continuation)},
        "probe":{"elapsed_ns":p.elapsed,"load_calls":p.loads,"loaded_fields":p.fields,"load_decode_ns":p.load_ns,
            "loader_capacity_peak":p.loader_capacity,"owner_visits":p.visits,"term_callbacks":p.callbacks,
            "read_calls":p.io.read_calls,"read_bytes":p.io.read_bytes,"read_ns":p.io.read_ns},
        "grouped":{"groups":s.group_count,"owners":s.group_owner_counts,"terms":s.group_term_counts,
            "baseline_callbacks":s.baseline_term_callbacks,"template_terms":s.template_term_count,"template_capacity_bytes":s.template_capacity_bytes,
            "bank_callbacks":s.bank_term_callbacks,"handoff_callbacks":s.handoff_term_callbacks,"state_peak_capacity_bytes":s.grouped_state_peak_capacity_bytes,
            "local_rounds":s.local_rounds,"owner_handoff":s.owner_handoff_count,
            "weight_sums":s.group_weight_sums.iter().map(|v|h41_fr(*v)).collect::<Vec<_>>(),
            "d_contributions":s.group_d_local_contributions.iter().map(|v|h41_fr(*v)).collect::<Vec<_>>(),
            "baseline_ns":s.baseline_elapsed_ns,"bank_build_ns":s.bank_build_elapsed_ns,"local_v_ns":s.local_v_elapsed_ns,"handoff_ns":s.owner_handoff_elapsed_ns},
        "boolean":{"prefix_builds":u.prefix_builds,"shared_term_iterations":u.shared_term_iterations,
            "owner_term_selections":u.owner_term_selections,"checked_loads":u.boolean_checked_loads,"checked_fields":u.boolean_checked_fields,
            "zero_anchor_skipped":u.zero_anchor_sweep_skipped,"entry_bytes":u.preweight_entry_size_bytes,
            "preweight_peak_bytes":u.preweight_peak_capacity_bytes,"u_state_peak_bytes":u.u_state_peak_capacity_bytes,
            "u_preflight_bytes":u.u_preflight_capacity_bound_bytes,"u_phase_peak_bytes":u.u_phase_peak_capacity_bytes,
            "preweight_ns":u.u_prefix_preweight_elapsed_ns,"owner_selection_ns":u.u_owner_selection_elapsed_ns,"x_fold_ns":u.u_x_fold_elapsed_ns},
        "subset4":table,"kernel_trace":p.trace.iter().map(|m|serde_json::json!([m.name,m.elapsed_ns])).collect::<Vec<_>>()})
}
fn report(n:u64,w:&witness::stream40::WriterStats,key:&Historical41KeyPolicy,baseline:&Produced,p:&Produced,
    proof_sha:&str,package_sha:&str)->serde_json::Value{
    let claim=Claim{point:p.claim.point.clone(),value:p.claim.value};
    serde_json::json!({"schema":"boolean-fold45-v1","case":if n==5{"n5"}else{"n8"},"result":"PASS","headers":n,
        "key":{"bytes":25584,"log_n":23,"sha256":h41_hex(&key.sha).to_uppercase(),"id":h41_hex(&key.id),"review":h41_hex(&key.review).to_uppercase()},
        "package_binding":package_sha,"role1_claim":h41_claim(&claim),"writer":w,
        "routes":[route_report("baseline_boolean",baseline,proof_sha),route_report("subset4",p,proof_sha)],
        "files":10,"public_bytes":70389,"gkr_new":2,"gkr_exported":1,"gkr_reused":6,"opening_new":0,"opening_reused":1,
        "checks":{"exact_packet":true,"derived_claim":true,"transcript":true,"actual_c":true,"all_ten_bytes":true,"fresh_consumer":true,"custody":true,"producer_dropped":true},
        "atomic_consumers":1,"boolean_u":true,"full_history":false,"production":false})
}
// Serializer-only maxima, not an admissible telemetry report or a native run.
fn size_controls()->Result<(),String>{
    let m=usize::MAX;let u=u64::MAX;let mut stats=GroupedVStats::default();
    stats.group_count=m;stats.group_owner_counts=vec![m];stats.group_term_counts=vec![m];
    stats.baseline_term_callbacks=m;stats.template_term_count=m;stats.template_capacity_bytes=m;
    stats.bank_term_callbacks=m;stats.handoff_term_callbacks=m;stats.grouped_state_peak_capacity_bytes=m;
    stats.local_rounds=m;stats.owner_handoff_count=m;stats.group_weight_sums=vec![-Fr::one()];stats.group_d_local_contributions=vec![-Fr::one()];
    stats.baseline_elapsed_ns=u;stats.bank_build_elapsed_ns=u;stats.local_v_elapsed_ns=u;stats.owner_handoff_elapsed_ns=u;
    let boolean=BooleanUPreweightStats{prefix_builds:m,shared_term_iterations:m,owner_term_selections:m,
        boolean_checked_loads:m,boolean_checked_fields:m,zero_anchor_sweep_skipped:true,preweight_entry_size_bytes:m,
        preweight_peak_capacity_bytes:m,u_state_peak_capacity_bytes:m,u_preflight_capacity_bound_bytes:m,
        u_prefix_preweight_elapsed_ns:u,u_owner_selection_elapsed_ns:u,u_x_fold_elapsed_ns:u,u_phase_peak_capacity_bytes:[m;6]};
    let table=BooleanSubset4Stats{builds:m,values_built:m,build_additions:m,apply_calls:m,lookups:m,apply_additions:m,mask_bits:m,
        table_payload_peak_bytes:m,extra_reserved_bytes:m,component_reserved_peak_bytes:m,preflight_bound_bytes:m,build_ns:u,apply_ns:u};
    let mut p=Produced{proof:GkrProof{layers:Vec::new()},claim:InputClaim{point:vec![-Fr::one();23],value:-Fr::one()},
        counters:[u;3],continuation:-Fr::one(),stats,loads:u,fields:u,load_ns:u,loader_capacity:m,visits:u,callbacks:u,
        boolean,table:None,
        io:packed::PackedIoSnapshot{read_calls:u,read_bytes:u,read_ns:u128::from(u),..Default::default()},elapsed:u,
        trace:KERNEL.iter().map(|name|TestPhaseMark{name:(*name).into(),elapsed_ns:u128::from(u)}).collect()};
    let writer=witness::stream40::WriterStats{sink_calls:m,written_bytes:m,finish_observed:true,output_capacity_peak:m,seen_capacity_peak:m,
        mask_capacity:m,header_capacity_peak:m,local_map_peak:m,frontier_peak:m,native_scans:m,scan_leaf_hashes:m,scan_node_hashes:m};
    let key=Historical41KeyPolicy::transport(25584,[255;32],[255;32],23,[255;32])?;
    let baseline=route_report("baseline_boolean",&p,&"F".repeat(64));p.table=Some(table);
    let mut value=report(8,&writer,&key,&p,&p,&"F".repeat(64),&"F".repeat(64));
    value["routes"][0]=baseline;
    value["elapsed_ns"]=serde_json::json!(u);
    let phases:std::collections::BTreeMap<_,_>=STAGES.iter().filter(|x|x.1=="begin").map(|x|(x.0,u)).collect();
    value["phase_ns"]=serde_json::json!(phases);let bytes=encode(&value)?;
    // Each real marker has a closed name and at most20 decimal digits.
    let kernel_bound:usize=KERNEL.iter().map(|name|format!("NIPOPOW_ROLE1_PHASE {{\"name\":\"{name}\",\"elapsed_ns\":{u}}}\n").len()).sum();
    let outer_bound:usize=STAGES.iter().map(|(phase,event)|format!("BOOLEAN_FOLD45_STAGE n8 {phase} {event} {u}\n").len()).sum();
    need(bytes.len()+2*kernel_bound+outer_bound+4096+256<=65536,"boolean_fold45 output envelope")
}
fn run(n:u64,t:&mut Trace)->Result<(),String>{
    t.mark("admission","begin")?;admitted(&Admission::closed(n),|_|Ok(()))?;size_controls()?;
    let material=H41Key::load()?;let reference=std::path::PathBuf::from(h41_env("NIPOPOW_BOOLEAN_FOLD45_REFERENCE_DIR",240)?);
    let expected=pins(n)?;need(h41_snapshot(&reference)?==expected,"boolean_fold45 reference pins")?;
    let(frame,mut artifact)=h41_load(&reference,&expected)?;let package_sha=binding(&expected)?;
    let output=artifact_directory()?;need(output.is_absolute(),"boolean_fold45 output directory")?;generic37_metadata(&output,true)?;
    need(output.read_dir().map_err(|e|e.to_string())?.next().is_none(),"boolean_fold45 output not empty")?;
    let private=std::env::temp_dir().join(format!("boolean_fold45-n{n}-{}.bits",std::process::id()));need(!private.exists(),"boolean_fold45 private exists")?;
    t.mark("admission","end")?;t.mark("writer","begin")?;
    let headers=h41_headers(n as usize)?;let(source,summary,writer)=witness::stream40::write_h3_packed(&headers,&private)?;drop(headers);
    let public=Public{headers:n,root:summary.root,total:summary.total,tip:summary.tip,tip_time:summary.tip_time};
    need(historical41_frame(&public)?==frame,"boolean_fold45 reconstructed public")?;
    need(source.input_len()==1<<23&&writer.written_bytes==1048576&&writer.sink_calls==8&&writer.finish_observed,"boolean_fold45 writer extent")?;
    t.mark("writer","end")?;t.mark("commit","begin")?;
    let key=material.policy.admit(&material.key,&material.metadata)?;
    {let setup=pcs::generate_setup(23)?;
        need(setup.id==material.policy.id&&pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier.clone()))?==material.key,
            "boolean_fold45 setup identity")?;
        let committed=packed::commit(&source,&setup)?;need(pcs::encode_commitment(&committed.commitment)?==artifact.commitment,"boolean_fold45 actual C")?;
    } // Setup, verifier clone and committed rows drop before the only producer graph.
    t.mark("commit","end")?;t.mark("context","begin")?;
    let(baseline,produced)={let consumer=historical41_consumer(&public)?;let context=ProofContext::historical_h3(&consumer,&frame)?;
        t.mark("context","end")?;t.mark("reference","begin")?;
        let old=context.verify_role(&artifact.roles[1],&key,&artifact.commitment).map_err(|e|format!("boolean_fold45 reference {e:?}"))?;
        t.mark("reference","end")?;t.mark("baseline_boolean","begin")?;
        let baseline=produce(&context,&source,&key,&artifact.commitment,false)?;
        {let bytes=gkr::encode_proof(&baseline.proof)?;let claim=Claim{point:baseline.claim.point.clone(),value:baseline.claim.value};
            packet_equal(&bytes,&artifact.roles[1].bytes,&claim,&old.claim,baseline.counters,old.counters,baseline.continuation,old.continuation)?;
            let packet=RoleProof{role:1,bytes};let v=context.verify_role(&packet,&key,&artifact.commitment)
                .map_err(|_|"boolean_fold45 baseline role verification")?;
            packet_equal(&packet.bytes,&artifact.roles[1].bytes,&v.claim,&claim,v.counters,baseline.counters,v.continuation,baseline.continuation)?;
            need(source.evaluate(&claim.point)?==claim.value,"boolean_fold45 baseline held MLE")?;}
        t.mark("baseline_boolean","end")?;t.mark("subset4","begin")?;
        let produced=produce(&context,&source,&key,&artifact.commitment,true)?;
        let bytes=gkr::encode_proof(&produced.proof)?;let claim=Claim{point:produced.claim.point.clone(),value:produced.claim.value};
        packet_equal(&bytes,&artifact.roles[1].bytes,&claim,&old.claim,produced.counters,old.counters,produced.continuation,old.continuation)?;
        let packet=RoleProof{role:1,bytes};let verified=context.verify_role(&packet,&key,&artifact.commitment)
            .map_err(|e|format!("boolean_fold45 new role {e:?}"))?;
        packet_equal(&packet.bytes,&artifact.roles[1].bytes,&verified.claim,&claim,verified.counters,produced.counters,verified.continuation,produced.continuation)?;
        need(source.evaluate(&claim.point)?==claim.value,"boolean_fold45 held MLE")?;
        artifact.roles[1]=packet;t.mark("subset4","end")?;(baseline,produced)
    };drop(source);drop(key);t.mark("producer_drop","end")?;
    let proof_sha=h41_sha(&artifact.roles[1].bytes)?;t.mark("export","begin")?;generic37_metadata(&output,true)?;
    need(output.read_dir().map_err(|e|e.to_string())?.next().is_none(),"boolean_fold45 output drift")?;
    for(i,(name,_))in H41_MEMBERS.iter().enumerate(){h41_loaded(&expected,name,buffer(&frame,&artifact,i))?;
        write_new(&output.join(name),buffer(&frame,&artifact,i))?;}
    need(h41_snapshot(&output)?==expected,"boolean_fold45 export pins")?;
    {let(f,a)=h41_load(&output,&expected)?;for i in 0..10{need(buffer(&f,&a,i)==buffer(&frame,&artifact,i),"boolean_fold45 exact ten buffers")?;}}
    drop(artifact);drop(frame);t.mark("export","end")?;t.mark("consumer","begin")?;
    {let(f,a)=h41_load(&output,&expected)?;let claims=verify_historical_h3_bytes(&f,&a,&material.key,&material.metadata,&material.policy)?;
        need(claims[1]==Claim{point:produced.claim.point.clone(),value:produced.claim.value},"boolean_fold45 fresh role1 claim")?;}
    t.mark("consumer","end")?;t.mark("custody","begin")?;
    need(h41_snapshot(&reference)?==expected&&h41_snapshot(&output)?==expected,"boolean_fold45 final pins")?;
    let _=h41_load(&reference,&expected)?;let _=h41_load(&output,&expected)?;material.custody()?;
    std::fs::remove_file(&private).map_err(|e|e.to_string())?;t.mark("custody","end")?;
    let mut value=report(n,&writer,&material.policy,&baseline,&produced,&proof_sha,&package_sha);
    let elapsed=nanos(t.start)?;value["phase_ns"]=serde_json::json!(t.phases());value["elapsed_ns"]=serde_json::json!(elapsed);
    let bytes=encode(&value)?;t.at("complete","end",elapsed)?;
    let mut stdout=std::io::stdout().lock();stdout.write_all(b"\nBOOLEAN_FOLD45_REPORT ").map_err(|e|e.to_string())?;
    stdout.write_all(&bytes).map_err(|e|e.to_string())?;stdout.write_all(b"\n").map_err(|e|e.to_string())?;stdout.flush().map_err(|e|e.to_string())
}
fn execute(n:u64){let mut t=Trace{case:if n==5{"n5"}else{"n8"},start:Instant::now(),events:Vec::with_capacity(22)};
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(n,&mut t)));
    let error=match result{Ok(Ok(()))=>return,Ok(Err(e))=>e,Err(_)=>"boolean_fold45 panic".into()};
    let reason:String=error.chars().filter(|v|v.is_ascii_graphic()||*v==' ').take(200).collect();
    let phase=t.events.last().map(|(p,e,_)|format!("{p}:{e}")).unwrap_or_else(||"entry".into());
    eprintln!("BOOLEAN_FOLD45_HOLD {} {phase} {} {reason}",t.case,t.start.elapsed().as_nanos());panic!("boolean_fold45 HOLD");
}

#[test]
fn ordinary_admission(){
    let groups=GroupedVAdmission::try_new(3,&[0;8],&[TERMS]).unwrap();
    let wrong_count=GroupedVAdmission::try_new(3,&[0;8],&[TERMS-1]).unwrap();
    let wrong_group=GroupedVAdmission::try_new(3,&[0,0,0,0,0,0,0,1],&[TERMS,TERMS]).unwrap();
    for fault in 0..11{let active=Cell::new(false);let mut t=Transcript::new(b"boolean-fold45-hook-guard");
        let(n,i,c,r,f,m,cache)=match fault{0=>(4,20,3,19,0,[19],Some(0)),1=>(5,19,3,19,0,[19],Some(0)),
            2=>(5,20,2,19,0,[19],Some(0)),3=>(5,20,3,18,0,[19],Some(0)),4=>(5,20,3,19,1,[19],Some(0)),
            5=>(5,20,3,19,0,[18],Some(0)),6=>(5,20,3,19,0,[19],None),7=>(5,20,3,19,0,[19],Some(1)),
            _=>(5,20,3,19,0,[19],Some(0))};
        if fault==8{t.try_challenge_scalar(b"already").unwrap();}
        let actual_groups=if fault==9{&wrong_count}else if fault==10{&wrong_group}else{&groups};
        let before=t.challenges();let result=crate::sparse_stream_roster::prove_historical_role1_subset4_for_test(
            n,i,c,r,f,&m,cache,actual_groups,|_|{active.set(true);Err("must not load".into())},&mut t,|_|active.set(true),
            |_,_|{active.set(true);Ok(())},|_,_,_|{active.set(true);Ok([Fr::zero();4])});
        assert_eq!(result.err().as_deref(),Some(if fault==8{"subset4 transcript already challenged"}else{"subset4 closed historical admission"}));
        assert!(!active.get());assert_eq!(t.challenges(),before);}
    for n in [5u64,8]{let good=Admission::closed(n);let activity=Cell::new(0);
        admitted(&good,|_|{activity.set(activity.get()+1);Ok(())}).unwrap();assert_eq!(activity.get(),1);
        for fault in 0..13{let mut bad=good.clone();let expected=match fault{
            0=>{bad.n=4;"boolean_fold45 headers"},1=>{bad.h=2;"boolean_fold45 geometry"},2=>{bad.slots=4;"boolean_fold45 geometry"},
            3=>{bad.input=19;"boolean_fold45 geometry"},4=>{bad.copies=2;"boolean_fold45 geometry"},5=>{bad.rows=18;"boolean_fold45 geometry"},
            6=>{bad.family=1;"boolean_fold45 geometry"},7=>{bad.members=[18];"boolean_fold45 geometry"},
            8=>{bad.key_log=22;"boolean_fold45 key dimension"},9=>{bad.groups[7]=1;"boolean_fold45 owner groups"},
            10=>{bad.terms-=1;"boolean_fold45 term admission"},11=>{bad.cache=None;"boolean_fold45 cache budget"},
            _=>{bad.cache=Some(1);"boolean_fold45 cache budget"}};
            activity.set(0);let result=admitted(&bad,|_|{activity.set(1);Ok(())});
            assert_eq!(result.err().as_deref(),Some(expected));assert_eq!(activity.get(),0);}
        let expected=pins(n).unwrap();h41_pins(&expected).unwrap();assert_ne!(binding(&expected).unwrap(),binding(&pins(if n==5{8}else{5}).unwrap()).unwrap());
    }
    let bytes=vec![7;5248];let claim=Claim{point:vec![Fr::one();23],value:Fr::one()};let counts=[69,70,71];
    packet_equal(&bytes,&bytes,&claim,&claim,counts,counts,Fr::one(),Fr::one()).unwrap();
    for extent in [5247,5249]{let mut b=bytes.clone();b.resize(extent,0);
        assert_eq!(packet_equal(&b,&bytes,&claim,&claim,counts,counts,Fr::one(),Fr::one()).err().as_deref(),Some("boolean_fold45 exact role1 packet"));}
    for fault in 0..30{let mut b=bytes.clone();let mut c=claim.clone();let mut counters=counts;let mut next=Fr::one();
        let expected=match fault{0=>{b[0]^=1;"boolean_fold45 exact role1 packet"},1..=23=>{c.point[fault-1]+=Fr::one();"boolean_fold45 role1 derived claim"},
            24=>{c.value+=Fr::one();"boolean_fold45 role1 derived claim"},25=>{counters[0]+=1;"boolean_fold45 role1 counters"},
            26=>{next+=Fr::one();"boolean_fold45 role1 continuation"},27=>{c.point.pop();"boolean_fold45 role1 derived claim"},
            28=>{counters[1]+=1;"boolean_fold45 role1 counters"},_=>{counters[2]+=1;"boolean_fold45 role1 counters"}};
        assert_eq!(packet_equal(&b,&bytes,&c,&claim,counters,counts,next,Fr::one()).err().as_deref(),Some(expected));}
    let trace:Vec<_>=KERNEL.iter().enumerate().map(|(i,name)|TestPhaseMark{name:(*name).into(),elapsed_ns:i as u128}).collect();
    trace_valid(&trace,12).unwrap();assert_eq!(trace_valid(&trace[..12],12).err().as_deref(),Some("boolean_fold45 kernel trace roster"));
    let mut bad=trace.clone();bad[5].name="wrong".into();assert_eq!(trace_valid(&bad,12).err().as_deref(),Some("boolean_fold45 kernel trace order/time"));
    assert_eq!(trace_valid(&trace,11).err().as_deref(),Some("boolean_fold45 kernel trace order/time"));
    assert_eq!(encode(&serde_json::json!({"large":"x".repeat(16384)})).err().as_deref(),Some("boolean_fold45 report cap"));
    size_controls().unwrap();
}
#[test]
#[ignore="closed N5 Boolean baseline then subset4; admitted43 key/package required"]
fn n5_boolean_and_subset4(){execute(5);}
#[test]
#[ignore="closed N8 Boolean baseline then subset4; independent N5 acceptance required"]
fn n8_boolean_and_subset4(){execute(8);}


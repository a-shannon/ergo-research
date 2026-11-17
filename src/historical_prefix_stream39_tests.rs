//! Complete historical tiny streaming joins; retained hashes are transport only.
use super::*;
use ark_ff::{BigInteger, PrimeField};
use std::{collections::BTreeMap, path::PathBuf};

const PACKET_STAGES: &[(&str,&str)] = &[("admission","begin"),("admission","end"),
    ("witness","begin"),("witness","end"),("reference","begin"),("reference","end"),
    ("role2","begin"),("role2","end"),("role5","begin"),("role5","end"),("role6","begin"),("role6","end"),
    ("producer_drop","end"),("export","begin"),("export","end"),("consumer","begin"),("consumer","end"),
    ("custody","begin"),("custody","end"),("complete","end")];
const FULL_STAGES: &[(&str,&str)] = &[("admission","begin"),("admission","end"),
    ("witness","begin"),("witness","end"),("setup_commit","begin"),("setup_commit","end"),
    ("reference","begin"),("reference","end"),
    ("role0","begin"),("role0","end"),("role1","begin"),("role1","end"),("role2","begin"),("role2","end"),
    ("role3","begin"),("role3","end"),("role4","begin"),("role4","end"),("role5","begin"),("role5","end"),
    ("role6","begin"),("role6","end"),("graph_drop","end"),("opening","begin"),("opening","end"),
    ("producer_drop","end"),("export","begin"),("export","end"),("consumer","begin"),("consumer","end"),
    ("custody","begin"),("custody","end"),("complete","end")];
const ROLE_STAGES: [&str;7]=["role0","role1","role2","role3","role4","role5","role6"];
const REPORT_CAP: usize=16384;
const RECEIPT_CAP: usize=65536;
const RETAINED_BUFFERS: usize=4*1024*1024;

struct Trace {
    started: Instant, full: bool, position: usize, events: Vec<(&'static str,&'static str,u64)>,
    phase: &'static str, role: usize, completed_roles: usize,
}
impl Trace {
    fn new(full:bool)->Self { Self {started:Instant::now(),full,position:0,events:Vec::with_capacity(33),
        phase:"admission",role:7,completed_roles:0} }
    fn limit(&self)->u64 {if self.full {360_000_000_000}else{180_000_000_000}}
    fn stages(&self)->&'static [(&'static str,&'static str)] {if self.full {FULL_STAGES}else{PACKET_STAGES}}
    fn elapsed(&self)->Result<u64,String>{u64::try_from(self.started.elapsed().as_nanos()).map_err(|_|"stream39 clock".into())}
    fn mark_at(&mut self,phase:&'static str,event:&'static str,ns:u64)->Result<(),String>{
        if self.stages().get(self.position)!=Some(&(phase,event)) {return Err("stream39 marker order".into());}
        if ns>self.limit() || self.events.last().is_some_and(|(_,_,previous)|*previous>ns) {return Err("stream39 deadline or clock".into());}
        self.phase=phase;
        eprintln!("HISTORY_STREAM39_STAGE {} {phase} {event} {ns}",if self.full {"complete"}else{"packet"});
        self.events.push((phase,event,ns));self.position+=1;Ok(())
    }
    fn mark(&mut self,phase:&'static str,event:&'static str)->Result<(),String>{let ns=self.elapsed()?;self.mark_at(phase,event,ns)}
    fn phase_ns(&self)->BTreeMap<&'static str,u64>{
        let mut result=BTreeMap::new();
        for pair in self.events.windows(2) {if pair[0].0==pair[1].0 && pair[0].1=="begin" && pair[1].1=="end" {
            result.insert(pair[0].0,pair[1].2-pair[0].2);
        }}result
    }
}

fn scalar(value:Fr)->String {
    let mut bytes=value.into_bigint().to_bytes_le();bytes.resize(32,0);
    bytes.iter().map(|byte|format!("{byte:02x}")).collect()
}
fn claim_json(claim:&Claim)->serde_json::Value {
    serde_json::json!({"point":claim.point.iter().map(|v|scalar(*v)).collect::<Vec<_>>(),"value":scalar(claim.value)})
}
fn digest(bytes:&[u8])->Result<String,String>{
    Ok(crate::native_prefix_auth_plan::role0_sha256(bytes)?.iter().map(|byte|format!("{byte:02x}")).collect())
}

// Used by both actual production and isolated equality-channel controls.
fn equal_packet(bytes:&[u8],claim:&Claim,sender:Option<([u64;3],Fr)>,
    reference_bytes:&[u8],reference:&VerifiedRole)->Result<(),String> {
    if bytes!=reference_bytes {return Err("stream39 proof equality".into());}
    if claim!=&reference.claim {return Err("stream39 claim equality".into());}
    if matches!(reference.role,2|4|5|6) && sender.is_none() {return Err("stream39 sender missing".into());}
    if let Some((counters,continuation))=sender {
        if counters!=reference.counters {return Err("stream39 counter equality".into());}
        if continuation!=reference.continuation {return Err("stream39 continuation equality".into());}
    }
    Ok(())
}

fn produced_observation(role:usize,produced:&History39Produced,bytes:&[u8],
    claim:&Claim,reference:&VerifiedRole,full:bool)->Result<serde_json::Value,String>{
    let io_ns=u64::try_from(produced.io.read_ns).map_err(|_|"stream39 IO clock")?;
    if produced.edge.as_ref().is_some_and(|m|m.io.read_ns>u64::MAX as u128) {return Err("stream39 IO clock".into());}
    let stream=produced.edge.as_ref().map(|m|serde_json::json!({
        "endpoint_calls":m.endpoint_calls,"callbacks":m.callbacks,"left_terms":m.left_terms,"right_terms":m.right_terms,
        "load_calls":m.load_calls,"loaded_fields":m.loaded_fields,"load_decode_ns":m.load_decode_ns,
        "loader_capacity_peak":m.loader_capacity_peak,"read_calls":m.io.read_calls,"read_bytes":m.io.read_bytes,"read_ns":m.io.read_ns as u64}));
    let linear=produced.linear.as_ref().map(|m|serde_json::json!({"phase_ns":m.phase_ns,"read_calls":m.read_calls,
        "reconstructed_fields":m.reconstructed_fields,"peak_bound":m.combined_bound_peak_bytes,
        "preflight_bound":m.preflight_bound_bytes,"retained":m.retained_capacity_bytes,"limit":m.scoped_limit_bytes,
        "load_calls":produced.load_calls,"loaded_fields":produced.loaded_fields,"load_decode_ns":produced.load_decode_ns,
        "loader_capacity_peak":produced.loader_capacity_peak,"read_bytes":produced.io.read_bytes,"read_ns":io_ns}));
    let sender=produced.sender.map(|(counters,continuation)|serde_json::json!({"counters":counters,"continuation":scalar(continuation)}));
    let mut value=serde_json::json!({"role":role,"terms":produced.terms,"proof_bytes":bytes.len(),"proof_sha256":digest(bytes)?,
        "producer_ns":produced.elapsed_ns,"sender":sender,"stream":stream,"linear":linear});
    if !full {
        value["reference_claim"]=claim_json(&reference.claim);value["producer_claim"]=claim_json(claim);
        value["reference_counters"]=serde_json::json!(reference.counters);
        value["reference_continuation"]=serde_json::json!(scalar(reference.continuation));
    }
    Ok(value)
}

fn report(full:bool,headers:u64,observations:Vec<serde_json::Value>,claims:&[Claim;7],
    phases:BTreeMap<&str,u64>,elapsed:u64)->serde_json::Value {
    let hashes=observations.iter().map(|v|v["proof_sha256"].clone()).collect::<Vec<_>>();
    let observations=if full {observations.into_iter().filter_map(|mut v| {
        if !matches!(v["role"].as_u64(),Some(2|4|5|6)) {return None;}
        // Full legacy producers expose no sender transcript. Their actual
        // phase times and packet hashes are reported without invented metrics.
        v.as_object_mut().unwrap().remove("proof_sha256");Some(v)
    }).collect::<Vec<_>>()}else{observations};
    let mut value=serde_json::json!({"schema":if full {"stream39-full-v1"}else{"stream39-packet-v1"},"result":"PASS",
        "mode":"historical_tiny_testonly","headers":headers,"roles":7,"files":10,"public_bytes":66133,
        "statement_bytes":568,"gkr_bytes":33600,"commitment_bytes":384,"opening_bytes":31581,
        "proofs_regenerated":if full {7}else{3},"reference_roles_verified":7,"observations":observations,
        "checks":{"proof_bytes_equal":true,"claims_equal":true,"sender_counters_equal":true,"sender_continuations_equal":true,
            "held_mle_equal":true,"canonical_codec":true,"same_commitment_as_retained":true,"all_ten_bytes_equal":true,
            "atomic_seven_claims_equal":true,"producer_dropped":true,"corrupt_gkr_sumcheck":true,"custody_equal":true},
        "internal":{"observed":false,"cache_peak":null,"input_vector_clones":null},
        "ledger":{"retained_buffers":RETAINED_BUFFERS,"replay_payload_bound":301989888,"stack_min":67108864,
            "worker_stack_reserve":268435456,"whole_process_bound":null},
        "phase_ns":phases,"elapsed_ns":elapsed,"sender_roles":if full {vec![2,4,5,6]}else{vec![2,5,6]},
        "legacy_sender_observed":false,"expected_public_in_receiver":false,"expected_c_in_receiver":false,
        "witness_in_receiver":false,"setup_in_receiver":false,"full_history":false,"production":false});
    if full {value["claims"]=serde_json::json!(claims.iter().map(claim_json).collect::<Vec<_>>());
        value["proof_sha256"]=serde_json::json!(hashes);}
    value
}
fn encode_report(value:&serde_json::Value)->Result<Vec<u8>,String>{
    let bytes=serde_json::to_vec(value).map_err(|e|e.to_string())?;
    if bytes.len()>REPORT_CAP {return Err("stream39 report capacity".into());}Ok(bytes)
}

fn witness_bits(headers:u64,decoded:&crate::historical_prefix_public::NativePublic)->Result<Vec<u8>,String>{
    let w=witness::build(&witness::retained_headers_n(headers as usize)?)?;
    if (w.root,w.total,w.tip,w.tip_time)!=(decoded.root,decoded.total,decoded.tip,decoded.tip_time) {
        return Err("stream39 fixture agreement".into());
    }
    if w.values.len()!=1<<22 {return Err("stream39 witness width".into());}
    let mut bits=vec![0u8;524288];
    for (index,value) in w.values.iter().enumerate(){
        if !value.is_zero()&&!value.is_one(){return Err("stream39 Boolean witness".into());}
        if value.is_one(){bits[index/8]|=1<<(index%8);}
    }
    Ok(bits) // Dense witness is dropped before the caller creates its graph.
}

fn export(output:&Path,statement:&[u8],artifact:&Artifact,pins:&[(String,String)])->Result<(),String>{
    generic37_metadata(output,true)?;
    if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("stream39 output admission drift".into());}
    generic37_loaded_member(pins,"statement.bin",statement)?;
    generic37_loaded_member(pins,"commitment.bin",&artifact.commitment)?;
    for packet in &artifact.roles {generic37_loaded_member(pins,&format!("role-{}.gkr",packet.role),&packet.bytes)?;}
    generic37_loaded_member(pins,"openings.bin",&artifact.batch)?;
    write_new(&output.join("statement.bin"),statement)?;write_new(&output.join("commitment.bin"),&artifact.commitment)?;
    for packet in &artifact.roles {write_new(&output.join(format!("role-{}.gkr",packet.role)),&packet.bytes)?;}
    write_new(&output.join("openings.bin"),&artifact.batch)?;
    if generic37_snapshot(output)?!=pins {return Err("stream39 exported pins".into());}Ok(())
}

fn produce_one(context:&ProofContext<'_>,source:&PackedFile,key:&verifier_key::AdmittedVerifierKey,
    reference:&Artifact,role:usize,full:bool)->Result<(RoleProof,Claim,serde_json::Value),String>{
    let verified=context.verify_role(&reference.roles[role],key,&reference.commitment).map_err(|e|e.message)?;
    let produced=prove_historical_stream39(context,source,key,&reference.commitment,role,RETAINED_BUFFERS)?;
    let bytes=gkr::encode_proof(&produced.proof)?;
    if bytes.len()!=context.geometry.proof_bytes(role)?
        || gkr::encode_proof(&gkr::decode_dimensions(&[context.geometry.input_bits[role]],&bytes)?)?!=bytes {
        return Err("stream39 canonical proof".into());
    }
    let point=if role==3 {context.point_role.project(&produced.claim.point)?}else{produced.claim.point.clone()};
    let claim=Claim{point,value:produced.claim.value};
    equal_packet(&bytes,&claim,produced.sender,&reference.roles[role].bytes,&verified)?;
    if source.evaluate(&claim.point)?!=claim.value {return Err("stream39 held MLE".into());}
    let mut corrupt=produced.proof.clone();corrupt.layers[0].rounds[0][0]+=Fr::one();
    let bad=RoleProof{role,bytes:gkr::encode_proof(&corrupt)?};
    let failure=context.verify_role(&bad,key,&reference.commitment).err().ok_or("stream39 corrupt proof accepted")?;
    if failure.stage!=RoleStage::Gkr || failure.message!=GkrError::SumcheckIdentity.to_string()
        || !failure.observation.canonical_decode || !failure.observation.verifier_entered {return Err("stream39 corrupt proof attribution".into());}
    let observation=produced_observation(role,&produced,&bytes,&claim,&verified,full)?;
    Ok((RoleProof{role,bytes},claim,observation))
}

fn join(headers:u64,full:bool){
    let mut trace=Trace::new(full);
    let operation=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||->Result<(),String>{
        trace.mark("admission","begin")?;
        if !matches!(headers,3|4) || full&&headers!=4 {return Err("stream39 lane profile".into());}
        let input=std::env::var_os("NIPOPOW_STREAM39_INPUT_DIR").map(PathBuf::from).ok_or("stream39 input directory")?;
        let output=artifact_directory()?;
        if !output.is_absolute() || output==input {return Err("stream39 fresh output".into());}
        generic37_metadata(&output,true)?;
        if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("stream39 nonempty output".into());}
        let pins=generic37_snapshot(&input)?;let (statement,reference)=generic37_load(&input,&pins)?;
        let decoded=crate::historical_prefix_public::decode_tiny_candidate(&statement)?;
        if decoded.headers!=headers {return Err("stream39 retained profile".into());}
        let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
        if pcs::encode_commitment(&pcs::decode_commitment(&reference.commitment)?)?!=reference.commitment {return Err("stream39 canonical C".into());}
        let private=std::env::temp_dir().join(format!("stream39-{}-n{headers}-{}.bits",if full {"full"}else{"packet"},std::process::id()));
        if private.exists(){return Err("stream39 private path exists".into());}trace.mark("admission","end")?;
        trace.mark("witness","begin")?;let bits=witness_bits(headers,&decoded)?;trace.mark("witness","end")?;
        let (artifact,claims,observations)={
            if full {trace.mark("setup_commit","begin")?;}
            let source=packed_source(&private,&bits)?;drop(bits);
            let setup=if full {Some(pcs::generate_setup(22)?)}else{None};
            let committed=if let Some(setup)=&setup {
                if setup.id!=*key.id(){return Err("stream39 setup identity".into());}
                let committed=packed::commit(&source,setup)?;
                let c=pcs::encode_commitment(&committed.commitment)?;
                if c!=reference.commitment {return Err("stream39 mandatory retained C equality".into());}
                Some(committed)
            }else{None};
            if full {trace.mark("setup_commit","end")?;}
            let public=generic37_public(decoded);
            let (roles,claims,observations,corpus_id)={
                let consumer=Consumer::new(&public)?;let context=ProofContext::historical_tiny(&consumer,&statement)?;
                trace.mark("reference","begin")?;
                let mut claims=context.verify_roles(&reference,&key).map_err(|e|format!("stream39 retained roles: {e:?}"))?;
                trace.mark("reference","end")?;
                let mut roles=reference.roles.clone();let mut observations=Vec::with_capacity(if full {7}else{3});
                let selected:&[usize]=if full {&[0,1,2,3,4,5,6]}else{&[2,5,6]};
                for role in selected {
                    trace.role=*role;trace.mark(ROLE_STAGES[*role],"begin")?;
                    let (packet,claim,observation)=produce_one(&context,&source,&key,&reference,*role,full)?;
                    roles[*role]=packet;claims[*role]=claim;observations.push(observation);
                    trace.completed_roles+=1;trace.mark(ROLE_STAGES[*role],"end")?;
                }
                (roles,claims,observations,context.corpus_id)
            }; // Unique producer graph/context dropped before any Dory opening.
            let batch=if full {
                trace.role=7;trace.mark("graph_drop","end")?;trace.mark("opening","begin")?;
                let setup=setup.as_ref().ok_or("stream39 full setup")?;
                let committed=committed.as_ref().ok_or("stream39 full commitment")?;
                let common=opening_batch::Statement{log_n:22,setup_id:setup.id,commitment:committed.commitment,
                    corpus_id:Some(corpus_id),claims:claims.clone()};
                let (proof,_,_)=opening_batch::prove(&source,committed,setup,&common)?;
                let bytes=opening_batch::encode_proof(&proof,22)?;
                if bytes!=reference.batch || opening_batch::encode_proof(&opening_batch::decode_proof(&bytes,22)?,22)?!=bytes {
                    return Err("stream39 common proof equality".into());
                }
                trace.mark("opening","end")?;bytes
            }else{reference.batch.clone()};
            (Artifact{commitment:reference.commitment.clone(),roles,batch},claims,observations)
        }; // Source/setup/committed rows/public and all owned producer objects drop.
        drop(key);drop(reference);trace.role=7;trace.mark("producer_drop","end")?;
        trace.mark("export","begin")?;export(&output,&statement,&artifact,&pins)?;drop(artifact);drop(statement);trace.mark("export","end")?;
        trace.mark("consumer","begin")?;
        let (fresh_statement,fresh)=generic37_load(&output,&pins)?;
        let actual=verify_historical_tiny_bytes(&fresh_statement,&fresh)?;
        if actual!=claims {return Err("stream39 atomic claims equality".into());}
        trace.mark("consumer","end")?;trace.mark("custody","begin")?;
        if generic37_snapshot(&input)?!=pins || generic37_snapshot(&output)?!=pins {return Err("stream39 final custody".into());}
        let _=generic37_load(&input,&pins)?;let _=generic37_load(&output,&pins)?;
        std::fs::remove_file(&private).map_err(|e|e.to_string())?;trace.mark("custody","end")?;
        let elapsed=trace.elapsed()?;
        let value=report(full,headers,observations,&actual,trace.phase_ns(),elapsed);let encoded=encode_report(&value)?;
        if trace.elapsed()?>trace.limit() {return Err("stream39 transport deadline".into());}
        trace.mark_at("complete","end",elapsed)?;
        let prefix=if full {"\nHISTORY_STREAM39_FULL_REPORT "}else{"\nHISTORY_STREAM39_PACKET_REPORT "};
        let mut out=std::io::stdout().lock();out.write_all(prefix.as_bytes()).map_err(|e|e.to_string())?;
        out.write_all(&encoded).map_err(|e|e.to_string())?;out.write_all(b"\n").map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())?;
        Ok(())
    }));
    if let Some(error)=match operation {Ok(Ok(()))=>None,Ok(Err(e))=>Some(e),Err(_)=>Some("stream39 panic".into())} {
        let error:String=error.chars().filter(|c|c.is_ascii_graphic()||*c==' ').take(240).collect();
        eprintln!("HISTORY_STREAM39_HOLD {} {} {} {} {} {error}",if full {"complete"}else{"packet"},trace.phase,
            trace.role,trace.completed_roles,trace.started.elapsed().as_nanos());
        panic!("stream39 historical tiny HOLD");
    }
}

type Occurrence=(usize,usize,usize,[[u64;4];4]);
fn occurrence(term:&Term)->Occurrence {
    (term.row,term.gate.left,term.gate.right,[term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3].map(|v|v.into_bigint().0))
}
fn same_terms(expected:&[Term],actual:&[Term])->bool {
    let mut a:Vec<_>=expected.iter().map(occurrence).collect();let mut b:Vec<_>=actual.iter().map(occurrence).collect();
    a.sort();b.sort();a==b
}
struct Weights(Vec<(usize,Vec<Fr>)>);
impl Weights {
    fn new(point:&[Fr])->Self {
        Self(point.chunks(8).enumerate().map(|(chunk,coordinates)| {
            let weights=(0..1usize<<coordinates.len()).map(|index|coordinates.iter().enumerate().fold(Fr::one(),|value,(bit,x)|
                value*if index>>bit&1==1 {*x}else{Fr::one()-x})).collect();(chunk*8,weights)
        }).collect())
    }
    fn at(&self,index:usize)->Fr {self.0.iter().fold(Fr::one(),|v,(shift,table)|v*table[(index>>shift)&(table.len()-1)])}
}

fn ordinary_relation(context:&ProofContext<'_>,role:usize){
    let shape=history39_admit(context,role,1<<22,16,RETAINED_BUFFERS).unwrap();
    let canonical=context.small_circuit(role).unwrap();
    assert!(canonical.terms.len()<=1<<18 && canonical.terms.capacity()<=1<<18);
    assert_eq!(canonical.terms.len() as u64,shape.terms);
    let mut b2_constant=false;let mut predecessor=false;let mut local_dummy=false;let mut zero=false;
    let mut special=[false;4];
    for left in [true,false] {for owner in 0..4 {
        let expected:Vec<_>=canonical.terms.iter().filter(|term|(if left {term.gate.left}else{term.gate.right})/layout::WIDTH==owner).cloned().collect();
        let mut actual=Vec::with_capacity(expected.len());
        history39_visit(context,role,&shape,left,owner,&mut |edge|{
            if role==2 {let b2=context.consumer.parent.topology().families.len();
                b2_constant|=edge.family_row>>14==b2 && edge.source_slot>0 && edge.term.gate.left==0 && !edge.term.gate.c0.is_zero();
            }else{
                predecessor|=left&&owner>0&&edge.source_slot!=owner;
                local_dummy|=edge.term.gate.right!=0&&edge.term.gate.c2.is_zero()&&edge.term.gate.c3.is_zero();
            }
            zero|=edge.term.gate.c0.is_zero()||edge.term.gate.c1.is_zero()||edge.term.gate.c2.is_zero()||edge.term.gate.c3.is_zero();
            actual.push(edge.term);Ok(())
        }).unwrap();
        assert!(same_terms(&expected,&actual));
        // Isolate the reached seam variants instead of relying only on a
        // generic first-occurrence fault or on endpoint self-tests elsewhere.
        let b2=context.consumer.parent.topology().families.len();
        for variant in 0..if role==2 {2}else{4} {
            let at=actual.iter().position(|term|match (role,variant) {
                (2,0)=>term.row>>(14+context.geometry.slot_log)==b2
                    && (term.row&((1usize<<(14+context.geometry.slot_log))-1))>>11>0
                    && term.gate.left==0&&!term.gate.c0.is_zero(),
                (2,1)|(6,3)=>term.gate.c0.is_zero(),
                (6,0)=>left&&owner>0&&(term.row>>12)!=owner,
                (6,1)=>term.gate.right!=0&&term.gate.c2.is_zero()&&term.gate.c3.is_zero(),
                (6,2)=>!left&&owner==0&&(term.row>>12)==context.geometry.headers as usize-1&&term.gate.right==0,
                _=>false,
            });
            if let Some(at)=at {
            special[variant]=true;
            let mut omitted=actual.clone();omitted.remove(at);assert!(!same_terms(&expected,&omitted));
            drop(omitted);
            let mut duplicated=actual.clone();duplicated.push(actual[at].clone());assert!(!same_terms(&expected,&duplicated));
            drop(duplicated);
        }}
        if role==6 && context.geometry.headers==3 && owner==3 {assert!(actual.is_empty());}
        if !actual.is_empty(){
            let original=actual[0].clone();actual.remove(0);assert!(!same_terms(&expected,&actual));actual.insert(0,original.clone());
            actual.push(original);assert!(!same_terms(&expected,&actual));actual.pop();
            for field in 0..7 {let mut wrong=actual.clone();match field {
                0=>wrong[0].row^=1,1=>wrong[0].gate.left^=1,2=>wrong[0].gate.right^=1,
                3=>wrong[0].gate.c0+=Fr::one(),4=>wrong[0].gate.c1+=Fr::one(),5=>wrong[0].gate.c2+=Fr::one(),_=>wrong[0].gate.c3+=Fr::one()};
                assert!(!same_terms(&expected,&wrong));
            }
        }
    }}
    assert!(zero);if role==2 {assert!(b2_constant&&special[0]&&special[1]);}
    else{assert!(predecessor&&local_dummy&&special.into_iter().all(|reached|reached));}
    let point=|bits:usize,offset:u64|(0..bits).map(|i|Fr::from(offset+29*i as u64)).collect::<Vec<_>>();
    let r=point(context.geometry.row_bits[role],3);let u=point(22,101);let v=point(22,401);
    let (rw,uw,vw)=(Weights::new(&r),Weights::new(&u),Weights::new(&v));let mut reference=[Fr::zero();4];
    for term in &canonical.terms {let weight=rw.at(term.row)*uw.at(term.gate.left)*vw.at(term.gate.right);
        for (sum,c) in reference.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]) {*sum+=weight*c;}}
    assert_eq!(reference,context.coefficients(role,&r,&u,&v).unwrap());
    assert_eq!(history39_visit(context,role,&shape,true,4,&mut |_|panic!("invalid owner reached sink")).err().unwrap(),"stream39 endpoint owner");
    assert_eq!(history39_visit(context,role,&shape,true,0,&mut |_|Err("stream39 isolated sink".into())).err().unwrap(),"stream39 isolated sink");
}

fn equality_controls(){
    let mut reference=VerifiedRole{role:2,claim:Claim{point:vec![Fr::from(7u64);22],value:Fr::from(11u64)},
        observation:RoleObservation::default(),counters:[67,68,9000],continuation:Fr::from(19u64)};
    let bytes=vec![1u8;5024];let sender=Some((reference.counters,reference.continuation));
    equal_packet(&bytes,&reference.claim,sender,&bytes,&reference).unwrap();
    for role in [2,4,5,6] {reference.role=role;
        assert_eq!(equal_packet(&bytes,&reference.claim,None,&bytes,&reference).err().unwrap(),"stream39 sender missing");}
    for role in [0,1,3] {reference.role=role;equal_packet(&bytes,&reference.claim,None,&bytes,&reference).unwrap();}
    reference.role=2;
    let mut wrong=bytes.clone();wrong[0]^=1;
    assert_eq!(equal_packet(&wrong,&reference.claim,sender,&bytes,&reference).err().unwrap(),"stream39 proof equality");
    for index in 0..23 {let mut claim=reference.claim.clone();if index==22 {claim.value+=Fr::one();}else{claim.point[index]+=Fr::one();}
        assert_eq!(equal_packet(&bytes,&claim,sender,&bytes,&reference).err().unwrap(),"stream39 claim equality");}
    for index in 0..3 {let mut counters=reference.counters;counters[index]+=1;
        assert_eq!(equal_packet(&bytes,&reference.claim,Some((counters,reference.continuation)),&bytes,&reference).err().unwrap(),"stream39 counter equality");}
    assert_eq!(equal_packet(&bytes,&reference.claim,Some((reference.counters,reference.continuation+Fr::one())),&bytes,&reference).err().unwrap(),"stream39 continuation equality");
    let mut t=Transcript::new(b"stream39-transaction-fixture");let before=prefix_snapshot(&t);
    let result:Result<(),String>=history39_transaction(&mut t,|working|{working.append_bytes(b"late",b"changed");
        let _=working.try_challenge_scalar(b"reached")?;Err("stream39 late fixture".into())});
    assert_eq!(result.err().unwrap(),"stream39 late fixture");assert_eq!(before,prefix_snapshot(&t));
    history39_transaction(&mut t,|working|{working.append_bytes(b"success",b"committed");Ok(())}).unwrap();assert_ne!(before,prefix_snapshot(&t));
}

fn serializer_controls(){
    // These are synthetic capacity fixtures through the actual production
    // report/observation serializers, not proofs or accepted native receipts.
    let claim=Claim{point:vec![-Fr::one();22],value:-Fr::one()};let claims=std::array::from_fn(|_|claim.clone());
    for full in [false,true] {
        let mut observations=Vec::new();let roles:&[usize]=if full {&[0,1,2,3,4,5,6]}else{&[2,5,6]};
        for role in roles {
            let mut linear=crate::segment_adjacency::linear_for_test::Stats::default();
            linear.phase_ns=[u64::MAX;4];linear.read_calls=[u64::MAX;4];linear.reconstructed_fields=[u64::MAX;4];
            linear.combined_bound_peak_bytes=[usize::MAX;4];linear.preflight_bound_bytes=usize::MAX;
            linear.retained_capacity_bytes=usize::MAX;linear.scoped_limit_bytes=usize::MAX;
            let mut produced=History39Produced {proof:GkrProof{layers:vec![]},claim:InputClaim{point:claim.point.clone(),value:claim.value},
                sender:if matches!(*role,2|4|5|6){Some(([u64::MAX;3],-Fr::one()))}else{None},
                edge:if matches!(*role,2|4|6){Some(HistoryStreamMetrics{endpoint_calls:u64::MAX,callbacks:u64::MAX,
                    left_terms:u64::MAX,right_terms:u64::MAX,load_calls:u64::MAX,loaded_fields:u64::MAX,load_decode_ns:u64::MAX,
                    loader_capacity_peak:usize::MAX,io:packed::PackedIoSnapshot{read_calls:u64::MAX,read_bytes:u64::MAX,read_ns:u64::MAX as u128,..Default::default()}})}else{None},
                linear:if *role==5 {Some(linear)}else{None},io:packed::PackedIoSnapshot{read_bytes:u64::MAX,read_ns:u64::MAX as u128,..Default::default()},
                elapsed_ns:u64::MAX,load_calls:u64::MAX,loaded_fields:u64::MAX,load_decode_ns:u64::MAX,loader_capacity_peak:usize::MAX,terms:u64::MAX};
            let reference=VerifiedRole{role:*role,claim:claim.clone(),observation:RoleObservation::default(),counters:[u64::MAX;3],continuation:-Fr::one()};
            produced.io.read_ns=u128::MAX;
            assert_eq!(produced_observation(*role,&produced,&vec![0;5024],&claim,&reference,full).err().unwrap(),"stream39 IO clock");
            produced.io.read_ns=u64::MAX as u128;
            observations.push(produced_observation(*role,&produced,&vec![0;if *role==3 {3456}else{5024}],&claim,&reference,full).unwrap());
        }
        let stages=if full {FULL_STAGES}else{PACKET_STAGES};let mut phases=BTreeMap::new();
        for (phase,event) in stages {if *event=="begin" {phases.insert(*phase,u64::MAX);}}
        let value=report(full,4,observations,&claims,phases,u64::MAX);let encoded=encode_report(&value).unwrap();
        assert!(encoded.len()<=REPORT_CAP);
        let markers=stages.iter().map(|(phase,event)|format!("HISTORY_STREAM39_STAGE {} {phase} {event} {}\n",if full {"complete"}else{"packet"},u64::MAX)).collect::<String>();
        assert!(encoded.len()+markers.len()+2048+64<65536);
        // Conservative final receipt model includes the full parsed report,
        // all markers, raw identities/audits/capture and a bounded late error.
        let identity=serde_json::json!({"path":"p".repeat(512),"size":u64::MAX,"sha256":"f".repeat(64),"volume":u64::MAX,"file":u64::MAX});
        let custody=vec![identity.clone();40];
        for state in ["PASS","HOLD"] {
            let receipt=serde_json::json!({"state":state,"report":value,"progress":markers,
                "inputs_pre_post":custody,"source_audits":[identity.clone(),identity.clone()],"capture":identity,
                "errors":if state=="HOLD"{vec!["E".repeat(240);4]}else{vec![]}});
            assert!(serde_json::to_vec(&receipt).unwrap().len()<=RECEIPT_CAP);
        }
    }
    assert_eq!(encode_report(&serde_json::json!({"oversized":"x".repeat(REPORT_CAP)})).err().unwrap(),"stream39 report capacity");
}

#[test]
fn ordinary_boundaries(){
    equality_controls();serializer_controls();
    assert_eq!(history39_vector(vec![Fr::zero();7],8).err().unwrap(),"stream39 loader length");
    let mut spare=Vec::with_capacity(16);spare.resize(8,Fr::zero());
    assert_eq!(history39_vector(spare,8).err().unwrap(),"stream39 loader capacity");
    assert_eq!(history39_vector(vec![Fr::zero();8],8).unwrap().len(),8);
    for headers in [3,4] {
        let public=Public::native(headers).unwrap();let consumer=Consumer::new(&public).unwrap();
        let encoded=literal_public_bytes(&public).unwrap();let mut context=ProofContext::historical_tiny(&consumer,&encoded).unwrap();
        let before=prefix_snapshot(&context.base);
        for role in 0..7 {history39_admit(&context,role,1<<22,16,RETAINED_BUFFERS).unwrap();}
        for (role,len,chunk,retained,error) in [(7,1<<22,16,RETAINED_BUFFERS,"stream39 role"),
            (5,(1<<22)-1,16,RETAINED_BUFFERS,"stream39 source extent"),
            (5,1<<22,15,RETAINED_BUFFERS,"stream39 chunk width"),
            (5,1<<22,16,crate::segment_adjacency::linear_for_test::LIMIT+1,"stream39 retained extent")] {
            assert_eq!(history39_admit(&context,role,len,chunk,retained).err().unwrap(),error);
        }
        context.height_binding=HeightBinding::LegacyN3N4;
        assert_eq!(history39_admit(&context,2,1<<22,16,RETAINED_BUFFERS).err().unwrap(),"stream39 historical mode");
        context.height_binding=HeightBinding::HistoricalDiagnostic;
        let original=context.geometry.clone();
        for fault in 0..18 {
            let mut changed=original.clone();match fault {0=>changed.headers=5,1=>changed.slot_log=3,2=>changed.slots=8,3=>changed.common_input=23,
                4..=10=>changed.input_bits[fault-4]+=1,_=>changed.row_bits[fault-11]+=1};context.geometry=changed;
            assert_eq!(history39_admit(&context,2,1<<22,16,RETAINED_BUFFERS).err().unwrap(),"stream39 tiny geometry");
        }
        context.geometry=original.clone();
        for (fault,error) in [(0,"geometry core bank bits mismatch"),(1,"geometry height split mismatch"),
            (2,"geometry DAA split mismatch"),(3,"geometry DAA base mismatch"),
            (4,"geometry point local mismatch"),(5,"geometry point local mismatch")] {
            let mut changed=original.clone();match fault {0=>changed.bank_bits+=1,1=>changed.height_row+=1,
                2=>changed.daa_row+=1,3=>changed.daa_row_base+=1,4=>changed.point_local_input+=1,_=>changed.point_local_row+=1};
            context.geometry=changed;
            assert_eq!(history39_admit(&context,2,1<<22,16,RETAINED_BUFFERS).err().unwrap(),error);
        }
        context.geometry=original;assert_eq!(before,prefix_snapshot(&context.base));
        let descriptor=consumer.adjacency.linear_descriptor_for_test().unwrap();
        for (len,chunk) in [((1<<22)-1,16),(1<<22,15)] {
            assert_eq!(descriptor.validate(len,chunk).err().unwrap(),"linear diagnostic geometry/source rejected before activity");
        }
        ordinary_relation(&context,2);ordinary_relation(&context,6);
    }
    // One Consumer only. The second object is a same-geometry parent, not a
    // second point graph/context; its payload is charged by the test ledger.
    {
        let public=Public::native(3).unwrap();
        let foreign=WorkTreeHistoryPlan::compile(3,2,public.root,public.total).unwrap();
        let consumer=Consumer::new(&public).unwrap();let encoded=literal_public_bytes(&public).unwrap();
        let mut context=ProofContext::historical_tiny(&consumer,&encoded).unwrap();let before=prefix_snapshot(&context.base);
        context.height=HeightWork::compile_history(&foreign).unwrap();
        assert_eq!(history39_admit(&context,2,1<<22,16,RETAINED_BUFFERS).err().unwrap(),"stream39 parent identity");
        context.height=HeightWork::compile_history(&consumer.parent).unwrap();context.daa=DaaHistoryRoster::compile(&foreign).unwrap();
        assert_eq!(history39_admit(&context,6,1<<22,16,RETAINED_BUFFERS).err().unwrap(),"stream39 parent identity");
        assert_eq!(before,prefix_snapshot(&context.base));
    }
}

#[test]
#[ignore="stream39 historical N3 packet join; separate bounded admission"]
fn historical_n3_streaming_join(){join(3,false);}
#[test]
#[ignore="stream39 historical N4 packet join; separate bounded admission"]
fn historical_n4_streaming_join(){join(4,false);}
#[test]
#[ignore="stream39 complete N4 producer; requires accepted packet closure and separate admission"]
fn historical_n4_complete_producer(){join(4,true);}

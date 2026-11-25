//! Provisional Historical H12 roles3/5/1 joins; no production or PCS admission.
use super::*;
use ark_serialize::{CanonicalDeserialize,CanonicalSerialize};
use std::{fs::File,io::{Read,Seek,SeekFrom},path::PathBuf};
use std::os::windows::{fs::OpenOptionsExt,io::AsRawHandle};

const RAW_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const PACK_BLAKE:&str="725d7b1215e1185c52c1012d9294260612653acad53a02429b8eaafd0f0770c8";
const KEY_SHA:&str="D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2";
const C_SHA:&str="2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90";
const META_SHA:&str="E44408DC018E99711273794DF3575BE7D180CF347448A021AA7EEC6BD0143401";
const ID:&str="1AE7BADC1E529C7A5CDA709AD1B418AF6AE2EFB6B7B4D909816D091C3260A51B";
const STAGES:[(&str,&str);19]=[("admission","begin"),("admission","end"),("producer","begin"),("producer","end"),
    ("producer_drop","end"),("export","begin"),("export","end"),("consumer","begin"),("consumer","end"),
    ("consumer_drop","end"),("public_bindings","begin"),("public_bindings","end"),
    ("claim_controls","begin"),("claim_controls","end"),("custody","begin"),("custody","end"),
    ("result","begin"),("result","end"),("complete","end")];
fn need(ok:bool,error:&str)->Result<(),String>{if ok{Ok(())}else{Err(error.into())}}
fn ns(start:Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"historical50 clock".into())}
fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
fn snapshot(t:&Transcript)->Result<([u64;3],Fr),String>{Ok((counters(t),t.clone().try_challenge_scalar(b"historical50-prefix-control-v1")?))}
fn role_shape(role:usize)->Result<(usize,usize,usize,u64),String>{match role{
    3=>Ok((25,5696,77,1180295168)),5=>Ok((32,7264,86,786944)),1=>Ok((32,7264,96,1624305664)),
    _=>Err("historical50 role".into())}}
fn members(role:usize)->Result<[(&'static str,usize);4],String>{
    let (_,bytes,_,_)=role_shape(role)?;let name=match role{3=>"role-3.gkr",5=>"role-5.gkr",1=>"role-1.gkr",_=>unreachable!()};
    Ok([("statement.bin",571),("commitment.bin",384),(name,bytes),("result.json",16384)])
}
fn synthetic_c()->Result<Vec<u8>,String>{
    pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero()))
}
#[repr(C)]
#[derive(Default,PartialEq,Eq)]
struct Identity{attributes:u32,created:[u32;2],accessed:[u32;2],written:[u32;2],volume:u32,
    high:u32,low:u32,links:u32,index_high:u32,index_low:u32}
fn identity(file:&File)->Result<Identity,String>{
    #[link(name="kernel32")]extern "system"{fn GetFileInformationByHandle(h:*mut std::ffi::c_void,p:*mut Identity)->i32;}
    let mut id=Identity::default();
    if unsafe{GetFileInformationByHandle(file.as_raw_handle(),&mut id)}==0{return Err("historical50 file identity".into());}
    need(id.attributes&0x410==0&&id.links==1,"historical50 ordinary single-link file")?;id.accessed=[0;2];Ok(id)
}
struct Held{file:File,path:PathBuf,id:Identity,bytes:Vec<u8>,digest:String}
impl Held{
    fn open(env:&str,size:usize,expected:&str,pack:bool)->Result<Self,String>{
        let path=PathBuf::from(std::env::var_os(env).ok_or("historical50 missing input")?);
        need(path.is_absolute()&&path.as_os_str().len()<=1024,"historical50 input path")?;
        need(generic37_metadata(&path,false)?.len()==size as u64,"historical50 input extent")?;
        let mut file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|_|"historical50 input open")?;
        let id=identity(&file)?;need((u64::from(id.high)<<32)|u64::from(id.low)==size as u64,"historical50 held extent")?;
        let mut bytes=Vec::new();let digest;
        if pack{let mut state=Blake2b::<U32>::new();let mut scratch=[0u8;65536];let mut total=0usize;
            loop{let n=file.read(&mut scratch).map_err(|_|"historical50 PACK read")?;if n==0{break;}
                total=total.checked_add(n).ok_or("historical50 PACK overflow")?;
                need(total<=size,"historical50 PACK trailing")?;state.update(&scratch[..n]);}
            need(total==size,"historical50 PACK truncated")?;digest=h41_hex(&state.finalize());
        }else{need(size<=869449,"historical50 bounded input")?;bytes.resize(size,0);
            file.read_exact(&mut bytes).map_err(|_|"historical50 input read")?;
            let mut tail=[0;1];need(file.read(&mut tail).map_err(|_|"historical50 input tail")?==0,"historical50 input trailing")?;
            digest=h41_sha(&bytes)?;}
        need(digest==expected,"historical50 input digest")?;let held=Self{file,path,id,bytes,digest};held.check()?;Ok(held)
    }
    fn check(&self)->Result<(),String>{
        generic37_metadata(&self.path,false)?;need(identity(&self.file)?==self.id,"historical50 held custody")?;
        let named=OpenOptions::new().read(true).share_mode(1).open(&self.path).map_err(|_|"historical50 custody reopen")?;
        need(identity(&named)?==self.id,"historical50 named custody")
    }
    fn rehash(&mut self,pack:bool)->Result<(),String>{
        self.check()?;self.file.seek(SeekFrom::Start(0)).map_err(|_|"historical50 custody seek")?;
        if pack{let mut state=Blake2b::<U32>::new();let mut scratch=[0u8;65536];let mut total=0usize;
            loop{let n=self.file.read(&mut scratch).map_err(|_|"historical50 custody read")?;if n==0{break;}
                total=total.checked_add(n).ok_or("historical50 custody overflow")?;need(total<=536870912,"historical50 custody extent")?;state.update(&scratch[..n]);}
            need(total==536870912&&h41_hex(&state.finalize())==self.digest,"historical50 PACK custody hash")?;
        }else{let mut actual=vec![0;self.bytes.len()];self.file.read_exact(&mut actual).map_err(|_|"historical50 custody read")?;
            let mut tail=[0;1];need(self.file.read(&mut tail).map_err(|_|"historical50 custody tail")?==0
                &&actual==self.bytes&&h41_sha(&actual)?==self.digest,"historical50 buffer custody")?;}self.check()
    }
    fn heap(&self)->Result<usize,String>{h50_sum(&[self.bytes.capacity(),self.digest.capacity(),self.path.capacity()])}
}
fn raw_input(bytes:&[u8])->Result<crate::packed_owner_assembly::NativePrefix,String>{
    let mut at=0usize;let mut raws=Vec::with_capacity(3073);
    for _ in 0..3073{let n=u32::from_le_bytes(historical47_take(bytes,&mut at)?) as usize;
        need((1..=514).contains(&n),"historical50 RAW record extent")?;let end=at.checked_add(n).ok_or("historical50 RAW overflow")?;
        raws.push(bytes.get(at..end).ok_or("historical50 RAW truncated")?.to_vec());at=end;}
    need(at==bytes.len(),"historical50 RAW trailing")?;
    crate::packed_owner_assembly::NativePrefix::from_raw_iter(3073,raws.into_iter().map(Ok))
}
thread_local!{static GRAPHS:std::cell::Cell<[u64;4]>=const{std::cell::Cell::new([0;4])};}
fn graph_counts()->[u64;4]{GRAPHS.with(|v|v.get())}
struct Graph{consumer:Consumer}
impl Graph{
    fn new(a:&Historical47Admission)->Result<Self,String>{Self::from_public(&a.public)}
    fn from_public(public:&Public)->Result<Self,String>{
        need(graph_counts()[0]==0,"historical50 concurrent graph")?;historical47_policy(public.headers,12,4096,32)?;
        let OwnedLayouts{parent,adjacency,metadata,points,point_template}=compile_layouts(&LayoutRequest{
            headers:public.headers,slot_log:12,root:public.root,total:public.total,tip:public.tip,tip_time:public.tip_time})?;
        let consumer=Consumer{public:public.clone(),parent,adjacency,metadata,points,point_template};
        GRAPHS.with(|v|{let mut c=v.get();c[0]+=1;c[1]=c[1].max(c[0]);c[2]+=1;v.set(c)});Ok(Self{consumer})
    }
}
impl Drop for Graph{fn drop(&mut self){GRAPHS.with(|v|{let mut c=v.get();assert_eq!(c[0],1);c[0]-=1;c[3]+=1;v.set(c)})}}
fn output_dir()->Result<PathBuf,String>{
    let path=PathBuf::from(std::env::var_os("NIPOPOW_HISTORICAL50_OUTPUT_DIR").ok_or("historical50 missing output")?);
    need(path.is_absolute()&&path.as_os_str().len()<=1024,"historical50 output path")?;generic37_metadata(&path,true)?;
    need(path.read_dir().map_err(|_|"historical50 output scan")?.next().is_none(),"historical50 output not empty")?;Ok(path)
}
fn roster(dir:&Path,role:usize,complete:bool)->Result<(),String>{
    generic37_metadata(dir,true)?;let mut names=Vec::with_capacity(4);
    for entry in dir.read_dir().map_err(|_|"historical50 output scan")?{need(names.len()<4,"historical50 output roster")?;
        let entry=entry.map_err(|_|"historical50 output entry")?;generic37_metadata(&entry.path(),false)?;
        names.push(entry.file_name().into_string().map_err(|_|"historical50 output name")?);}
    names.sort();let mut expected:Vec<_>=members(role)?[..if complete{4}else{3}].iter().map(|x|x.0.to_owned()).collect();expected.sort();
    need(names==expected,"historical50 output roster")
}
fn read_export(dir:&Path,role:usize,name:&str,expected:&[u8])->Result<Vec<u8>,String>{
    let bound=members(role)?.iter().find(|x|x.0==name).ok_or("historical50 export name")?.1;
    need(expected.len()<=bound&&(name=="result.json"||expected.len()==bound),"historical50 export extent")?;
    let bytes=generic37_read(&dir.join(name),expected.len())?;need(bytes==expected,"historical50 export bytes")?;Ok(bytes)
}
fn fr_from_json(v:&serde_json::Value)->Result<Fr,String>{
    let s=v.as_str().ok_or("historical50 scalar type")?;
    need(s.len()==64&&s.bytes().all(|b|b.is_ascii_digit()||(b'a'..=b'f').contains(&b)),"historical50 scalar encoding")?;
    let mut bytes=[0u8;32];for(i,pair)in s.as_bytes().chunks_exact(2).enumerate(){bytes[i]=u8::from_str_radix(
        std::str::from_utf8(pair).map_err(|_|"historical50 scalar UTF8")?,16).map_err(|_|"historical50 scalar hex")?;}
    let value=Fr::deserialize_compressed(&bytes[..]).map_err(|_|"historical50 scalar canonical")?;
    let mut encoded=Vec::new();value.serialize_compressed(&mut encoded).map_err(|_|"historical50 scalar encode")?;
    need(encoded==bytes,"historical50 scalar roundtrip")?;Ok(value)
}
fn claim_from_json(v:&serde_json::Value,width:usize)->Result<Claim,String>{
    let o=v.as_object().ok_or("historical50 claim type")?;need(o.len()==2&&o.contains_key("point")&&o.contains_key("value"),"historical50 claim keys")?;
    let p=o["point"].as_array().ok_or("historical50 claim point")?;need(p.len()==width,"historical50 claim dimension")?;
    Ok(Claim{point:p.iter().map(fr_from_json).collect::<Result<Vec<_>,_>>()?,value:fr_from_json(&o["value"])?})
}
fn close_claim(v:&serde_json::Value,verified:&Claim,mle:Fr)->Result<(),String>{
    need(claim_from_json(v,32)?==*verified&&verified.value==mle,"historical50 reported claim/MLE")
}
fn common_projection(role:usize,raw:&Claim)->Result<Claim,String>{
    let (width,_,_,_)=role_shape(role)?;need(raw.point.len()==width,"historical50 raw point dimension")?;
    let point=if role==3{let mut p=Vec::with_capacity(32);p.extend_from_slice(&raw.point[..13]);
        p.extend([0u64,0,0,0,0,1,1].map(Fr::from));p.extend_from_slice(&raw.point[13..]);p}else{raw.point.clone()};
    Ok(Claim{point,value:raw.value})
}
fn verify_failure(role:usize,result:Result<VerifiedRole,RoleFailure>,stage:RoleStage,entered:bool)->Result<(),String>{
    let e=match result{Ok(_)=>return Err("historical50 negative accepted".into()),Err(e)=>e};
    need(e.role==role||stage==RoleStage::Shape,"historical50 failure role")?;
    need(e.stage==stage&&e.observation.verifier_entered==entered&&e.observation.canonical_decode==entered,"historical50 negative stage")
}
fn receiver_controls(context:&ProofContext<'_>,packet:&RoleProof,a:&Historical47Admission,positive:&VerifiedRole)->Result<(),String>{
    let role=packet.role;let(width,extent,_,_)=role_shape(role)?;
    let normal=context.transcript(role,&a.key,&a.commitment);
    let nofault=context.historical50_control_prefix(role,&a.key,&a.commitment,Historical50PrefixFault::NoFault)?;
    need(snapshot(&normal)?==snapshot(&nofault)?,"historical50 NoFault prefix")?;
    let control=context.verify_role_historical50_control(packet,&a.key,&a.commitment,Historical50PrefixFault::NoFault)
        .map_err(|e|format!("historical50 NoFault {:?}",e.stage))?;
    need(control.claim==positive.claim&&control.counters==positive.counters&&control.continuation==positive.continuation,"historical50 NoFault consumer")?;
    for size in [extent-1,extent+1]{let mut bad=packet.clone();bad.bytes.resize(size,0);
        verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Shape,false)?;}
    let mut bad=packet.clone();bad.role=7;verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Shape,false)?;
    let key22=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    verify_failure(role,context.verify_role(packet,&key22,&a.commitment),RoleStage::Shape,false)?;
    for bytes in [vec![0;383],vec![255;384]]{verify_failure(role,context.verify_role(packet,&a.key,&bytes),RoleStage::Commitment,false)?;}
    let mut bad=packet.clone();bad.bytes[..32].fill(255);verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Decode,false)?;
    let mut proof=gkr::decode_dimensions(&[width],&packet.bytes)?;proof.layers[0].rounds[0][0]+=Fr::one();
    let bad=RoleProof{role,bytes:gkr::encode_proof(&proof)?};need(bad.bytes!=packet.bytes,"historical50 reached round mutant")?;
    verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Gkr,true)?;
    let c=synthetic_c()?;need(c!=a.commitment,"historical50 alternate C reached")?;historical47_commitment(&c)?;
    verify_failure(role,context.verify_role(packet,&a.key,&c),RoleStage::Gkr,true)?;
    let extra=context.historical50_control_prefix(role,&a.key,&a.commitment,Historical50PrefixFault::ExtraRoleBinder)?;
    need(counters(&extra)[..2]==[0,0]&&extra.bytes_absorbed()>normal.bytes_absorbed(),"historical50 extra binder reached")?;
    verify_failure(role,context.verify_role_historical50_control(packet,&a.key,&a.commitment,Historical50PrefixFault::ExtraRoleBinder),RoleStage::Gkr,true)
}
fn public_controls(public:&Public,packet:&RoleProof,key:&[u8],meta:&[u8],c:&[u8])->Result<(),String>{
    for field in 0..4{let mut p=public.clone();match field{0=>p.root[0]^=1,1=>p.total[0]^=1,2=>p.tip[0]^=1,_=>p.tip_time^=1}
        let a=Historical47Admission::new(&historical47_frame(&p)?,key,meta,c)?;let graph=Graph::new(&a)?;
        let(context,_)=ProofContext::historical_h12(&graph.consumer,&a)?;
        verify_failure(packet.role,context.verify_role(packet,&a.key,&a.commitment),RoleStage::Gkr,true)?;drop(context);drop(graph);}
    need(graph_counts()==[0,1,6,6],"historical50 sequential graphs")
}
fn io_json(io:packed::PackedIoSnapshot)->Result<serde_json::Value,String>{Ok(serde_json::json!({
    "read_calls":io.read_calls,"read_bytes":io.read_bytes,"read_ns":u64::try_from(io.read_ns).map_err(|_|"historical50 I/O clock")?,
    "write_calls":io.write_calls,"write_bytes":io.write_bytes,"write_ns":u64::try_from(io.write_ns).map_err(|_|"historical50 I/O clock")?,
    "sync_calls":io.sync_calls,"sync_ns":u64::try_from(io.sync_ns).map_err(|_|"historical50 I/O clock")?}))}

fn grouped_json(g:&sparse_stream_roster::GroupedVStats)->Result<serde_json::Value,String>{
    need(g.group_count<=2&&g.group_owner_counts.len()==g.group_count&&g.group_term_counts.len()==g.group_count
        &&g.group_weight_sums.len()==g.group_count&&g.group_d_local_contributions.len()==g.group_count,"historical50 grouped roster")?;
    let mut v=serde_json::json!({"group_count":g.group_count,"group_owner_counts":g.group_owner_counts,
        "group_term_counts":g.group_term_counts,"group_weight_sums":g.group_weight_sums.iter().map(|x|h41_fr(*x)).collect::<Vec<_>>(),
        "group_d_local_contributions":g.group_d_local_contributions.iter().map(|x|h41_fr(*x)).collect::<Vec<_>>(),
        "baseline_term_callbacks":g.baseline_term_callbacks,"template_term_count":g.template_term_count,
        "template_capacity_bytes":g.template_capacity_bytes,"bank_term_callbacks":g.bank_term_callbacks,
        "handoff_term_callbacks":g.handoff_term_callbacks,"grouped_state_peak_capacity_bytes":g.grouped_state_peak_capacity_bytes,
        "local_rounds":g.local_rounds,"owner_handoff_count":g.owner_handoff_count});
    merge(&mut v,serde_json::json!({"timings_ns":[g.baseline_elapsed_ns,g.bank_build_elapsed_ns,g.local_v_elapsed_ns,g.owner_handoff_elapsed_ns]}))?;Ok(v)
}
fn boolean_json(u:&sparse_stream_roster::BooleanUPreweightStats)->serde_json::Value{serde_json::json!({
    "prefix_builds":u.prefix_builds,"shared_term_iterations":u.shared_term_iterations,"owner_term_selections":u.owner_term_selections,
    "boolean_checked_loads":u.boolean_checked_loads,"boolean_checked_fields":u.boolean_checked_fields,
    "zero_anchor_sweep_skipped":u.zero_anchor_sweep_skipped,"preweight_entry_size_bytes":u.preweight_entry_size_bytes,
    "preweight_peak_capacity_bytes":u.preweight_peak_capacity_bytes,"u_state_peak_capacity_bytes":u.u_state_peak_capacity_bytes,
    "u_preflight_capacity_bound_bytes":u.u_preflight_capacity_bound_bytes,
    "timings_ns":[u.u_prefix_preweight_elapsed_ns,u.u_owner_selection_elapsed_ns,u.u_x_fold_elapsed_ns],
    "u_phase_peak_capacity_bytes":u.u_phase_peak_capacity_bytes})}
fn merge(target:&mut serde_json::Value,part:serde_json::Value)->Result<(),String>{
    let into=target.as_object_mut().ok_or("historical50 report target")?;
    let serde_json::Value::Object(from)=part else{return Err("historical50 report map".into());};
    for(k,v)in from{need(!into.contains_key(&k),"historical50 duplicate report key")?;into.insert(k,v);}Ok(())
}
fn engine(produced:&Historical50Produced)->Result<serde_json::Value,String>{
    let mut v=serde_json::json!({"kind":if produced.role==5{"adjacency-sparse-support"}else{"boolean-grouped"},
        "memory":produced.memory,"baseline_owners":produced.baseline_owners,"baseline_terms":produced.baseline_terms,
        "progress_events":produced.progress_events,"grouped_preflight":produced.grouped_preflight});
    let(g,u)=match &produced.grouped{Some((g,u))=>(grouped_json(g)?,boolean_json(u)),None=>(serde_json::Value::Null,serde_json::Value::Null)};
    let(l,s)=match &produced.linear{Some((l,s))=>(serde_json::to_value(l).map_err(|_|"historical50 linear encoding")?,
        serde_json::to_value(s).map_err(|_|"historical50 support encoding")?),None=>(serde_json::Value::Null,serde_json::Value::Null)};
    merge(&mut v,serde_json::json!({"grouped":g,"boolean_u":u,"linear":l,"support":s}))?;Ok(v)
}
fn producer_stats(p:&Historical50Produced)->Result<(),String>{
    let(_,_,challenges,terms)=role_shape(p.role)?;
    need(p.baseline_owners==4096&&p.baseline_terms==terms&&p.counters[0]==challenges as u64
        &&p.memory.retained_bytes<=p.memory.constructor_bound&&p.memory.constructor_bound<=536870912,"historical50 producer inventory")?;
    if let Some((g,u))=&p.grouped{
        let (owners,counts,local)=if p.role==3{(vec![4096],vec![288158],13)}else{(vec![4095,1],vec![396561,388369],20)};
        need(g.group_owner_counts==owners&&g.group_term_counts==counts&&g.group_count==owners.len()
            &&g.baseline_term_callbacks as u64==terms&&g.local_rounds==local&&g.owner_handoff_count==4096
            &&u.u_state_peak_capacity_bytes<=u.u_preflight_capacity_bound_bytes&&u.u_preflight_capacity_bound_bytes<=536870912
            &&p.grouped_preflight[0]==u.u_preflight_capacity_bound_bytes&&g.grouped_state_peak_capacity_bytes<=p.grouped_preflight[1]
            &&p.grouped_preflight[1]<=536870912&&p.progress_events==0&&p.linear.is_none(),"historical50 grouped observations")?;
    }else{let(l,s)=p.linear.as_ref().ok_or("historical50 linear observations")?;
        need(p.role==5&&p.progress_events==67&&l.scoped_limit_bytes==536870912&&l.preflight_bound_bytes<=536870912
            &&l.combined_bound_peak_bytes.iter().all(|x|*x<=l.preflight_bound_bytes)
            &&l.retained_capacity_bytes==p.memory.retained_bytes+256&&s.control_capacity_bytes==256
            &&s.chunks_per_owner==16&&s.parent_chunk_mask==256&&s.digest_chunk_mask==1024&&s.support_chunks==[3074,3073]
            &&s.low_round_read_calls==[49184,49168]&&s.low_round_skipped_chunks==[999392,999408]
            &&l.read_calls==[65536,114720,114704,65536]&&l.reconstructed_fields==l.read_calls.map(|n|n*65536)
            &&l.high_fold_coordinates==[16,16]&&l.initial_padding_chunks==16368&&l.line_input_fields==1usize<<32,
            "historical50 linear capacity observations")?;}
    Ok(())
}
struct ResultData{
    role:usize,public:Public,frame_sha:String,proof_sha:String,raw:Claim,sender:Claim,receiver:Claim,
    sender_counts:[u64;3],receiver_counts:[u64;3],sender_next:Fr,receiver_next:Fr,prefix:[u64;3],mle:Fr,
    times:[u64;7],subtimes:[u64;5],actual_source_digest:String,binding_io:packed::PackedIoSnapshot,
    proof_io:packed::PackedIoSnapshot,mle_io:packed::PackedIoSnapshot,graphs:[u64;4],engine:serde_json::Value,
}
fn report(d:&ResultData)->Result<serde_json::Value,String>{
    let(width,extent,_,_)=role_shape(d.role)?;
    let mut value=serde_json::json!({"schema":"historical32-role135-join50-v1","result":"PASS","role":d.role,"headers":3073,
        "slot_log":12,"slots":4096,"input_log":32,"raw_claim_log":width,"common_claim_log":32,
        "profile":std::str::from_utf8(H47_PROFILE).map_err(|_|"historical50 profile UTF8")?,"public":h41_public(&d.public),
        "frame":{"bytes":571,"sha256":d.frame_sha},"proof":{"bytes":extent,"sha256":d.proof_sha},
        "key":{"bytes":33264,"metadata_bytes":40,"log_n":32,"sha256":KEY_SHA,"setup_id":ID},
        "commitment":{"bytes":384,"sha256":C_SHA}});
    merge(&mut value,serde_json::json!({"producer":{"terminal_claim":h41_claim(&d.raw),"claim":h41_claim(&d.sender),
            "counters":d.sender_counts,"continuation":h41_fr(d.sender_next)},
        "consumer":{"claim":h41_claim(&d.receiver),"counters":d.receiver_counts,"continuation":h41_fr(d.receiver_next),
            "mle":h41_fr(d.mle),"canonical_decode":true,"verifier_entered":true,"prefix":d.prefix},
        "timings_ns":d.times,"subtimings_ns":d.subtimes,"graphs":d.graphs,"engine":d.engine,
        "io":{"source_binding":io_json(d.binding_io)?,"proof":io_json(d.proof_io)?,"mle":io_json(d.mle_io)?}}))?;
    merge(&mut value,serde_json::json!({"checks":{"same_parent":true,"NoFault":true,"codec":true,"round":true,"alternate_c":true,
        "extra_binder":true,"public_fields":true,"wrong_key_log":true,"claim_mle":true,"exports_replayed":true,
        "parents_sequential":true,"baseline_before_fs":true,"component_bounds":true,"source_reader_binding":true,"raw_projection":true},
        "custody":{"raw_sha256":RAW_SHA,"pack_blake2b256":PACK_BLAKE,"key_metadata_sha256":META_SHA,
            "actual_source_blake2b256":d.actual_source_digest,"post":true},
        "new_gkr":1,"pcs_invoked":false,"setup_generated":false,"witness_generated":false,"all_seven":false,
        "common_opening":false,"full_history":false,"production":false}))?;Ok(value)
}
fn result_claims(v:&serde_json::Value,d:&ResultData)->Result<(),String>{
    close_claim(&v["producer"]["claim"],&d.receiver,d.mle)?;close_claim(&v["consumer"]["claim"],&d.receiver,d.mle)?;
    need(fr_from_json(&v["consumer"]["mle"])?==d.mle,"historical50 reported MLE")?;
    let(width,_,_,_)=role_shape(d.role)?;let raw=claim_from_json(&v["producer"]["terminal_claim"],width)?;
    let projected=common_projection(d.role,&raw)?;
    need(raw==d.raw&&projected==d.receiver,"historical50 reported raw projection")
}
fn claim_controls(d:&ResultData)->Result<(),String>{
    let good=report(d)?;result_claims(&good,d)?;
    for side in ["producer","consumer"]{let mut bad=good.clone();bad[side]["claim"]["value"]=serde_json::json!(h41_fr(d.receiver.value+Fr::one()));
        need(result_claims(&bad,d).err().as_deref()==Some("historical50 reported claim/MLE"),"historical50 claim value fault")?;
        for coordinate in 0..32{let mut bad=good.clone();bad[side]["claim"]["point"][coordinate]=serde_json::json!(h41_fr(d.receiver.point[coordinate]+Fr::one()));
            need(result_claims(&bad,d).err().as_deref()==Some("historical50 reported claim/MLE"),"historical50 claim coordinate fault")?;}}
    let mut bad=good.clone();bad["consumer"]["mle"]=serde_json::json!(h41_fr(d.mle+Fr::one()));
    need(result_claims(&bad,d).err().as_deref()==Some("historical50 reported MLE"),"historical50 MLE fault")?;
    for coordinate in 0..d.raw.point.len(){let mut bad=good.clone();bad["producer"]["terminal_claim"]["point"][coordinate]=serde_json::json!(h41_fr(d.raw.point[coordinate]+Fr::one()));
        need(result_claims(&bad,d).err().as_deref()==Some("historical50 reported raw projection"),"historical50 raw coordinate fault")?;}
    let mut bad=good;bad["producer"]["terminal_claim"]["value"]=serde_json::json!(h41_fr(d.raw.value+Fr::one()));
    need(result_claims(&bad,d).err().as_deref()==Some("historical50 reported raw projection"),"historical50 raw value fault")?;
    for extra in [false,true]{let mut bad=report(d)?;let point=bad["producer"]["terminal_claim"]["point"].as_array_mut().ok_or("historical50 raw shape fixture")?;
        if extra{point.push(serde_json::json!(h41_fr(Fr::one())));}else{point.pop();}
        need(result_claims(&bad,d).err().as_deref()==Some("historical50 claim dimension"),"historical50 raw shape fault")?;}Ok(())
}
struct Trace{start:Instant,next:usize}
impl Trace{fn mark(&mut self,phase:&str,event:&str)->Result<(),String>{
    need(STAGES.get(self.next)==Some(&(phase,event)),"historical50 stage order")?;
    eprintln!("HISTORICAL32_ROLE135_50_STAGE {phase} {event} {}",self.start.elapsed().as_nanos());self.next+=1;Ok(())}}
fn capability_controls(context:&ProofContext<'_>,bound:&Historical50BoundSource<'_>,a:&Historical47Admission,
    role:usize,buffers:Historical50Buffers)->Result<(),String>{
    let io=bound.source.io_metrics_snapshot();let mut t=context.transcript(role,&a.key,&a.commitment);let before=snapshot(&t)?;
    if role==5{let token=Historical50Role5Admission::new(context,bound,a,buffers)?;
        let foreign=HeaderAdjacencyLayout::compile(3,2,[0;32],[0;32])?;
        rejected(token.require_layout(&foreign),"historical50 foreign adjacency capability")?;
        rejected(token.load_chunk(65536),"historical50 role5 chunk bound")?;
        let descriptor=token.descriptor()?;
        need(descriptor.validate(descriptor.input_len(),descriptor.chunk_bits()).is_err(),"historical50 descriptor cannot grant generic admission")?;
        let prepared=token.prepare_binding(&t)?;let mut normal=t.clone();context.bind_role(5,&mut normal);
        need(snapshot(&prepared)?==snapshot(&normal)?&&snapshot(&t)?==before,"historical50 role5 prepare exact binder")?;
        rejected(token.prepare_binding(&t),"historical50 role5 binder freshness/once")?;
        rejected(token.complete(),"historical50 role5 incomplete producer")?;
    }else{let token=Historical50GroupedAdmission::new(context,bound,a,role,buffers)?;
        rejected(token.load_owner(4096),"historical50 owner bound")?;
        let terms=role_shape(role)?.3;
        for(next,total)in[(0,0),(4095,terms),(4096,terms-1)]{token.next.set(next);token.terms.set(total);
            rejected(token.bind_statement(&mut t),"historical50 incomplete baseline")?;
            need(snapshot(&t)?==before&&!token.bound_once.get(),"historical50 actual token completion before FS")?;}
    }
    need(bound.source.io_metrics_snapshot()==io&&snapshot(&t)?==before,"historical50 capability refusal before source/FS")
}
fn run(t:&mut Trace,role:usize)->Result<(),String>{
    let(_,extent,_,_)=role_shape(role)?;let proof_name=members(role)?[2].0;
    let mut times=[0u64;7];let mut subtimes=[0u64;5];need(graph_counts()==[0;4],"historical50 fresh graph ledger")?;
    need(std::env::var_os("NIPOPOW_CORE_POOL_PROFILE").is_none(),"historical50 extra profile output forbidden")?;
    t.mark("admission","begin")?;let started=Instant::now();
    let mut raw=Held::open("NIPOPOW_HISTORICAL50_RAW_PATH",869449,RAW_SHA,false)?;
    let mut pack=Held::open("NIPOPOW_HISTORICAL50_PACK_PATH",536870912,PACK_BLAKE,true)?;
    let mut key=Held::open("NIPOPOW_HISTORICAL50_KEY_PATH",33264,KEY_SHA,false)?;
    let mut c=Held::open("NIPOPOW_HISTORICAL50_COMMITMENT_PATH",384,C_SHA,false)?;
    let mut meta=Held::open("NIPOPOW_HISTORICAL50_KEY_METADATA_PATH",40,META_SHA,false)?;
    let dir=output_dir()?;let source=PackedFile::open_with_limit(&pack.path,32,32)?;pack.check()?;
    let bound=Historical50BoundSource::new(&source)?;let actual_source_digest=h41_hex(&bound.digest);let binding_io=bound.io;
    let input=raw_input(&raw.bytes)?;
    let public=Public{headers:3073,root:input.root(),total:input.total_be28(),tip:ergo_header_core::blake2b256(input.raw(3073)?),tip_time:input.timestamp(3073)?};
    let a=Historical47Admission::new(&historical47_frame(&public)?,&key.bytes,&meta.bytes,&c.bytes)?;
    times[0]=ns(started)?;t.mark("admission","end")?;
    t.mark("producer","begin")?;let started=Instant::now();let sub=Instant::now();
    let graph=Graph::new(&a)?;crate::packed_owner_assembly::validate_native_plan_input(&graph.consumer.parent,&input)?;drop(input);
    let(context,_)=ProofContext::historical_h12(&graph.consumer,&a)?;subtimes[0]=ns(sub)?;
    let normal=context.transcript(role,&a.key,&a.commitment);
    let nofault=context.historical50_control_prefix(role,&a.key,&a.commitment,Historical50PrefixFault::NoFault)?;
    need(snapshot(&normal)?==snapshot(&nofault)?&&counters(&normal)[..2]==[0,0],"historical50 preproof NoFault freshness")?;drop(normal);drop(nofault);
    // Only live caller-owned state is additive. No exports exist during the
    // heavy producer; its returned proof and normalized templates are charged
    // by the unchanged kernel. Vendor/graph heaps stay inside the whole Job.
    let caller_heap=h50_sum(&[raw.heap()?,pack.heap()?,key.heap()?,c.heap()?,meta.heap()?,dir.capacity(),actual_source_digest.capacity(),
        std::mem::size_of::<std::sync::Mutex<packed::PackedIoSnapshot>>()+2*std::mem::size_of::<usize>()])?;
    let caller_inline=h50_sum(&[5*std::mem::size_of::<Held>(),std::mem::size_of_val(&source),std::mem::size_of_val(&bound),
        std::mem::size_of_val(&public),std::mem::size_of_val(&dir),std::mem::size_of_val(&actual_source_digest),
        std::mem::size_of_val(&times),std::mem::size_of_val(&subtimes),std::mem::size_of_val(&binding_io)])?;
    let buffers=Historical50Buffers{caller_inline,caller_heap,observer_inline:std::mem::size_of::<Trace>(),export_retained:0};
    capability_controls(&context,&bound,&a,role,buffers)?;
    let sub=Instant::now();let produced=prove_role_historical50(&context,&bound,&a,role,buffers)?;subtimes[1]=ns(sub)?;
    producer_stats(&produced)?;let engine=engine(&produced)?;
    let Historical50Produced{proof,raw_claim,common_claim:sender,counters:sender_counts,continuation:sender_next,io:proof_io,..}=produced;
    let raw_claim=Claim{point:raw_claim.point,value:raw_claim.value};
    need(common_projection(role,&raw_claim)?==sender,"historical50 actual point projection")?;
    let proof_bytes=gkr::encode_proof(&proof)?;need(proof_bytes.len()==extent,"historical50 proof extent")?;drop(proof);
    times[1]=ns(started)?;t.mark("producer","end")?;drop(context);drop(graph);
    need(graph_counts()==[0,1,1,1],"historical50 producer dropped")?;t.mark("producer_drop","end")?;
    t.mark("export","begin")?;let started=Instant::now();
    write_new(&dir.join("statement.bin"),&a.frame)?;write_new(&dir.join("commitment.bin"),&a.commitment)?;write_new(&dir.join(proof_name),&proof_bytes)?;roster(&dir,role,false)?;
    let frame=read_export(&dir,role,"statement.bin",&a.frame)?;let commitment=read_export(&dir,role,"commitment.bin",&a.commitment)?;
    let packet=RoleProof{role,bytes:read_export(&dir,role,proof_name,&proof_bytes)?};drop(proof_bytes);times[2]=ns(started)?;t.mark("export","end")?;
    t.mark("consumer","begin")?;let started=Instant::now();let sub=Instant::now();
    let receiver_a=Historical47Admission::new(&frame,&key.bytes,&meta.bytes,&commitment)?;let graph=Graph::new(&receiver_a)?;
    let(context,_)=ProofContext::historical_h12(&graph.consumer,&receiver_a)?;subtimes[2]=ns(sub)?;
    let sub=Instant::now();let verified=context.verify_role(&packet,&receiver_a.key,&receiver_a.commitment)
        .map_err(|e|format!("historical50 receiver {:?}",e.stage))?;subtimes[3]=ns(sub)?;
    need(verified.role==role&&verified.observation.canonical_decode&&verified.observation.verifier_entered
        &&verified.observation.prefix_challenges==0&&verified.observation.prefix_raw_queries==0,"historical50 actual receiver")?;
    need(verified.claim==sender&&verified.counters==sender_counts&&verified.continuation==sender_next,"historical50 sender receiver identity")?;
    source.reset_io_metrics();let sub=Instant::now();let mle=source.evaluate(&verified.claim.point)?;subtimes[4]=ns(sub)?;
    let mle_io=source.io_metrics_snapshot();need(mle==verified.claim.value,"historical50 held PACK MLE")?;receiver_controls(&context,&packet,&receiver_a,&verified)?;
    times[3]=ns(started)?;t.mark("consumer","end")?;drop(context);drop(graph);
    need(graph_counts()==[0,1,2,2],"historical50 receiver dropped")?;t.mark("consumer_drop","end")?;
    t.mark("public_bindings","begin")?;let started=Instant::now();public_controls(&public,&packet,&key.bytes,&meta.bytes,&c.bytes)?;
    times[4]=ns(started)?;t.mark("public_bindings","end")?;
    let mut data=ResultData{role,public,frame_sha:h41_sha(&frame)?,proof_sha:h41_sha(&packet.bytes)?,raw:raw_claim,sender,receiver:verified.claim,
        sender_counts,receiver_counts:verified.counters,sender_next,receiver_next:verified.continuation,
        prefix:[verified.observation.prefix_challenges,verified.observation.prefix_raw_queries,verified.observation.prefix_bytes],mle,times,subtimes,
        actual_source_digest,binding_io,proof_io,mle_io,graphs:graph_counts(),engine};
    t.mark("claim_controls","begin")?;let started=Instant::now();claim_controls(&data)?;times[5]=ns(started)?;t.mark("claim_controls","end")?;
    t.mark("custody","begin")?;let started=Instant::now();raw.rehash(false)?;pack.rehash(true)?;key.rehash(false)?;c.rehash(false)?;meta.rehash(false)?;
    need(graph_counts()==[0,1,6,6],"historical50 final graph ledger")?;times[6]=ns(started)?;t.mark("custody","end")?;
    t.mark("result","begin")?;let started=Instant::now();data.times=times;
    let result=serde_json::to_vec(&report(&data)?).map_err(|_|"historical50 report encoding")?;need(result.len()<=16384,"historical50 report cap")?;
    write_new(&dir.join("result.json"),&result)?;roster(&dir,role,true)?;
    let replay=read_export(&dir,role,"result.json",&result)?;let replay:serde_json::Value=serde_json::from_slice(&replay).map_err(|_|"historical50 result replay")?;result_claims(&replay,&data)?;
    read_export(&dir,role,"statement.bin",&frame)?;read_export(&dir,role,"commitment.bin",&commitment)?;read_export(&dir,role,proof_name,&packet.bytes)?;
    let result_export_ns=ns(started)?;t.mark("result","end")?;
    let envelope=serde_json::to_vec(&serde_json::json!({"report":replay,"result_export_ns":result_export_ns})).map_err(|_|"historical50 envelope encoding")?;
    need(envelope.len()<=16384,"historical50 envelope cap")?;t.mark("complete","end")?;
    println!("\nHISTORICAL32_ROLE135_50 {}",String::from_utf8(envelope).map_err(|_|"historical50 report UTF8")?);Ok(())
}
fn rejected<T>(value:Result<T,String>,message:&str)->Result<(),String>{
    need(value.err().as_deref()==Some(message),"historical50 ordinary failure attribution")
}
fn binding_controls()->Result<(),String>{
    let dir=std::env::temp_dir();generic37_metadata(&dir,true)?;
    let paths=[dir.join(format!("historical50-reader-a-{}.bin",std::process::id())),dir.join(format!("historical50-reader-b-{}.bin",std::process::id()))];
    let a:Vec<u8>=(0..96u8).collect();let mut b=a.clone();b[47]^=1;let golden:[u8;32]=Blake2b::<U32>::digest(&a).into();
    let mut created=Vec::new();let result=(||->Result<(),String>{
        for(path,bytes)in paths.iter().zip([&a,&b]){let mut f=OpenOptions::new().write(true).create_new(true).open(path).map_err(|_|"historical50 fixture create")?;
            created.push(path.clone());f.write_all(bytes).map_err(|_|"historical50 fixture write")?;f.sync_all().map_err(|_|"historical50 fixture sync")?;}
        let read=|path:&Path|->Result<[u8;32],String>{let mut f=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|_|"historical50 fixture open")?;
            need(f.metadata().map_err(|_|"historical50 fixture metadata")?.len()==96,"historical50 fixture extent")?;
            historical50_hash_windows(3,32,golden,|_|{let mut bytes=vec![0;32];f.read_exact(&mut bytes).map_err(|_|"historical50 fixture read")?;Ok(bytes)})};
        need(read(&paths[0])?==golden,"historical50 actual small reader golden")?;
        rejected(read(&paths[1]),"historical50 actual reader digest")?;
        rejected(historical50_hash_windows(0,32,golden,|_|panic!("closed reader must not run")),"historical50 reader binding bounds")?;
        rejected(historical50_hash_windows(3,32,golden,|_|Ok(vec![0;31])),"historical50 reader window")?;
        Ok(())})();
    let mut cleanup=Ok(());for path in created{if std::fs::remove_file(path).is_err(){cleanup=Err("historical50 fixture cleanup".into());}}result.and(cleanup)
}
fn admission_controls(public:&Public)->Result<(),String>{
    let graph=Graph::from_public(public)?;let parts=RelationParts::compile(graph.consumer.layout_refs(),HeightBinding::HistoricalDiagnostic)?;
    let frame=historical47_frame(public)?;
    for role in [3,5,1]{
        let admit=|refs:RelationRefs<'_, '_>,size,log,bytes:&[u8]|historical50_admit(&graph.consumer,refs,role,size,log,bytes);
        admit(parts.refs(),1usize<<32,32,&frame)?;
        let mut refs=parts.refs();refs.mode=HeightBinding::LegacyN3N4;
        rejected(admit(refs,1usize<<32,32,&frame),"admission47 historical mode")?;
        for size in [(1usize<<32)-1,(1usize<<32)+1]{rejected(admit(parts.refs(),size,32,&frame),"historical50 closed admission")?;}
        rejected(admit(parts.refs(),1usize<<32,22,&frame),"admission47 closed policy")?;
        let mut bad=frame.clone();bad[139]^=1;rejected(admit(parts.refs(),1usize<<32,32,&bad),"historical50 closed admission")?;
        for i in 0..7{let mut g=parts.geometry.clone();g.input_bits[i]+=1;let mut refs=parts.refs();refs.geometry=&g;
            need(admit(refs,1usize<<32,32,&frame).is_err(),"historical50 geometry input mutant")?;
            let mut g=parts.geometry.clone();g.row_bits[i]+=1;let mut refs=parts.refs();refs.geometry=&g;
            need(admit(refs,1usize<<32,32,&frame).is_err(),"historical50 geometry row mutant")?;}
    }
    for role in [0,2,4,6,7]{rejected(historical50_admit(&graph.consumer,parts.refs(),role,1usize<<32,32,&frame),"historical50 closed admission")?;}
    {let foreign=WorkTreeHistoryPlan::compile(5,3,[1;32],[0;28])?;let mut refs=parts.refs();refs.layouts.parent=&foreign;
        rejected(historical50_admit(&graph.consumer,refs,3,1usize<<32,32,&frame),"admission47 parent identity")?;}
    // The real point adapter supplies the same fixed seven bank bits. All
    // raw coordinates and every inserted bank coordinate are isolated here.
    let point=PointRole::new(&graph.consumer,&parts.geometry)?;
    for owner in [0usize,3071,3072,4095]{let mut emitted=0usize;
        let counts=parts.daa.visit_header_terms(owner as u64,|term|{
            need((owner*(1usize<<19)..(owner+1)*(1usize<<19)).contains(&term.row)
                &&(owner*(1usize<<20)..(owner+1)*(1usize<<20)).contains(&term.gate.left)
                &&(owner*(1usize<<20)..(owner+1)*(1usize<<20)).contains(&term.gate.right),"historical50 representative term window")?;
            emitted=emitted.checked_add(1).ok_or("historical50 representative count overflow")?;Ok(())})?;
        need(counts.emitted==if owner==3072{388369}else{396561}&&emitted==counts.emitted&&counts.omitted_worktree==78194
            &&counts.omitted_mature_a4==0&&counts.omitted_short_a4==if owner==3072{8192}else{0},"historical50 representative group/padding census")?;}
    let raw=Claim{point:(1..=25).map(|n|Fr::from(n as u64)).collect(),value:Fr::one()};
    let projected=common_projection(3,&raw)?;need(point.project(&raw.point)?==projected.point,"historical50 actual projection golden")?;
    for i in 0..25{let mut bad=raw.clone();bad.point[i]+=Fr::one();let p=common_projection(3,&bad)?;
        let j=if i<13{i}else{i+7};let mut expected=projected.point.clone();expected[j]+=Fr::one();
        need(p.point==expected&&p.point==point.project(&bad.point)?,"historical50 raw coordinate projection")?;}
    for i in 13..20{let mut bad=projected.point.clone();bad[i]+=Fr::one();need(bad!=point.project(&raw.point)?,"historical50 inserted coordinate projection")?;}
    for role in [3,1]{let terms=role_shape(role)?.3;historical50_baseline_complete(role,4096,terms)?;
        for(next,total)in [(0,0),(4095,terms),(4096,terms-1),(4096,terms+1),(4097,terms)]{
            let mut t=Transcript::new(b"historical50-baseline-control");let before=snapshot(&t)?;
            let attempt=(||->Result<(),String>{historical50_baseline_complete(role,next,total)?;t.append_bytes(b"binder",b"must-not-run");Ok(())})();
            rejected(attempt,"historical50 incomplete baseline")?;need(snapshot(&t)?==before,"historical50 incomplete baseline before FS")?;}}
    drop(parts);drop(graph);need(graph_counts()==[0,1,1,1],"historical50 ordinary graph dropped")
}
fn binding_shape_currentness()->Result<(),String>{
    // These bytes close the private Binding shape without exporting a new DAA
    // API or pretending that a reconstructed JSON value is the real Binding.
    need(h41_sha(include_bytes!("daa_work_actions.rs"))?=="F2B64E6FF7C426797E7E4B6E76DC36DE18CDB1B87DC500B01EE63A1F86569354"
        &&h41_sha(include_bytes!("work_tree_work.rs"))?=="F8F071C73405ED0CA430C38374212FE30089DE6E9BDA404D67D2329F190B0FBB","historical50 binding derivation source drift")?;
    let mut skeleton=serde_json::json!({"schema":"","headers":0,"slot_log":0,"slots":0,"row_log":0,"input_log":0,
        "coordinates":"","work_wires":vec![0;224],"work_schema":"","native_work_sha256":"","canonical_nbits_required":false,
        "genesis_id":vec![0;32],"genesis_nbits":0,"constants":vec![[0,0];3],"singleton_height":0,"short_owners":vec![0;7],"mature_schedule":vec![0;3]});
    let bytes=serde_json::to_vec(&skeleton).map_err(|_|"historical50 binding skeleton")?;
    need(bytes.len()==835&&835+279*19+236==H50_ROLE1_NUMERIC_BINDING_SERIALIZED_MAX
        &&3*H50_ROLE1_NUMERIC_BINDING_SERIALIZED_MAX==H50_ROLE1_NUMERIC_BINDING_HELPER_BOUND,"historical50 binding derived scratch")?;
    // The actual serializer path is to_vec(Vec::with_capacity(128)); this
    // maximum fixture separates serialized length from its logical capacity.
    fn max_numbers(v:&mut serde_json::Value){match v{serde_json::Value::Number(_)=>*v=serde_json::json!(u64::MAX),
        serde_json::Value::Array(a)=>for x in a{max_numbers(x)},serde_json::Value::Object(o)=>for x in o.values_mut(){max_numbers(x)},_=>()}}
    max_numbers(&mut skeleton);for(k,n)in[("schema",35),("coordinates",111),("work_schema",26),("native_work_sha256",64)]{skeleton[k]=serde_json::json!("x".repeat(n));}
    let encoded=serde_json::to_vec(&skeleton).map_err(|_|"historical50 binding maximum")?;
    need(encoded.len()==6372&&encoded.capacity()<12744,"historical50 binding serialization maximum")?;
    need(h50_sum(&[usize::MAX,1]).is_err()&&h50_mul(usize::MAX,2).is_err(),"historical50 checked capacity arithmetic")?;
    for role in [3,5,1]{let overhead=historical50_constructor_bound(role,0)?;
        need(historical50_constructor_bound(role,H50_COMPONENT_LIMIT-overhead)?==H50_COMPONENT_LIMIT,"historical50 constructor exact bound")?;
        rejected(historical50_constructor_bound(role,H50_COMPONENT_LIMIT-overhead+1),"historical50 constructor capacity")?;
        need(historical50_constructor_bound(role,usize::MAX).is_err(),"historical50 constructor overflow")?;}Ok(())
}
fn maximal_engine(role:usize)->Result<serde_json::Value,String>{
    let m=u64::MAX;let z=usize::MAX;
    let mut memory=serde_json::to_value(Historical50Memory::default()).map_err(|_|"historical50 memory fixture")?;
    for v in memory.as_object_mut().ok_or("historical50 memory fixture map")?.values_mut(){if v.is_number(){*v=serde_json::json!(m);}}
    if role==5{
        use crate::segment_adjacency::linear_for_test::{Stats,SupportStats};
        let s=Stats{phase_ns:[m;4],read_calls:[m;4],reconstructed_fields:[m;4],direct_vector_capacity_peak_bytes:[z;4],
            helper_scratch_bound_peak_bytes:[z;4],combined_bound_peak_bytes:[z;4],preflight_bound_bytes:z,scoped_limit_bytes:z,
            retained_capacity_bytes:z,fixed_typed_bound_bytes:z,high_fold_coordinates:[z;2],initial_padding_chunks:z,line_input_fields:z,helper_bounds_measured:false};
        let support=SupportStats{chunks_per_owner:z,parent_chunk_mask:u16::MAX,digest_chunk_mask:u16::MAX,support_chunks:[z;2],
            low_round_read_calls:[m;2],low_round_skipped_chunks:[m;2],control_capacity_bytes:z};
        Ok(serde_json::json!({"kind":"adjacency-sparse-support","memory":memory,"grouped":null,"boolean_u":null,
            "linear":serde_json::to_value(s).map_err(|_|"historical50 linear maximum")?,"support":serde_json::to_value(support).map_err(|_|"historical50 support maximum")?,
            "grouped_preflight":vec![z;2],"baseline_owners":m,"baseline_terms":m,"progress_events":m}))
    }else{
        let mut g=sparse_stream_roster::GroupedVStats::default();g.group_count=2;g.group_owner_counts=vec![z;2];g.group_term_counts=vec![z;2];
        g.group_weight_sums=vec![Fr::one();2];g.group_d_local_contributions=vec![Fr::one();2];g.baseline_term_callbacks=z;g.template_term_count=z;
        g.template_capacity_bytes=z;g.bank_term_callbacks=z;g.handoff_term_callbacks=z;g.grouped_state_peak_capacity_bytes=z;g.local_rounds=z;
        g.owner_handoff_count=z;g.baseline_elapsed_ns=m;g.bank_build_elapsed_ns=m;g.local_v_elapsed_ns=m;g.owner_handoff_elapsed_ns=m;
        let u=sparse_stream_roster::BooleanUPreweightStats{prefix_builds:z,shared_term_iterations:z,owner_term_selections:z,boolean_checked_loads:z,
            boolean_checked_fields:z,zero_anchor_sweep_skipped:false,preweight_entry_size_bytes:z,preweight_peak_capacity_bytes:z,u_state_peak_capacity_bytes:z,
            u_preflight_capacity_bound_bytes:z,u_prefix_preweight_elapsed_ns:m,u_owner_selection_elapsed_ns:m,u_x_fold_elapsed_ns:m,u_phase_peak_capacity_bytes:[z;6]};
        Ok(serde_json::json!({"kind":"boolean-grouped","memory":memory,"grouped":grouped_json(&g)?,"boolean_u":boolean_json(&u),
            "linear":null,"support":null,"grouped_preflight":vec![z;2],"baseline_owners":m,"baseline_terms":m,"progress_events":m}))
    }
}
fn ordinary()->Result<(),String>{
    binding_controls()?;binding_shape_currentness()?;sparse_stream_roster::historical50_resource_controls_for_test()?;
    crate::segment_adjacency::linear_for_test::historical50_resource_controls_for_test()?;
    let p=Public{headers:3073,root:[2;32],total:[3;28],tip:[4;32],tip_time:i64::MIN};admission_controls(&p)?;
    let frame=historical47_frame(&p)?;need(frame.len()==571&&historical47_frame(&historical47_decode(&frame)?)?==frame,"historical50 frame roundtrip")?;
    let m=u64::MAX;let io=packed::PackedIoSnapshot{read_calls:m,read_bytes:m,read_ns:m as u128,write_calls:m,write_bytes:m,write_ns:m as u128,sync_calls:m,sync_ns:m as u128};
    for role in [3,5,1]{let(width,extent,_,_)=role_shape(role)?;let bytes=vec![0u8;extent];let proof=gkr::decode_dimensions(&[width],&bytes)?;
        need(proof.layers.len()==1&&proof.layers[0].rounds.len()==2*width&&proof.layers[0].line_coefficients.len()==width+1
            &&gkr::encode_proof(&proof)?==bytes,"historical50 codec shape fixture")?;
        for n in [extent-1,extent+1]{need(gkr::decode_dimensions(&[width],&vec![0;n]).is_err(),"historical50 codec extent negative")?;}
        let mut bad=bytes;bad[..32].fill(255);need(gkr::decode_dimensions(&[width],&bad).is_err(),"historical50 codec canonical negative")?;
        let raw=Claim{point:vec![Fr::one();width],value:Fr::one()};let common=common_projection(role,&raw)?;
        let d=ResultData{role,public:p.clone(),frame_sha:"F".repeat(64),proof_sha:"F".repeat(64),raw:Claim{point:raw.point,value:raw.value},
            sender:common.clone(),receiver:common,sender_counts:[m;3],receiver_counts:[m;3],sender_next:Fr::one(),receiver_next:Fr::one(),prefix:[m;3],mle:Fr::one(),
            times:[m;7],subtimes:[m;5],actual_source_digest:"f".repeat(64),binding_io:io,proof_io:io,mle_io:io,graphs:[m;4],engine:maximal_engine(role)?};
        let v=report(&d)?;let result=serde_json::to_vec(&v).map_err(|_|"historical50 maximum report")?;
        let envelope=serde_json::to_vec(&serde_json::json!({"report":v,"result_export_ns":m})).map_err(|_|"historical50 maximum envelope")?;
        need(result.len()<=16384&&envelope.len()<=16384&&envelope.len()+8192<=65536,"historical50 maximal serializers")?;claim_controls(&d)?;
    }
    let mut v=serde_json::json!({"a":0});rejected(merge(&mut v,serde_json::json!({"a":1})),"historical50 duplicate report key")?;
    need(graph_counts()==[0,1,1,1],"historical50 ordinary graph closure")
}
#[test]
fn historical50_ordinary()->Result<(),String>{ordinary()}
fn native(role:usize){
    let mut t=Trace{start:Instant::now(),next:0};let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(&mut t,role)));
    let error=match result{Ok(Ok(()))=>return,Ok(Err(e))=>e,Err(_)=>"historical50 panic".into()};
    let reason:String=error.chars().filter(|c|c.is_ascii_graphic()||*c==' ').take(160).collect();
    eprintln!("HISTORICAL32_ROLE135_50_HOLD {} {} {reason}",t.next,t.start.elapsed().as_nanos());panic!("historical50 HOLD");
}
#[test]
#[ignore]
fn historical50_role3(){native(3)}
#[test]
#[ignore]
fn historical50_role5(){native(5)}
#[test]
#[ignore]
fn historical50_role1(){native(1)}

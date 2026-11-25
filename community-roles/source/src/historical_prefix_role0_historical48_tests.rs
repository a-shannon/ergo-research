//! One genuine Historical H12 role0 producer/receiver join; no PCS operation.
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
const MEMBERS:[(&str,usize);4]=[("statement.bin",571),("commitment.bin",384),("role-0.gkr",7264),("result.json",16384)];
fn need(ok:bool,error:&str)->Result<(),String>{if ok{Ok(())}else{Err(error.into())}}
fn ns(start:Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"historical48 clock".into())}
fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
fn snapshot(t:&Transcript)->Result<([u64;3],Fr),String>{Ok((counters(t),t.clone().try_challenge_scalar(b"historical48-prefix-control-v1")?))}
fn synthetic_c()->Result<Vec<u8>,String>{
    pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero()))
}

// Held/named Windows identity matches the reviewed47 ABI. Access time is excluded.
#[repr(C)]
#[derive(Default,PartialEq,Eq)]
struct Identity{attributes:u32,created:[u32;2],accessed:[u32;2],written:[u32;2],volume:u32,
    high:u32,low:u32,links:u32,index_high:u32,index_low:u32}
fn identity(file:&File)->Result<Identity,String>{
    #[link(name="kernel32")]extern "system"{fn GetFileInformationByHandle(h:*mut std::ffi::c_void,p:*mut Identity)->i32;}
    let mut id=Identity::default();
    // BY_HANDLE_FILE_INFORMATION layout; the borrowed File outlives this call.
    if unsafe{GetFileInformationByHandle(file.as_raw_handle(),&mut id)}==0{return Err("historical48 file identity".into());}
    need(id.attributes&0x410==0&&id.links==1,"historical48 ordinary single-link file")?;id.accessed=[0;2];Ok(id)
}
struct Held{file:File,path:PathBuf,id:Identity,bytes:Vec<u8>,digest:String}
impl Held{
    fn open(env:&str,size:usize,expected:&str,pack:bool)->Result<Self,String>{
        let path=PathBuf::from(std::env::var_os(env).ok_or("historical48 missing input")?);
        need(path.is_absolute()&&path.as_os_str().len()<=1024,"historical48 input path")?;
        let md=generic37_metadata(&path,false)?;need(md.len()==size as u64,"historical48 input extent")?;
        let mut file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|_|"historical48 input open")?;
        let id=identity(&file)?;need((u64::from(id.high)<<32)|u64::from(id.low)==size as u64,"historical48 held extent")?;
        let mut bytes=Vec::new();let digest;
        if pack{let mut state=Blake2b::<U32>::new();let mut scratch=[0u8;65536];let mut total=0usize;
            loop{let n=file.read(&mut scratch).map_err(|_|"historical48 PACK read")?;if n==0{break;}
                total=total.checked_add(n).ok_or("historical48 PACK overflow")?;
                need(total<=size,"historical48 PACK trailing")?;state.update(&scratch[..n]);}
            need(total==size,"historical48 PACK truncated")?;digest=h41_hex(&state.finalize());
        }else{need(size<=869449,"historical48 bounded input")?;bytes.resize(size,0);
            file.read_exact(&mut bytes).map_err(|_|"historical48 input read")?;
            let mut tail=[0;1];need(file.read(&mut tail).map_err(|_|"historical48 input tail")?==0,"historical48 input trailing")?;
            digest=h41_sha(&bytes)?;}
        need(digest==expected,"historical48 input digest")?;
        let held=Self{file,path,id,bytes,digest};held.check()?;Ok(held)
    }
    fn check(&self)->Result<(),String>{
        generic37_metadata(&self.path,false)?;need(identity(&self.file)?==self.id,"historical48 held custody")?;
        let named=OpenOptions::new().read(true).share_mode(1).open(&self.path).map_err(|_|"historical48 custody reopen")?;
        need(identity(&named)?==self.id,"historical48 named custody")
    }
    fn rehash(&mut self,pack:bool)->Result<(),String>{
        self.check()?;self.file.seek(SeekFrom::Start(0)).map_err(|_|"historical48 custody seek")?;
        if pack{let mut state=Blake2b::<U32>::new();let mut scratch=[0u8;65536];let mut total=0usize;
            loop{let n=self.file.read(&mut scratch).map_err(|_|"historical48 custody read")?;if n==0{break;}
                total=total.checked_add(n).ok_or("historical48 custody overflow")?;
                need(total<=536870912,"historical48 custody extent")?;state.update(&scratch[..n]);}
            need(total==536870912&&h41_hex(&state.finalize())==self.digest,"historical48 PACK custody hash")?;
        }else{let mut actual=vec![0;self.bytes.len()];self.file.read_exact(&mut actual).map_err(|_|"historical48 custody read")?;
            let mut tail=[0;1];need(self.file.read(&mut tail).map_err(|_|"historical48 custody tail")?==0
                &&actual==self.bytes&&h41_sha(&actual)?==self.digest,"historical48 buffer custody")?;}
        self.check()
    }
}
fn raw_input(bytes:&[u8])->Result<crate::packed_owner_assembly::NativePrefix,String>{
    let mut at=0usize;let mut raws=Vec::with_capacity(3073);
    for _ in 0..3073{let n=u32::from_le_bytes(historical47_take(bytes,&mut at)?) as usize;
        need((1..=514).contains(&n),"historical48 RAW record extent")?;
        let end=at.checked_add(n).ok_or("historical48 RAW overflow")?;
        raws.push(bytes.get(at..end).ok_or("historical48 RAW truncated")?.to_vec());at=end;}
    need(at==bytes.len(),"historical48 RAW trailing")?;
    crate::packed_owner_assembly::NativePrefix::from_raw_iter(3073,raws.into_iter().map(Ok))
}

// Private streaming factor. Only bind_actual_source selects the runtime shape;
// ordinary controls supply small real File readers to falsify digest binding.
fn hash_windows(count:usize,width:usize,expected:&str,
    mut read:impl FnMut(usize)->Result<Vec<u8>,String>)->Result<String,String>{
    need(count>0&&count<=4096&&width>0&&width<=131072
        &&count.checked_mul(width).is_some_and(|n|n<=536870912),"historical48 binding window policy")?;
    need(expected.len()==64&&expected.bytes().all(|b|b.is_ascii_digit()||(b'a'..=b'f').contains(&b)),
        "historical48 binding digest policy")?;
    let mut state=Blake2b::<U32>::new();
    for owner in 0..count{let bytes=read(owner)?;
        need(bytes.len()==width&&bytes.capacity()==width,"historical48 binding window extent")?;
        state.update(&bytes);drop(bytes);}
    let observed=h41_hex(&state.finalize());
    need(observed==expected,"historical48 actual source digest")?;Ok(observed)
}
fn bind_actual_source(source:&PackedFile)->Result<String,String>{
    // This exact object is kept for both the prover and MLE. PackedFile opens
    // with FILE_SHARE_READ only; the actual reader cannot be written/deleted.
    let view=source.native_role0_view()?;view.require_same_source(source)?;
    source.reset_io_metrics();
    let digest=hash_windows(4096,131072,PACK_BLAKE,|owner|Ok(view.read_copy(owner)?.into_bytes()))?;
    let io=source.io_metrics_snapshot();
    need(io.read_calls==4096&&io.read_bytes==536870912&&io.write_calls==0&&io.sync_calls==0,
        "historical48 actual source scan")?;Ok(digest)
}
fn binding_controls()->Result<(),String>{
    let dir=std::env::temp_dir();generic37_metadata(&dir,true)?;
    let paths=[dir.join(format!("historical48-reader-a-{}.bin",std::process::id())),
        dir.join(format!("historical48-reader-b-{}.bin",std::process::id()))];
    let a:Vec<u8>=(0..96u8).collect();let mut b=a.clone();b[47]^=1;
    let golden=h41_hex(&Blake2b::<U32>::digest(&a));let mut created=Vec::new();
    let result=(||->Result<(),String>{
        for(path,bytes)in paths.iter().zip([&a,&b]){
            let mut file=OpenOptions::new().write(true).create_new(true).open(path).map_err(|_|"historical48 binding fixture create")?;
            created.push(path.clone());file.write_all(bytes).map_err(|_|"historical48 binding fixture write")?;
            file.sync_all().map_err(|_|"historical48 binding fixture sync")?;}
        let read_file=|path:&Path|->Result<String,String>{
            let mut file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|_|"historical48 binding fixture open")?;
            need(file.metadata().map_err(|_|"historical48 binding fixture metadata")?.len()==96,"historical48 binding fixture extent")?;
            hash_windows(3,32,&golden,|_|{let mut bytes=vec![0;32];
                file.read_exact(&mut bytes).map_err(|_|"historical48 binding fixture read")?;Ok(bytes)})
        };
        need(read_file(&paths[0])?==golden,"historical48 binding golden")?;
        need(read_file(&paths[1]).err().as_deref()==Some("historical48 actual source digest"),
            "historical48 different reader attribution")
    })();
    // Remove only files whose exclusive creation succeeded, including failures.
    // A pre-existing name is never owned, overwritten or removed by this test.
    let mut cleanup=Ok(());for path in created{if std::fs::remove_file(path).is_err(){cleanup=Err("historical48 binding fixture cleanup".into());}}
    result.and(cleanup)
}

std::thread_local!{static GRAPHS:std::cell::Cell<[u64;4]>=const{std::cell::Cell::new([0;4])};}
fn graph_counts()->[u64;4]{GRAPHS.with(|v|v.get())}
struct Graph{consumer:Consumer}
impl Graph{
    fn new(a:&Historical47Admission)->Result<Self,String>{
        need(graph_counts()[0]==0,"historical48 concurrent graph")?;
        let consumer=historical47_consumer(a)?;
        GRAPHS.with(|v|{let mut c=v.get();c[0]+=1;c[1]=c[1].max(c[0]);c[2]+=1;v.set(c)});
        Ok(Self{consumer})
    }
}
impl Drop for Graph{
    fn drop(&mut self){GRAPHS.with(|v|{let mut c=v.get();assert_eq!(c[0],1);c[0]-=1;c[3]+=1;v.set(c)})}
}
fn output_dir()->Result<PathBuf,String>{
    let path=PathBuf::from(std::env::var_os("NIPOPOW_HISTORICAL48_OUTPUT_DIR").ok_or("historical48 missing output")?);
    need(path.is_absolute()&&path.as_os_str().len()<=1024,"historical48 output path")?;
    generic37_metadata(&path,true)?;
    need(path.read_dir().map_err(|_|"historical48 output scan")?.next().is_none(),"historical48 output not empty")?;Ok(path)
}
fn roster(dir:&Path,complete:bool)->Result<(),String>{
    generic37_metadata(dir,true)?;let mut names=Vec::with_capacity(4);
    for entry in dir.read_dir().map_err(|_|"historical48 output scan")?{
        need(names.len()<4,"historical48 output roster")?;
        let entry=entry.map_err(|_|"historical48 output entry")?;generic37_metadata(&entry.path(),false)?;
        names.push(entry.file_name().into_string().map_err(|_|"historical48 output name")?);}
    names.sort();let mut expected:Vec<_>=MEMBERS[..if complete{4}else{3}].iter().map(|v|v.0.to_owned()).collect();expected.sort();
    need(names==expected,"historical48 output roster")
}
fn read_export(dir:&Path,name:&str,expected:&[u8])->Result<Vec<u8>,String>{
    let bound=MEMBERS.iter().find(|v|v.0==name).ok_or("historical48 export name")?.1;
    need(expected.len()<=bound&&(name=="result.json"||expected.len()==bound),"historical48 export extent")?;
    let bytes=generic37_read(&dir.join(name),expected.len())?;
    need(bytes==expected,"historical48 export bytes")?;Ok(bytes)
}
fn fr_from_json(v:&serde_json::Value)->Result<Fr,String>{
    let s=v.as_str().ok_or("historical48 scalar type")?;
    need(s.len()==64&&s.bytes().all(|b|b.is_ascii_digit()||(b'a'..=b'f').contains(&b)),"historical48 scalar encoding")?;
    let mut bytes=[0u8;32];for(i,pair)in s.as_bytes().chunks_exact(2).enumerate(){
        bytes[i]=u8::from_str_radix(std::str::from_utf8(pair).map_err(|_|"historical48 scalar UTF8")?,16).map_err(|_|"historical48 scalar hex")?;}
    let value=Fr::deserialize_compressed(&bytes[..]).map_err(|_|"historical48 scalar canonical")?;
    let mut encoded=Vec::new();value.serialize_compressed(&mut encoded).map_err(|_|"historical48 scalar encode")?;
    need(encoded==bytes,"historical48 scalar roundtrip")?;Ok(value)
}
fn claim_from_json(v:&serde_json::Value)->Result<Claim,String>{
    let o=v.as_object().ok_or("historical48 claim type")?;
    need(o.len()==2&&o.contains_key("point")&&o.contains_key("value"),"historical48 claim keys")?;
    let p=o["point"].as_array().ok_or("historical48 claim point")?;need(p.len()==32,"historical48 claim dimension")?;
    Ok(Claim{point:p.iter().map(fr_from_json).collect::<Result<Vec<_>,_>>()?,value:fr_from_json(&o["value"])?})
}
fn close_claim(v:&serde_json::Value,verified:&Claim,mle:Fr)->Result<(),String>{
    let actual=claim_from_json(v)?;
    need(actual==*verified&&actual.value==mle,"historical48 reported claim/MLE")
}
fn verify_failure(result:Result<VerifiedRole,RoleFailure>,stage:RoleStage,entered:bool)->Result<(),String>{
    let error=match result{Ok(_)=>return Err("historical48 negative accepted".into()),Err(e)=>e};
    need(error.role==0||stage==RoleStage::Shape,"historical48 failure role")?;
    need(error.stage==stage&&error.observation.verifier_entered==entered,"historical48 negative stage")?;
    need(error.observation.canonical_decode==entered,"historical48 negative canonical attribution")
}
fn receiver_controls(context:&ProofContext<'_>,packet:&RoleProof,a:&Historical47Admission,positive:&VerifiedRole)->Result<(),String>{
    let normal=context.transcript(0,&a.key,&a.commitment);
    let nofault=context.historical48_control_prefix(0,&a.key,&a.commitment,Historical48PrefixFault::NoFault)?;
    need(snapshot(&normal)?==snapshot(&nofault)?,"historical48 NoFault prefix identity")?;
    let plain=context.verify_role_historical48_control(packet,&a.key,&a.commitment,Historical48PrefixFault::NoFault)
        .map_err(|e|format!("historical48 NoFault receiver {:?}",e.stage))?;
    need(plain.claim==positive.claim&&plain.counters==positive.counters&&plain.continuation==positive.continuation,
        "historical48 NoFault receiver identity")?;
    for size in [7263,7265]{let mut bad=packet.clone();bad.bytes.resize(size,0);
        verify_failure(context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Shape,false)?;}
    let mut bad=packet.clone();bad.role=7;
    verify_failure(context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Shape,false)?;
    let key22=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    verify_failure(context.verify_role(packet,&key22,&a.commitment),RoleStage::Shape,false)?;
    for bytes in [vec![0;383],vec![255;384]]{
        verify_failure(context.verify_role(packet,&a.key,&bytes),RoleStage::Commitment,false)?;}
    let mut bad=packet.clone();bad.bytes[..32].fill(255);
    verify_failure(context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Decode,false)?;
    let mut proof=gkr::decode_dimensions(&[32],&packet.bytes)?;proof.layers[0].rounds[0][0]+=Fr::one();
    let bad=RoleProof{role:0,bytes:gkr::encode_proof(&proof)?};need(bad.bytes!=packet.bytes,"historical48 reached round mutant")?;
    verify_failure(context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Gkr,true)?;
    let alternate=synthetic_c()?;need(alternate!=a.commitment,"historical48 alternate C reached")?;
    historical47_commitment(&alternate)?;
    verify_failure(context.verify_role(packet,&a.key,&alternate),RoleStage::Gkr,true)?;
    let extra=context.historical48_control_prefix(0,&a.key,&a.commitment,Historical48PrefixFault::ExtraRole0Binder)?;
    need(counters(&extra)[..2]==[0,0]&&extra.bytes_absorbed()>normal.bytes_absorbed(),"historical48 extra binder reached")?;
    verify_failure(context.verify_role_historical48_control(packet,&a.key,&a.commitment,Historical48PrefixFault::ExtraRole0Binder),RoleStage::Gkr,true)
}
fn public_controls(public:&Public,packet:&RoleProof,key:&[u8],meta:&[u8],c:&[u8])->Result<(),String>{
    for field in 0..4{let mut p=public.clone();match field{0=>p.root[0]^=1,1=>p.total[0]^=1,2=>p.tip[0]^=1,_=>p.tip_time^=1}
        let a=Historical47Admission::new(&historical47_frame(&p)?,key,meta,c)?;
        let graph=Graph::new(&a)?;let(context,_)=ProofContext::historical_h12(&graph.consumer,&a)?;
        verify_failure(context.verify_role(packet,&a.key,&a.commitment),RoleStage::Gkr,true)?;
        drop(context);drop(graph);}
    need(graph_counts()==[0,1,6,6],"historical48 sequential graphs")
}
fn io_json(io:packed::PackedIoSnapshot)->Result<serde_json::Value,String>{
    Ok(serde_json::json!({"read_calls":io.read_calls,"read_bytes":io.read_bytes,
        "read_ns":u64::try_from(io.read_ns).map_err(|_|"historical48 I/O clock")?,
        "write_calls":io.write_calls,"write_bytes":io.write_bytes,
        "write_ns":u64::try_from(io.write_ns).map_err(|_|"historical48 I/O clock")?,
        "sync_calls":io.sync_calls,"sync_ns":u64::try_from(io.sync_ns).map_err(|_|"historical48 I/O clock")?}))
}
struct ResultData{
    public:Public,frame_sha:String,proof_sha:String,sender:Claim,receiver:Claim,sender_counts:[u64;3],receiver_counts:[u64;3],
    sender_next:Fr,receiver_next:Fr,prefix:[u64;3],mle:Fr,times:[u64;7],subtimes:[u64;5],
    actual_source_digest:String,binding_io:packed::PackedIoSnapshot,
    proof_io:packed::PackedIoSnapshot,mle_io:packed::PackedIoSnapshot,graphs:[u64;4],
}
fn report(d:&ResultData)->Result<serde_json::Value,String>{
    Ok(serde_json::json!({"schema":"historical32-role0-join48-v1","result":"PASS","role":0,"headers":3073,
        "slot_log":12,"slots":4096,"input_log":32,"row_log":33,"profile":std::str::from_utf8(H47_PROFILE).map_err(|_|"historical48 profile UTF8")?,
        "public":h41_public(&d.public),"frame":{"bytes":571,"sha256":d.frame_sha},"proof":{"bytes":7264,"sha256":d.proof_sha},
        "key":{"bytes":33264,"metadata_bytes":40,"log_n":32,"sha256":KEY_SHA,"setup_id":ID},
        "commitment":{"bytes":384,"sha256":C_SHA},
        "producer":{"claim":h41_claim(&d.sender),"counters":d.sender_counts,"continuation":h41_fr(d.sender_next)},
        "consumer":{"claim":h41_claim(&d.receiver),"counters":d.receiver_counts,"continuation":h41_fr(d.receiver_next),"mle":h41_fr(d.mle),
            "canonical_decode":true,"verifier_entered":true,"prefix":d.prefix},
        "timings_ns":d.times,"subtimings_ns":d.subtimes,"graphs":d.graphs,
        "io":{"source_binding":io_json(d.binding_io)?,"proof":io_json(d.proof_io)?,"mle":io_json(d.mle_io)?},
        "known_buffers":{"owner_packet_bytes":131072,"high_records":65536,"high_vector_data_bytes":6291456,
            "scoped_capacity_measured":false,"whole_job_peak_bytes":null},
        "checks":{"same_parent":true,"NoFault":true,"codec":true,"round":true,"alternate_c":true,"extra_binder":true,
            "public_fields":true,"wrong_key_log":true,"claim_mle":true,"exports_replayed":true,"parents_sequential":true},
        "custody":{"raw_sha256":RAW_SHA,"pack_blake2b256":PACK_BLAKE,"key_metadata_sha256":META_SHA,
            "actual_source_blake2b256":d.actual_source_digest,"post":true},
        "new_gkr":1,"pcs_invoked":false,"setup_generated":false,"witness_generated":false,"all_seven":false,
        "common_opening":false,"full_history":false,"production":false}))
}
fn result_claims(v:&serde_json::Value,d:&ResultData)->Result<(),String>{
    close_claim(&v["producer"]["claim"],&d.receiver,d.mle)?;
    close_claim(&v["consumer"]["claim"],&d.receiver,d.mle)?;
    need(fr_from_json(&v["consumer"]["mle"])?==d.mle,"historical48 reported MLE")
}
fn claim_controls(d:&ResultData)->Result<(),String>{
    let good=report(d)?;result_claims(&good,d)?;
    for side in ["producer","consumer"]{let mut bad=good.clone();bad[side]["claim"]["value"]=serde_json::json!(h41_fr(d.receiver.value+Fr::one()));
        need(result_claims(&bad,d).err().as_deref()==Some("historical48 reported claim/MLE"),"historical48 claim fault attribution")?;
        for coordinate in 0..32{let mut bad=good.clone();
            bad[side]["claim"]["point"][coordinate]=serde_json::json!(h41_fr(d.receiver.point[coordinate]+Fr::one()));
            need(result_claims(&bad,d).err().as_deref()==Some("historical48 reported claim/MLE"),
                "historical48 claim coordinate attribution")?;}}
    let mut bad=good.clone();bad["consumer"]["mle"]=serde_json::json!(h41_fr(d.mle+Fr::one()));
    need(result_claims(&bad,d).err().as_deref()==Some("historical48 reported MLE"),"historical48 MLE fault attribution")
}
struct Trace{start:Instant,next:usize}
impl Trace{
    fn mark(&mut self,phase:&str,event:&str)->Result<(),String>{
        need(STAGES.get(self.next)==Some(&(phase,event)),"historical48 stage order")?;
        eprintln!("HISTORICAL32_ROLE0_48_STAGE {phase} {event} {}",self.start.elapsed().as_nanos());self.next+=1;Ok(())
    }
}
fn run(t:&mut Trace)->Result<(),String>{
    let mut times=[0u64;7];let mut subtimes=[0u64;5];
    need(graph_counts()==[0;4],"historical48 fresh graph ledger")?;
    need(std::env::var_os("NIPOPOW_CORE_POOL_PROFILE").is_none(),"historical48 extra profile output forbidden")?;
    t.mark("admission","begin")?;let started=Instant::now();
    let mut raw=Held::open("NIPOPOW_HISTORICAL48_RAW_PATH",869449,RAW_SHA,false)?;
    let mut pack=Held::open("NIPOPOW_HISTORICAL48_PACK_PATH",536870912,PACK_BLAKE,true)?;
    let mut key=Held::open("NIPOPOW_HISTORICAL48_KEY_PATH",33264,KEY_SHA,false)?;
    let mut c=Held::open("NIPOPOW_HISTORICAL48_COMMITMENT_PATH",384,C_SHA,false)?;
    let mut meta=Held::open("NIPOPOW_HISTORICAL48_KEY_METADATA_PATH",40,META_SHA,false)?;
    let dir=output_dir()?;let source=PackedFile::open_with_limit(&pack.path,32,32)?;pack.check()?;
    // Held's named handle can be a different object after an ancestor ABA.
    // Bind the bytes of the actual locked prover/MLE reader before any graph/FS.
    let actual_source_digest=bind_actual_source(&source)?;let binding_io=source.io_metrics_snapshot();
    let input=raw_input(&raw.bytes)?;
    let public=Public{headers:3073,root:input.root(),total:input.total_be28(),
        tip:ergo_header_core::blake2b256(input.raw(3073)?),tip_time:input.timestamp(3073)?};
    let a=Historical47Admission::new(&historical47_frame(&public)?,&key.bytes,&meta.bytes,&c.bytes)?;
    times[0]=ns(started)?;t.mark("admission","end")?;
    t.mark("producer","begin")?;let started=Instant::now();let sub=Instant::now();
    let graph=Graph::new(&a)?;crate::packed_owner_assembly::validate_native_plan_input(&graph.consumer.parent,&input)?;drop(input);
    let(context,_)=ProofContext::historical_h12(&graph.consumer,&a)?;subtimes[0]=ns(sub)?;
    let normal=context.transcript(0,&a.key,&a.commitment);
    let nofault=context.historical48_control_prefix(0,&a.key,&a.commitment,Historical48PrefixFault::NoFault)?;
    need(snapshot(&normal)?==snapshot(&nofault)?,"historical48 preproof NoFault identity")?;
    need(counters(&normal)[..2]==[0,0],"historical48 preproof freshness")?;drop(normal);drop(nofault);
    let sub=Instant::now();let produced=prove_role0_historical48(&context,&source,&a)?;subtimes[1]=ns(sub)?;
    let Historical48Produced{proof,claim,counters:sender_counts,continuation:sender_next,io:proof_io}=produced;
    let proof_bytes=gkr::encode_proof(&proof)?;need(proof_bytes.len()==7264,"historical48 proof extent")?;drop(proof);
    let sender=Claim{point:claim.point,value:claim.value};times[1]=ns(started)?;t.mark("producer","end")?;
    drop(context);drop(graph);need(graph_counts()==[0,1,1,1],"historical48 producer dropped")?;t.mark("producer_drop","end")?;
    t.mark("export","begin")?;let started=Instant::now();
    write_new(&dir.join("statement.bin"),&a.frame)?;write_new(&dir.join("commitment.bin"),&a.commitment)?;
    write_new(&dir.join("role-0.gkr"),&proof_bytes)?;roster(&dir,false)?;
    let frame=read_export(&dir,"statement.bin",&a.frame)?;let commitment=read_export(&dir,"commitment.bin",&a.commitment)?;
    let packet=RoleProof{role:0,bytes:read_export(&dir,"role-0.gkr",&proof_bytes)?};drop(proof_bytes);
    times[2]=ns(started)?;t.mark("export","end")?;
    t.mark("consumer","begin")?;let started=Instant::now();let sub=Instant::now();
    let receiver_a=Historical47Admission::new(&frame,&key.bytes,&meta.bytes,&commitment)?;
    let graph=Graph::new(&receiver_a)?;let(context,_)=ProofContext::historical_h12(&graph.consumer,&receiver_a)?;subtimes[2]=ns(sub)?;
    let sub=Instant::now();let verified=context.verify_role(&packet,&receiver_a.key,&receiver_a.commitment)
        .map_err(|e|format!("historical48 receiver {:?}",e.stage))?;subtimes[3]=ns(sub)?;
    need(verified.role==0&&verified.observation.canonical_decode&&verified.observation.verifier_entered
        &&verified.observation.prefix_challenges==0&&verified.observation.prefix_raw_queries==0,"historical48 actual receiver")?;
    need(verified.claim==sender&&verified.counters==sender_counts&&verified.continuation==sender_next,"historical48 sender receiver identity")?;
    source.reset_io_metrics();let sub=Instant::now();let mle=source.evaluate(&verified.claim.point)?;subtimes[4]=ns(sub)?;
    let mle_io=source.io_metrics_snapshot();need(mle==verified.claim.value,"historical48 held PACK MLE")?;
    receiver_controls(&context,&packet,&receiver_a,&verified)?;
    times[3]=ns(started)?;t.mark("consumer","end")?;
    drop(context);drop(graph);need(graph_counts()==[0,1,2,2],"historical48 receiver dropped")?;t.mark("consumer_drop","end")?;
    t.mark("public_bindings","begin")?;let started=Instant::now();
    public_controls(&public,&packet,&key.bytes,&meta.bytes,&c.bytes)?;
    times[4]=ns(started)?;t.mark("public_bindings","end")?;
    let mut data=ResultData{public,frame_sha:h41_sha(&frame)?,proof_sha:h41_sha(&packet.bytes)?,sender,receiver:verified.claim,
        sender_counts,receiver_counts:verified.counters,sender_next,receiver_next:verified.continuation,
        prefix:[verified.observation.prefix_challenges,verified.observation.prefix_raw_queries,verified.observation.prefix_bytes],mle,
        times,subtimes,actual_source_digest,binding_io,proof_io,mle_io,graphs:graph_counts()};
    t.mark("claim_controls","begin")?;let started=Instant::now();claim_controls(&data)?;
    times[5]=ns(started)?;t.mark("claim_controls","end")?;
    t.mark("custody","begin")?;let started=Instant::now();
    raw.rehash(false)?;pack.rehash(true)?;key.rehash(false)?;c.rehash(false)?;meta.rehash(false)?;
    need(graph_counts()==[0,1,6,6],"historical48 final graph ledger")?;
    times[6]=ns(started)?;t.mark("custody","end")?;
    t.mark("result","begin")?;let started=Instant::now();data.times=times;
    // The seven exported durations exclude this result's own write/replay.
    // Its eighth duration is observed in the final stdout envelope instead.
    let result=serde_json::to_vec(&report(&data)?).map_err(|_|"historical48 report encoding")?;
    need(result.len()<=16384,"historical48 report cap")?;write_new(&dir.join("result.json"),&result)?;roster(&dir,true)?;
    let replay=read_export(&dir,"result.json",&result)?;
    let replay:serde_json::Value=serde_json::from_slice(&replay).map_err(|_|"historical48 result replay")?;result_claims(&replay,&data)?;
    read_export(&dir,"statement.bin",&frame)?;read_export(&dir,"commitment.bin",&commitment)?;read_export(&dir,"role-0.gkr",&packet.bytes)?;
    let result_export_ns=ns(started)?;t.mark("result","end")?;
    let envelope=serde_json::to_vec(&serde_json::json!({"report":replay,"result_export_ns":result_export_ns})).map_err(|_|"historical48 envelope encoding")?;
    need(envelope.len()<=16384,"historical48 envelope cap")?;
    t.mark("complete","end")?;
    println!("\nHISTORICAL32_ROLE0_48 {}",String::from_utf8(envelope).map_err(|_|"historical48 report UTF8")?);Ok(())
}

fn ordinary()->Result<(),String>{
    binding_controls()?;
    let p=Public{headers:3073,root:[2;32],total:[3;28],tip:[4;32],tip_time:5};let frame=historical47_frame(&p)?;
    need(frame.len()==571&&historical47_frame(&historical47_decode(&frame)?)?==frame,"historical48 frame roundtrip")?;
    need(&frame[255..265]==b"corepool11"&&u64::from_le_bytes(frame[265..273].try_into().map_err(|_|"historical48 frame input")?)==32
        &&u64::from_le_bytes(frame[273..281].try_into().map_err(|_|"historical48 frame row")?)==33,"historical48 frame offsets")?;
    let key22=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;need(key22.log_n()==22,"historical48 real key22")?;
    let bytes=vec![0u8;7264];let proof=gkr::decode_dimensions(&[32],&bytes)?;
    need(proof.layers.len()==1&&proof.layers[0].rounds.len()==64&&proof.layers[0].line_coefficients.len()==33
        &&gkr::encode_proof(&proof)?==bytes,"historical48 codec-only shape fixture")?;
    for n in [7263,7265]{need(gkr::decode_dimensions(&[32],&vec![0;n]).is_err(),"historical48 codec extent negative")?;}
    let mut bad=bytes;bad[..32].fill(255);need(gkr::decode_dimensions(&[32],&bad).is_err(),"historical48 codec canonical negative")?;
    let scalar=serde_json::json!(h41_fr(Fr::one()));need(fr_from_json(&scalar)?==Fr::one(),"historical48 scalar golden")?;
    need(fr_from_json(&serde_json::json!("f".repeat(64))).is_err(),"historical48 scalar canonical negative")?;
    let claim=Claim{point:vec![Fr::zero();32],value:Fr::one()};let m=u64::MAX;
    let io=packed::PackedIoSnapshot{read_calls:m,read_bytes:m,read_ns:m as u128,write_calls:m,write_bytes:m,write_ns:m as u128,sync_calls:m,sync_ns:m as u128};
    let d=ResultData{public:Public{tip_time:i64::MIN,..p},frame_sha:"F".repeat(64),proof_sha:"F".repeat(64),sender:claim.clone(),receiver:claim,
        sender_counts:[m;3],receiver_counts:[m;3],sender_next:Fr::one(),receiver_next:Fr::one(),prefix:[m;3],mle:Fr::one(),
        times:[m;7],subtimes:[m;5],actual_source_digest:"f".repeat(64),binding_io:io,proof_io:io,mle_io:io,graphs:[m;4]};
    let report=report(&d)?;let result=serde_json::to_vec(&report).map_err(|_|"historical48 report encoding")?;
    let envelope=serde_json::to_vec(&serde_json::json!({"report":report,"result_export_ns":m})).map_err(|_|"historical48 envelope encoding")?;
    need(result.len()<16384&&envelope.len()<16384&&envelope.len()+8192<65536,"historical48 maximal serializers")?;
    claim_controls(&d)?;need(graph_counts()==[0;4],"historical48 ordinary has no H12 graph")
}
#[test]
fn historical48_ordinary()->Result<(),String>{ordinary()}
#[test]
#[ignore]
fn historical48_native32_role0(){
    let mut t=Trace{start:Instant::now(),next:0};
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(&mut t)));
    let error=match result{Ok(Ok(()))=>return,Ok(Err(e))=>e,Err(_)=>"historical48 panic".into()};
    let reason:String=error.chars().filter(|v|v.is_ascii_graphic()||*v==' ').take(160).collect();
    eprintln!("HISTORICAL32_ROLE0_48_HOLD {} {} {reason}",t.next,t.start.elapsed().as_nanos());panic!("historical48 HOLD");
}

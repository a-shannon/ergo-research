//! Historical H12 role6 packed-line join; retained49 is the exact reference.
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
const REF_PROOF_SHA:&str="E220544731D83E99CA728CA3283855FEA0B3D0DAB2013C8E548F46EE70D25213";
const REF_RESULT_SHA:&str="3F30FDC6F1A9620389F52A3D545DF9953AAB90D3B3E2FC586FA116D1588953ED";
const REF_FRAME_SHA:&str="C44FDFD8F42EED0AAFF6DCD0543F6C877F4A63562A7C61131DA4344786695295";
const REFERENCE:[(&str,usize,&str);4]=[("statement.bin",571,REF_FRAME_SHA),("commitment.bin",384,C_SHA),
    ("role-6.gkr",7264,REF_PROOF_SHA),("result.json",9355,REF_RESULT_SHA)];
const STAGES:[(&str,&str);19]=[("admission","begin"),("admission","end"),("producer","begin"),("producer","end"),
    ("producer_drop","end"),("export","begin"),("export","end"),("consumer","begin"),("consumer","end"),
    ("consumer_drop","end"),("public_bindings","begin"),("public_bindings","end"),
    ("claim_controls","begin"),("claim_controls","end"),("custody","begin"),("custody","end"),
    ("result","begin"),("result","end"),("complete","end")];
fn members(role:usize)->Result<[(&'static str,usize);4],String>{
    historical52_role(role)?;let proof="role-6.gkr";
    Ok([("statement.bin",571),("commitment.bin",384),(proof,7264),("result.json",16384)])
}
fn need(ok:bool,error:&str)->Result<(),String>{if ok{Ok(())}else{Err(error.into())}}
fn ns(start:Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"historical52 clock".into())}
fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
fn snapshot(t:&Transcript)->Result<([u64;3],Fr),String>{Ok((counters(t),t.clone().try_challenge_scalar(b"historical52-prefix-control-v1")?))}
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
    if unsafe{GetFileInformationByHandle(file.as_raw_handle(),&mut id)}==0{return Err("historical52 file identity".into());}
    need(id.attributes&0x410==0&&id.links==1,"historical52 ordinary single-link file")?;id.accessed=[0;2];Ok(id)
}
struct Held{file:File,path:PathBuf,id:Identity,bytes:Vec<u8>,digest:String}
impl Held{
    fn open(env:&str,size:usize,expected:&str,pack:bool)->Result<Self,String>{
        let path=PathBuf::from(std::env::var_os(env).ok_or("historical52 missing input")?);
        need(path.is_absolute()&&path.as_os_str().len()<=1024,"historical52 input path")?;
        let md=generic37_metadata(&path,false)?;need(md.len()==size as u64,"historical52 input extent")?;
        let mut file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|_|"historical52 input open")?;
        let id=identity(&file)?;need((u64::from(id.high)<<32)|u64::from(id.low)==size as u64,"historical52 held extent")?;
        let mut bytes=Vec::new();let digest;
        if pack{let mut state=Blake2b::<U32>::new();let mut scratch=[0u8;65536];let mut total=0usize;
            loop{let n=file.read(&mut scratch).map_err(|_|"historical52 PACK read")?;if n==0{break;}
                total=total.checked_add(n).ok_or("historical52 PACK overflow")?;
                need(total<=size,"historical52 PACK trailing")?;state.update(&scratch[..n]);}
            need(total==size,"historical52 PACK truncated")?;digest=h41_hex(&state.finalize());
        }else{need(size<=869449,"historical52 bounded input")?;bytes.resize(size,0);
            file.read_exact(&mut bytes).map_err(|_|"historical52 input read")?;
            let mut tail=[0;1];need(file.read(&mut tail).map_err(|_|"historical52 input tail")?==0,"historical52 input trailing")?;
            digest=h41_sha(&bytes)?;}
        need(digest==expected,"historical52 input digest")?;
        let held=Self{file,path,id,bytes,digest};held.check()?;Ok(held)
    }
    fn check(&self)->Result<(),String>{
        generic37_metadata(&self.path,false)?;need(identity(&self.file)?==self.id,"historical52 held custody")?;
        let named=OpenOptions::new().read(true).share_mode(1).open(&self.path).map_err(|_|"historical52 custody reopen")?;
        need(identity(&named)?==self.id,"historical52 named custody")
    }
    fn rehash(&mut self,pack:bool)->Result<(),String>{
        self.check()?;self.file.seek(SeekFrom::Start(0)).map_err(|_|"historical52 custody seek")?;
        if pack{let mut state=Blake2b::<U32>::new();let mut scratch=[0u8;65536];let mut total=0usize;
            loop{let n=self.file.read(&mut scratch).map_err(|_|"historical52 custody read")?;if n==0{break;}
                total=total.checked_add(n).ok_or("historical52 custody overflow")?;
                need(total<=536870912,"historical52 custody extent")?;state.update(&scratch[..n]);}
            need(total==536870912&&h41_hex(&state.finalize())==self.digest,"historical52 PACK custody hash")?;
        }else{let mut actual=vec![0;self.bytes.len()];self.file.read_exact(&mut actual).map_err(|_|"historical52 custody read")?;
            let mut tail=[0;1];need(self.file.read(&mut tail).map_err(|_|"historical52 custody tail")?==0
                &&actual==self.bytes&&h41_sha(&actual)?==self.digest,"historical52 buffer custody")?;}
        self.check()
    }
}
fn raw_input(bytes:&[u8])->Result<crate::packed_owner_assembly::NativePrefix,String>{
    let mut at=0usize;let mut raws=Vec::with_capacity(3073);
    for _ in 0..3073{let n=u32::from_le_bytes(historical47_take(bytes,&mut at)?) as usize;
        need((1..=514).contains(&n),"historical52 RAW record extent")?;
        let end=at.checked_add(n).ok_or("historical52 RAW overflow")?;
        raws.push(bytes.get(at..end).ok_or("historical52 RAW truncated")?.to_vec());at=end;}
    need(at==bytes.len(),"historical52 RAW trailing")?;
    crate::packed_owner_assembly::NativePrefix::from_raw_iter(3073,raws.into_iter().map(Ok))
}

// Private streaming factor. Only bind_actual_source selects the runtime shape;
// ordinary controls supply small real File readers to falsify digest binding.
fn hash_windows(count:usize,width:usize,expected:&str,
    mut read:impl FnMut(usize)->Result<Vec<u8>,String>)->Result<String,String>{
    need(count>0&&count<=4096&&width>0&&width<=131072
        &&count.checked_mul(width).is_some_and(|n|n<=536870912),"historical52 binding window policy")?;
    need(expected.len()==64&&expected.bytes().all(|b|b.is_ascii_digit()||(b'a'..=b'f').contains(&b)),
        "historical52 binding digest policy")?;
    let mut state=Blake2b::<U32>::new();
    for owner in 0..count{let bytes=read(owner)?;
        need(bytes.len()==width&&bytes.capacity()==width,"historical52 binding window extent")?;
        state.update(&bytes);drop(bytes);}
    let observed=h41_hex(&state.finalize());
    need(observed==expected,"historical52 actual source digest")?;Ok(observed)
}
fn bind_actual_source(source:&PackedFile)->Result<String,String>{
    // This exact object is kept for both the prover and MLE. PackedFile opens
    // with FILE_SHARE_READ only; the actual reader cannot be written/deleted.
    let view=source.native_role0_view()?;view.require_same_source(source)?;
    source.reset_io_metrics();
    let digest=hash_windows(4096,131072,PACK_BLAKE,|owner|Ok(view.read_copy(owner)?.into_bytes()))?;
    let io=source.io_metrics_snapshot();
    need(io.read_calls==4096&&io.read_bytes==536870912&&io.write_calls==0&&io.sync_calls==0,
        "historical52 actual source scan")?;Ok(digest)
}
fn binding_controls()->Result<(),String>{
    let dir=std::env::temp_dir();generic37_metadata(&dir,true)?;
    let paths=[dir.join(format!("historical52-reader-a-{}.bin",std::process::id())),
        dir.join(format!("historical52-reader-b-{}.bin",std::process::id()))];
    let a:Vec<u8>=(0..96u8).collect();let mut b=a.clone();b[47]^=1;
    let golden=h41_hex(&Blake2b::<U32>::digest(&a));let mut created=Vec::new();
    let result=(||->Result<(),String>{
        for(path,bytes)in paths.iter().zip([&a,&b]){
            let mut file=OpenOptions::new().write(true).create_new(true).open(path).map_err(|_|"historical52 binding fixture create")?;
            created.push(path.clone());file.write_all(bytes).map_err(|_|"historical52 binding fixture write")?;
            file.sync_all().map_err(|_|"historical52 binding fixture sync")?;}
        let read_file=|path:&Path|->Result<String,String>{
            let mut file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|_|"historical52 binding fixture open")?;
            need(file.metadata().map_err(|_|"historical52 binding fixture metadata")?.len()==96,"historical52 binding fixture extent")?;
            hash_windows(3,32,&golden,|_|{let mut bytes=vec![0;32];
                file.read_exact(&mut bytes).map_err(|_|"historical52 binding fixture read")?;Ok(bytes)})
        };
        need(read_file(&paths[0])?==golden,"historical52 binding golden")?;
        need(read_file(&paths[1]).err().as_deref()==Some("historical52 actual source digest"),
            "historical52 different reader attribution")
    })();
    // Remove only files whose exclusive creation succeeded, including failures.
    // A pre-existing name is never owned, overwritten or removed by this test.
    let mut cleanup=Ok(());for path in created{if std::fs::remove_file(path).is_err(){cleanup=Err("historical52 binding fixture cleanup".into());}}
    result.and(cleanup)
}

std::thread_local!{static GRAPHS:std::cell::Cell<[u64;4]>=const{std::cell::Cell::new([0;4])};}
fn graph_counts()->[u64;4]{GRAPHS.with(|v|v.get())}
struct Graph{consumer:Consumer}
impl Graph{
    fn new(a:&Historical47Admission)->Result<Self,String>{
        historical47_policy(a.public.headers,12,4096,a.key.log_n())?;
        Self::from_public(&a.public)
    }
    fn from_public(public:&Public)->Result<Self,String>{
        need(graph_counts()[0]==0,"historical52 concurrent graph")?;
        historical47_policy(public.headers,12,4096,32)?;
        let OwnedLayouts{parent,adjacency,metadata,points,point_template}=compile_layouts(&LayoutRequest{
            headers:public.headers,slot_log:12,root:public.root,total:public.total,tip:public.tip,tip_time:public.tip_time})?;
        let consumer=Consumer{public:public.clone(),parent,adjacency,metadata,points,point_template};
        GRAPHS.with(|v|{let mut c=v.get();c[0]+=1;c[1]=c[1].max(c[0]);c[2]+=1;v.set(c)});
        Ok(Self{consumer})
    }
}
impl Drop for Graph{
    fn drop(&mut self){GRAPHS.with(|v|{let mut c=v.get();assert_eq!(c[0],1);c[0]-=1;c[3]+=1;v.set(c)})}
}
fn output_dir()->Result<PathBuf,String>{
    let path=PathBuf::from(std::env::var_os("NIPOPOW_HISTORICAL52_OUTPUT_DIR").ok_or("historical52 missing output")?);
    need(path.is_absolute()&&path.as_os_str().len()<=1024,"historical52 output path")?;
    generic37_metadata(&path,true)?;
    need(path.read_dir().map_err(|_|"historical52 output scan")?.next().is_none(),"historical52 output not empty")?;Ok(path)
}
fn roster(dir:&Path,role:usize,complete:bool)->Result<(),String>{
    generic37_metadata(dir,true)?;let mut names=Vec::with_capacity(4);
    for entry in dir.read_dir().map_err(|_|"historical52 output scan")?{
        need(names.len()<4,"historical52 output roster")?;
        let entry=entry.map_err(|_|"historical52 output entry")?;generic37_metadata(&entry.path(),false)?;
        names.push(entry.file_name().into_string().map_err(|_|"historical52 output name")?);}
    names.sort();let mut expected:Vec<_>=members(role)?[..if complete{4}else{3}].iter().map(|v|v.0.to_owned()).collect();expected.sort();
    need(names==expected,"historical52 output roster")
}
fn read_export(dir:&Path,role:usize,name:&str,expected:&[u8])->Result<Vec<u8>,String>{
    let bound=members(role)?.iter().find(|v|v.0==name).ok_or("historical52 export name")?.1;
    need(expected.len()<=bound&&(name=="result.json"||expected.len()==bound),"historical52 export extent")?;
    let bytes=generic37_read(&dir.join(name),expected.len())?;
    need(bytes==expected,"historical52 export bytes")?;Ok(bytes)
}
fn fr_from_json(v:&serde_json::Value)->Result<Fr,String>{
    let s=v.as_str().ok_or("historical52 scalar type")?;
    need(s.len()==64&&s.bytes().all(|b|b.is_ascii_digit()||(b'a'..=b'f').contains(&b)),"historical52 scalar encoding")?;
    let mut bytes=[0u8;32];for(i,pair)in s.as_bytes().chunks_exact(2).enumerate(){
        bytes[i]=u8::from_str_radix(std::str::from_utf8(pair).map_err(|_|"historical52 scalar UTF8")?,16).map_err(|_|"historical52 scalar hex")?;}
    let value=Fr::deserialize_compressed(&bytes[..]).map_err(|_|"historical52 scalar canonical")?;
    let mut encoded=Vec::new();value.serialize_compressed(&mut encoded).map_err(|_|"historical52 scalar encode")?;
    need(encoded==bytes,"historical52 scalar roundtrip")?;Ok(value)
}
fn claim_from_json(v:&serde_json::Value)->Result<Claim,String>{
    let o=v.as_object().ok_or("historical52 claim type")?;
    need(o.len()==2&&o.contains_key("point")&&o.contains_key("value"),"historical52 claim keys")?;
    let p=o["point"].as_array().ok_or("historical52 claim point")?;need(p.len()==32,"historical52 claim dimension")?;
    Ok(Claim{point:p.iter().map(fr_from_json).collect::<Result<Vec<_>,_>>()?,value:fr_from_json(&o["value"])?})
}
fn close_claim(v:&serde_json::Value,verified:&Claim,mle:Fr)->Result<(),String>{
    let actual=claim_from_json(v)?;
    need(actual==*verified&&actual.value==mle,"historical52 reported claim/MLE")
}
struct Reference{dir:PathBuf,proof:Vec<u8>,claim:Claim,counts:[u64;3],next:Fr}
fn reference_buffers(dir:&Path)->Result<Vec<Vec<u8>>,String>{
    roster(dir,6,true)?;
    REFERENCE.iter().map(|(name,size,digest)|{
        let bytes=generic37_read(&dir.join(name),*size)?;
        need(h41_sha(&bytes)?==*digest,"historical52 reference digest")?;Ok(bytes)
    }).collect()
}
fn reference_counts(value:&serde_json::Value)->Result<[u64;3],String>{
    let a=value.as_array().ok_or("historical52 reference counters")?;
    need(a.len()==3,"historical52 reference counters")?;
    Ok([a[0].as_u64().ok_or("historical52 reference counters")?,a[1].as_u64().ok_or("historical52 reference counters")?,
        a[2].as_u64().ok_or("historical52 reference counters")?])
}
impl Reference{
    fn open(a:&Historical47Admission)->Result<Self,String>{
        let dir=PathBuf::from(std::env::var_os("NIPOPOW_HISTORICAL52_REFERENCE_DIR").ok_or("historical52 missing reference")?);
        need(dir.is_absolute()&&dir.as_os_str().len()<=1024,"historical52 reference path")?;
        let mut buffers=reference_buffers(&dir)?;
        need(buffers[0]==a.frame&&buffers[1]==a.commitment,"historical52 reference public bytes")?;
        let value:serde_json::Value=serde_json::from_slice(&buffers[3]).map_err(|_|"historical52 reference JSON")?;
        need(value["schema"]=="historical32-role246-join49-v1"&&value["result"]=="PASS"&&value["role"]==6,
            "historical52 reference role/schema")?;
        let claim=claim_from_json(&value["producer"]["claim"])?;
        let counts=reference_counts(&value["producer"]["counters"])?;
        let next=fr_from_json(&value["producer"]["continuation"])?;
        need(claim_from_json(&value["consumer"]["claim"])?==claim&&reference_counts(&value["consumer"]["counters"])?==counts
            &&fr_from_json(&value["consumer"]["continuation"])?==next,"historical52 reference original coherence")?;
        let proof=std::mem::take(&mut buffers[2]);
        need(proof.capacity()==7264&&claim.point.capacity()==32&&dir.capacity()<=4096,"historical52 reference retained capacity")?;
        let retained=std::mem::size_of::<Self>().checked_add(proof.capacity())
            .and_then(|n|claim.point.capacity().checked_mul(std::mem::size_of::<Fr>()).and_then(|m|n.checked_add(m)))
            .and_then(|n|n.checked_add(dir.capacity())).ok_or("historical52 reference capacity overflow")?;
        need(retained<=32768,"historical52 reference reservation")?;
        Ok(Self{dir,proof,claim,counts,next})
    }
    fn check(&self)->Result<(),String>{let _=reference_buffers(&self.dir)?;Ok(())}
}
fn close_reference(r:&Reference,proof:&[u8],claim:&Claim,counts:[u64;3],next:Fr)->Result<(),String>{
    need(proof==r.proof,"historical52 retained packet bytes")?;
    need(*claim==r.claim&&counts==r.counts&&next==r.next,"historical52 retained observations")
}
fn reference_controls()->Result<(),String>{
    let r=Reference{dir:PathBuf::new(),proof:vec![0;7264],claim:Claim{point:vec![Fr::zero();32],value:Fr::one()},
        counts:[89,109,141320],next:Fr::from(3u64)};
    close_reference(&r,&r.proof,&r.claim,r.counts,r.next)?;
    let mut bad=r.proof.clone();bad[0]^=1;
    rejected(close_reference(&r,&bad,&r.claim,r.counts,r.next),"historical52 retained packet bytes")?;
    for field in 0..33{let mut bad=r.claim.clone();if field<32{bad.point[field]+=Fr::one();}else{bad.value+=Fr::one();}
        rejected(close_reference(&r,&r.proof,&bad,r.counts,r.next),"historical52 retained observations")?;}
    for field in 0..3{let mut bad=r.counts;bad[field]+=1;
        rejected(close_reference(&r,&r.proof,&r.claim,bad,r.next),"historical52 retained observations")?;}
    rejected(close_reference(&r,&r.proof,&r.claim,r.counts,r.next+Fr::one()),"historical52 retained observations")
}
fn verify_failure(role:usize,result:Result<VerifiedRole,RoleFailure>,stage:RoleStage,entered:bool)->Result<(),String>{
    let error=match result{Ok(_)=>return Err("historical52 negative accepted".into()),Err(e)=>e};
    need(error.role==role||stage==RoleStage::Shape,"historical52 failure role")?;
    need(error.stage==stage&&error.observation.verifier_entered==entered,"historical52 negative stage")?;
    need(error.observation.canonical_decode==entered,"historical52 negative canonical attribution")
}
fn receiver_controls(context:&ProofContext<'_>,packet:&RoleProof,a:&Historical47Admission,positive:&VerifiedRole)->Result<(),String>{
    let role=packet.role;
    let normal=context.transcript(role,&a.key,&a.commitment);
    let nofault=context.historical49_control_prefix(role,&a.key,&a.commitment,Historical49PrefixFault::NoFault)?;
    need(snapshot(&normal)?==snapshot(&nofault)?,"historical52 NoFault prefix identity")?;
    let plain=context.verify_role_historical49_control(packet,&a.key,&a.commitment,Historical49PrefixFault::NoFault)
        .map_err(|e|format!("historical52 NoFault receiver {:?}",e.stage))?;
    need(plain.claim==positive.claim&&plain.counters==positive.counters&&plain.continuation==positive.continuation,
        "historical52 NoFault receiver identity")?;
    for size in [7263,7265]{let mut bad=packet.clone();bad.bytes.resize(size,0);
        verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Shape,false)?;}
    let mut bad=packet.clone();bad.role=7;
    verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Shape,false)?;
    let key22=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    verify_failure(role,context.verify_role(packet,&key22,&a.commitment),RoleStage::Shape,false)?;
    for bytes in [vec![0;383],vec![255;384]]{
        verify_failure(role,context.verify_role(packet,&a.key,&bytes),RoleStage::Commitment,false)?;}
    let mut bad=packet.clone();bad.bytes[..32].fill(255);
    verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Decode,false)?;
    let mut proof=gkr::decode_dimensions(&[32],&packet.bytes)?;proof.layers[0].rounds[0][0]+=Fr::one();
    let bad=RoleProof{role,bytes:gkr::encode_proof(&proof)?};need(bad.bytes!=packet.bytes,"historical52 reached round mutant")?;
    verify_failure(role,context.verify_role(&bad,&a.key,&a.commitment),RoleStage::Gkr,true)?;
    let alternate=synthetic_c()?;need(alternate!=a.commitment,"historical52 alternate C reached")?;
    historical47_commitment(&alternate)?;
    verify_failure(role,context.verify_role(packet,&a.key,&alternate),RoleStage::Gkr,true)?;
    let extra=context.historical49_control_prefix(role,&a.key,&a.commitment,Historical49PrefixFault::ExtraRoleBinder)?;
    need(counters(&extra)[..2]==[0,0]&&extra.bytes_absorbed()>normal.bytes_absorbed(),"historical52 extra binder reached")?;
    verify_failure(role,context.verify_role_historical49_control(packet,&a.key,&a.commitment,Historical49PrefixFault::ExtraRoleBinder),RoleStage::Gkr,true)
}
fn public_controls(public:&Public,packet:&RoleProof,key:&[u8],meta:&[u8],c:&[u8])->Result<(),String>{
    let role=packet.role;
    for field in 0..4{let mut p=public.clone();match field{0=>p.root[0]^=1,1=>p.total[0]^=1,2=>p.tip[0]^=1,_=>p.tip_time^=1}
        let a=Historical47Admission::new(&historical47_frame(&p)?,key,meta,c)?;
        let graph=Graph::new(&a)?;let(context,_)=ProofContext::historical_h12(&graph.consumer,&a)?;
        verify_failure(role,context.verify_role(packet,&a.key,&a.commitment),RoleStage::Gkr,true)?;
        drop(context);drop(graph);}
    need(graph_counts()==[0,1,6,6],"historical52 sequential graphs")
}
fn io_json(io:packed::PackedIoSnapshot)->Result<serde_json::Value,String>{
    Ok(serde_json::json!({"read_calls":io.read_calls,"read_bytes":io.read_bytes,
        "read_ns":u64::try_from(io.read_ns).map_err(|_|"historical52 I/O clock")?,
        "write_calls":io.write_calls,"write_bytes":io.write_bytes,
        "write_ns":u64::try_from(io.write_ns).map_err(|_|"historical52 I/O clock")?,
        "sync_calls":io.sync_calls,"sync_ns":u64::try_from(io.sync_ns).map_err(|_|"historical52 I/O clock")?}))
}
struct ResultData{
    fast:sparse_stream_roster::PackedLineStats,role:usize,shape:Historical49Shape,edge:sparse_stream_roster::EdgeFullStats,packed:sparse_stream_roster::PackedEdgeMetrics,
    component_bound:usize,census:Historical49Census,left:[u64;4],right:[u64;4],
    public:Public,frame_sha:String,proof_sha:String,sender:Claim,receiver:Claim,sender_counts:[u64;3],receiver_counts:[u64;3],
    sender_next:Fr,receiver_next:Fr,prefix:[u64;3],mle:Fr,times:[u64;7],subtimes:[u64;5],
    actual_source_digest:String,binding_io:packed::PackedIoSnapshot,
    proof_io:packed::PackedIoSnapshot,mle_io:packed::PackedIoSnapshot,graphs:[u64;4],
}
fn side_summary(counts:&[usize])->Result<[u64;4],String>{
    need(counts.len()==4096,"historical52 side roster")?;
    let total=counts.iter().try_fold(0u64,|a,n|a.checked_add(*n as u64).ok_or("historical52 side overflow"))?;
    Ok([4096,total,*counts.iter().min().ok_or("historical52 side min")? as u64,
        *counts.iter().max().ok_or("historical52 side max")? as u64])
}
fn report(d:&ResultData)->Result<serde_json::Value,String>{
    let endpoint=serde_json::json!({"base_row_bits":d.shape.base,"family_bits":d.shape.family,"member_row_bits":d.shape.strides,
        "expected_terms":d.shape.terms,"expected_challenges":d.shape.challenges,"left":d.left,"right":d.right,
        "final_left":d.census.left,"final_right":d.census.right,"observer_events":d.census.events});
    let kernel=serde_json::json!({"direct":true,"incremental_u":false,"incremental_v":false,
        "term_callbacks":d.edge.term_callbacks,"owner_requests":d.edge.owner_requests,"emitted_fields":d.edge.emitted_fields,
        "prefix_plans":d.edge.prefix_plans,"suffix_tables":d.edge.suffix_tables,"pattern_tables":d.edge.pattern_tables,
        "sequential_x_folds":d.edge.sequential_x_folds,"sequential_bank_folds":d.edge.sequential_bank_folds,
        "input_vector_clones":d.edge.input_vector_clones,"line_internal_clones":d.edge.line_internal_clones,
        "line_cloned_fields":d.edge.line_cloned_fields,
        "capacity":{"prefix_full":d.edge.prefix_full,"prefix_suffix":d.edge.prefix_suffix,"prefix_patterns":d.edge.prefix_patterns,
            "prefix_metadata":d.edge.prefix_metadata,"banks":d.edge.banks,"x":d.edge.x,"row_lookup":d.edge.row_lookup,
            "u_weights":d.edge.u_weights,"owner_weights":d.edge.owner_weights},
        "timings_ns":{"prefix_build":d.edge.prefix_build_ns,"message":d.edge.message_ns,"line":d.edge.line_ns,
            "census":d.edge.census_ns,"high":d.edge.high_ns,"passes":d.edge.pass_ns}});
    let packed=serde_json::json!({"logical_gets":d.packed.logical_gets,"scalar_gets":d.packed.scalar_gets,"successful_loads":d.packed.successful_loads,
        "packed_bytes":d.packed.packed_bytes,"vector_expansions":d.packed.vector_expansions,"expanded_fields":d.packed.expanded_fields,
        "load_ns":d.packed.load_ns,"decode_ns":d.packed.decode_ns,"packet_capacity_peak_bytes":d.packed.packet_capacity_peak_bytes,
        "cache_capacity_peak_bytes":d.packed.cache_capacity_peak_bytes,"metadata_capacity_bytes":d.packed.metadata_capacity_bytes,
        "projection_calls":d.packed.projection_calls,"projection_fields":d.packed.projection_fields,"projection_ns":d.packed.projection_ns});
    let capacity=serde_json::json!({"checked_component_bound_bytes":d.component_bound,"component_limit_bytes":536870912,
        "includes_graph":false,"whole_job_peak_bytes":null});
    let packed_line=serde_json::json!({"builds":d.fast.builds,"owners":d.fast.owners,"coefficients":d.fast.coefficients,
        "input_expanded_fields":d.fast.input_expanded_fields,"lut_fields":d.fast.lut_fields,"work_fields":d.fast.work_fields,
        "result_fields":d.fast.result_fields,"plan_reserved_bytes":d.fast.plan_reserved_bytes,"plan_actual_bytes":d.fast.plan_actual_bytes,
        "extra_reserved_bytes":d.fast.extra_reserved_bytes,"caller_reference_reserved_bytes":32768,"component_bound":d.fast.component_bound,
        "build_ns":d.fast.build_ns,"apply_ns":d.fast.apply_ns,"whole_ns":d.fast.whole_ns});
    let mut value=serde_json::json!({"schema":"historical32-role6-packed-line52-v1","result":"PASS","role":d.role,"headers":3073,
        "slot_log":12,"slots":4096,"input_log":32,"row_log":if d.role==6{24}else{32},"profile":std::str::from_utf8(H47_PROFILE).map_err(|_|"historical52 profile UTF8")?,
        "public":h41_public(&d.public),"frame":{"bytes":571,"sha256":d.frame_sha},"proof":{"bytes":7264,"sha256":d.proof_sha},
        "key":{"bytes":33264,"metadata_bytes":40,"log_n":32,"sha256":KEY_SHA,"setup_id":ID},
        "commitment":{"bytes":384,"sha256":C_SHA},
        "producer":{"claim":h41_claim(&d.sender),"counters":d.sender_counts,"continuation":h41_fr(d.sender_next)},
        "consumer":{"claim":h41_claim(&d.receiver),"counters":d.receiver_counts,"continuation":h41_fr(d.receiver_next),"mle":h41_fr(d.mle),
            "canonical_decode":true,"verifier_entered":true,"prefix":d.prefix},
        "timings_ns":d.times,"subtimings_ns":d.subtimes,"graphs":d.graphs,
        "io":{"source_binding":io_json(d.binding_io)?,"proof":io_json(d.proof_io)?,"mle":io_json(d.mle_io)?}});
    let tail=serde_json::json!({"known_buffers":{"owner_packet_bytes":131072,"packed_owners":4,"owner_fields":1048576,"whole_expanded_source":false},
        "checks":{"same_parent":true,"NoFault":true,"codec":true,"round":true,"alternate_c":true,"extra_binder":true,
            "public_fields":true,"wrong_key_log":true,"claim_mle":true,"exports_replayed":true,"parents_sequential":true,
            "endpoint_census":true,"direct_strategy":true,"component_bounds":true,"source_reader_binding":true,
            "retained_packet":true,"retained_observations":true},
        "custody":{"raw_sha256":RAW_SHA,"pack_blake2b256":PACK_BLAKE,"key_metadata_sha256":META_SHA,
            "actual_source_blake2b256":d.actual_source_digest,"reference_proof_sha256":REF_PROOF_SHA,
            "reference_result_sha256":REF_RESULT_SHA,"post":true},
        "new_gkr":1,"pcs_invoked":false,"setup_generated":false,"witness_generated":false,"all_seven":false,
        "common_opening":false,"full_history":false,"production":false});
    let object=value.as_object_mut().ok_or("historical52 report object")?;
    for(key,item)in[("endpoint",endpoint),("kernel",kernel),("packed",packed),("capacity",capacity),("packed_line",packed_line)]{
        need(!object.contains_key(key),"historical52 duplicate report key")?;
        object.insert(key.into(),item);
    }
    let serde_json::Value::Object(tail)=tail else{return Err("historical52 report tail object".into());};
    for(key,item)in tail{
        need(!object.contains_key(&key),"historical52 duplicate report key")?;
        object.insert(key,item);
    }
    Ok(value)
}
fn result_claims(v:&serde_json::Value,d:&ResultData)->Result<(),String>{
    close_claim(&v["producer"]["claim"],&d.receiver,d.mle)?;
    close_claim(&v["consumer"]["claim"],&d.receiver,d.mle)?;
    need(fr_from_json(&v["consumer"]["mle"])?==d.mle,"historical52 reported MLE")
}
fn claim_controls(d:&ResultData)->Result<(),String>{
    let good=report(d)?;result_claims(&good,d)?;
    for side in ["producer","consumer"]{let mut bad=good.clone();bad[side]["claim"]["value"]=serde_json::json!(h41_fr(d.receiver.value+Fr::one()));
        need(result_claims(&bad,d).err().as_deref()==Some("historical52 reported claim/MLE"),"historical52 claim fault attribution")?;
        for coordinate in 0..32{let mut bad=good.clone();
            bad[side]["claim"]["point"][coordinate]=serde_json::json!(h41_fr(d.receiver.point[coordinate]+Fr::one()));
            need(result_claims(&bad,d).err().as_deref()==Some("historical52 reported claim/MLE"),
                "historical52 claim coordinate attribution")?;}}
    let mut bad=good.clone();bad["consumer"]["mle"]=serde_json::json!(h41_fr(d.mle+Fr::one()));
    need(result_claims(&bad,d).err().as_deref()==Some("historical52 reported MLE"),"historical52 MLE fault attribution")
}
struct Trace{start:Instant,next:usize}
impl Trace{
    fn mark(&mut self,phase:&str,event:&str)->Result<(),String>{
        need(STAGES.get(self.next)==Some(&(phase,event)),"historical52 stage order")?;
        eprintln!("HISTORICAL32_ROLE6_52_STAGE {phase} {event} {}",self.start.elapsed().as_nanos());self.next+=1;Ok(())
    }
}
fn run(t:&mut Trace,role:usize)->Result<(),String>{
    historical49_role(role)?;let proof_name=members(role)?[2].0;
    let mut times=[0u64;7];let mut subtimes=[0u64;5];
    historical52_role(role)?;
    need(graph_counts()==[0;4],"historical52 fresh graph ledger")?;
    need(std::env::var_os("NIPOPOW_CORE_POOL_PROFILE").is_none(),"historical52 extra profile output forbidden")?;
    t.mark("admission","begin")?;let started=Instant::now();
    let mut raw=Held::open("NIPOPOW_HISTORICAL52_RAW_PATH",869449,RAW_SHA,false)?;
    let mut pack=Held::open("NIPOPOW_HISTORICAL52_PACK_PATH",536870912,PACK_BLAKE,true)?;
    let mut key=Held::open("NIPOPOW_HISTORICAL52_KEY_PATH",33264,KEY_SHA,false)?;
    let mut c=Held::open("NIPOPOW_HISTORICAL52_COMMITMENT_PATH",384,C_SHA,false)?;
    let mut meta=Held::open("NIPOPOW_HISTORICAL52_KEY_METADATA_PATH",40,META_SHA,false)?;
    let dir=output_dir()?;let source=PackedFile::open_with_limit(&pack.path,32,32)?;pack.check()?;
    // Held's named handle can be a different object after an ancestor ABA.
    // Bind the bytes of the actual locked prover/MLE reader before any graph/FS.
    let actual_source_digest=bind_actual_source(&source)?;let binding_io=source.io_metrics_snapshot();
    let input=raw_input(&raw.bytes)?;
    let public=Public{headers:3073,root:input.root(),total:input.total_be28(),
        tip:ergo_header_core::blake2b256(input.raw(3073)?),tip_time:input.timestamp(3073)?};
    let a=Historical47Admission::new(&historical47_frame(&public)?,&key.bytes,&meta.bytes,&c.bytes)?;
    let reference=Reference::open(&a)?;
    times[0]=ns(started)?;t.mark("admission","end")?;
    t.mark("producer","begin")?;let started=Instant::now();let sub=Instant::now();
    let graph=Graph::new(&a)?;crate::packed_owner_assembly::validate_native_plan_input(&graph.consumer.parent,&input)?;drop(input);
    let(context,_)=ProofContext::historical_h12(&graph.consumer,&a)?;subtimes[0]=ns(sub)?;
    let normal=context.transcript(role,&a.key,&a.commitment);
    let nofault=context.historical49_control_prefix(role,&a.key,&a.commitment,Historical49PrefixFault::NoFault)?;
    need(snapshot(&normal)?==snapshot(&nofault)?,"historical52 preproof NoFault identity")?;
    need(counters(&normal)[..2]==[0,0],"historical52 preproof freshness")?;drop(normal);drop(nofault);
    let sub=Instant::now();let produced=prove_role_historical52(&context,&source,&a,role)?;subtimes[1]=ns(sub)?;
    let Historical52Produced{legacy,fast}=produced;
    let Historical49Produced{proof,claim,counters:sender_counts,continuation:sender_next,io:proof_io,shape,edge,packed,component_bound,census}=legacy;
    let disjoint=u128::from(edge.census_ns[0])+u128::from(edge.census_ns[1])+u128::from(edge.high_ns[0])+u128::from(edge.high_ns[1])
        +edge.pass_ns.iter().map(|v|u128::from(*v)).sum::<u128>()+u128::from(fast.whole_ns);
    need(disjoint<=u128::from(subtimes[1]),"historical52 disjoint kernel timers")?;
    let proof_bytes=gkr::encode_proof(&proof)?;need(proof_bytes.len()==7264,"historical52 proof extent")?;drop(proof);
    let sender=Claim{point:claim.point,value:claim.value};
    close_reference(&reference,&proof_bytes,&sender,sender_counts,sender_next)?;
    times[1]=ns(started)?;t.mark("producer","end")?;
    drop(context);drop(graph);need(graph_counts()==[0,1,1,1],"historical52 producer dropped")?;t.mark("producer_drop","end")?;
    t.mark("export","begin")?;let started=Instant::now();
    write_new(&dir.join("statement.bin"),&a.frame)?;write_new(&dir.join("commitment.bin"),&a.commitment)?;
    write_new(&dir.join(proof_name),&proof_bytes)?;roster(&dir,role,false)?;
    let frame=read_export(&dir,role,"statement.bin",&a.frame)?;let commitment=read_export(&dir,role,"commitment.bin",&a.commitment)?;
    let packet=RoleProof{role,bytes:read_export(&dir,role,proof_name,&proof_bytes)?};drop(proof_bytes);
    times[2]=ns(started)?;t.mark("export","end")?;
    t.mark("consumer","begin")?;let started=Instant::now();let sub=Instant::now();
    let receiver_a=Historical47Admission::new(&frame,&key.bytes,&meta.bytes,&commitment)?;
    let graph=Graph::new(&receiver_a)?;let(context,_)=ProofContext::historical_h12(&graph.consumer,&receiver_a)?;subtimes[2]=ns(sub)?;
    let sub=Instant::now();let verified=context.verify_role(&packet,&receiver_a.key,&receiver_a.commitment)
        .map_err(|e|format!("historical52 receiver {:?}",e.stage))?;subtimes[3]=ns(sub)?;
    need(verified.role==role&&verified.observation.canonical_decode&&verified.observation.verifier_entered
        &&verified.observation.prefix_challenges==0&&verified.observation.prefix_raw_queries==0,"historical52 actual receiver")?;
    need(verified.claim==sender&&verified.counters==sender_counts&&verified.continuation==sender_next,"historical52 sender receiver identity")?;
    source.reset_io_metrics();let sub=Instant::now();let mle=source.evaluate(&verified.claim.point)?;subtimes[4]=ns(sub)?;
    let mle_io=source.io_metrics_snapshot();need(mle==verified.claim.value,"historical52 held PACK MLE")?;
    receiver_controls(&context,&packet,&receiver_a,&verified)?;
    times[3]=ns(started)?;t.mark("consumer","end")?;
    drop(context);drop(graph);need(graph_counts()==[0,1,2,2],"historical52 receiver dropped")?;t.mark("consumer_drop","end")?;
    t.mark("public_bindings","begin")?;let started=Instant::now();
    public_controls(&public,&packet,&key.bytes,&meta.bytes,&c.bytes)?;
    times[4]=ns(started)?;t.mark("public_bindings","end")?;
    let left=side_summary(&edge.left_counts)?;let right=side_summary(&edge.right_counts)?;
    let mut data=ResultData{fast,role,shape,edge,packed,component_bound,census,left,right,public,frame_sha:h41_sha(&frame)?,proof_sha:h41_sha(&packet.bytes)?,sender,receiver:verified.claim,
        sender_counts,receiver_counts:verified.counters,sender_next,receiver_next:verified.continuation,
        prefix:[verified.observation.prefix_challenges,verified.observation.prefix_raw_queries,verified.observation.prefix_bytes],mle,
        times,subtimes,actual_source_digest,binding_io,proof_io,mle_io,graphs:graph_counts()};
    t.mark("claim_controls","begin")?;let started=Instant::now();claim_controls(&data)?;
    times[5]=ns(started)?;t.mark("claim_controls","end")?;
    t.mark("custody","begin")?;let started=Instant::now();
    raw.rehash(false)?;pack.rehash(true)?;key.rehash(false)?;c.rehash(false)?;meta.rehash(false)?;
    reference.check()?;
    need(graph_counts()==[0,1,6,6],"historical52 final graph ledger")?;
    times[6]=ns(started)?;t.mark("custody","end")?;
    t.mark("result","begin")?;let started=Instant::now();data.times=times;
    // The seven exported durations exclude this result's own write/replay.
    // Its eighth duration is observed in the final stdout envelope instead.
    let result=serde_json::to_vec(&report(&data)?).map_err(|_|"historical52 report encoding")?;
    need(result.len()<=16384,"historical52 report cap")?;write_new(&dir.join("result.json"),&result)?;roster(&dir,role,true)?;
    let replay=read_export(&dir,role,"result.json",&result)?;
    let replay:serde_json::Value=serde_json::from_slice(&replay).map_err(|_|"historical52 result replay")?;result_claims(&replay,&data)?;
    read_export(&dir,role,"statement.bin",&frame)?;read_export(&dir,role,"commitment.bin",&commitment)?;read_export(&dir,role,proof_name,&packet.bytes)?;
    let result_export_ns=ns(started)?;t.mark("result","end")?;
    let envelope=serde_json::to_vec(&serde_json::json!({"report":replay,"result_export_ns":result_export_ns})).map_err(|_|"historical52 envelope encoding")?;
    need(envelope.len()<=16384,"historical52 envelope cap")?;
    t.mark("complete","end")?;
    println!("\nHISTORICAL32_ROLE6_52 {}",String::from_utf8(envelope).map_err(|_|"historical52 report UTF8")?);Ok(())
}

fn rejected<T>(value:Result<T,String>,message:&str)->Result<(),String>{
    need(value.err().as_deref()==Some(message),"historical52 ordinary failure attribution")
}
fn admission_controls(public:&Public)->Result<(),String>{
    let graph=Graph::from_public(public)?;
    let parts=RelationParts::compile(graph.consumer.layout_refs(),HeightBinding::HistoricalDiagnostic)?;
    let frame=historical47_frame(public)?;
    let key22=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    for role in [6]{
        let admit=|refs:RelationRefs<'_, '_>,len,log,bytes:&[u8]|historical52_admit(&graph.consumer,refs,role,len,log,bytes);
        let shape=admit(parts.refs(),1usize<<32,32,&frame)?;historical49_shape_policy(&shape)?;
        let mut refs=parts.refs();refs.mode=HeightBinding::LegacyN3N4;
        rejected(admit(refs,1usize<<32,32,&frame),"historical49 historical mode")?;
        for size in [(1usize<<32)-1,(1usize<<32)+1]{rejected(admit(parts.refs(),size,32,&frame),"historical49 source extent")?;}
        rejected(admit(parts.refs(),1usize<<32,key22.log_n(),&frame),"historical49 key dimension")?;
        let mut bad_frame=frame.clone();bad_frame[139]^=1;
        rejected(admit(parts.refs(),1usize<<32,32,&bad_frame),"historical49 candidate frame")?;
        let mut g=parts.geometry.clone();g.row_bits[role]+=1;let mut refs=parts.refs();refs.geometry=&g;
        rejected(admit(refs,1usize<<32,32,&frame),"admission47 geometry")?;
        for fault in 0..5{let mut bad=shape.clone();match fault{0=>bad.base+=1,1=>bad.family+=1,2=>bad.terms+=1,
            3=>bad.challenges+=1,_=>{bad.strides.pop();}}
            rejected(historical49_shape_policy(&bad),"historical49 endpoint shape/census")?;}
        let mut bad=shape.clone();bad.strides[0]=bad.base+1;
        rejected(historical49_shape_policy(&bad),"historical49 endpoint strides")?;
    }
    for role in [0,1,2,3,4,5,7]{rejected(historical52_admit(&graph.consumer,parts.refs(),role,1usize<<32,32,&frame),
        "historical52 closed role6")?;}
    // The production guard and this fault use the same borrowed-reference check.
    {let foreign=WorkTreeHistoryPlan::compile(public.headers,12,public.root,public.total)?;
        let mut refs=parts.refs();refs.layouts.parent=&foreign;
        rejected(historical52_admit(&graph.consumer,refs,6,1usize<<32,32,&frame),"admission47 parent identity")?;}
    drop(parts);drop(graph);need(graph_counts()==[0,1,1,1],"historical52 ordinary graph dropped")
}
fn census_controls()->Result<(),String>{
    use sparse_stream_roster::EdgeFullEvent;
    fn event(left:bool,terms:u64)->EdgeFullEvent{EdgeFullEvent{stage:if left{"census_left"}else{"census_right"},
        event:b'p',round:0,owners:4096,terms}}
    for role in [6]{let expected=historical49_role(role)?.3;
        let mut good=Historical49Census::new(expected)?;
        good.observe(event(true,expected))?;good.observe(event(false,expected))?;good.complete()?;
        let mut t=Transcript::new(b"historical52-census-controls-v1");let called=std::cell::Cell::new(false);
        good.try_bind(&mut t,|t|{called.set(true);t.append_bytes(b"binder-control",b"reached");})?;
        need(called.get()&&counters(&t)[..2]==[0,0],"historical52 census golden binder")?;
        for fault in 0..7{let mut bad=Historical49Census::new(expected)?;
            let message=match fault{
                0=>{rejected(bad.observe(event(true,expected+1)),"historical49 left census")?;"historical49 incomplete census"},
                1=>{bad.observe(event(true,expected))?;rejected(bad.observe(event(false,expected+1)),"historical49 right census")?;"historical49 incomplete census"},
                2=>"historical49 incomplete census",
                3=>{bad.observe(event(true,expected))?;"historical49 incomplete census"},
                4=>{bad.observe(event(true,expected))?;rejected(bad.observe(event(true,expected)),"historical49 census completion order")?;"historical49 incomplete census"},
                5=>{rejected(bad.observe(event(false,expected)),"historical49 census completion order")?;"historical49 incomplete census"},
                _=>{bad.observe(event(true,expected))?;bad.observe(event(false,expected))?;
                    rejected(bad.observe(event(false,expected)),"historical49 census completion order")?;"historical49 incomplete census"},
            };
            let mut t=Transcript::new(b"historical52-census-controls-v1");let before=snapshot(&t)?;
            let called=std::cell::Cell::new(false);
            rejected(bad.try_bind(&mut t,|_|called.set(true)),message)?;
            need(!called.get()&&snapshot(&t)?==before,"historical52 rejected census before FS")?;
        }
        let mut bad=Historical49Census::new(expected)?;let mut marker=event(true,expected);marker.round=1;
        rejected(bad.observe(marker),"historical49 census marker")?;
        let mut bad=Historical49Census::new(expected)?;bad.events=1024;
        rejected(bad.observe(event(true,expected)),"historical49 bounded observer")?;
    }Ok(())
}
fn maximal_stats()->(sparse_stream_roster::EdgeFullStats,sparse_stream_roster::PackedEdgeMetrics){
    let m=u64::MAX;let z=usize::MAX;
    let edge=sparse_stream_roster::EdgeFullStats{term_callbacks:m,owner_requests:m,emitted_fields:m,prefix_plans:m,suffix_tables:m,
        pattern_tables:m,sequential_x_folds:m,sequential_bank_folds:m,input_vector_clones:m,line_internal_clones:m,line_cloned_fields:m,
        prefix_full:z,prefix_suffix:z,prefix_patterns:z,prefix_metadata:z,banks:z,x:z,row_lookup:z,u_weights:z,owner_weights:z,
        prefix_build_ns:m,message_ns:m,line_ns:m,census_ns:[m;2],high_ns:[m;2],pass_ns:vec![m;42],left_counts:Vec::new(),right_counts:Vec::new()};
    let packed=sparse_stream_roster::PackedEdgeMetrics{logical_gets:m,scalar_gets:m,successful_loads:m,packed_bytes:m,
        vector_expansions:m,expanded_fields:m,load_ns:m,decode_ns:m,packet_capacity_peak_bytes:z,cache_capacity_peak_bytes:z,
        metadata_capacity_bytes:z,projection_calls:m,projection_fields:m,projection_ns:m};(edge,packed)
}
// Arithmetic fixtures exercise the actual statistics consumer, not GKR or
// measured telemetry. Native captures supply the returned kernel observations.
fn statistics_fixture(shape:&Historical49Shape)->(sparse_stream_roster::EdgeFullStats,
    sparse_stream_roster::PackedEdgeMetrics,packed::PackedIoSnapshot){
    let t=shape.terms;let mut counts=vec![0usize;4096];counts[0]=t as usize;
    let edge=sparse_stream_roster::EdgeFullStats{term_callbacks:44*t,owner_requests:176128,emitted_fields:17179860992,
        prefix_plans:42,suffix_tables:36,pattern_tables:40,line_internal_clones:0,line_cloned_fields:0,
        left_counts:counts.clone(),right_counts:counts,pass_ns:vec![0;42],..Default::default()};
    let packed=sparse_stream_roster::PackedEdgeMetrics{scalar_gets:21*t,logical_gets:21*t+176128,successful_loads:1,
        packed_bytes:131072,vector_expansions:8192,expanded_fields:8589934592,projection_calls:163840,
        projection_fields:8589926400,metadata_capacity_bytes:400,..Default::default()};
    let io=packed::PackedIoSnapshot{read_calls:1,read_bytes:131072,..Default::default()};(edge,packed,io)
}
fn maximal_fast()->sparse_stream_roster::PackedLineStats{
    let m=u64::MAX;let z=usize::MAX;
    sparse_stream_roster::PackedLineStats{builds:m,owners:m,coefficients:m,input_expanded_fields:m,lut_fields:z,work_fields:z,
        result_fields:z,plan_reserved_bytes:z,plan_actual_bytes:z,extra_reserved_bytes:z,component_bound:z,
        build_ns:m,apply_ns:m,whole_ns:m}
}
fn fast_fixture(metadata:usize)->Result<sparse_stream_roster::PackedLineStats,String>{
    let(bound,plan,extra)=sparse_stream_roster::packed_line52_reservation_for_test(metadata)?;
    Ok(sparse_stream_roster::PackedLineStats{builds:1,owners:4096,coefficients:86016,input_expanded_fields:0,
        lut_fields:1024,work_fields:524288,result_fields:21,plan_reserved_bytes:plan,plan_actual_bytes:plan,
        extra_reserved_bytes:extra,component_bound:bound,build_ns:5,apply_ns:7,whole_ns:12})
}
fn statistics_controls()->Result<(),String>{
    let(base,family,_,terms,challenges)=historical49_role(6)?;
    let shape=Historical49Shape{role:6,base,family,strides:vec![12],terms,challenges};
    let(e,p,io)=statistics_fixture(&shape);let fast=fast_fixture(p.metadata_capacity_bytes)?;
    need(historical52_stats(&shape,&e,&p,&fast,&io)?==fast.component_bound,"historical52 statistics golden")?;
    need(fast.plan_reserved_bytes==16814656&&fast.extra_reserved_bytes==33024,"historical52 capacity reservation ledger")?;
    for fault in 0..16{
        let(mut e,p,io)=statistics_fixture(&shape);let fast=fast_fixture(p.metadata_capacity_bytes)?;
        match fault{0=>{e.left_counts.pop();},1=>{e.right_counts.pop();},2=>e.left_counts[0]+=1,3=>e.right_counts[0]+=1,
            4=>e.term_callbacks+=1,5=>e.owner_requests+=1,6=>e.emitted_fields+=1,7=>e.prefix_plans+=1,
            8=>e.suffix_tables+=1,9=>e.pattern_tables+=1,10=>e.sequential_x_folds=1,11=>e.sequential_bank_folds=1,
            12=>e.input_vector_clones=1,13=>e.line_internal_clones=1,14=>e.line_cloned_fields=1,_=>{e.pass_ns.pop();}}
        rejected(historical52_stats(&shape,&e,&p,&fast,&io),"historical52 direct census statistics")?;
    }
    for fault in 0..15{
        let(e,mut p,mut io)=statistics_fixture(&shape);let fast=fast_fixture(p.metadata_capacity_bytes)?;
        match fault{0=>p.scalar_gets+=1,1=>p.logical_gets+=1,2=>p.vector_expansions+=1,3=>p.expanded_fields+=1,
            4=>p.projection_calls+=1,5=>p.projection_fields+=1,6=>p.packed_bytes+=1,7=>p.successful_loads=0,
            8=>io.read_calls+=1,9=>io.read_bytes+=1,10=>io.write_calls=1,11=>io.write_bytes=1,12=>io.write_ns=1,
            13=>io.sync_calls=1,_=>io.sync_ns=1}
        rejected(historical52_stats(&shape,&e,&p,&fast,&io),"historical52 packed census statistics")?;
    }
    for fault in 0..14{
        let(e,p,io)=statistics_fixture(&shape);let mut fast=fast_fixture(p.metadata_capacity_bytes)?;
        match fault{0=>fast.builds+=1,1=>fast.owners+=1,2=>fast.coefficients+=1,3=>fast.input_expanded_fields=1,
            4=>fast.lut_fields+=1,5=>fast.work_fields+=1,6=>fast.result_fields+=1,7=>fast.plan_reserved_bytes+=1,
            8=>fast.plan_actual_bytes+=1,9=>fast.extra_reserved_bytes+=1,10=>fast.component_bound+=1,
            11=>fast.build_ns=13,12=>fast.apply_ns=13,_=>fast.whole_ns=11}
        rejected(historical52_stats(&shape,&e,&p,&fast,&io),"historical52 packed line statistics")?;
    }
    for fault in 0..11{
        let(mut e,mut p,io)=statistics_fixture(&shape);let fast=fast_fixture(p.metadata_capacity_bytes)?;
        match fault{0=>p.packet_capacity_peak_bytes=131073,1=>p.cache_capacity_peak_bytes=524689,
            2=>e.prefix_full=33554433,3=>e.prefix_suffix=4194305,4=>e.prefix_patterns=8193,5=>e.prefix_metadata=1025,
            6=>e.banks=100663297,7=>e.x=33554433,8=>e.row_lookup=65537,9=>e.u_weights=33554433,_=>e.owner_weights=131073}
        rejected(historical52_stats(&shape,&e,&p,&fast,&io),"historical52 direct component capacity")?;
    }
    let(e,mut p,io)=statistics_fixture(&shape);p.metadata_capacity_bytes=536870912;
    rejected(historical52_stats(&shape,&e,&p,&fast,&io),"historical52 component bound")
}
fn ordinary()->Result<(),String>{
    binding_controls()?;
    reference_controls()?;
    census_controls()?;
    statistics_controls()?;
    sparse_stream_roster::packed_line52_controls_for_test()?;
    let p=Public{headers:3073,root:[2;32],total:[3;28],tip:[4;32],tip_time:5};let frame=historical47_frame(&p)?;
    admission_controls(&p)?;
    need(frame.len()==571&&historical47_frame(&historical47_decode(&frame)?)?==frame,"historical52 frame roundtrip")?;
    need(&frame[255..265]==b"corepool11"&&u64::from_le_bytes(frame[265..273].try_into().map_err(|_|"historical52 frame input")?)==32
        &&u64::from_le_bytes(frame[273..281].try_into().map_err(|_|"historical52 frame row")?)==33,"historical52 frame offsets")?;
    let key22=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;need(key22.log_n()==22,"historical52 real key22")?;
    let bytes=vec![0u8;7264];let proof=gkr::decode_dimensions(&[32],&bytes)?;
    need(proof.layers.len()==1&&proof.layers[0].rounds.len()==64&&proof.layers[0].line_coefficients.len()==33
        &&gkr::encode_proof(&proof)?==bytes,"historical52 codec-only shape fixture")?;
    for n in [7263,7265]{need(gkr::decode_dimensions(&[32],&vec![0;n]).is_err(),"historical52 codec extent negative")?;}
    let mut bad=bytes;bad[..32].fill(255);need(gkr::decode_dimensions(&[32],&bad).is_err(),"historical52 codec canonical negative")?;
    let scalar=serde_json::json!(h41_fr(Fr::one()));need(fr_from_json(&scalar)?==Fr::one(),"historical52 scalar golden")?;
    need(fr_from_json(&serde_json::json!("f".repeat(64))).is_err(),"historical52 scalar canonical negative")?;
    let claim=Claim{point:vec![Fr::zero();32],value:Fr::one()};let m=u64::MAX;
    let io=packed::PackedIoSnapshot{read_calls:m,read_bytes:m,read_ns:m as u128,write_calls:m,write_bytes:m,write_ns:m as u128,sync_calls:m,sync_ns:m as u128};
    let(edge,packed)=maximal_stats();let mut census=Historical49Census::new(m)?;census.left=Some(m);census.right=Some(m);census.events=m;
    let shape=Historical49Shape{role:6,base:usize::MAX,family:usize::MAX,strides:vec![usize::MAX;1],terms:m,challenges:m};
    let d=ResultData{fast:maximal_fast(),role:6,shape,edge,packed,component_bound:usize::MAX,census,left:[m;4],right:[m;4],
        public:Public{tip_time:i64::MIN,..p},frame_sha:"F".repeat(64),proof_sha:"F".repeat(64),sender:claim.clone(),receiver:claim,
        sender_counts:[m;3],receiver_counts:[m;3],sender_next:Fr::one(),receiver_next:Fr::one(),prefix:[m;3],mle:Fr::one(),
        times:[m;7],subtimes:[m;5],actual_source_digest:"f".repeat(64),binding_io:io,proof_io:io,mle_io:io,graphs:[m;4]};
    let report=report(&d)?;let result=serde_json::to_vec(&report).map_err(|_|"historical52 report encoding")?;
    let envelope=serde_json::to_vec(&serde_json::json!({"report":report,"result_export_ns":m})).map_err(|_|"historical52 envelope encoding")?;
    need(result.len()<16384&&envelope.len()<16384&&envelope.len()+8192<65536,"historical52 maximal serializers")?;
    claim_controls(&d)?;need(graph_counts()==[0,1,1,1],"historical52 ordinary graph closure")
}
#[test]
fn historical52_ordinary()->Result<(),String>{ordinary()}
fn native(role:usize){
    let mut t=Trace{start:Instant::now(),next:0};
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(&mut t,role)));
    let error=match result{Ok(Ok(()))=>return,Ok(Err(e))=>e,Err(_)=>"historical52 panic".into()};
    let reason:String=error.chars().filter(|v|v.is_ascii_graphic()||*v==' ').take(160).collect();
    eprintln!("HISTORICAL32_ROLE6_52_HOLD {} {} {reason}",t.next,t.start.elapsed().as_nanos());panic!("historical52 HOLD");
}

#[test]
#[ignore]
fn historical52_role6(){native(6)}

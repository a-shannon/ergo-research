//! Provisional Historical seven-role/common PCS diagnostic. Import/runtime
//! authority and actual50 closure belong to the separately reviewed parent.
use super::*;
use crate::{gkr,historical_prefix_proof::{self as historical,Historical51PublicBytes,Historical51TrustedKeyPolicy,
    Historical51Diagnostics,Historical51ByteSuccess},native_prefix_auth_plan::role0_sha256};
use ark_serialize::CanonicalSerialize;
use blake2::{digest::consts::U32,Blake2b,Digest};
use dory_pcs::backends::arkworks::{ArkG1,ArkG2,ArkGT,ArkworksVerifierSetup};
use serde_json::{json,Value};
use std::{fs::{File,OpenOptions},io::{Read,Seek,SeekFrom,Write},mem::{size_of,size_of_val},path::{Path,PathBuf}};
use std::os::windows::{fs::{OpenOptionsExt,MetadataExt},io::AsRawHandle};

const PUBLIC_NAMES:[&str;10]=["statement.bin","commitment.bin","role-0.gkr","role-1.gkr","role-2.gkr",
    "role-3.gkr","role-4.gkr","role-5.gkr","role-6.gkr","common-opening.bin"];
const EXTENTS:[usize;7]=[7264,7264,7264,5696,7264,7264,7264];
const COMMON_CAP:usize=65536;
const PACKAGE_CAP:usize=131072;
const REPORT_CAP:usize=16384;
const METADATA_CAP:usize=8*1024*1024;
const COMPONENT_CAP:usize=512*1024*1024;
const CONTINUATION:&[u8]=b"native-seven-distinct-join-continuation-v1";
const PRODUCER_STAGES:[&str;13]=["start","admission","assembly","source_binding","setup","commit","frontend","open","codec","drop","export","custody","complete"];
const RECEIVER_STAGES:[&str;4]=["start","admission","consume","custody_complete"];
const NEGATIVE_STAGES:[&str;4]=["start","admission","negatives","custody_complete"];

fn need(ok:bool,error:&str)->Result<(),String>{if ok{Ok(())}else{Err(error.into())}}
fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("common51 capacity overflow".into())}
fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or("common51 capacity overflow".into())}
fn cap<T>(v:&Vec<T>)->Result<usize,String>{mul(v.capacity(),size_of::<T>())}
fn ns(start:Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"common51 clock overflow".into())}
fn narrow(n:u128)->Result<u64,String>{u64::try_from(n).map_err(|_|"common51 observation clock overflow".into())}
fn hex(b:&[u8])->String{b.iter().map(|v|format!("{v:02X}")).collect()}
fn scalar(v:&Fr)->Result<String,String>{let mut b=[0;32];v.serialize_compressed(&mut b[..]).map_err(|_|"common51 scalar codec")?;
    Ok(b.iter().map(|v|format!("{v:02x}")).collect())}
fn sha(b:&[u8])->Result<String,String>{Ok(hex(&role0_sha256(b)?))}
fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
fn claims_digest(claims:&[Claim;7])->Result<String,String>{
    need(claims.iter().all(|c|c.point.len()==32),"common51 claim dimensions")?;
    let mut bytes=Vec::with_capacity(7*33*32);
    for c in claims{for v in c.point.iter().chain(std::iter::once(&c.value)){v.serialize_compressed(&mut bytes).map_err(|_|"common51 claim codec")?;}}
    need(bytes.len()==7392,"common51 claim digest extent")?;sha(&bytes)
}
fn merge(target:&mut Value,extra:Value)->Result<(),String>{
    let left=target.as_object_mut().ok_or("common51 report target")?;
    for(k,v)in extra.as_object().ok_or("common51 report object")?{
        need(!left.contains_key(k),"common51 duplicate report key")?;left.insert(k.clone(),v.clone());
    }Ok(())
}
struct Limited(Vec<u8>);
impl Write for Limited{
    fn write(&mut self,b:&[u8])->std::io::Result<usize>{if b.len()>REPORT_CAP.saturating_sub(self.0.len()){
        return Err(std::io::Error::other("common51 report cap"));}self.0.extend_from_slice(b);Ok(b.len())}
    fn flush(&mut self)->std::io::Result<()>{Ok(())}
}
fn shape(value:&Value,maximum:&Value)->Result<(),String>{match(value,maximum){
    (Value::Object(a),Value::Object(b))=>{need(a.len()==b.len(),"common51 report key roster")?;
        for(k,v)in b{shape(a.get(k).ok_or("common51 report missing key")?,v)?;}Ok(())},
    (Value::Array(a),Value::Array(b))=>{need(a.len()==b.len(),"common51 report array extent")?;
        for(a,b)in a.iter().zip(b){shape(a,b)?;}Ok(())},
    (Value::String(a),Value::String(b))=>need(a.len()<=b.len(),"common51 report string extent"),
    (Value::Number(a),Value::Number(_))=>need(a.as_u64().is_some(),"common51 report unsigned width"),
    (Value::Bool(_),Value::Bool(_))=>Ok(()),_=>Err("common51 report field type".into())}}
fn encoded_report(v:&Value)->Result<Vec<u8>,String>{
    let mode=v.get("mode").and_then(Value::as_str).ok_or("common51 report mode")?;
    need(v.get("schema").and_then(Value::as_str)==Some("historical32-seven-common51-v1"),"common51 report schema")?;
    need(matches!(v.get("state").and_then(Value::as_str),Some("PASS"|"SIZE_FIXTURE")),"common51 report state")?;
    shape(v,&maximum_report(mode)?)?;let mut out=Limited(Vec::with_capacity(REPORT_CAP));
    serde_json::to_writer(&mut out,v).map_err(|_|"common51 report serializer")?;Ok(out.0)}
fn emit(v:&Value)->Result<(),String>{need(v.get("state").and_then(Value::as_str)==Some("PASS"),"common51 emitted state")?;
    let bytes=encoded_report(v)?;let mut out=std::io::stdout().lock();
    writeln!(out,"\nHISTORICAL_SEVEN_COMMON51 {}",std::str::from_utf8(&bytes).map_err(|_|"common51 report UTF8")?)
        .map_err(|_|"common51 report output")?;out.flush().map_err(|_|"common51 report flush".into())}

fn path_ok(path:&Path)->Result<(),String>{need(path.is_absolute()&&path.as_os_str().len()<=1024,"common51 bounded absolute path")}
fn directory(path:&Path)->Result<(),String>{path_ok(path)?;for p in path.ancestors(){let m=std::fs::symlink_metadata(p).map_err(|_|"common51 directory metadata")?;
    need(m.is_dir()&&m.file_attributes()&0x400==0,"common51 plain directory ancestry")?;}Ok(())}
#[repr(C)]
#[derive(Default,PartialEq,Eq)]
struct Identity{attributes:u32,created:[u32;2],accessed:[u32;2],written:[u32;2],volume:u32,
    size_high:u32,size_low:u32,links:u32,index_high:u32,index_low:u32}
fn identity(file:&File)->Result<Identity,String>{
    #[link(name="kernel32")]extern "system"{fn GetFileInformationByHandle(h:*mut std::ffi::c_void,p:*mut Identity)->i32;}
    let mut id=Identity::default();if unsafe{GetFileInformationByHandle(file.as_raw_handle(),&mut id)}==0{return Err("common51 file identity".into());}
    need(id.attributes&0x410==0&&id.links==1,"common51 ordinary single-link file")?;id.accessed=[0;2];Ok(id)
}
struct Held{path:PathBuf,file:File,id:Identity,bytes:Vec<u8>,sha:String}
impl Held{
    fn open(path:PathBuf,extent:usize)->Result<Self,String>{path_ok(&path)?;directory(path.parent().ok_or("common51 input parent")?)?;
        let m=std::fs::symlink_metadata(&path).map_err(|_|"common51 input metadata")?;
        need(m.is_file()&&m.file_attributes()&0x400==0&&m.len()==extent as u64&&extent<=PACKAGE_CAP,"common51 input type/extent")?;
        let mut file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|_|"common51 held input open")?;
        let id=identity(&file)?;need(((u64::from(id.size_high)<<32)|u64::from(id.size_low))==extent as u64,"common51 held extent")?;
        let mut bytes=Vec::new();bytes.try_reserve_exact(extent).map_err(|_|"common51 held allocation")?;
        Read::by_ref(&mut file).take(extent as u64+1).read_to_end(&mut bytes).map_err(|_|"common51 held read")?;
        need(bytes.len()==extent,"common51 held exact read")?;let sha=sha(&bytes)?;let held=Self{path,file,id,bytes,sha};held.check()?;Ok(held)
    }
    fn env(name:&str,extent:usize)->Result<Self,String>{Self::open(PathBuf::from(std::env::var_os(name).ok_or("common51 input env absent")?),extent)}
    fn check(&self)->Result<(),String>{directory(self.path.parent().ok_or("common51 input parent")?)?;
        need(identity(&self.file)?==self.id,"common51 held identity changed")?;
        let mut reader=self.file.try_clone().map_err(|_|"common51 held clone")?;reader.seek(SeekFrom::Start(0)).map_err(|_|"common51 held seek")?;
        let mut bytes=Vec::new();bytes.try_reserve_exact(self.bytes.len()).map_err(|_|"common51 custody allocation")?;
        reader.take(self.bytes.len() as u64+1).read_to_end(&mut bytes).map_err(|_|"common51 custody read")?;
        need(bytes==self.bytes&&sha(&bytes)?==self.sha,"common51 held bytes changed")?;
        let named=OpenOptions::new().read(true).share_mode(1).open(&self.path).map_err(|_|"common51 named input")?;
        need(identity(&named)?==self.id,"common51 named identity changed")
    }
    fn heap(&self)->Result<usize,String>{add(add(self.bytes.capacity(),self.sha.capacity())?,mul(self.path.capacity(),size_of::<u16>())?)}
}
fn env_path(name:&str)->Result<PathBuf,String>{let path=PathBuf::from(std::env::var_os(name).ok_or("common51 env absent")?);path_ok(&path)?;Ok(path)}
fn extent(index:usize,dir:&Path)->Result<usize,String>{match index{0=>Ok(571),1=>Ok(384),2..=8=>Ok(EXTENTS[index-2]),9=>{
    let m=std::fs::symlink_metadata(dir.join(PUBLIC_NAMES[9])).map_err(|_|"common51 common metadata")?;
    need(m.is_file()&&m.file_attributes()&0x400==0&&m.len()>0&&m.len()<=COMMON_CAP as u64,"common51 common bound")?;Ok(m.len() as usize)},_=>Err("common51 member index".into())}}
fn roster(dir:&Path,complete:bool)->Result<(),String>{directory(dir)?;let count=if complete{10}else{9};let mut names=Vec::with_capacity(count);
    for entry in std::fs::read_dir(dir).map_err(|_|"common51 package scan")?{need(names.len()<count,"common51 extra package member")?;
        let entry=entry.map_err(|_|"common51 package entry")?;names.push(entry.file_name().into_string().map_err(|_|"common51 package UTF8")?);}
    need(names.len()==count&&PUBLIC_NAMES[..count].iter().all(|n|names.iter().filter(|s|s.as_str()==*n).count()==1),"common51 exact public roster")
}
fn read_public(complete:bool)->Result<(PathBuf,Vec<Held>),String>{let dir=env_path("NIPOPOW_COMMON51_PUBLIC_DIR")?;roster(&dir,complete)?;
    let mut held=Vec::with_capacity(if complete{10}else{9});let mut total=0;
    for i in 0..if complete{10}else{9}{let n=extent(i,&dir)?;total=add(total,n)?;need(total<=PACKAGE_CAP,"common51 public package bound")?;
        held.push(Held::open(dir.join(PUBLIC_NAMES[i]),n)?);}Ok((dir,held))}
fn views<'a>(held:&'a[Held],common:&'a[u8])->Result<Historical51PublicBytes<'a>,String>{need(held.len()==9||held.len()==10,"common51 view roster")?;
    Ok(Historical51PublicBytes{frame:&held[0].bytes,commitment:&held[1].bytes,roles:std::array::from_fn(|i|held[i+2].bytes.as_slice()),common})}
fn key_pair()->Result<(Held,Held),String>{Ok((Held::env("NIPOPOW_COMMON51_KEY_PATH",33264)?,Held::env("NIPOPOW_COMMON51_KEY_METADATA_PATH",40)?))}
fn environment(mode:&str)->Result<(),String>{
    let mut names=vec!["NIPOPOW_COMMON51_PUBLIC_DIR","NIPOPOW_COMMON51_KEY_PATH","NIPOPOW_COMMON51_KEY_METADATA_PATH"];
    if mode=="producer"{names.extend(["NIPOPOW_COMMON51_PACK_PATH","NIPOPOW_COMMON51_OLD_OPENING_PATH","NIPOPOW_COMMON51_OUTPUT_DIR"]);}
    for(k,_)in std::env::vars_os(){let key=k.to_string_lossy().to_ascii_uppercase();
        if key.starts_with("NIPOPOW_"){need(names.iter().any(|n|*n==key),"common51 unexpected authority env")?;}}
    need(names.iter().all(|n|std::env::var_os(n).is_some()),"common51 missing authority env")
}
struct Clock{mode:&'static str,start:Instant,next:usize,marks:Vec<u64>}
impl Clock{
    fn new(mode:&'static str)->Self{Self{mode,start:Instant::now(),next:0,marks:Vec::with_capacity(13)}}
    fn stages(&self)->&'static[&'static str]{match self.mode{"producer"=>&PRODUCER_STAGES,"receiver"=>&RECEIVER_STAGES,_=>&NEGATIVE_STAGES}}
    fn tick(&mut self,name:&str)->Result<(),String>{need(self.stages().get(self.next)==Some(&name),"common51 closed stage order")?;
        let elapsed=ns(self.start)?;let mut out=std::io::stderr().lock();writeln!(out,"HISTORICAL_SEVEN_COMMON51_STAGE {} {} {} {}",self.mode,self.next,name,elapsed)
            .map_err(|_|"common51 stage output")?;out.flush().map_err(|_|"common51 stage flush")?;self.marks.push(elapsed);self.next+=1;Ok(())}
}
fn metadata(held:&Vec<Held>,key:&Held,meta:&Held,extra:usize)->Result<usize,String>{let mut n=add(cap(held)?,add(size_of::<Held>()*2,extra)?)?;
    for h in held.iter().chain([key,meta]){n=add(n,h.heap()?)?;}n=add(n,4*1024*1024)?;
    need(n<=METADATA_CAP,"common51 metadata capacity")?;Ok(n)}
fn setup_capacity(setup:&Setup)->Result<usize,String>{let mut n=add(size_of::<Setup>(),add(cap(&setup.prover.g1_vec)?,cap(&setup.prover.g2_vec)?)?)?;
    let v=&setup.verifier;for x in [&v.delta_1l,&v.delta_1r,&v.delta_2l,&v.delta_2r,&v.chi]{n=add(n,cap(x)?)?;}Ok(n)}
fn producer_bound(retained:usize,setup:usize,rows:usize,row_clone:usize)->Result<usize,String>{
    let n=add(add(add(add(add(retained,setup)?,rows)?,row_clone)?,FRONTEND_CAPACITY_LIMIT)?,96*1024*1024)?;
    need(n<=COMPONENT_CAP,"common51 producer preflight capacity")?;Ok(n)}
fn actual_bound(actual:usize,preflight:usize)->Result<(),String>{need(actual<=preflight&&preflight<=COMPONENT_CAP,"common51 actual producer capacity")}
fn io(v:crate::packed::PackedIoSnapshot)->Result<Value,String>{need(v.write_calls==0&&v.write_bytes==0&&v.sync_calls==0,"common51 packed readonly")?;
    Ok(json!({"read_calls":v.read_calls,"read_bytes":v.read_bytes,"read_ns":narrow(v.read_ns)?}))}
fn base(mode:&str,clock:&Clock)->Result<Value,String>{need(clock.next==clock.stages().len(),"common51 incomplete phases")?;
    Ok(json!({"schema":"historical32-seven-common51-v1","state":"PASS","mode":mode,"marks_ns":clock.marks,
        "scope":{"roles":[0,1,2,3,4,5,6],"input_log":32,"full_history":false,"production":false}}))}
fn inputs(held:&[Held],key:&Held,meta:&Held,common:&[u8])->Result<Value,String>{
    Ok(json!({"frame_sha256":held[0].sha,"commitment_sha256":held[1].sha,"key_sha256":key.sha,"metadata_sha256":meta.sha,
        "role_sha256":held[2..9].iter().map(|h|h.sha.as_str()).collect::<Vec<_>>(),"common_sha256":sha(common)?}))}
fn export(held:&[Held],common:&[u8])->Result<(Vec<Held>,usize),String>{let dir=env_path("NIPOPOW_COMMON51_OUTPUT_DIR")?;directory(&dir)?;
    need(std::fs::read_dir(&dir).map_err(|_|"common51 output scan")?.next().is_none(),"common51 output not empty")?;
    let mut retained=Vec::with_capacity(10);let mut total=0;
    for i in 0..10{let bytes=if i==9{common}else{held[i].bytes.as_slice()};total=add(total,bytes.len())?;need(total<=PACKAGE_CAP,"common51 output package bound")?;
        let path=dir.join(PUBLIC_NAMES[i]);let mut out=OpenOptions::new().write(true).create_new(true).share_mode(1).open(&path).map_err(|_|"common51 export create")?;
        out.write_all(bytes).map_err(|_|"common51 export write")?;out.sync_all().map_err(|_|"common51 export sync")?;drop(out);
        let readback=Held::open(path,bytes.len())?;need(readback.bytes==bytes,"common51 export readback")?;retained.push(readback);}
    roster(&dir,true)?;Ok((retained,total))}

fn producer(clock:&mut Clock)->Result<Value,String>{
    environment("producer")?;clock.tick("start")?;let(input_dir,held)=read_public(false)?;let(key,meta)=key_pair()?;
    let old=Held::env("NIPOPOW_COMMON51_OLD_OPENING_PATH",45501)?;let policy=Historical51TrustedKeyPolicy::fixed32_testonly();
    let retained=metadata(&held,&key,&meta,add(size_of_val(&old),old.heap()?)?)?;clock.tick("admission")?;
    let derived=historical::prepare_historical_h12_opening51(&views(&held,&old.bytes)?,&key.bytes,&meta.bytes,&policy)?;
    // A has dropped its only graph; only producer opening input crosses to B.
    let role_continuations=derived.role_continuations.iter().map(scalar).collect::<Result<Vec<_>,_>>()?;
    let role_ns=derived.role_ns.iter().map(|n|narrow(*n)).collect::<Result<Vec<_>,_>>()?;
    let points=derived.statement.claims.iter().try_fold(0usize,|n,c|add(n,cap(&c.point)?))?;
    let retained=add(retained,add(size_of_val(&derived),points)?)?;let claims_sha=claims_digest(&derived.statement.claims)?;clock.tick("assembly")?;
    let pack_path=env_path("NIPOPOW_COMMON51_PACK_PATH")?;directory(pack_path.parent().ok_or("common51 PACK parent")?)?;
    let source=PackedFile::open_with_limit(&pack_path,32,32)?;let binding=historical::bind_historical51_packed_source(&source)?;clock.tick("source_binding")?;
    let generator=mul(65536,add(size_of::<ArkG1>(),size_of::<ArkG2>())?)?;let row_bound=mul(65536,size_of::<ArkG1>())?;
    let preflight=producer_bound(retained,add(generator,1024*1024)?,row_bound,row_bound)?;
    let started=Instant::now();let setup=pcs::generate_setup_for_scale_diagnostic(32)?;
    need(setup.id==derived.statement.setup_id&&pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))?==key.bytes,"common51 regenerated key/setup")?;
    let setup_bytes=setup_capacity(&setup)?;need(setup_bytes<=add(generator,1024*1024)?,"common51 setup preflight")?;
    let setup_ns=ns(started)?;clock.tick("setup")?;
    source.reset_io_metrics();let started=Instant::now();let committed=packed::commit(&source,&setup)?;
    need(committed.rows.len()==65536&&committed.nu==16&&committed.sigma==16
        &&pcs::encode_commitment(&committed.commitment)?==held[1].bytes,"common51 regenerated commitment/rows")?;
    let row_bytes=cap(&committed.rows)?;need(row_bytes==row_bound,"common51 row capacity")?;
    let row_clone=mul(committed.rows.len(),size_of::<ArkG1>())?;let bound=producer_bound(retained,setup_bytes,row_bytes,row_clone)?;
    actual_bound(bound,preflight)?;let commit_io=io(source.io_metrics_snapshot())?;let commit_ns=ns(started)?;clock.tick("commit")?;
    source.reset_io_metrics();let started=Instant::now();let mut sender=Transcript::new(DOMAIN);
    let mut audit=FrontendAudit::new(&derived.statement,retained,false)?;
    let frontend=prove_frontend_on_mode(&source,&derived.statement,&mut sender,None,ProjectionMode::Fused,Some(&mut audit))?;
    need(frontend.rounds.len()==32&&frontend.point.len()==32,"common51 complete fixed frontend")?;
    let frontend_ns=ns(started)?;let frontend_io=io(source.io_metrics_snapshot())?;clock.tick("frontend")?;
    source.reset_io_metrics();let started=Instant::now();let opening=packed::open(&committed,&source,&frontend.point,&setup,&mut sender)?;
    let open_ns=ns(started)?;let open_io=io(source.io_metrics_snapshot())?;clock.tick("open")?;
    let started=Instant::now();let proof=Proof{rounds:frontend.rounds,terminal:frontend.terminal,pcs:opening};let common=encode_proof(&proof,32)?;
    need(!common.is_empty()&&common.len()<=COMMON_CAP,"common51 produced common bound")?;
    let decoded=decode_proof(&common,32)?;need(encode_proof(&decoded,32)?==common,"common51 canonical common codec")?;drop(decoded);drop(proof);
    let codec_ns=ns(started)?;clock.tick("codec")?;
    let frontend_owned=audit.stats.state_peak_capacity_bytes;let frontend_bound=audit.stats.preflight_capacity_bound_bytes;
    let common_counters=counters(&sender);let continuation=scalar(&sender.clone().try_challenge_scalar(CONTINUATION)?)?;
    let started=Instant::now();drop(committed);drop(setup);drop(audit);drop(frontend.point);drop(source);let drop_ns=ns(started)?;clock.tick("drop")?;
    let(outputs,package_bytes)=export(&held,&common)?;clock.tick("export")?;
    for h in held.iter().chain([&key,&meta,&old]).chain(outputs.iter()){h.check()?;}roster(&input_dir,false)?;clock.tick("custody")?;clock.tick("complete")?;
    let mut v=base("producer",clock)?;merge(&mut v,json!({"inputs":inputs(&held,&key,&meta,&common)?,"claims_sha256":claims_sha,
        "role_counters":derived.role_counters,"role_continuations":role_continuations,"role_ns":role_ns}))?;
    merge(&mut v,json!({"common":{"bytes":common.len(),"counters":common_counters,"continuation":continuation},
        "assembly":{"old_sha256":old.sha,"old_rejection":derived.old_common_rejection,"old_frontend_entries":derived.diagnostic.frontend_entries,
            "old_pcs_entries":derived.diagnostic.pcs_entries,"role_order":derived.diagnostic.role_completion_order}}))?;
    merge(&mut v,json!({"phase_ns":{"admission":narrow(derived.admission_ns)?,"context":narrow(derived.context_ns)?,"roles":narrow(derived.roles_ns)?,
        "old_common":narrow(derived.old_common_ns)?,"setup":setup_ns,"commit":commit_ns,"frontend":frontend_ns,"open":open_ns,"codec":codec_ns,"drop":drop_ns}}))?;
    merge(&mut v,json!({"memory":{"retained_bound":retained,"setup_owned":setup_bytes,"rows_owned":row_bytes,"row_clone_bound":row_clone,
        "producer_bound":bound,"preflight":preflight,"frontend_owned":frontend_owned,"frontend_bound":frontend_bound,
        "assembly_component":derived.capacity,"opaque_graph_heap_measured":false,"vendor_scratch_measured":false},"package":{"files":outputs.len(),"bytes":package_bytes,"readback":true}}))?;
    merge(&mut v,json!({"io":{"binding":io(binding)?,"commit":commit_io,"frontend":frontend_io,"open":open_io},
        "checks":{"old_rejected_before_setup":true,"actual_reader_bound":true,"key_equal":true,"commitment_equal":true,
            "graph_dropped_before_setup":true,"producer_dropped_before_export":true,"gkr_regenerated":false,"setup_generated":true,"custody":true}}))?;Ok(v)
}

fn receiver(clock:&mut Clock)->Result<Value,String>{
    environment("receiver")?;clock.tick("start")?;let(dir,held)=read_public(true)?;let(key,meta)=key_pair()?;
    let retained=metadata(&held,&key,&meta,size_of::<Historical51ByteSuccess>())?;clock.tick("admission")?;
    let mut diagnostic=Historical51Diagnostics::default();let verified=historical::verify_historical_h12_bytes_observed51(
        &views(&held,&held[9].bytes)?,&key.bytes,&meta.bytes,&Historical51TrustedKeyPolicy::fixed32_testonly(),&mut diagnostic)?;
    need(diagnostic.role_entries==[1;7]&&diagnostic.role_completions==[1;7]&&diagnostic.role_completion_order==[0,1,2,3,4,5,6]
        &&diagnostic.common_entries==1&&diagnostic.pcs_entries==1&&diagnostic.pcs_completions==1&&diagnostic.successes==1,"common51 atomic completion")?;
    clock.tick("consume")?;for h in held.iter().chain([&key,&meta]){h.check()?;}roster(&dir,true)?;clock.tick("custody_complete")?;
    let o=&verified.observations;let mut v=base("receiver",clock)?;
    merge(&mut v,json!({"inputs":inputs(&held,&key,&meta,&held[9].bytes)?,"claims_sha256":claims_digest(&verified.claims)?,
        "role_counters":o.role_counters,"role_continuations":o.role_continuations.iter().map(scalar).collect::<Result<Vec<_>,_>>()?,
        "role_ns":o.role_ns.iter().map(|n|narrow(*n)).collect::<Result<Vec<_>,_>>()?}))?;
    merge(&mut v,json!({"common":{"bytes":held[9].bytes.len(),"counters":o.common_counters,"continuation":scalar(&o.common_continuation)?},
        "phase_ns":{"admission":narrow(o.admission_ns)?,"context":narrow(o.context_ns)?,"roles":narrow(o.roles_ns)?,"common":narrow(o.common_ns)?,
            "frontend":narrow(o.frontend_ns)?,"pcs":narrow(o.pcs_ns)?,"inner_total":narrow(o.total_ns)?}}))?;
    merge(&mut v,json!({"memory":{"retained_bound":retained,"component":o.capacity,"opaque_graph_heap_measured":false,"vendor_scratch_measured":false},
        "package":{"files":held.len(),"bytes":held.iter().map(|h|h.bytes.len()).sum::<usize>()},
        "checks":{"all_seven_derived":true,"canonical_common":true,"pcs_invoked":true,"role_order":diagnostic.role_completion_order,
            "witness_free":true,"setup_generated":false,"gkr_regenerated":false,"custody":true}}))?;Ok(v)
}

fn no_success<T>(result:Result<T,String>,diagnostic:&Historical51Diagnostics,pcs:Option<u8>)->Result<(),String>{
    need(result.is_err()&&diagnostic.successes==0&&pcs.map_or(true,|n|diagnostic.pcs_entries==n),"common51 isolated negative accepted/wrong stage")
}
fn negatives(clock:&mut Clock)->Result<Value,String>{
    environment("negatives")?;clock.tick("start")?;let(dir,held)=read_public(true)?;let(key,meta)=key_pair()?;
    let retained=metadata(&held,&key,&meta,0)?;let policy=Historical51TrustedKeyPolicy::fixed32_testonly();let base_bytes=views(&held,&held[9].bytes)?;
    let admitted=policy.admit_key(&base_bytes,&key.bytes,&meta.bytes)?;clock.tick("admission")?;
    let mut d=Historical51Diagnostics::default();let baseline=historical::verify_historical_h12_bytes_observed51(&base_bytes,&key.bytes,&meta.bytes,&policy,&mut d)?;
    need(d.successes==1&&d.pcs_entries==1,"common51 negative baseline")?;
    let mut role_count=0;let mut public_count=0;let mut commitment_count=0;let mut key_count=0;let mut codec_count=0;let mut frontend_count=0;let mut pcs_count=0;let mut statement_count=0;
    for role in 0..7{let width=if role==3{25}else{32};let mut proof=gkr::decode_dimensions(&[width],base_bytes.roles[role])?;
        proof.layers[0].rounds[0][0]+=Fr::one();let bad=gkr::encode_proof(&proof)?;let mut roles=base_bytes.roles;roles[role]=&bad;
        let bytes=Historical51PublicBytes{frame:base_bytes.frame,commitment:base_bytes.commitment,roles,common:base_bytes.common};let mut d=Historical51Diagnostics::default();
        let result=historical::verify_historical_h12_bytes_observed51(&bytes,&key.bytes,&meta.bytes,&policy,&mut d);
        need(d.role_entries[role]==1&&d.role_completions[role]==0&&d.common_entries==0,"common51 role rejection attribution")?;no_success(result,&d,Some(0))?;role_count+=1;}
    // Fixed frame offsets derive from profile43 + genesis32 + anchor32 + four u64s.
    for at in [139usize,171,199,231]{let mut frame=base_bytes.frame.to_vec();frame[at]^=1;let bytes=Historical51PublicBytes{frame:&frame,
        commitment:base_bytes.commitment,roles:base_bytes.roles,common:base_bytes.common};let mut d=Historical51Diagnostics::default();
        no_success(historical::verify_historical_h12_bytes_observed51(&bytes,&key.bytes,&meta.bytes,&policy,&mut d),&d,Some(0))?;public_count+=1;}
    let zero=<ArkGT as dory_pcs::primitives::arithmetic::Group>::identity();let original=pcs::decode_commitment(base_bytes.commitment)?;
    let alternate=pcs::encode_commitment(&if original==zero{admitted.verifier().ht}else{zero})?;need(alternate!=base_bytes.commitment,"common51 alternate C distinct")?;
    let bytes=Historical51PublicBytes{frame:base_bytes.frame,commitment:&alternate,roles:base_bytes.roles,common:base_bytes.common};let mut d=Historical51Diagnostics::default();
    no_success(historical::verify_historical_h12_bytes_observed51(&bytes,&key.bytes,&meta.bytes,&policy,&mut d),&d,Some(0))?;commitment_count+=1;
    let mut bad_key=key.bytes.clone();bad_key[100]^=1;let mut d=Historical51Diagnostics::default();no_success(historical::verify_historical_h12_bytes_observed51(
        &base_bytes,&bad_key,&meta.bytes,&policy,&mut d),&d,Some(0))?;key_count+=1;
    let mut bad_meta=meta.bytes.clone();bad_meta[0]=31;let mut d=Historical51Diagnostics::default();no_success(historical::verify_historical_h12_bytes_observed51(
        &base_bytes,&key.bytes,&bad_meta,&policy,&mut d),&d,Some(0))?;key_count+=1;
    let proof=decode_proof(base_bytes.common,32)?;
    for bad in [base_bytes.common[..base_bytes.common.len()-1].to_vec(),{let mut b=base_bytes.common.to_vec();b.push(0);b}]{let mut d=Historical51Diagnostics::default();
        let bytes=Historical51PublicBytes{frame:base_bytes.frame,commitment:base_bytes.commitment,roles:base_bytes.roles,common:&bad};
        no_success(historical::verify_historical_h12_bytes_observed51(&bytes,&key.bytes,&meta.bytes,&policy,&mut d),&d,Some(0))?;codec_count+=1;}
    for fault in 0..3{let mut bad=Proof{rounds:proof.rounds.clone(),terminal:proof.terminal,pcs:proof.pcs.clone()};
        match fault{0=>bad.rounds[0][0]+=Fr::one(),1=>bad.terminal+=Fr::one(),_=>{let prior=bad.pcs.vmv_message.c;
            bad.pcs.vmv_message.c=if prior==zero{admitted.verifier().ht}else{zero};need(bad.pcs.vmv_message.c!=prior,"common51 PCS mutation distinct")?;}}
        let bad=encode_proof(&bad,32)?;let canonical=decode_proof(&bad,32)?;need(encode_proof(&canonical,32)?==bad,"common51 negative canonical proof")?;
        let bytes=Historical51PublicBytes{frame:base_bytes.frame,commitment:base_bytes.commitment,roles:base_bytes.roles,common:&bad};let mut d=Historical51Diagnostics::default();
        no_success(historical::verify_historical_h12_bytes_observed51(&bytes,&key.bytes,&meta.bytes,&policy,&mut d),&d,Some(if fault==2{1}else{0}))?;
        if fault==2{need(d.pcs_completions==0,"common51 PCS-only rejection")?;pcs_count+=1;}else{frontend_count+=1;}}
    // These are producer-statement mutants; the normal byte consumer above
    // never takes an expected Statement or transported claim as input.
    let component=baseline.observations.capacity;
    let statement=Statement{log_n:32,setup_id:*admitted.id(),commitment:original,corpus_id:Some(Blake2b::<U32>::digest(base_bytes.frame).into()),claims:baseline.claims};
    for role in 0..7{for coordinate in 0..33{let mut bad=statement.clone();if coordinate==32{bad.claims[role].value+=Fr::one();}
        else{bad.claims[role].point[coordinate]+=Fr::one();}need(verify_admitted(&bad,&admitted,&proof).is_err(),"common51 isolated statement claim accepted")?;statement_count+=1;}}
    for role in 0..7{let mut bad=statement.clone();bad.claims.swap(role,(role+1)%7);need(verify_admitted(&bad,&admitted,&proof).is_err(),"common51 claim-index swap accepted")?;statement_count+=1;}
    for fault in 0..2{let mut bad=statement.clone();if fault==0{bad.setup_id[0]^=1;}else{bad.corpus_id=Some([0;32]);}
        need(verify_admitted(&bad,&admitted,&proof).is_err(),"common51 statement setup/corpus accepted")?;statement_count+=1;}
    clock.tick("negatives")?;for h in held.iter().chain([&key,&meta]){h.check()?;}roster(&dir,true)?;clock.tick("custody_complete")?;
    let mut v=base("negatives",clock)?;merge(&mut v,json!({"inputs":inputs(&held,&key,&meta,base_bytes.common)?,"negative_counts":{
        "roles":role_count,"public_fields":public_count,"commitment":commitment_count,"key_policy":key_count,"common_codec":codec_count,
        "common_frontend":frontend_count,"pcs_only":pcs_count,"statement":statement_count},"memory":{"retained_bound":retained,"component":component},
        "checks":{"baseline_pcs":true,"isolated":true,"custody":true,"setup_generated":false,"gkr_regenerated":false}}))?;Ok(v)
}

// This is a structural maximum, not a semantic telemetry golden. The same
// shape consumer admits every real report before the bounded serializer.
fn maximum_report(mode:&str)->Result<Value,String>{
    need(matches!(mode,"producer"|"receiver"|"negatives"),"common51 closed report mode")?;
    let m=u64::MAX;let mut value=json!({"schema":"historical32-seven-common51-v1","state":"SIZE_FIXTURE","mode":mode,
        "marks_ns":vec![m;if mode=="producer"{13}else{4}],
        "scope":{"roles":vec![m;7],"input_log":m,"full_history":false,"production":false}});
    merge(&mut value,json!({"inputs":{"frame_sha256":"F".repeat(64),"commitment_sha256":"F".repeat(64),"key_sha256":"F".repeat(64),
        "metadata_sha256":"F".repeat(64),"role_sha256":vec!["F".repeat(64);7],"common_sha256":"F".repeat(64)}}))?;
    let component=json!({"known_owned_bytes":m,"caller_reservation":m,"auxiliary_reservation":m,"original_point_terms":m,
        "point_boxes":m,"component_bound":m});
    if mode=="negatives"{
        merge(&mut value,json!({"negative_counts":{"roles":m,"public_fields":m,"commitment":m,"key_policy":m,"common_codec":m,
            "common_frontend":m,"pcs_only":m,"statement":m},"memory":{"retained_bound":m,"component":component},
            "checks":{"baseline_pcs":false,"isolated":false,"custody":false,"setup_generated":false,"gkr_regenerated":false}}))?;
        return Ok(value);
    }
    merge(&mut value,json!({
        "claims_sha256":"F".repeat(64),"role_counters":vec![[m;3];7],"role_continuations":vec!["f".repeat(64);7],"role_ns":vec![m;7]}))?;
    merge(&mut value,json!({"common":{"bytes":m,"counters":vec![m;3],"continuation":"f".repeat(64)}}))?;
    if mode=="receiver"{
        merge(&mut value,json!({"phase_ns":{"admission":m,"context":m,"roles":m,"common":m,"frontend":m,"pcs":m,"inner_total":m},
            "memory":{"retained_bound":m,"component":component,"opaque_graph_heap_measured":false,"vendor_scratch_measured":false},
            "package":{"files":m,"bytes":m}}))?;
        merge(&mut value,json!({"checks":{"all_seven_derived":false,"canonical_common":false,"pcs_invoked":false,"role_order":vec![m;7],
            "witness_free":false,"setup_generated":false,"gkr_regenerated":false,"custody":false}}))?;return Ok(value);
    }
    merge(&mut value,json!({"assembly":{"old_sha256":"F".repeat(64),"old_rejection":"\0".repeat(512),
        "old_frontend_entries":m,"old_pcs_entries":m,"role_order":vec![m;7]}}))?;
    merge(&mut value,json!({"phase_ns":{"admission":m,"context":m,"roles":m,"old_common":m,"setup":m,"commit":m,"frontend":m,"open":m,"codec":m,"drop":m},
        "memory":{"retained_bound":m,"setup_owned":m,"rows_owned":m,"row_clone_bound":m,"producer_bound":m,"preflight":m,"frontend_owned":m,"frontend_bound":m,
            "assembly_component":component,"opaque_graph_heap_measured":false,"vendor_scratch_measured":false}}))?;
    merge(&mut value,json!({"io":{"binding":{"read_calls":m,"read_bytes":m,"read_ns":m},"commit":{"read_calls":m,"read_bytes":m,"read_ns":m},
        "frontend":{"read_calls":m,"read_bytes":m,"read_ns":m},"open":{"read_calls":m,"read_bytes":m,"read_ns":m}},"package":{"files":m,"bytes":m,"readback":false}}))?;
    merge(&mut value,json!({"checks":{"old_rejected_before_setup":false,"actual_reader_bound":false,"key_equal":false,"commitment_equal":false,
        "graph_dropped_before_setup":false,"producer_dropped_before_export":false,"gkr_regenerated":false,"setup_generated":false,"custody":false}}))?;Ok(value)
}
fn ordinary()->Result<(),String>{
    need(producer_bound(usize::MAX,0,0,0).is_err()&&producer_bound(0,COMPONENT_CAP,0,0).is_err(),"common51 capacity guards")?;
    actual_bound(COMPONENT_CAP,COMPONENT_CAP)?;
    need(actual_bound(COMPONENT_CAP+1,COMPONENT_CAP).is_err(),"common51 actual/preflight guard")?;
    need(historical::historical51_component_guard(COMPONENT_CAP,0,0)?==COMPONENT_CAP,"common51 component equality")?;
    need(historical::historical51_component_guard(COMPONENT_CAP,1,0).is_err()
        &&historical::historical51_component_guard(usize::MAX,1,0).is_err(),"common51 component boundary/overflow")?;
    let mut duplicate=json!({"x":0});need(merge(&mut duplicate,json!({"x":1})).is_err(),"common51 duplicate-key guard")?;
    let policy=Historical51TrustedKeyPolicy::fixed32_testonly();let bytes=Historical51PublicBytes{frame:&[],commitment:&[],roles:[&[];7],common:&[]};
    let mut d=Historical51Diagnostics::default();no_success(historical::verify_historical_h12_bytes_observed51(&bytes,&[],&[],&policy,&mut d),&d,Some(0))?;
    need(d.role_entries==[0;7]&&d.common_entries==0,"common51 pre-admission shape guard")?;
    // Real facade rejects each envelope extent before policy/key admission,
    // owned Artifact copies or context construction. These are not GKR goldens.
    let frame=vec![0;571];let commitment=vec![0;384];let packets:[Vec<u8>;7]=std::array::from_fn(|i|vec![0;EXTENTS[i]]);
    let common=vec![0;COMMON_CAP];
    for fault in 0..11{
        let mut bytes=Historical51PublicBytes{frame:&frame,commitment:&commitment,
            roles:std::array::from_fn(|i|packets[i].as_slice()),common:&common};
        let over=vec![0;COMMON_CAP+1];
        match fault{0=>bytes.frame=&frame[..570],1=>bytes.commitment=&commitment[..383],
            2..=8=>{let role=fault-2;bytes.roles[role]=&packets[role][..EXTENTS[role]-1];},9=>bytes.common=&[],_=>bytes.common=&over}
        let mut d=Historical51Diagnostics::default();
        let error=historical::verify_historical_h12_bytes_observed51(&bytes,&[],&[],&policy,&mut d).err().ok_or("common51 extent accepted")?;
        let expected=if (2..=8).contains(&fault){format!("common51 role{} packet extent",fault-2)}else{"common51 public envelope extent".into()};
        need(error==expected&&d.role_entries==[0;7]&&d.common_entries==0&&d.pcs_entries==0&&d.successes==0,"common51 isolated extent guard")?;
    }
    for mode in ["producer","receiver","negatives"]{
        let value=maximum_report(mode)?;need(encoded_report(&value)?.len()<=REPORT_CAP,"common51 maximum serializer")?;
        let mut missing=value.clone();missing.as_object_mut().ok_or("common51 fixture object")?.remove("checks");
        need(encoded_report(&missing).is_err(),"common51 maximum fixture missing field")?;
        let mut extra=value.clone();extra.as_object_mut().ok_or("common51 fixture object")?.insert("extra".into(),json!(0));
        need(encoded_report(&extra).is_err(),"common51 report extra field")?;
        let mut duration=value.clone();duration["marks_ns"].as_array_mut().ok_or("common51 fixture marks")?.pop();
        need(encoded_report(&duration).is_err(),"common51 report duration extent")?;
    }Ok(())
}
fn run(mode:&'static str){let mut clock=Clock::new(mode);let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||match mode{
    "producer"=>producer(&mut clock),"receiver"=>receiver(&mut clock),"negatives"=>negatives(&mut clock),_=>Err("common51 closed mode".into())}));
    let error=match result{Ok(Ok(value))=>match emit(&value){Ok(())=>return,Err(e)=>e},Ok(Err(e))=>e,Err(_)=>"common51 panic".into()};
    let reason:String=error.chars().map(|c|if c.is_ascii_graphic(){c}else{'_'}).take(160).collect();
    eprintln!("HISTORICAL_SEVEN_COMMON51_HOLD {} {} {} {}",mode,clock.next,clock.start.elapsed().as_nanos(),reason);panic!("common51 HOLD")}
#[test]
fn historical51_ordinary()->Result<(),String>{ordinary()}
#[test]
#[ignore="provisional51; requires adopted exact50/import/source/runtime gates"]
fn historical51_producer(){run("producer")}
#[test]
#[ignore="provisional51 positive public consumer in a fresh process"]
fn historical51_receiver(){run("receiver")}
#[test]
#[ignore="provisional51 isolated negatives outside positive receiver latency"]
fn historical51_negatives(){run("negatives")}

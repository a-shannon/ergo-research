//! Sealed native32 frontend diagnostic. No setup, commitment or PCS operation.
#[path = "same_x_stage1b_tests.rs"]
mod same_x_stage1b_tests;
use super::*;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use blake2::{digest::consts::U32, Blake2b, Digest};
use serde::{Serialize, Serializer, ser::SerializeSeq};
use std::{fs::{File, OpenOptions}, io::{Read, Seek, SeekFrom, Write}, path::{Path, PathBuf}, mem::{size_of,size_of_val}};
use std::os::windows::{fs::{OpenOptionsExt, MetadataExt}, io::AsRawHandle};
use crate::{gkr::{self, InputClaim}, native_prefix_auth_plan::{Candidate, NativePrefixAuthPlan,
    NativeRole1DiagnosticContext, Selection, role0_sha256}, packed_owner_assembly::NativePrefix,
    work_tree_history_plan::WorkTreeHistoryPlan};
use crate::sparse;

const META_LIMIT: usize = 8 * 1024 * 1024;
const FRONTEND_LIMIT: usize = 64 * 1024 * 1024;
const REPORT_CAP: usize = 32768;
const SOURCE_MF: &str = "B112444F23ABA3751D03EE237F260EA0C3916162C5988DD0BAEFF76357FE34D6";
const SOURCE_BINARY: &str = "45FD574340B92BDCCA83BB2EB02E9AFD38FB81682DC324A087F129151A21D8CA";
const RAW_SHA: &str = "ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const RAW_BLAKE: &str = "8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
const WITNESS_SHA: &str = "C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
const WITNESS_BLAKE: &str = "725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";
const KEY_SHA: &str = "D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2";
const COMMIT_SHA: &str = "2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90";
const PROOF_SHA: &str = "BDB697533E1FA3DE78DAB4D5F61F8735B5051818FC5AA7D5BE4D56398739FE11";
const RESULT_SHA: &str = "F553E03080822B67F7808FD34F40C297B37776B017E9B346022DAB810BB29FBD";
const RECEIPT_SHA: &str = "07AD7A69AB7D9CC9ABA1BB64F43E81D05F907B02792A1AE987FB3A61493C080E";
const REVIEW_SHA: &str = "A6C54AEAF3A4881B598821F95F03292E86851332A789E3454912408926691C8A";
const SETUP_ID: &str = "1AE7BADC1E529C7A5CDA709AD1B418AF6AE2EFB6B7B4D909816D091C3260A51B";
const CONTINUATION: &[u8] = b"opening-native32-frontend-continuation";

fn need(ok: bool, message: &str) -> Result<(), String> { if ok { Ok(()) } else { Err(message.into()) } }
fn add(a: usize, b: usize) -> Result<usize, String> { a.checked_add(b).ok_or("native frontend capacity overflow".into()) }
fn hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{b:02X}")).collect() }
fn bytes32(text: &str) -> Result<[u8;32], String> {
    need(text.len()==64 && text.bytes().all(|c| c.is_ascii_digit() || (b'A'..=b'F').contains(&c)), "canonical uppercase hex32")?;
    let mut out=[0u8;32];
    for (i,b) in out.iter_mut().enumerate() { *b=u8::from_str_radix(&text[2*i..2*i+2],16).map_err(|e|e.to_string())?; }
    Ok(out)
}
fn scalar(text: &str) -> Result<Fr,String> {
    let bytes=bytes32(text)?; let value=Fr::deserialize_compressed(&bytes[..]).map_err(|e|e.to_string())?;
    let mut encoded=[0u8;32]; value.serialize_compressed(&mut encoded[..]).map_err(|e|e.to_string())?;
    need(encoded==bytes,"canonical Fr encoding")?; Ok(value)
}
fn check_pin(bytes:&[u8], length:usize, expected:&str)->Result<(),String>{
    need(bytes.len()==length,"native frontend exact input extent")?;
    need(hex(&role0_sha256(bytes)?)==expected,"native frontend exact SHA256")
}
fn source_extent(input_len:usize)->Result<(),String>{need(input_len==1usize<<32,"native frontend source length")}
fn witness_digest(digest:&[u8])->Result<(),String>{need(hex(digest)==WITNESS_BLAKE,"native witness admitted digest")}

// Same bounded Windows identity ABI as the accepted native consumer. All held
// handles deny write/delete sharing; access time is excluded from identity.
#[repr(C)]
#[derive(Default,Debug,PartialEq,Eq)]
struct Identity { attributes:u32, created:[u32;2], accessed:[u32;2], written:[u32;2],
    volume:u32, size_high:u32, size_low:u32, links:u32, index_high:u32, index_low:u32 }
fn identity(file:&File)->Result<Identity,String>{
    #[link(name="kernel32")]
    extern "system" { fn GetFileInformationByHandle(handle:*mut std::ffi::c_void, info:*mut Identity)->i32; }
    let mut out=Identity::default();
    // Identity is repr(C), fully writable, and the borrowed File outlives this call.
    if unsafe {GetFileInformationByHandle(file.as_raw_handle(),&mut out)}==0 {return Err(std::io::Error::last_os_error().to_string());}
    need(out.attributes&0x410==0 && out.links==1,"regular single-link immutable input")?;
    out.accessed=[0;2]; Ok(out)
}
struct Held { path:PathBuf, file:File, identity:Identity, bytes:Vec<u8> }
impl Held {
    fn open(env:&str, length:usize, sha:Option<&str>)->Result<Self,String>{
        let path=PathBuf::from(std::env::var_os(env).ok_or_else(||format!("{env} absent"))?);
        need(path.is_absolute() && path.as_os_str().len()<=1024,"bounded absolute native frontend input path")?;
        let md=std::fs::symlink_metadata(&path).map_err(|e|e.to_string())?;
        need(md.is_file() && md.file_attributes()&0x400==0 && md.len()==length as u64,"native frontend file type/extent")?;
        let file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|e|e.to_string())?;
        let id=identity(&file)?;
        need(((u64::from(id.size_high)<<32)|u64::from(id.size_low))==length as u64,"native frontend held extent")?;
        let mut bytes=Vec::new();
        if let Some(pin)=sha {
            bytes.try_reserve_exact(length).map_err(|e|e.to_string())?;
            file.try_clone().map_err(|e|e.to_string())?.take(length as u64+1).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
            check_pin(&bytes,length,pin)?;
        }
        let out=Self{path,file,identity:id,bytes};out.check()?;Ok(out)
    }
    fn check(&self)->Result<(),String>{
        need(identity(&self.file)?==self.identity,"native frontend held identity changed")?;
        let current=OpenOptions::new().read(true).share_mode(1).open(&self.path).map_err(|e|e.to_string())?;
        need(identity(&current)?==self.identity,"native frontend path identity changed")
    }
    fn clear_bytes(&mut self){self.bytes=Vec::new();}
    fn heap_bytes(&self)->Result<usize,String>{
        // OsString capacity is conservatively charged as UTF16 units on Windows.
        add(self.path.capacity().checked_mul(2)
            .ok_or("native frontend path capacity overflow")?,self.bytes.capacity())
    }
}

fn accepted_record(report:&serde_json::Value, receipt:&serde_json::Value, claim:&InputClaim)->Result<(),String>{
    need(report["schema"]=="native-prefix-role1-diagnostic-gkr-v1" && report["state"]=="ROLE1_DIAGNOSTIC_GKR_PASS"
        && report["scope"]["role"]==1 && report["scope"]["input_log"]==32 && report["scope"]["output_row_log"]==31,
        "accepted native1 exact role/shape")?;
    need(report["proof"]["independent_verify"]==true && report["proof"]["source_evaluation_crosscheck"]==true
        && report["proof"]["sha256"]==PROOF_SHA && report["proof"]["bytes"]==7264
        && report["admission"]["setup_id"]==SETUP_ID && report["admission"]["verifier_key_sha256"]==KEY_SHA
        && report["admission"]["commitment_sha256"]==COMMIT_SHA,"accepted native1 artifact/MLE provenance")?;
    need(receipt["schema"]=="nipopow-native-role1-native32-full-capture-v1" && receipt["status"]=="PASS"
        && receipt["source_manifest_sha256"]==SOURCE_MF && receipt["binary_sha256"]==SOURCE_BINARY
        && receipt["binary_bytes"]==60135936,"accepted native1 source/binary provenance")?;
    need(claim.point.len()==32,"native1 independently verified claim width")?;
    let points=report["claim"]["point_hex"].as_array().ok_or("native1 claim point array")?;
    need(points.len()==32,"accepted native1 claim width")?;
    for (actual,encoded) in claim.point.iter().zip(points){
        need(*actual==scalar(encoded.as_str().ok_or("native1 coordinate string")?)?,"accepted native1 claim point mismatch")?;
    }
    need(claim.value==scalar(report["claim"]["value_hex"].as_str().ok_or("native1 claim scalar string")?)?,
        "accepted native1 claim value mismatch")
}
fn admission_boundary<S:RowSource>(source:&S,report:&serde_json::Value,receipt:&serde_json::Value,
    claim:&InputClaim,transcript:&mut Transcript)->Result<(),String>{
    // Called by both native admission and ordinary controls. Reject before any
    // frontend source row or Fiat-Shamir operation; this is not a binder.
    need(transcript.challenges()==0 && transcript.raw_queries()==0
        && transcript.bytes_absorbed()==Transcript::new(DOMAIN).bytes_absorbed(),"fresh frontend transcript admission")?;
    source_extent(source.input_len())?;accepted_record(report,receipt,claim)
}

fn verify_native1(raw:&[u8], proof_bytes:&[u8], key:&[u8], commitment:&[u8])->Result<InputClaim,String>{
    need(raw.len()==869449 && crate::work_tree_layout::hash_bytes(raw)==RAW_BLAKE.to_ascii_lowercase(),"native RAW digest")?;
    let mut position=0usize;let mut headers=Vec::with_capacity(3073);
    for _ in 0..3073 {
        let end=position.checked_add(4).ok_or("native RAW length overflow")?;
        let size=u32::from_le_bytes(raw.get(position..end).ok_or("native RAW length")?.try_into().map_err(|_|"native RAW u32")?) as usize;
        position=end;need((1..=514).contains(&size),"native RAW header extent")?;
        let end=position.checked_add(size).ok_or("native RAW header overflow")?;
        headers.push(raw.get(position..end).ok_or("native RAW header bytes")?.to_vec());position=end;
    }
    need(position==raw.len(),"native RAW exact EOF")?;
    let native=NativePrefix::from_raw_headers(&headers)?;drop(headers);
    let root=native.root();let total=native.total_be28();
    let candidate=Candidate{n:3073,root,total,tip:ergo_header_core::blake2b256(native.raw(3073)?),tip_time:native.timestamp(3073)?};
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;drop(native);
    let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate)?;
    let context=NativeRole1DiagnosticContext::admit(key,commitment)?;
    let proof=gkr::decode_dimensions(&[32],proof_bytes)?;
    need(gkr::encode_proof(&proof)?==proof_bytes && proof.layers.len()==1 && proof.layers[0].rounds.len()==64
        && proof.layers[0].line_coefficients.len()==33,"accepted native1 canonical proof shape")?;
    let mut transcript=context.transcript();let mut preflight=transcript.clone();
    plan.bind_role1_diagnostic_context(&mut preflight,&context)?;
    let claim=gkr::verify_with_wiring(&[32],1usize<<31,&proof,&mut transcript,
        |t|plan.bind_role1_diagnostic_context(t,&context).expect("immutable native1 binding prevalidated"),
        |layer,r,u,v|if layer==0{plan.coefficients(1,r,u,v).map_err(|_|gkr::GkrError::PointDimension)}
            else{Err(gkr::GkrError::PointDimension)}).map_err(|e|e.to_string())?;
    // All large admission state is scoped to this call and drops before frontend.
    Ok(claim)
}

struct Admitted { source:PackedFile, held:Vec<Held>, statement:Statement, output:PathBuf, report_path:PathBuf }
fn admit_native()->Result<Admitted,String>{
    admit_native_for("NIPOPOW_OPENING_BATCH_NATIVE32_CAPTURE_DIR")
}
fn admit_native_for(output_env:&str)->Result<Admitted,String>{
    let mut held=Vec::with_capacity(8);
    held.push(Held::open("NIPOPOW_NATIVE_AUTH_FIXTURE",869449,Some(RAW_SHA))?);
    held.push(Held::open("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS",536870912,None)?);
    held.push(Held::open("NIPOPOW_ROLE4_KEY_PATH",33264,Some(KEY_SHA))?);
    held.push(Held::open("NIPOPOW_NATIVE_ROLE0_COMMITMENT_PATH",384,Some(COMMIT_SHA))?);
    held.push(Held::open("NIPOPOW_NATIVE_ROLE1_PROOF_PATH",7264,Some(PROOF_SHA))?);
    held.push(Held::open("NIPOPOW_NATIVE_ROLE1_RESULT_PATH",6862,Some(RESULT_SHA))?);
    held.push(Held::open("NIPOPOW_NATIVE_ROLE1_RECEIPT_PATH",12041,Some(RECEIPT_SHA))?);
    held.push(Held::open("NIPOPOW_NATIVE_ROLE1_REVIEW_PATH",3654,Some(REVIEW_SHA))?);
    let source=PackedFile::open_with_limit(&held[1].path,32,32)?;
    source_extent(source.input_len())?;held[1].check()?;
    let mut witness=held[1].file.try_clone().map_err(|e|e.to_string())?;
    witness.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;
    let mut scratch=vec![0u8;1<<20];let mut digest=Blake2b::<U32>::new();
    for _ in 0..512 {witness.read_exact(&mut scratch).map_err(|e|e.to_string())?;digest.update(&scratch);}
    // Exact locked extent is already checked; 512 payload read_exact calls are
    // sufficient and no extra EOF read is charged as a frontend source scan.
    witness_digest(&digest.finalize())?;drop(scratch);drop(witness);
    let claim=verify_native1(&held[0].bytes,&held[4].bytes,&held[2].bytes,&held[3].bytes)?;
    // Only exactly pinned bounded JSON is parsed; no caller-controlled document.
    let report:serde_json::Value=serde_json::from_slice(&held[5].bytes).map_err(|e|e.to_string())?;
    let receipt:serde_json::Value=serde_json::from_slice(&held[6].bytes).map_err(|e|e.to_string())?;
    admission_boundary(&source,&report,&receipt,&claim,&mut Transcript::new(DOMAIN))?;drop(report);drop(receipt);
    let statement=Statement{log_n:32,setup_id:bytes32(SETUP_ID)?,commitment:pcs::decode_commitment(&held[3].bytes)?,
        corpus_id:Some(bytes32(WITNESS_BLAKE)?),claims:std::array::from_fn(|_|Claim{point:claim.point.clone(),value:claim.value})};
    drop(claim);
    for input in &mut held {input.check()?;input.clear_bytes();}
    let output=PathBuf::from(std::env::var_os(output_env).ok_or("native frontend output env absent")?);
    need(output.is_absolute() && output.as_os_str().len()<=1024 && output.parent().is_some_and(Path::is_dir),"native frontend output path")?;
    match std::fs::symlink_metadata(&output){
        Ok(_)=>return Err("native frontend output already exists".into()),
        Err(error) if error.kind()==std::io::ErrorKind::NotFound=>(),Err(error)=>return Err(error.to_string()),
    }
    need(!output.parent().ok_or("native frontend output parent")?.canonicalize().map_err(|e|e.to_string())?
        .starts_with(std::env::temp_dir().canonicalize().map_err(|e|e.to_string())?),"native frontend output inside TEMP")?;
    let report_path=output.join("frontend-native32-result.json");
    Ok(Admitted{source,held,statement,output,report_path})
}

// Stack-backed canonical scalar encoding avoids a heap of hex strings during
// export. The writer never extends beyond its already reserved output capacity.
struct ScalarHex<'a>(&'a Fr);
impl Serialize for ScalarHex<'_>{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{
    let mut bytes=[0u8;32];self.0.serialize_compressed(&mut bytes[..]).map_err(serde::ser::Error::custom)?;
    let mut text=[0u8;64];let digits=b"0123456789ABCDEF";
    for (i,b) in bytes.iter().enumerate(){text[2*i]=digits[(b>>4) as usize];text[2*i+1]=digits[(b&15) as usize];}
    s.serialize_str(std::str::from_utf8(&text).map_err(serde::ser::Error::custom)?)
}}
struct Points<'a>(&'a [Fr]);
impl Serialize for Points<'_>{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{
    let mut seq=s.serialize_seq(Some(self.0.len()))?;for x in self.0{seq.serialize_element(&ScalarHex(x))?;}seq.end()
}}
struct Rounds<'a>(&'a [[Fr;3]]);
impl Serialize for Rounds<'_>{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{
    let mut seq=s.serialize_seq(Some(self.0.len()))?;for x in self.0{seq.serialize_element(&Points(x))?;}seq.end()
}}
struct BoundedBytes(Vec<u8>);
impl Write for BoundedBytes{
    fn write(&mut self,bytes:&[u8])->std::io::Result<usize>{
        if bytes.len()>REPORT_CAP.saturating_sub(self.0.len()){return Err(std::io::Error::other("native frontend report cap"));}
        self.0.extend_from_slice(bytes);Ok(bytes.len())
    }
    fn flush(&mut self)->std::io::Result<()>{Ok(())}
}

#[derive(Serialize)]
struct Scope{input_log:usize,claims:usize,repeated_role1:bool,pcs_invoked:bool,setup_invoked:bool,
    commitment_recomputed:bool,all_seven_roles:bool,full_history:bool,production:bool}
#[derive(Serialize)]
struct Inputs{source8_manifest_sha256:&'static str,source8_binary_sha256:&'static str,native1_receipt_sha256:&'static str,
    native1_result_sha256:&'static str,native1_proof_sha256:&'static str,native1_review_sha256:&'static str,
    raw_sha256:&'static str,raw_blake2b256:&'static str,witness_sha256:&'static str,witness_blake2b256:&'static str,
    key_sha256:&'static str,commitment_sha256:&'static str,setup_id:&'static str}
#[derive(Serialize)]
struct Admission{native1_independent_verify:bool,claim_equal_accepted:bool,historical_source_mle_evidence_bound:bool,
    held_identity_stable:bool,retained_metadata_bytes:usize,metadata_limit_bytes:usize,admission_peak_measured:bool,
    witness_admission_read_bytes:u64,witness_admission_read_calls:u64}
#[derive(Serialize)]
struct FrontendView<'a>{rounds:Rounds<'a>,point:Points<'a>,terminal_hex:ScalarHex<'a>,round_count:usize,point_count:usize,
    transcript_counters:[u64;3],continuation_hex:ScalarHex<'a>}
#[derive(Serialize,Clone,Copy)]
struct Inventory{field_capacity_bytes:usize,descriptor_capacity_bytes:usize,row_scratch_capacity_bytes:usize,total_capacity_bytes:usize}
#[derive(Serialize)]
struct Memory{frontend_limit_bytes:usize,held_capacity_bytes:usize,fixed_capacity_bytes:usize,preflight_capacity_bound_bytes:usize,
    state_peak_capacity_bytes:usize,phase_peak_capacity_bytes:[usize;6],phase_peak_inventory:[Inventory;6]}
#[derive(Serialize)]
struct Io{read_calls:u64,read_bytes:u64,read_ns:u128,write_calls:u64,write_bytes:u64,sync_calls:u64}
#[derive(Serialize,Clone,Copy)]
struct Mark{name:&'static str,elapsed_ns:u128}
#[derive(Serialize)]
struct Timing{admission:u128,frontend:u128,total_before_export:u128}
#[derive(Serialize)]
struct Report<'a>{schema:&'static str,state:&'static str,scope:Scope,inputs:Inputs,admission:Admission,
    frontend:FrontendView<'a>,memory:Memory,io:Io,phase_marks:[Mark;8],timing_ms:Timing}

fn held_capacity(admitted:&Admitted,output:&BoundedBytes)->Result<usize,String>{
    let mut size=add(size_of::<Admitted>(),admitted.held.capacity().checked_mul(size_of::<Held>()).ok_or("held capacity overflow")?)?;
    // Statement itself and all seven point payloads are owned by FrontendAudit.
    size=size.checked_sub(size_of::<Statement>()).ok_or("held statement accounting")?;
    for input in &admitted.held{size=add(size,input.heap_bytes()?)?;}
    size=add(size,admitted.output.capacity().checked_mul(2).ok_or("output path capacity")?)?;
    size=add(size,admitted.report_path.capacity().checked_mul(2).ok_or("report path capacity")?)?;
    // PackedFile's test-only Arc<Mutex<PackedIoSnapshot>> payload and Arc counters
    // are not inline in PackedFile. OS handle/kernel allocations belong to Job.
    size=add(size,add(size_of::<std::sync::Mutex<crate::packed::PackedIoSnapshot>>(),2*size_of::<usize>())?)?;
    size=add(size,output.0.capacity())?;size=add(size,size_of::<BoundedBytes>())?;
    size=add(size,size_of::<Report<'_>>())?;
    // Explicit bounded stack scratch: scalar encoding, serializer frames, file
    // identity and path checks. No parsed Value or native plan survives here.
    size=add(size,4096)?;
    need(size<=META_LIMIT,"native frontend retained metadata exceeds 8MiB")?;Ok(size)
}

fn execute()->Result<(),String>{
    let began=Instant::now();let admitted=admit_native()?;let admission_ms=began.elapsed().as_millis();
    let mut output=BoundedBytes(Vec::with_capacity(REPORT_CAP));
    need(output.0.capacity()==REPORT_CAP,"native frontend exact export capacity")?;
    let held_bytes=held_capacity(&admitted,&output)?;
    let mut transcript=Transcript::new(DOMAIN);
    let mut audit=FrontendAudit::new(&admitted.statement,held_bytes,true)?;
    admitted.source.reset_io_metrics();let frontend_started=Instant::now();
    let frontend=prove_frontend_on_mode(&admitted.source,&admitted.statement,&mut transcript,None,ProjectionMode::Fused,Some(&mut audit))?;
    let frontend_ms=frontend_started.elapsed().as_millis();let io=admitted.source.io_metrics_snapshot();
    need(frontend.rounds.len()==32 && frontend.point.len()==32 && frontend.metrics.pre_pcs_fields==0
        && frontend.metrics.projection_scans==1 && frontend.metrics.transition_scans==1,"native frontend complete shape/scans")?;
    need(io.read_calls==131072 && io.read_bytes==1073741824 && io.write_calls==0 && io.write_bytes==0 && io.sync_calls==0,
        "native frontend exact two scans / zero writes")?;
    need(audit.stats.row_loads==[65536,65536] && audit.stats.state_peak_capacity_bytes<=FRONTEND_LIMIT
        && audit.stats.held_capacity_bytes==held_bytes,"native frontend observed capacity/source inventory")?;
    need(transcript.challenges()==33 && (33..=135168).contains(&transcript.raw_queries()) && transcript.bytes_absorbed()==33173,
        "native frontend transcript counters")?;
    for held in &admitted.held{held.check()?;}
    let continuation=transcript.clone().challenge_scalar(CONTINUATION);
    let stats=&audit.stats;
    let inventory=std::array::from_fn(|i|{let p=&stats.phase_peak_inventory[i];Inventory{field_capacity_bytes:p.field_capacity_bytes,
        descriptor_capacity_bytes:p.descriptor_capacity_bytes,row_scratch_capacity_bytes:p.row_scratch_capacity_bytes,total_capacity_bytes:p.total_capacity_bytes}});
    let report=Report{schema:"native32-opening-frontend-diagnostic-v1",state:"FRONTEND_ONLY_COMPLETE",
        scope:Scope{input_log:32,claims:7,repeated_role1:true,pcs_invoked:false,setup_invoked:false,commitment_recomputed:false,
            all_seven_roles:false,full_history:false,production:false},
        inputs:Inputs{source8_manifest_sha256:SOURCE_MF,source8_binary_sha256:SOURCE_BINARY,native1_receipt_sha256:RECEIPT_SHA,
            native1_result_sha256:RESULT_SHA,native1_proof_sha256:PROOF_SHA,native1_review_sha256:REVIEW_SHA,raw_sha256:RAW_SHA,
            raw_blake2b256:RAW_BLAKE,witness_sha256:WITNESS_SHA,witness_blake2b256:WITNESS_BLAKE,key_sha256:KEY_SHA,
            commitment_sha256:COMMIT_SHA,setup_id:SETUP_ID},
        admission:Admission{native1_independent_verify:true,claim_equal_accepted:true,historical_source_mle_evidence_bound:true,
            held_identity_stable:true,retained_metadata_bytes:held_bytes,metadata_limit_bytes:META_LIMIT,admission_peak_measured:false,
            witness_admission_read_bytes:536870912,witness_admission_read_calls:512},
        frontend:FrontendView{rounds:Rounds(&frontend.rounds),point:Points(&frontend.point),terminal_hex:ScalarHex(&frontend.terminal),
            round_count:32,point_count:32,transcript_counters:[transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()],
            continuation_hex:ScalarHex(&continuation)},
        memory:Memory{frontend_limit_bytes:FRONTEND_LIMIT,held_capacity_bytes:held_bytes,fixed_capacity_bytes:stats.fixed_capacity_bytes,
            preflight_capacity_bound_bytes:stats.preflight_capacity_bound_bytes,state_peak_capacity_bytes:stats.state_peak_capacity_bytes,
            phase_peak_capacity_bytes:stats.phase_peak_capacity_bytes,phase_peak_inventory:inventory},
        io:Io{read_calls:io.read_calls,read_bytes:io.read_bytes,read_ns:io.read_ns,write_calls:io.write_calls,write_bytes:io.write_bytes,sync_calls:io.sync_calls},
        phase_marks:std::array::from_fn(|i|Mark{name:stats.phase_marks[i].name,elapsed_ns:stats.phase_marks[i].elapsed_ns}),
        timing_ms:Timing{admission:admission_ms,frontend:frontend_ms,total_before_export:began.elapsed().as_millis()}};
    serde_json::to_writer(&mut output,&report).map_err(|e|e.to_string())?;
    need(output.0.capacity()==REPORT_CAP && output.0.len()<=REPORT_CAP,"native frontend bounded export")?;
    // No field-bank allocation remains at this boundary; the output reservation
    // and typed borrowed report were included in every frontend phase inventory.
    drop(report);drop(frontend);drop(audit);
    std::fs::create_dir(&admitted.output).map_err(|e|e.to_string())?;
    let mut file=OpenOptions::new().write(true).create_new(true).open(&admitted.report_path).map_err(|e|e.to_string())?;
    file.write_all(&output.0).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;drop(file);
    for held in &admitted.held{held.check()?;}Ok(())
}

#[test]
#[ignore="native32 repeated verified role1 frontend only; separate reviewed capture required"]
fn native32_repeated_role1_frontend_bounded(){execute().unwrap();}

#[test]
fn native32_frontend_admission_controls(){
    struct Unread { length:usize, rows:std::cell::Cell<usize> }
    impl RowSource for Unread {
        fn input_len(&self)->usize{self.length}
        fn read_row(&self,_:usize,_:usize)->Result<Vec<Fr>,String>{self.rows.set(self.rows.get()+1);Err("unexpected admission row".into())}
    }
    let source=Unread{length:1usize<<32,rows:std::cell::Cell::new(0)};
    let claim=InputClaim{point:vec![Fr::from(3u64);32],value:Fr::from(7u64)};
    let coordinate=hex(&{let mut b=[0u8;32];claim.point[0].serialize_compressed(&mut b[..]).unwrap();b});
    let value=hex(&{let mut b=[0u8;32];claim.value.serialize_compressed(&mut b[..]).unwrap();b});
    let report=serde_json::json!({"schema":"native-prefix-role1-diagnostic-gkr-v1","state":"ROLE1_DIAGNOSTIC_GKR_PASS",
        "scope":{"role":1,"input_log":32,"output_row_log":31},"proof":{"independent_verify":true,"source_evaluation_crosscheck":true,
        "sha256":PROOF_SHA,"bytes":7264},"admission":{"setup_id":SETUP_ID,"verifier_key_sha256":KEY_SHA,"commitment_sha256":COMMIT_SHA},
        "claim":{"point_hex":vec![coordinate;32],"value_hex":value}});
    let receipt=serde_json::json!({"schema":"nipopow-native-role1-native32-full-capture-v1","status":"PASS",
        "source_manifest_sha256":SOURCE_MF,"binary_sha256":SOURCE_BINARY,"binary_bytes":60135936});
    let mut t=Transcript::new(DOMAIN);let before=(t.challenges(),t.raw_queries(),t.bytes_absorbed());
    admission_boundary(&source,&report,&receipt,&claim,&mut t).unwrap();
    let mut cases=0usize;
    for pointer in ["/scope/role","/scope/input_log","/scope/output_row_log","/proof/bytes"]{
        let mut bad=report.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!(0);
        assert!(admission_boundary(&source,&bad,&receipt,&claim,&mut t).is_err());cases+=1;
    }
    for pointer in ["/proof/sha256","/admission/setup_id","/admission/verifier_key_sha256","/admission/commitment_sha256"]{
        let mut bad=report.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!("00");
        assert!(admission_boundary(&source,&bad,&receipt,&claim,&mut t).is_err());cases+=1;
    }
    for pointer in ["/proof/independent_verify","/proof/source_evaluation_crosscheck"]{
        let mut bad=report.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!(false);
        assert!(admission_boundary(&source,&bad,&receipt,&claim,&mut t).is_err());cases+=1;
    }
    let mut bad=report.clone();bad["claim"]["point_hex"].as_array_mut().unwrap().pop();assert!(admission_boundary(&source,&bad,&receipt,&claim,&mut t).is_err());cases+=1;
    let mut bad_claim=claim.clone();bad_claim.value+=Fr::one();assert!(admission_boundary(&source,&report,&receipt,&bad_claim,&mut t).is_err());cases+=1;
    let mut bad_claim=claim.clone();bad_claim.point[31]+=Fr::one();assert!(admission_boundary(&source,&report,&receipt,&bad_claim,&mut t).is_err());cases+=1;
    let mut bad_claim=claim.clone();bad_claim.point.pop();assert!(admission_boundary(&source,&report,&receipt,&bad_claim,&mut t).is_err());cases+=1;
    for pointer in ["/schema","/state"]{
        let mut bad=report.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!("wrong");
        assert!(admission_boundary(&source,&bad,&receipt,&claim,&mut t).is_err());cases+=1;
    }
    for pointer in ["/source_manifest_sha256","/binary_sha256","/schema","/status"]{
        let mut bad=receipt.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!("wrong");
        assert!(admission_boundary(&source,&report,&bad,&claim,&mut t).is_err());cases+=1;
    }
    let mut bad=receipt.clone();bad["binary_bytes"]=serde_json::json!(60135935);
    assert!(admission_boundary(&source,&report,&bad,&claim,&mut t).is_err());cases+=1;
    assert_eq!(cases,21);assert_eq!(before,(t.challenges(),t.raw_queries(),t.bytes_absorbed()));
    let mut dirty=Transcript::new(DOMAIN);dirty.append_bytes(b"unexpected-before-admission",b"one-fault");
    let dirty_before=(dirty.challenges(),dirty.raw_queries(),dirty.bytes_absorbed());
    assert!(admission_boundary(&source,&report,&receipt,&claim,&mut dirty).is_err());
    assert_eq!(dirty_before,(dirty.challenges(),dirty.raw_queries(),dirty.bytes_absorbed()));
    let short=Unread{length:1usize<<31,rows:std::cell::Cell::new(0)};
    assert!(admission_boundary(&short,&report,&receipt,&claim,&mut t).is_err());
    assert_eq!(source.rows.get(),0);assert_eq!(short.rows.get(),0);
    assert_eq!(before,(t.challenges(),t.raw_queries(),t.bytes_absorbed()));
    assert!(scalar(&"FF".repeat(32)).is_err());assert!(bytes32(&"aa".repeat(32)).is_err());
    check_pin(b"abc",3,"BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD").unwrap();
    assert!(check_pin(b"abc",2,"BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD").is_err());
    assert!(check_pin(b"abd",3,"BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD").is_err());
    source_extent(1usize<<32).unwrap();assert!(source_extent(1usize<<31).is_err());
    witness_digest(&bytes32(WITNESS_BLAKE).unwrap()).unwrap();
    let mut wrong_corpus=bytes32(WITNESS_BLAKE).unwrap();wrong_corpus[0]^=1;assert!(witness_digest(&wrong_corpus).is_err());
    let mut bytes=BoundedBytes(Vec::with_capacity(REPORT_CAP));bytes.write_all(&vec![0;REPORT_CAP]).unwrap();
    let original=bytes.0.clone();assert!(bytes.write_all(&[1]).is_err());assert_eq!(bytes.0,original);
    // The continuation is clone-only in the producer; this local probe confirms
    // no challenge is needed merely to parse or reject native admission data.
    t.append_bytes(b"ordinary-control-done",b"closed");
}


// Source10: sealed continuation of the separately recovered frontend tuple.
// Public producer/key admission and every PCS/backend implementation are unchanged.
const FRONTEND_HOLD_SHA:&str="E21F31717F77FED9FB6431CED5B5B36B6C8B6097BD804DFDB393E5E4D0A29FB1";
const FRONTEND_RESULT_SHA:&str="A77C91661B72E62C8804DC0D97C395190B2DC96A3F5DEA4B957C3B8E1BE4FA60";
const FRONTEND_REPLAY_SHA:&str="BE2BB282C27F5A890B63C0E1C51B42C69A5DC1CFE69EE30136A4AFE4A42A4D3F";
const FRONTEND_REVIEW_SHA:&str="C6B2BEB76A08545FC290DE10EF109CC3B5AF31CDFFC231066D37D5DB5EB3AF7F";
const FRONTEND_CONTROLLER_SHA:&str="FAD1BAB39669A95A7E0DDACF0C13FC528D06CB7FD9006242076B348D27118438";
const FRONTEND_SOURCE_MF:&str="721A8B33E482CA9A8BE4280578DA50095C1997E48BF5FF02692B7B1DDB54DFB0";
const FRONTEND_BINARY_SHA:&str="8E3B97358EB59E083399911B40A1B305F261ED8B79030C8079C2BEEEC763E417";
const REPLAY_ADAPTER_SHA:&str="0DAA2B091909D3BF3842592319423507868554C34BBF222ED402A09156AE347E";
const DORY_CONTINUATION:&[u8]=b"opening-native32-dory-continuation";
const DORY_PHASES:[&str;9]=["admission_complete","replay_complete","endpoint_mle_complete",
    "setup_complete","commitment_complete","dory_open_complete","codec_complete","full_verify_complete","export_ready"];

fn dory_frontend_admission(front:&serde_json::Value,hold:&serde_json::Value,recovery:&serde_json::Value)->Result<(),String>{
    need(front["schema"]=="native32-opening-frontend-diagnostic-v1" && front["state"]=="FRONTEND_ONLY_COMPLETE"
        && front["scope"]["input_log"]==32 && front["scope"]["claims"]==7
        && front["scope"]["repeated_role1"]==true && front["scope"]["pcs_invoked"]==false,
        "recovered frontend exact scope")?;
    need(hold["schema"]=="nipopow-opening-native32-runtime-capture-v1" && hold["status"]=="HOLD"
        && hold["controller_sha256"]==FRONTEND_CONTROLLER_SHA && hold["source_manifest_sha256"]==FRONTEND_SOURCE_MF
        && hold["binary_sha256"]==FRONTEND_BINARY_SHA && hold["binary_bytes"]==59146240
        && hold["quiescent"]==true && hold["post_settlement_checks"]=="COMPLETED",
        "original immutable frontend HOLD lineage")?;
    need(hold["diagnostic_errors"]==serde_json::json!([
        "AttributeError:'types.SimpleNamespace' object has no attribute 'native1_result_bytes'"]),
        "original frontend sole reader API error")?;
    let audits=hold["source_audits"].as_array().ok_or("frontend source audit array")?;
    need(audits.len()==2 && audits.iter().all(|item|item["status"]=="PASS"
        && item["source_manifest_sha256"]==FRONTEND_SOURCE_MF),"frontend historical two source audits")?;
    need(hold["native_inputs"].is_object() && hold["native_inputs"]==hold["native_inputs_post"],
        "frontend historical input stability")?;
    let lanes=hold["selectors"].as_array().ok_or("frontend lane array")?;
    need(lanes.len()==1,"frontend one completed lane")?;let lane=&lanes[0];let raw=&lane["capture_raw"];
    need(lane["selector"]=="opening_batch::native32_tests::native32_repeated_role1_frontend_bounded"
        && lane["ignored"]==true && lane["wall_limit_seconds"]==600 && lane["test_result"]["result"]=="PASS"
        && lane["test_result"]["phase_markers"]==front["phase_marks"]
        && raw["status"]=="PASS" && raw["root_exit"]==0 && raw["killed"]==false && raw["uncertain"]==false
        && raw["final_active"]==0 && raw["total_processes"]==1 && raw["root_closed"]==true
        && raw["thread_closed"]==true && raw["job_closed"]==true
        && raw["child_handle_count"]==raw["child_handles_closed"] && raw["errors"]==serde_json::json!([]),
        "original frontend natural closed process")?;
    need(recovery["schema"]=="nipopow-opening-native32-offline-replay-v1"
        && recovery["status"]=="OFFLINE_REPLAY_PASS" && recovery["original_capture_status"]=="HOLD"
        && recovery["original_hold_sha256"]==FRONTEND_HOLD_SHA && recovery["report_sha256"]==FRONTEND_RESULT_SHA
        && recovery["adapter_sha256"]==REPLAY_ADAPTER_SHA
        && recovery["executed_controller_sha256"]==FRONTEND_CONTROLLER_SHA
        && recovery["source_manifest_sha256"]==FRONTEND_SOURCE_MF && recovery["binary_sha256"]==FRONTEND_BINARY_SHA
        && recovery["current_large_source_revalidated"]==false && recovery["native_rerun"]==false
        && recovery["pcs_invoked"]==false && recovery["frontend_result"]==*front,
        "separate reviewed offline recovery join")?;
    Ok(())
}

struct DoryRecorded {rounds:Vec<[Fr;3]>,terminal:Fr,point:Vec<Fr>,counters:[u64;3],continuation:Fr}
fn dory_recorded(front:&serde_json::Value)->Result<DoryRecorded,String>{
    let data=&front["frontend"];
    need(data["round_count"]==32 && data["point_count"]==32,"recorded frontend dimension")?;
    let rows=data["rounds"].as_array().ok_or("recorded quadratic array")?;
    let coordinates=data["point"].as_array().ok_or("recorded coordinate array")?;
    need(rows.len()==32 && coordinates.len()==32,"recorded frontend exact vector lengths")?;
    let mut rounds=Vec::with_capacity(32);
    for row in rows{
        let coefficients=row.as_array().ok_or("recorded quadratic")?;need(coefficients.len()==3,"recorded quadratic width")?;
        rounds.push([scalar(coefficients[0].as_str().ok_or("recorded Fr")?)?,
            scalar(coefficients[1].as_str().ok_or("recorded Fr")?)?,scalar(coefficients[2].as_str().ok_or("recorded Fr")?)?]);
    }
    let mut point=Vec::with_capacity(32);for coordinate in coordinates{point.push(scalar(coordinate.as_str().ok_or("recorded point Fr")?)?);}
    let counters=data["transcript_counters"].as_array().ok_or("recorded transcript counters")?;
    need(counters.len()==3,"recorded counter count")?;
    Ok(DoryRecorded{rounds,point,terminal:scalar(data["terminal_hex"].as_str().ok_or("recorded terminal")?)?,
        counters:[counters[0].as_u64().ok_or("recorded counter")?,counters[1].as_u64().ok_or("recorded counter")?,
            counters[2].as_u64().ok_or("recorded counter")?],
        continuation:scalar(data["continuation_hex"].as_str().ok_or("recorded continuation")?)?})
}
fn dory_counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
fn dory_replay_checked(statement:&Statement,record:&DoryRecorded)->Result<(Vec<Fr>,Transcript),String>{
    let mut transcript=Transcript::new(DOMAIN);
    let point=replay_frontend_on(statement,&record.rounds,record.terminal,&mut transcript,None)?;
    need(point==record.point && dory_counters(&transcript)==record.counters,"replayed point/counters mismatch")?;
    need(transcript.clone().challenge_scalar(CONTINUATION)==record.continuation,"clone-only frontend continuation mismatch")?;
    Ok((point,transcript))
}
fn dory_endpoint_equal(value:Fr,terminal:Fr)->Result<(),String>{need(value==terminal,"source MLE disagrees with replayed terminal")}
fn dory_read_locked(input:&Held,size:usize,pin:&str)->Result<Vec<u8>,String>{
    input.check()?;let mut file=input.file.try_clone().map_err(|e|e.to_string())?;
    file.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;
    let mut bytes=Vec::with_capacity(size);file.take(size as u64+1).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
    check_pin(&bytes,size,pin)?;input.check()?;Ok(bytes)
}
fn dory_codec_sizes()->Result<(usize,usize),String>{
    use ark_ec::pairing::PairingOutput;
    use ark_bn254::{Bn254,G1Projective,G2Projective};
    let g1=G1Projective::zero().compressed_size();let g2=G2Projective::zero().compressed_size();
    let gt=PairingOutput::<Bn254>::zero().compressed_size();
    let round=add(add(gt.checked_mul(6).ok_or("Dory size")?,g1.checked_mul(3).ok_or("Dory size")?)?,
        g2.checked_mul(3).ok_or("Dory size")?)?;
    let mut backend=gt.checked_mul(2).ok_or("Dory size")?;
    for bytes in [g1,4,round.checked_mul(16).ok_or("Dory size")?,1,g1,g2,8]{backend=add(backend,bytes)?;}
    let batch=add(add(add(12,32usize.checked_mul(96).ok_or("batch size")?)?,36)?,backend)?;
    need((backend,batch)==(42381,45501),"native32 canonical codec schema drift")?;Ok((backend,batch))
}
fn dory_capacity<T>(values:&Vec<T>)->Result<usize,String>{values.capacity().checked_mul(size_of::<T>()).ok_or("Dory capacity overflow".into())}
fn dory_verifier_capacity(verifier:&dory_pcs::VerifierSetup<dory_pcs::backends::arkworks::BN254>)->Result<usize,String>{
    let mut bytes=size_of_val(verifier);
    for values in [&verifier.delta_1l,&verifier.delta_1r,&verifier.delta_2l,&verifier.delta_2r,&verifier.chi]{
        bytes=add(bytes,dory_capacity(values)?)?;
    }Ok(bytes)
}
fn dory_setup_capacity(setup:&pcs::Setup)->Result<usize,String>{
    let mut bytes=size_of::<pcs::Setup>();bytes=add(bytes,dory_capacity(&setup.prover.g1_vec)?)?;
    bytes=add(bytes,dory_capacity(&setup.prover.g2_vec)?)?;
    // The verifier inline object is already in Setup.
    add(bytes,dory_verifier_capacity(&setup.verifier)?.checked_sub(size_of_val(&setup.verifier)).ok_or("verifier inventory")?)
}
fn dory_retained_capacity(admitted:&Admitted,record:&DoryRecorded,point:&Vec<Fr>,key:&Vec<u8>)->Result<usize,String>{
    let mut bytes=add(size_of::<Admitted>(),dory_capacity(&admitted.held)?)?;
    for held in &admitted.held{bytes=add(bytes,held.heap_bytes()?)?;}
    for claim in &admitted.statement.claims{bytes=add(bytes,dory_capacity(&claim.point)?)?;}
    for size in [dory_capacity(&record.rounds)?,dory_capacity(&record.point)?,dory_capacity(point)?,
        dory_capacity(key)?,admitted.output.capacity().checked_mul(2).ok_or("output path capacity")?,
        admitted.report_path.capacity().checked_mul(2).ok_or("report path capacity")?,
        size_of::<DoryRecorded>(),REPORT_CAP,size_of::<DoryReport<'_>>(),4096,
        size_of::<std::sync::Mutex<crate::packed::PackedIoSnapshot>>()+2*size_of::<usize>()]{
        bytes=add(bytes,size)?;
    }need(bytes<=META_LIMIT,"Dory retained metadata exceeds8MiB")?;Ok(bytes)
}
fn dory_io(snapshot:crate::packed::PackedIoSnapshot)->Result<Io,String>{
    need(snapshot.write_calls==0 && snapshot.write_bytes==0 && snapshot.sync_calls==0,"Dory source must remain readonly")?;
    Ok(Io{read_calls:snapshot.read_calls,read_bytes:snapshot.read_bytes,read_ns:snapshot.read_ns,
        write_calls:snapshot.write_calls,write_bytes:snapshot.write_bytes,sync_calls:snapshot.sync_calls})
}
fn dory_mark(start:Instant,index:usize,marks:&mut [Mark;9])->Result<(),String>{
    use std::io::Write;
    need(index<9,"Dory phase index")?;
    let mark=Mark{name:DORY_PHASES[index],elapsed_ns:start.elapsed().as_nanos()};
    let mut output=std::io::stdout().lock();
    if index==0{writeln!(output).map_err(|e|e.to_string())?;}
    writeln!(output,"NIPOPOW_OPENING_DORY_PHASE {{\"name\":\"{}\",\"elapsed_ns\":{}}}",mark.name,mark.elapsed_ns).map_err(|e|e.to_string())?;
    output.flush().map_err(|e|e.to_string())?;marks[index]=mark;Ok(())
}

#[derive(Serialize)]
struct DoryScope{input_log:usize,claims:usize,repeated_role1:bool,frontend_replayed:bool,pcs_invoked:bool,
    full_batch_verified:bool,all_seven_roles:bool,full_history:bool,production:bool}
#[derive(Serialize)]
struct DoryFrontendInputs{source9_manifest_sha256:&'static str,source9_binary_sha256:&'static str,
    controller_sha256:&'static str,hold_sha256:&'static str,result_sha256:&'static str,replay_sha256:&'static str,review_sha256:&'static str}
#[derive(Serialize)]
struct DoryInputs{native1:Inputs,frontend:DoryFrontendInputs}
#[derive(Serialize)]
struct DoryReplay<'a>{round_count:usize,point_count:usize,point_hex:Points<'a>,terminal_hex:ScalarHex<'a>,
    transcript_counters:[u64;3],continuation_hex:ScalarHex<'a>,matches_captured:bool}
#[derive(Serialize)]
struct DoryEndpoint{source_mle_equal:bool,io:Io}
#[derive(Serialize)]
struct DoryProducer{setup_key_equal:bool,setup_id_equal:bool,commitment_equal:bool,rows:usize,nu:usize,sigma:usize,
    setup_owned_capacity_bytes:usize,row_owned_capacity_bytes:usize,row_clone_payload_bound_bytes:usize,
    retained_capacity_bytes:usize,backend_scratch_measured:bool,process_limit_bytes:u64,commit_io:Io,open_io:Io,opener_additional_mle:bool}
#[derive(Serialize)]
struct DoryProofView<'a>{batch_bytes:usize,batch_sha256:&'a str,dory_bytes:usize,canonical_roundtrip:bool,
    full_verify_admitted:bool,sender_counters:[u64;3],verifier_counters:[u64;3],post_pcs_continuation_hex:ScalarHex<'a>,
    pcs_producer_invocations:usize,invalid_dory_rejected:bool,invalid_terminal_rejected:bool,invalid_point_rejected:bool,allocation_capacity_bytes:usize}
#[derive(Serialize)]
struct DoryTiming{admission:u128,replay:u128,endpoint_mle:u128,setup:u128,commit:u128,dory_open:u128,codec:u128,full_verify:u128,negative_controls:u128,total_before_export:u128}
#[derive(Serialize)]
struct DoryReport<'a>{schema:&'static str,state:&'static str,scope:DoryScope,inputs:DoryInputs,replay:DoryReplay<'a>,
    endpoint:DoryEndpoint,producer:DoryProducer,proof:DoryProofView<'a>,phase_marks:[Mark;9],timing_ms:DoryTiming}


fn execute_dory()->Result<(),String>{
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    use dory_pcs::primitives::arithmetic::Group;
    let began=Instant::now();
    let mut admitted=admit_native_for("NIPOPOW_OPENING_BATCH_DORY32_CAPTURE_DIR")?;
    for (env,size,sha) in [
        ("NIPOPOW_NATIVE_FRONTEND_HOLD_PATH",8125,FRONTEND_HOLD_SHA),
        ("NIPOPOW_NATIVE_FRONTEND_RESULT_PATH",12306,FRONTEND_RESULT_SHA),
        ("NIPOPOW_NATIVE_FRONTEND_REPLAY_PATH",16784,FRONTEND_REPLAY_SHA),
        ("NIPOPOW_NATIVE_FRONTEND_REVIEW_PATH",2936,FRONTEND_REVIEW_SHA)]{
        admitted.held.push(Held::open(env,size,Some(sha))?);
    }
    need(admitted.held.len()==12 && admitted.statement.log_n==32,"sealed Dory input geometry")?;
    let record={
        let hold:serde_json::Value=serde_json::from_slice(&admitted.held[8].bytes).map_err(|e|e.to_string())?;
        let front:serde_json::Value=serde_json::from_slice(&admitted.held[9].bytes).map_err(|e|e.to_string())?;
        let recovery:serde_json::Value=serde_json::from_slice(&admitted.held[10].bytes).map_err(|e|e.to_string())?;
        dory_frontend_admission(&front,&hold,&recovery)?;dory_recorded(&front)?
    };
    for held in &mut admitted.held{held.check()?;held.clear_bytes();}
    admitted.report_path=admitted.output.join("opening-native32-result.json");
    let key_bytes=dory_read_locked(&admitted.held[2],33264,KEY_SHA)?;
    let key=crate::verifier_key::admit_generated_test_key(32,&key_bytes,bytes32(SETUP_ID)?)?;
    let mut marks=[Mark{name:"",elapsed_ns:0};9];
    let admission_ms=began.elapsed().as_millis();dory_mark(began,0,&mut marks)?;
    let phase=Instant::now();let (point,mut sender)=dory_replay_checked(&admitted.statement,&record)?;
    let replay_ms=phase.elapsed().as_millis();dory_mark(began,1,&mut marks)?;
    admitted.source.reset_io_metrics();let phase=Instant::now();
    dory_endpoint_equal(admitted.source.evaluate(&point)?,record.terminal)?;
    for held in &admitted.held{held.check()?;}
    let endpoint_io=dory_io(admitted.source.io_metrics_snapshot())?;
    need(endpoint_io.read_bytes==536870912 && endpoint_io.read_calls>0,"endpoint one packed source MLE read")?;
    let endpoint_ms=phase.elapsed().as_millis();dory_mark(began,2,&mut marks)?;

    // Fresh producer objects are necessary: the accepted key/commitment artifacts
    // do not contain a Setup or the ordered 65536 row commitments.
    let phase=Instant::now();let setup=pcs::generate_setup_for_scale_diagnostic(32)?;
    need(setup.id==bytes32(SETUP_ID)? && setup.id==*key.id(),"reconstructed setup ID")?;
    let generated_key=pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))?;
    need(generated_key==key_bytes,"reconstructed setup must match pinned key")?;drop(generated_key);
    let setup_bytes=dory_setup_capacity(&setup)?;
    let setup_ms=phase.elapsed().as_millis();dory_mark(began,3,&mut marks)?;
    admitted.source.reset_io_metrics();let phase=Instant::now();
    let committed=packed::commit(&admitted.source,&setup)?;
    need(committed.rows.len()==65536 && committed.nu==16 && committed.sigma==16
        && pcs::encode_commitment(&committed.commitment)?==pcs::encode_commitment(&admitted.statement.commitment)?,
        "reconstructed rows and commitment match held source statement")?;
    let row_bytes=dory_capacity(&committed.rows)?;
    let clone_bytes=committed.rows.len().checked_mul(size_of::<dory_pcs::backends::arkworks::ArkG1>()).ok_or("row clone payload overflow")?;
    let verifier_heap=dory_verifier_capacity(key.verifier())?.checked_sub(size_of_val(key.verifier())).ok_or("key inventory")?;
    let retained=add(add(dory_retained_capacity(&admitted,&record,&point,&key_bytes)?,
        size_of::<crate::verifier_key::AdmittedVerifierKey>())?,verifier_heap)?;
    need(retained<=META_LIMIT,"Dory final retained metadata exceeds8MiB")?;
    // This is an owned-payload/clone reservation, not a measurement of unchanged
    // vendor scratch or process memory. The Windows Job separately caps 2GiB.
    let managed_bound=add(add(add(add(retained,setup_bytes)?,row_bytes)?,clone_bytes)?,1024*1024)?;
    need(managed_bound<=512*1024*1024,"Dory owned payload reservation exceeds512MiB")?;
    let commit_io=dory_io(admitted.source.io_metrics_snapshot())?;
    need(commit_io.read_bytes>0 && commit_io.read_calls>0,"fresh commitment observed source reads")?;
    let commit_ms=phase.elapsed().as_millis();dory_mark(began,4,&mut marks)?;

    admitted.source.reset_io_metrics();let phase=Instant::now();
    // Unconditional opening, including a zero batch factor. This opener performs
    // its own additional MLE evaluation before its Dory product reads.
    let opening=packed::open(&committed,&admitted.source,&point,&setup,&mut sender)?;
    let open_io=dory_io(admitted.source.io_metrics_snapshot())?;
    need(open_io.read_bytes>=536870912 && open_io.read_calls>0,"opener additional source evaluation observed")?;
    let open_ms=phase.elapsed().as_millis();dory_mark(began,5,&mut marks)?;
    let phase=Instant::now();let (dory_size,batch_size)=dory_codec_sizes()?;
    need(pcs::encode_proof(&opening)?.len()==dory_size,"canonical Dory32 extent")?;
    let proof=Proof{rounds:record.rounds,terminal:record.terminal,pcs:opening};
    let packet=encode_proof(&proof,32)?;
    need(packet.len()==batch_size,"canonical native32 batch extent")?;drop(proof);
    let decoded=decode_proof(&packet,32)?;
    need(encode_proof(&decoded,32)?==packet,"native32 batch canonical roundtrip")?;
    let allocation=add(add(add(add(size_of::<Proof>(),dory_capacity(&decoded.rounds)?)?,
        dory_capacity(&decoded.pcs.first_messages)?)?,dory_capacity(&decoded.pcs.second_messages)?)?,packet.capacity())?;
    need(allocation<=1024*1024,"canonical proof allocation exceeds codec reservation")?;
    let codec_ms=phase.elapsed().as_millis();dory_mark(began,6,&mut marks)?;

    let phase=Instant::now();
    let receiver=verify_admitted(&admitted.statement,&key,&decoded)?;
    need(dory_counters(&sender)==dory_counters(&receiver),"full sender/verifier counters")?;
    let continuation=sender.clone().challenge_scalar(DORY_CONTINUATION);
    need(continuation==receiver.clone().challenge_scalar(DORY_CONTINUATION),"full sender/verifier continuation")?;
    let verify_ms=phase.elapsed().as_millis();let negative_phase=Instant::now();
    // Exercise valid canonical corruption through the actual full verifier,
    // independently from malformed codec and the replay-prefix checks.
    {
        let mut bad_pcs=decoded.pcs.clone();
        let previous=bad_pcs.vmv_message.c;
        bad_pcs.vmv_message.c=if previous==<ArkGT as Group>::identity(){setup.prover.ht}else{<ArkGT as Group>::identity()};
        need(bad_pcs.vmv_message.c!=previous,"nontrivial Dory message fault")?;
        let bad=Proof{rounds:decoded.rounds.clone(),terminal:decoded.terminal,pcs:bad_pcs};
        let bytes=encode_proof(&bad,32)?;let canonical=decode_proof(&bytes,32)?;
        need(verify_admitted(&admitted.statement,&key,&canonical).is_err(),"changed canonical Dory message accepted")?;
    }
    {
        let bad=Proof{rounds:decoded.rounds.clone(),terminal:decoded.terminal+Fr::one(),pcs:decoded.pcs.clone()};
        need(verify_admitted(&admitted.statement,&key,&bad).is_err(),"substituted terminal accepted by full verifier")?;
    }
    {
        let mut wrong=admitted.statement.clone();wrong.claims[0].point[0]+=Fr::one();
        need(verify_admitted(&wrong,&key,&decoded).is_err(),"substituted expected point accepted by full verifier")?;
    }
    let negative_ms=negative_phase.elapsed().as_millis();dory_mark(began,7,&mut marks)?;
    for held in &admitted.held{held.check()?;}
    let batch_sha=hex(&role0_sha256(&packet)?);dory_mark(began,8,&mut marks)?;
    let report=DoryReport{
        schema:"native32-opening-batch-dory-diagnostic-v1",state:"REPEATED_NATIVE1_OPENING_COMPLETE",
        scope:DoryScope{input_log:32,claims:7,repeated_role1:true,frontend_replayed:true,pcs_invoked:true,
            full_batch_verified:true,all_seven_roles:false,full_history:false,production:false},
        inputs:DoryInputs{native1:Inputs{source8_manifest_sha256:SOURCE_MF,source8_binary_sha256:SOURCE_BINARY,
            native1_receipt_sha256:RECEIPT_SHA,native1_result_sha256:RESULT_SHA,native1_proof_sha256:PROOF_SHA,
            native1_review_sha256:REVIEW_SHA,raw_sha256:RAW_SHA,raw_blake2b256:RAW_BLAKE,witness_sha256:WITNESS_SHA,
            witness_blake2b256:WITNESS_BLAKE,key_sha256:KEY_SHA,commitment_sha256:COMMIT_SHA,setup_id:SETUP_ID},
            frontend:DoryFrontendInputs{source9_manifest_sha256:FRONTEND_SOURCE_MF,source9_binary_sha256:FRONTEND_BINARY_SHA,
                controller_sha256:FRONTEND_CONTROLLER_SHA,hold_sha256:FRONTEND_HOLD_SHA,result_sha256:FRONTEND_RESULT_SHA,
                replay_sha256:FRONTEND_REPLAY_SHA,review_sha256:FRONTEND_REVIEW_SHA}},
        replay:DoryReplay{round_count:32,point_count:32,point_hex:Points(&point),terminal_hex:ScalarHex(&decoded.terminal),
            transcript_counters:record.counters,continuation_hex:ScalarHex(&record.continuation),matches_captured:true},
        endpoint:DoryEndpoint{source_mle_equal:true,io:endpoint_io},
        producer:DoryProducer{setup_key_equal:true,setup_id_equal:true,commitment_equal:true,rows:65536,nu:16,sigma:16,
            setup_owned_capacity_bytes:setup_bytes,row_owned_capacity_bytes:row_bytes,row_clone_payload_bound_bytes:clone_bytes,
            retained_capacity_bytes:retained,backend_scratch_measured:false,process_limit_bytes:2147483648,
            commit_io,open_io,opener_additional_mle:true},
        proof:DoryProofView{batch_bytes:packet.len(),batch_sha256:&batch_sha,dory_bytes:dory_size,
            canonical_roundtrip:true,full_verify_admitted:true,sender_counters:dory_counters(&sender),verifier_counters:dory_counters(&receiver),
            post_pcs_continuation_hex:ScalarHex(&continuation),pcs_producer_invocations:1,invalid_dory_rejected:true,
            invalid_terminal_rejected:true,invalid_point_rejected:true,allocation_capacity_bytes:allocation},
        phase_marks:marks,timing_ms:DoryTiming{admission:admission_ms,replay:replay_ms,endpoint_mle:endpoint_ms,setup:setup_ms,
            commit:commit_ms,dory_open:open_ms,codec:codec_ms,full_verify:verify_ms,negative_controls:negative_ms,total_before_export:began.elapsed().as_millis()}};
    let mut output=BoundedBytes(Vec::with_capacity(REPORT_CAP));
    serde_json::to_writer(&mut output,&report).map_err(|e|e.to_string())?;
    need(output.0.len()<=REPORT_CAP && output.0.capacity()==REPORT_CAP,"bounded native32 Dory report")?;drop(report);
    std::fs::create_dir(&admitted.output).map_err(|e|e.to_string())?;
    for (path,bytes) in [(admitted.output.join("opening-native32.batch"),packet.as_slice()),(admitted.report_path.clone(),output.0.as_slice())]{
        let mut file=OpenOptions::new().write(true).create_new(true).open(path).map_err(|e|e.to_string())?;
        file.write_all(bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;
    }
    for held in &admitted.held{held.check()?;}Ok(())
}

#[test]
#[ignore="native32 replayed frontend plus complete Dory opening; separately reviewed capture required"]
fn native32_replayed_frontend_dory_bounded(){execute_dory().unwrap();}

#[test]
fn native32_replay_admission_controls(){
    use dory_pcs::primitives::arithmetic::Group;
    struct Tiny;
    impl RowSource for Tiny{
        fn input_len(&self)->usize{2}
        fn read_row(&self,width:usize,row:usize)->Result<Vec<Fr>,String>{
            if width!=2||row!=0{return Err("tiny source bounds".into());}Ok(vec![Fr::zero(),Fr::one()])
        }
    }
    let statement=Statement{log_n:1,setup_id:[0x71;32],commitment:<ArkGT as Group>::identity(),corpus_id:Some([0x53;32]),
        claims:std::array::from_fn(|_|Claim{point:vec![Fr::from(3u64)],value:Fr::from(3u64)})};
    let mut producer=Transcript::new(DOMAIN);
    let front=prove_frontend_on_mode(&Tiny,&statement,&mut producer,None,ProjectionMode::Fused,None).unwrap();
    let record=DoryRecorded{rounds:front.rounds,terminal:front.terminal,point:front.point,
        counters:dory_counters(&producer),continuation:producer.clone().challenge_scalar(CONTINUATION)};
    let (point,replayed)=dory_replay_checked(&statement,&record).unwrap();
    assert_eq!(point,record.point);assert_eq!(dory_counters(&replayed),dory_counters(&producer));
    assert_eq!(replayed.clone().challenge_scalar(DORY_CONTINUATION),producer.clone().challenge_scalar(DORY_CONTINUATION));
    let clone_record=||DoryRecorded{rounds:record.rounds.clone(),terminal:record.terminal,point:record.point.clone(),
        counters:record.counters,continuation:record.continuation};
    let mut bad=clone_record();bad.rounds[0][0]+=Fr::one();assert!(dory_replay_checked(&statement,&bad).is_err());
    let mut bad=clone_record();bad.point[0]+=Fr::one();assert!(dory_replay_checked(&statement,&bad).is_err());
    let mut bad=clone_record();bad.terminal+=Fr::one();assert!(dory_replay_checked(&statement,&bad).is_err());
    for index in 0..3{
        let mut bad=clone_record();bad.counters[index]+=1;assert!(dory_replay_checked(&statement,&bad).is_err());
    }
    let mut bad=clone_record();bad.continuation+=Fr::one();assert!(dory_replay_checked(&statement,&bad).is_err());
    for fault in 0..4{
        let mut changed=statement.clone();
        match fault{0=>changed.claims[0].point[0]+=Fr::one(),1=>changed.claims[0].value+=Fr::one(),
            2=>changed.corpus_id=Some([0x54;32]),_=>changed.setup_id[0]^=1}
        assert!(dory_replay_checked(&changed,&record).is_err());
    }
    dory_endpoint_equal(record.terminal,record.terminal).unwrap();
    assert!(dory_endpoint_equal(record.terminal+Fr::one(),record.terminal).is_err());
    assert_eq!(dory_codec_sizes().unwrap(),(42381,45501));
    assert!(decode_proof(&vec![0;45501],32).is_err());
    assert!(scalar(&"FF".repeat(32)).is_err());
    assert_eq!(dory_counters(&producer),record.counters,"clone continuation must not advance sender");
    // This is a boundary-only metadata fixture, not an accepted native receipt.
    let front=serde_json::json!({"schema":"native32-opening-frontend-diagnostic-v1","state":"FRONTEND_ONLY_COMPLETE",
        "scope":{"input_log":32,"claims":7,"repeated_role1":true,"pcs_invoked":false},"phase_marks":[]});
    let raw=serde_json::json!({"status":"PASS","root_exit":0,"killed":false,"uncertain":false,"final_active":0,
        "total_processes":1,"root_closed":true,"thread_closed":true,"job_closed":true,
        "child_handle_count":0,"child_handles_closed":0,"errors":[]});
    let hold=serde_json::json!({"schema":"nipopow-opening-native32-runtime-capture-v1","status":"HOLD",
        "controller_sha256":FRONTEND_CONTROLLER_SHA,"source_manifest_sha256":FRONTEND_SOURCE_MF,
        "binary_sha256":FRONTEND_BINARY_SHA,"binary_bytes":59146240,"quiescent":true,
        "post_settlement_checks":"COMPLETED","diagnostic_errors":[
            "AttributeError:'types.SimpleNamespace' object has no attribute 'native1_result_bytes'"],
        "source_audits":[{"status":"PASS","source_manifest_sha256":FRONTEND_SOURCE_MF},
            {"status":"PASS","source_manifest_sha256":FRONTEND_SOURCE_MF}],
        "native_inputs":{"boundary_fixture":1},"native_inputs_post":{"boundary_fixture":1},
        "selectors":[{"selector":"opening_batch::native32_tests::native32_repeated_role1_frontend_bounded",
            "ignored":true,"wall_limit_seconds":600,"test_result":{"result":"PASS","phase_markers":[]},"capture_raw":raw}]});
    let recovery=serde_json::json!({"schema":"nipopow-opening-native32-offline-replay-v1","status":"OFFLINE_REPLAY_PASS",
        "original_capture_status":"HOLD","original_hold_sha256":FRONTEND_HOLD_SHA,"report_sha256":FRONTEND_RESULT_SHA,
        "adapter_sha256":REPLAY_ADAPTER_SHA,"executed_controller_sha256":FRONTEND_CONTROLLER_SHA,
        "source_manifest_sha256":FRONTEND_SOURCE_MF,"binary_sha256":FRONTEND_BINARY_SHA,
        "current_large_source_revalidated":false,"native_rerun":false,"pcs_invoked":false,"frontend_result":front});
    dory_frontend_admission(&front,&hold,&recovery).unwrap();
    let mut faults=0usize;
    for pointer in ["/schema","/state"]{
        let mut bad=front.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!("wrong");
        assert!(dory_frontend_admission(&bad,&hold,&recovery).is_err());faults+=1;
    }
    for pointer in ["/scope/input_log","/scope/claims"]{
        let mut bad=front.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!(0);
        assert!(dory_frontend_admission(&bad,&hold,&recovery).is_err());faults+=1;
    }
    for pointer in ["/scope/repeated_role1","/scope/pcs_invoked"]{
        let mut bad=front.clone();let current=bad.pointer(pointer).unwrap().as_bool().unwrap();
        *bad.pointer_mut(pointer).unwrap()=serde_json::json!(!current);
        assert!(dory_frontend_admission(&bad,&hold,&recovery).is_err());faults+=1;
    }
    for pointer in ["/schema","/status","/controller_sha256","/source_manifest_sha256","/binary_sha256","/post_settlement_checks"]{
        let mut bad=hold.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!("wrong");
        assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    }
    let mut bad=hold.clone();bad["binary_bytes"]=serde_json::json!(1);
    assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    for pointer in ["/quiescent","/selectors/0/ignored","/selectors/0/capture_raw/root_closed",
        "/selectors/0/capture_raw/thread_closed","/selectors/0/capture_raw/job_closed"]{
        let mut bad=hold.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!(false);
        assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    }
    for pointer in ["/selectors/0/capture_raw/killed","/selectors/0/capture_raw/uncertain"]{
        let mut bad=hold.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!(true);
        assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    }
    for (pointer,value) in [("/selectors/0/capture_raw/root_exit",1),("/selectors/0/capture_raw/final_active",1),
        ("/selectors/0/capture_raw/total_processes",2),("/selectors/0/capture_raw/child_handles_closed",1),
        ("/selectors/0/wall_limit_seconds",601)]{
        let mut bad=hold.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!(value);
        assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    }
    for pointer in ["/schema","/status","/original_capture_status","/original_hold_sha256","/report_sha256",
        "/adapter_sha256","/executed_controller_sha256","/source_manifest_sha256","/binary_sha256"]{
        let mut bad=recovery.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!("wrong");
        assert!(dory_frontend_admission(&front,&hold,&bad).is_err());faults+=1;
    }
    for pointer in ["/current_large_source_revalidated","/native_rerun","/pcs_invoked"]{
        let mut bad=recovery.clone();*bad.pointer_mut(pointer).unwrap()=serde_json::json!(true);
        assert!(dory_frontend_admission(&front,&hold,&bad).is_err());faults+=1;
    }
    let mut bad=recovery.clone();bad["frontend_result"]["state"]=serde_json::json!("wrong");
    assert!(dory_frontend_admission(&front,&hold,&bad).is_err());faults+=1;
    let mut bad=hold.clone();bad["native_inputs_post"]["boundary_fixture"]=serde_json::json!(2);
    assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    let mut bad=hold.clone();bad["source_audits"].as_array_mut().unwrap().pop();
    assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    let mut bad=hold.clone();bad["diagnostic_errors"].as_array_mut().unwrap().push(serde_json::json!("extra"));
    assert!(dory_frontend_admission(&front,&bad,&recovery).is_err());faults+=1;
    assert_eq!(faults,41);
}

// Small same-X composition smoke. These literal domains and the canonical
// descriptor codec are shared with the later log31 test-only wrapper.
const SAME_X_SMOKE_DESCRIPTOR_TAG: &[u8] = b"nipopow-same-x-owner-projection-descriptor-v1";
const SAME_X_SMOKE_CORPUS_DOMAIN: &[u8] = b"nipopow-same-x-owner-projection-corpus-v1";
const SAME_X_SMOKE_GKR_DOMAIN: &[u8] = b"nipopow-same-x-owner-projection-gkr-v1";
const SAME_X_SMOKE_DIR_ENV: &str = "NIPOPOW_SAME_X_SMOKE_DIR";
const SAME_X_SMOKE_STATEMENT_MAGIC: &[u8; 8] = b"XSSTMT01";
const SAME_X_SMOKE_STATEMENT_LIMIT: usize = 2048;
const SAME_X_SMOKE_LOG_N: usize = 5;
const SAME_X_SMOKE_WIRE_BITS: usize = 3;
const SAME_X_SMOKE_OWNER_BITS: usize = 2;
const SAME_X_SMOKE_OWNER_IDS: [usize; 3] = [0, 2, 3];
const SAME_X_SMOKE_OWNER_SLOTS: [u8; 4] = [0, 3, 1, 2];
const SAME_X_SMOKE_ARTIFACTS: [&str; 5] = [
    "same-x-smoke-statement.bin",
    "same-x-smoke-commitment.bin",
    "same-x-smoke-verifier.key",
    "same-x-smoke-gkr.proof",
    "same-x-smoke-opening.proof",
];

fn same_x_smoke_u64(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(&(value as u64).to_le_bytes());
}

fn same_x_smoke_circuit(pin_wire_one: bool) -> (Vec<u8>, sparse::Circuit) {
    // Four owner slices of eight wires. Owner 1 is the omitted zero slice;
    // the nontrivial mapping is owner 0->slot 0, 2->slot 1, 3->slot 2.
    let pinned_zero = 2 * 8 + 1;
    let pinned_one = 2 * 8 + 6;
    let mut terms = vec![
        sparse::Term {
            row: 0,
            gate: gkr::Gate { left: pinned_zero, right: 0, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() },
        },
        sparse::Term {
            row: 1,
            gate: gkr::Gate { left: pinned_one, right: 0,
                c0: if pin_wire_one { -Fr::one() } else { Fr::zero() },
                c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() },
        },
        // A bilinear constraint and a second linear term share row 2:
        // slot0/wire0 * slot0/wire1 - slot0/wire2 = 0.
        sparse::Term {
            row: 2,
            gate: gkr::Gate { left: 0, right: 1, c0: Fr::zero(), c1: Fr::zero(), c2: Fr::zero(), c3: Fr::one() },
        },
        sparse::Term {
            row: 2,
            gate: gkr::Gate { left: 2, right: 0, c0: Fr::zero(), c1: -Fr::one(), c2: Fr::zero(), c3: Fr::zero() },
        },
        // A separate equality row ensures the toy circuit has more than pins.
        sparse::Term {
            row: 3,
            gate: gkr::Gate { left: 0, right: 0, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() },
        },
        sparse::Term {
            row: 3,
            gate: gkr::Gate { left: 1, right: 0, c0: Fr::zero(), c1: -Fr::one(), c2: Fr::zero(), c3: Fr::zero() },
        },
    ];
    let circuit = sparse::Circuit { input_len: 1 << SAME_X_SMOKE_LOG_N, row_count: 4, terms: std::mem::take(&mut terms) };
    let mut descriptor = Vec::new();
    descriptor.extend_from_slice(SAME_X_SMOKE_DESCRIPTOR_TAG);
    descriptor.push(0); // version separator
    same_x_smoke_u64(&mut descriptor, SAME_X_SMOKE_LOG_N);
    same_x_smoke_u64(&mut descriptor, SAME_X_SMOKE_WIRE_BITS);
    same_x_smoke_u64(&mut descriptor, SAME_X_SMOKE_OWNER_BITS);
    same_x_smoke_u64(&mut descriptor, circuit.input_len);
    same_x_smoke_u64(&mut descriptor, circuit.row_count);
    same_x_smoke_u64(&mut descriptor, SAME_X_SMOKE_OWNER_IDS.len());
    for (slot, owner) in SAME_X_SMOKE_OWNER_IDS.iter().copied().enumerate() {
        same_x_smoke_u64(&mut descriptor, owner);
        same_x_smoke_u64(&mut descriptor, slot);
    }
    // Explicitly bind the unused global owner and the zero local slot.
    same_x_smoke_u64(&mut descriptor, 1);
    same_x_smoke_u64(&mut descriptor, 3);
    descriptor.push(0); // slot 3 is the all-zero slice
    same_x_smoke_u64(&mut descriptor, 2); // public pin count
    for (row, wire, value) in [(0usize, pinned_zero, 0u8), (1, pinned_one, pin_wire_one as u8)] {
        same_x_smoke_u64(&mut descriptor, row);
        same_x_smoke_u64(&mut descriptor, wire);
        descriptor.push(value);
    }
    same_x_smoke_u64(&mut descriptor, circuit.terms.len());
    for term in &circuit.terms {
        same_x_smoke_u64(&mut descriptor, term.row);
        same_x_smoke_u64(&mut descriptor, term.gate.left);
        same_x_smoke_u64(&mut descriptor, term.gate.right);
        for value in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
            let mut encoded = [0u8; 32];
            value.serialize_compressed(&mut encoded[..]).expect("Fr canonical encoding");
            descriptor.extend_from_slice(&encoded);
        }
    }
    (descriptor, circuit)
}

fn same_x_smoke_corpus_id(descriptor: &[u8]) -> [u8; 32] {
    let mut hasher = Blake2b::<U32>::new();
    hasher.update(SAME_X_SMOKE_CORPUS_DOMAIN);
    hasher.update((descriptor.len() as u64).to_le_bytes());
    hasher.update(descriptor);
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn same_x_smoke_dir() -> PathBuf {
    let path = PathBuf::from(std::env::var_os(SAME_X_SMOKE_DIR_ENV).expect("smoke artifact directory env"));
    assert!(crate::preview_test_paths::absolute_outside_source(&path), "smoke artifacts must be absolute and outside source");
    assert!(path.is_dir(), "smoke artifact directory must be prepared by the controller");
    path
}

fn same_x_smoke_write(dir: &Path, name: &str, bytes: &[u8]) {
    let path = dir.join(name);
    let mut file = OpenOptions::new().write(true).create_new(true).open(path).expect("create-once smoke artifact");
    file.write_all(bytes).expect("write smoke artifact");
    file.sync_all().expect("sync smoke artifact");
}

fn same_x_smoke_read(dir: &Path, name: &str, cap: usize) -> Vec<u8> {
    let path = dir.join(name);
    let meta = std::fs::symlink_metadata(&path).expect("smoke artifact metadata");
    assert!(meta.is_file() && meta.len() <= cap as u64, "bounded regular smoke artifact");
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    File::open(path).expect("open smoke artifact").take(cap as u64 + 1)
        .read_to_end(&mut bytes).expect("read smoke artifact");
    assert_eq!(bytes.len() as u64, meta.len(), "stable smoke artifact extent");
    bytes
}

fn same_x_smoke_source_bytes() -> Vec<u8> {
    let mut bits = vec![0u8; 1usize << (SAME_X_SMOKE_LOG_N - 3)];
    let owner_slices: [[u8; 8]; 4] = [
        [1, 1, 1, 0, 1, 0, 0, 1], // global owner 0
        [0, 0, 0, 0, 0, 0, 0, 0], // global owner 1, omitted/zero
        [0, 1, 0, 0, 1, 1, 0, 0], // global owner 2
        [1, 0, 1, 1, 0, 0, 1, 0], // global owner 3; includes public pins
    ];
    for (owner, wires) in owner_slices.iter().enumerate() {
        for (wire, value) in wires.iter().copied().enumerate() {
            let index = owner * (1 << SAME_X_SMOKE_WIRE_BITS) + wire;
            if value != 0 { bits[index / 8] |= 1 << (index % 8); }
        }
    }
    bits
}

fn same_x_smoke_local_input(source: &PackedFile) -> Vec<Fr> {
    let mut input = Vec::with_capacity(1 << SAME_X_SMOKE_LOG_N);
    for slot in 0..4 {
        let owner = SAME_X_SMOKE_OWNER_SLOTS.iter().position(|mapped_slot| *mapped_slot as usize == slot)
            .expect("each toy local slot has one owner mapping");
        input.extend(source.read_copy(1 << SAME_X_SMOKE_WIRE_BITS, owner).expect("toy owner slice"));
    }
    input
}

fn same_x_smoke_owner_bits(owner: usize) -> [Fr; 2] {
    [Fr::from((owner & 1) as u64), Fr::from(((owner >> 1) & 1) as u64)]
}

fn same_x_smoke_expected_claims(source: &PackedFile, claim: &InputClaim) -> [Claim; 7] {
    assert_eq!(claim.point.len(), SAME_X_SMOKE_LOG_N);
    assert!(!claim.point[3].is_zero() && !claim.point[3].is_one(), "first selector coordinate must be non-Boolean");
    assert!(!claim.point[4].is_zero() && !claim.point[4].is_one(), "second selector coordinate must be non-Boolean");
    let points: Vec<Vec<Fr>> = SAME_X_SMOKE_OWNER_IDS.iter().map(|owner| {
        let mut point = claim.point[..SAME_X_SMOKE_WIRE_BITS].to_vec();
        point.extend(same_x_smoke_owner_bits(*owner));
        point
    }).collect();
    let values: Vec<Fr> = points.iter().map(|point| source.evaluate(point).expect("global owner MLE"))
        .collect();
    assert_ne!(values[0], values[1], "toy owner MLEs 0 and 2 must differ");
    assert_ne!(values[0], values[2], "toy owner MLEs 0 and 3 must differ");
    assert_ne!(values[1], values[2], "toy owner MLEs 2 and 3 must differ");
    let t0 = claim.point[3];
    let t1 = claim.point[4];
    let selector = (Fr::one() - t0) * (Fr::one() - t1) * values[0]
        + t0 * (Fr::one() - t1) * values[1]
        + (Fr::one() - t0) * t1 * values[2];
    assert_eq!(selector, claim.value, "selector-weighted global claims must equal GKR InputClaim");
    for (boolean_t0, boolean_t1) in [(0u64, 0u64), (1, 0), (0, 1), (1, 1)] {
        let b0 = Fr::from(boolean_t0);
        let b1 = Fr::from(boolean_t1);
        let boolean_selector = (Fr::one() - b0) * (Fr::one() - b1) * values[0]
            + b0 * (Fr::one() - b1) * values[1]
            + (Fr::one() - b0) * b1 * values[2];
        assert_ne!(boolean_selector, claim.value, "Boolean-only owner selector must fail this non-Boolean claim");
    }
    let mut claims: [Claim; 7] = std::array::from_fn(|i| {
        let index = match i { 0 => 0, 1 => 1, 2 => 2, 3 => 0, 4 => 1, 5 => 2, _ => 0 };
        Claim { point: points[index].clone(), value: values[index] }
    });
    // Keep this explicit so future changes to the duplicate schedule cannot
    // accidentally turn the four public duplicate claims into fresh queries.
    for (duplicate, primary) in [(3usize, 0usize), (4, 1), (5, 2), (6, 0)] {
        claims[duplicate] = claims[primary].clone();
    }
    claims
}

fn same_x_smoke_statement(
    source: &PackedFile,
    claim: &InputClaim,
    descriptor: &[u8],
    commitment: ArkGT,
    setup_id: [u8; 32],
) -> Statement {
    Statement {
        log_n: SAME_X_SMOKE_LOG_N,
        setup_id,
        commitment,
        corpus_id: Some(same_x_smoke_corpus_id(descriptor)),
        claims: same_x_smoke_expected_claims(source, claim),
    }
}

fn same_x_smoke_check_public_claims(statement: &Statement, claim: &InputClaim) -> Result<(), String> {
    if claim.point.len() != SAME_X_SMOKE_LOG_N || statement.claims.iter().any(|c| c.point.len() != SAME_X_SMOKE_LOG_N) {
        return Err("same-X GKR/public claim dimension rejected".into());
    }
    let t0 = claim.point[SAME_X_SMOKE_WIRE_BITS];
    let t1 = claim.point[SAME_X_SMOKE_WIRE_BITS + 1];
    if t0.is_zero() || t0.is_one() || t1.is_zero() || t1.is_one() {
        return Err("same-X selector coordinates must be non-Boolean".into());
    }
    let expected_points: Vec<Vec<Fr>> = SAME_X_SMOKE_OWNER_IDS.iter().map(|owner| {
        let mut point = claim.point[..SAME_X_SMOKE_WIRE_BITS].to_vec();
        point.extend(same_x_smoke_owner_bits(*owner));
        point
    }).collect();
    for index in 0..3 {
        if statement.claims[index].point != expected_points[index] {
            return Err(format!("same-X projected point {index} differs from GKR InputClaim"));
        }
    }
    for (duplicate, primary) in [(3usize, 0usize), (4, 1), (5, 2), (6, 0)] {
        if statement.claims[duplicate] != statement.claims[primary] {
            return Err(format!("same-X deterministic duplicate {duplicate} differs"));
        }
    }
    let values = [statement.claims[0].value, statement.claims[1].value, statement.claims[2].value];
    if values[0] == values[1] || values[0] == values[2] || values[1] == values[2] {
        return Err("same-X toy owner values must be pairwise distinct".into());
    }
    let selector = (Fr::one() - t0) * (Fr::one() - t1) * values[0]
        + t0 * (Fr::one() - t1) * values[1]
        + (Fr::one() - t0) * t1 * values[2];
    if selector != claim.value { return Err("same-X public-value selector equality rejected".into()); }
    for (boolean_t0, boolean_t1) in [(0u64, 0u64), (1, 0), (0, 1), (1, 1)] {
        let b0 = Fr::from(boolean_t0);
        let b1 = Fr::from(boolean_t1);
        let boolean_selector = (Fr::one() - b0) * (Fr::one() - b1) * values[0]
            + b0 * (Fr::one() - b1) * values[1]
            + (Fr::one() - b0) * b1 * values[2];
        if boolean_selector == claim.value { return Err("same-X Boolean-only selector unexpectedly matches".into()); }
    }
    Ok(())
}

fn same_x_smoke_statement_codec_len() -> usize {
    8 + 1 + 8 + 32 + 384 + 1 + 32 + 8 + 7 * (SAME_X_SMOKE_LOG_N + 1) * 32
}

fn same_x_smoke_encode_statement(statement: &Statement) -> Result<Vec<u8>, String> {
    if statement.log_n != SAME_X_SMOKE_LOG_N
        || statement.corpus_id.is_none()
        || statement.claims.iter().any(|claim| claim.point.len() != SAME_X_SMOKE_LOG_N)
    {
        return Err("same-X public statement dimensions rejected".into());
    }
    let commitment = pcs::encode_commitment(&statement.commitment)?;
    if commitment.len() != 384 { return Err("same-X commitment codec length rejected".into()); }
    let mut out = Vec::with_capacity(same_x_smoke_statement_codec_len());
    out.extend_from_slice(SAME_X_SMOKE_STATEMENT_MAGIC);
    out.push(1);
    same_x_smoke_u64(&mut out, statement.log_n);
    out.extend_from_slice(&statement.setup_id);
    out.extend_from_slice(&commitment);
    out.push(1);
    out.extend_from_slice(&statement.corpus_id.expect("checked public corpus ID"));
    same_x_smoke_u64(&mut out, statement.claims.len());
    for claim in &statement.claims {
        for scalar in claim.point.iter().chain(std::iter::once(&claim.value)) {
            let mut encoded = [0u8; 32];
            scalar.serialize_compressed(&mut encoded[..]).map_err(|e| e.to_string())?;
            out.extend_from_slice(&encoded);
        }
    }
    if out.len() > SAME_X_SMOKE_STATEMENT_LIMIT { return Err("same-X public statement exceeds byte cap".into()); }
    Ok(out)
}

fn same_x_smoke_decode_statement(bytes: &[u8]) -> Result<Statement, String> {
    if bytes.len() > SAME_X_SMOKE_STATEMENT_LIMIT || bytes.len() != same_x_smoke_statement_codec_len() {
        return Err("same-X public statement extent rejected".into());
    }
    let mut cursor = 0usize;
    let mut take = |count: usize| -> Result<&[u8], String> {
        let end = cursor.checked_add(count).ok_or("same-X statement offset overflow")?;
        let slice = bytes.get(cursor..end).ok_or("same-X public statement truncated")?;
        cursor = end;
        Ok(slice)
    };
    if take(8)? != SAME_X_SMOKE_STATEMENT_MAGIC { return Err("same-X statement magic rejected".into()); }
    if take(1)? != [1] { return Err("same-X statement version rejected".into()); }
    let log_n = usize::try_from(u64::from_le_bytes(take(8)?.try_into().unwrap()))
        .map_err(|_| "same-X statement log_n overflow")?;
    if log_n != SAME_X_SMOKE_LOG_N { return Err("same-X statement log_n rejected".into()); }
    let mut setup_id = [0u8; 32]; setup_id.copy_from_slice(take(32)?);
    let commitment_bytes = take(384)?;
    let commitment = pcs::decode_commitment(commitment_bytes)?;
    if pcs::encode_commitment(&commitment)? != commitment_bytes {
        return Err("same-X statement commitment encoding is noncanonical".into());
    }
    if take(1)? != [1] { return Err("same-X statement corpus marker rejected".into()); }
    let mut corpus_id = [0u8; 32]; corpus_id.copy_from_slice(take(32)?);
    if u64::from_le_bytes(take(8)?.try_into().unwrap()) != 7 {
        return Err("same-X public statement claim count rejected".into());
    }
    let mut claims = Vec::with_capacity(7);
    for _ in 0..7 {
        let mut point = Vec::with_capacity(log_n);
        for _ in 0..log_n {
            point.push(Fr::deserialize_compressed(take(32)?).map_err(|e| format!("same-X statement point scalar: {e}"))?);
        }
        let value = Fr::deserialize_compressed(take(32)?).map_err(|e| format!("same-X statement value scalar: {e}"))?;
        claims.push(Claim { point, value });
    }
    if cursor != bytes.len() { return Err("same-X public statement trailing bytes rejected".into()); }
    let claims: [Claim; 7] = claims.try_into().map_err(|_| "same-X public statement claim array rejected")?;
    let statement = Statement { log_n, setup_id, commitment, corpus_id: Some(corpus_id), claims };
    if same_x_smoke_encode_statement(&statement)? != bytes {
        return Err("same-X public statement encoding is noncanonical".into());
    }
    Ok(statement)
}

fn same_x_smoke_bind_gkr(
    transcript: &mut Transcript,
    descriptor: &[u8],
    circuit: &sparse::Circuit,
    commitment: ArkGT,
    setup_id: [u8; 32],
) {
    transcript.append_bytes(b"same-x-gkr-profile", SAME_X_SMOKE_GKR_DOMAIN);
    transcript.append_bytes(b"same-x-descriptor", descriptor);
    transcript.append_bytes(b"same-x-commitment", &pcs::encode_commitment(&commitment).expect("canonical commitment"));
    transcript.append_bytes(b"same-x-setup-id", &setup_id);
    sparse::bind(circuit, 0, transcript);
}

fn same_x_smoke_verify(
    key: &crate::verifier_key::AdmittedVerifierKey,
    descriptor: &[u8],
    circuit: &sparse::Circuit,
    statement: &Statement,
    opening: &Proof,
    gkr_bytes: &[u8],
) -> Result<(), String> {
    same_x_smoke_verify_with_gkr_binding(
        key, descriptor, circuit, statement, opening, gkr_bytes,
        statement.commitment, statement.setup_id,
    )
}

fn same_x_smoke_verify_with_gkr_binding(
    key: &crate::verifier_key::AdmittedVerifierKey,
    descriptor: &[u8],
    circuit: &sparse::Circuit,
    statement: &Statement,
    opening: &Proof,
    gkr_bytes: &[u8],
    gkr_bound_commitment: ArkGT,
    gkr_bound_setup_id: [u8; 32],
) -> Result<(), String> {
    if statement.log_n != SAME_X_SMOKE_LOG_N
        || statement.corpus_id != Some(same_x_smoke_corpus_id(descriptor)) {
        return Err("same-X descriptor/corpus binding rejected".into());
    }
    let shape = sparse::validate(circuit, 0).map_err(|e| e.to_string())?;
    let gkr_proof = sparse::decode_proof(circuit, 0, gkr_bytes)?;
    if gkr::encode_proof(&gkr_proof)? != gkr_bytes { return Err("same-X GKR codec is not canonical".into()); }
    let mut gkr_transcript = Transcript::new(SAME_X_SMOKE_GKR_DOMAIN);
    let input_claim = gkr::verify_with_wiring(
        &[shape.input_bits], shape.row_count, &gkr_proof, &mut gkr_transcript,
        |transcript| same_x_smoke_bind_gkr(transcript, descriptor, circuit, gkr_bound_commitment, gkr_bound_setup_id),
        |layer, r, u, v| if layer == 0 { sparse::wiring(circuit, &shape, r, u, v) }
            else { Err(gkr::GkrError::PointDimension) },
    ).map_err(|e| e.to_string())?;
    if statement.log_n != SAME_X_SMOKE_LOG_N
        || statement.corpus_id != Some(same_x_smoke_corpus_id(descriptor)) {
        return Err("same-X descriptor/corpus binding rejected".into());
    }
    same_x_smoke_check_public_claims(statement, &input_claim)?;
    verify_admitted(statement, key, opening).map(|_| ())
}

fn same_x_smoke_make_statement(
    source: &PackedFile,
    descriptor: &[u8],
    circuit: &sparse::Circuit,
    setup: &Setup,
    committed: &PackedCommitted,
) -> (Vec<u8>, InputClaim, Statement) {
    let local = same_x_smoke_local_input(source);
    let mut transcript = Transcript::new(SAME_X_SMOKE_GKR_DOMAIN);
    let (proof, input_claim) = sparse::prove_with_binding(circuit, &local, 0, &mut transcript,
        |transcript| same_x_smoke_bind_gkr(transcript, descriptor, circuit, committed.commitment, setup.id))
        .expect("descriptor-bound toy sparse GKR");
    let bytes = gkr::encode_proof(&proof).expect("canonical toy GKR encoding");
    let decoded = sparse::decode_proof(circuit, 0, &bytes).expect("toy GKR decode");
    assert_eq!(gkr::encode_proof(&decoded).expect("canonical GKR re-encoding"), bytes);
    let statement = same_x_smoke_statement(source, &input_claim, descriptor, committed.commitment, setup.id);
    (bytes, input_claim, statement)
}

#[test]
#[ignore = "small same-X producer; run before log31 and in a separate process from its receiver"]
fn same_x_composition_smoke_producer() {
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    let dir = same_x_smoke_dir();
    for name in SAME_X_SMOKE_ARTIFACTS { assert!(!dir.join(name).exists(), "fresh smoke output: {name}"); }
    let descriptor_and_circuit = same_x_smoke_circuit(true);
    let (descriptor, circuit) = descriptor_and_circuit;
    let source_bytes = same_x_smoke_source_bytes();
    assert_eq!(source_bytes.len(), 4);
    assert!(!dir.join("same-x-smoke-x.bits").exists(), "producer-private X path must be fresh");
    let mut writer = packed::PackedFileWriter::create_new(dir.join("same-x-smoke-x.bits"), SAME_X_SMOKE_LOG_N)
        .expect("create tiny same-X packed source");
    writer.write_bytes(&source_bytes).expect("write tiny same-X source");
    let source = writer.finish().expect("sync and reopen tiny same-X source");
    let setup = pcs::generate_setup(SAME_X_SMOKE_LOG_N).expect("toy same-X setup");
    let committed = packed::commit(&source, &setup).expect("commit one toy X");
    let (gkr_bytes, _claim, statement) = same_x_smoke_make_statement(&source, &descriptor, &circuit, &setup, &committed);
    let mut opening_transcript = Transcript::new(DOMAIN);
    let frontend = prove_frontend_on_mode(&source, &statement, &mut opening_transcript, None, ProjectionMode::Fused, None)
        .expect("seven-claim fused opening frontend over same X");
    let pcs_proof = packed::open(&committed, &source, &frontend.point, &setup, &mut opening_transcript)
        .expect("open same toy X at the seven-claim reduction point");
    let proof = Proof { rounds: frontend.rounds, terminal: frontend.terminal, pcs: pcs_proof };
    let opening_bytes = encode_proof(&proof, SAME_X_SMOKE_LOG_N).expect("canonical opening batch codec");
    let decoded = decode_proof(&opening_bytes, SAME_X_SMOKE_LOG_N).expect("opening batch decode");
    assert_eq!(encode_proof(&decoded, SAME_X_SMOKE_LOG_N).expect("canonical opening re-encoding"), opening_bytes);
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).expect("canonical toy commitment");
    let statement_bytes = same_x_smoke_encode_statement(&statement).expect("canonical public same-X statement");
    let decoded_statement = same_x_smoke_decode_statement(&statement_bytes).expect("canonical public statement decode");
    assert_eq!(same_x_smoke_encode_statement(&decoded_statement).expect("canonical statement re-encoding"), statement_bytes);
    let key_bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).expect("canonical toy verifier key");
    same_x_smoke_write(&dir, SAME_X_SMOKE_ARTIFACTS[0], &statement_bytes);
    same_x_smoke_write(&dir, SAME_X_SMOKE_ARTIFACTS[1], &commitment_bytes);
    same_x_smoke_write(&dir, SAME_X_SMOKE_ARTIFACTS[2], &key_bytes);
    same_x_smoke_write(&dir, SAME_X_SMOKE_ARTIFACTS[3], &gkr_bytes);
    same_x_smoke_write(&dir, SAME_X_SMOKE_ARTIFACTS[4], &opening_bytes);
    println!("SAME_X_SMOKE_PRODUCER_PASS log_n={} source_bytes={} statement_bytes={} gkr_bytes={} opening_bytes={} descriptor_bytes={} corpus_id={}",
        SAME_X_SMOKE_LOG_N, source_bytes.len(), statement_bytes.len(), gkr_bytes.len(), opening_bytes.len(), descriptor.len(), hex(&same_x_smoke_corpus_id(&descriptor)));
}

#[test]
#[ignore = "fresh-process same-X composition receiver with one-sided mutants"]
fn same_x_composition_smoke_fresh_receiver() {
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    use dory_pcs::primitives::arithmetic::Group;
    let dir = same_x_smoke_dir();
    assert!(!dir.join("same-x-smoke-x.bits").exists(), "fresh receiver directory must not contain X");
    let (descriptor, circuit) = same_x_smoke_circuit(true);
    let setup = pcs::generate_setup(SAME_X_SMOKE_LOG_N).expect("fresh reconstruct toy setup");
    let statement_bytes = same_x_smoke_read(&dir, SAME_X_SMOKE_ARTIFACTS[0], SAME_X_SMOKE_STATEMENT_LIMIT);
    let statement = same_x_smoke_decode_statement(&statement_bytes).expect("fresh canonical public statement decode");
    assert_eq!(same_x_smoke_encode_statement(&statement).expect("fresh canonical statement re-encoding"), statement_bytes);
    let claims_at = 8 + 1 + 8 + 32 + 384 + 1 + 32 + 8;
    let mut noncanonical = statement_bytes.clone();
    noncanonical[claims_at..claims_at + 32].fill(0xff);
    assert!(same_x_smoke_decode_statement(&noncanonical).is_err(), "noncanonical statement scalar must reject");
    assert!(same_x_smoke_decode_statement(&statement_bytes[..statement_bytes.len() - 1]).is_err(), "truncated statement must reject");
    let mut trailing = statement_bytes.clone(); trailing.push(0);
    assert!(same_x_smoke_decode_statement(&trailing).is_err(), "extra statement byte must reject");
    assert_eq!(statement.setup_id, setup.id, "independent deterministic toy setup ID pin");
    let commitment_bytes = same_x_smoke_read(&dir, SAME_X_SMOKE_ARTIFACTS[1], 4096);
    let commitment = pcs::decode_commitment(&commitment_bytes).expect("decode same-X commitment");
    assert_eq!(pcs::encode_commitment(&commitment).expect("canonical commitment re-encoding"), commitment_bytes);
    assert_eq!(commitment, statement.commitment, "statement commitment matches separately staged canonical C");
    let key_bytes = same_x_smoke_read(&dir, SAME_X_SMOKE_ARTIFACTS[2], 1 << 20);
    let generated_key = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).expect("fresh verifier-key encoding");
    assert_eq!(generated_key, key_bytes, "fresh key bytes must match producer setup");
    let key = crate::verifier_key::admit_generated_test_key(SAME_X_SMOKE_LOG_N, &key_bytes, setup.id)
        .expect("admit test-only generated verifier key");
    let gkr_bytes = same_x_smoke_read(&dir, SAME_X_SMOKE_ARTIFACTS[3], 1 << 20);
    let opening_bytes = same_x_smoke_read(&dir, SAME_X_SMOKE_ARTIFACTS[4], 1 << 20);
    let gkr_proof = sparse::decode_proof(&circuit, 0, &gkr_bytes).expect("fresh canonical GKR decode");
    assert_eq!(gkr::encode_proof(&gkr_proof).expect("fresh canonical GKR bytes"), gkr_bytes);
    let mut gkr_transcript = Transcript::new(SAME_X_SMOKE_GKR_DOMAIN);
    let shape = sparse::validate(&circuit, 0).expect("fresh sparse circuit shape");
    let input_claim = gkr::verify_with_wiring(
        &[shape.input_bits], shape.row_count, &gkr_proof, &mut gkr_transcript,
        |transcript| same_x_smoke_bind_gkr(transcript, &descriptor, &circuit, commitment, setup.id),
        |layer, r, u, v| if layer == 0 { sparse::wiring(&circuit, &shape, r, u, v) }
            else { Err(gkr::GkrError::PointDimension) },
    ).expect("fresh descriptor-bound sparse GKR verify");
    assert_eq!(statement.corpus_id, Some(same_x_smoke_corpus_id(&descriptor)));
    let opening = decode_proof(&opening_bytes, SAME_X_SMOKE_LOG_N).expect("fresh canonical opening decode");
    assert_eq!(encode_proof(&opening, SAME_X_SMOKE_LOG_N).expect("fresh canonical opening bytes"), opening_bytes);
    same_x_smoke_verify(&key, &descriptor, &circuit, &statement, &opening, &gkr_bytes)
        .expect("fresh composed same-X verification");

    let alternate_commitment = <ArkGT as Group>::identity();
    assert_ne!(pcs::encode_commitment(&alternate_commitment).unwrap(), commitment_bytes);
    assert!(same_x_smoke_verify_with_gkr_binding(&key, &descriptor, &circuit, &statement, &opening, &gkr_bytes,
        alternate_commitment, setup.id).is_err(), "GKR-only commitment mutation must reject with opening fixed");
    let mut alternate_setup = setup.id;
    alternate_setup[0] ^= 1;
    assert!(same_x_smoke_verify_with_gkr_binding(&key, &descriptor, &circuit, &statement, &opening, &gkr_bytes,
        commitment, alternate_setup).is_err(), "GKR-only setup mutation must reject with opening fixed");

    let mut changed_opening = statement.clone();
    changed_opening.commitment = alternate_commitment;
    assert!(same_x_smoke_verify_with_gkr_binding(&key, &descriptor, &circuit, &changed_opening, &opening, &gkr_bytes,
        commitment, setup.id).is_err(), "opening-only commitment mutation must reject with GKR binding fixed");
    let mut changed_opening = statement.clone();
    changed_opening.setup_id = alternate_setup;
    assert!(same_x_smoke_verify_with_gkr_binding(&key, &descriptor, &circuit, &changed_opening, &opening, &gkr_bytes,
        commitment, setup.id).is_err(), "opening-only setup mutation must reject with GKR binding fixed");

    let mut changed_descriptor = descriptor.clone();
    changed_descriptor[0] ^= 1;
    let mut changed = statement.clone();
    changed.corpus_id = Some(same_x_smoke_corpus_id(&changed_descriptor));
    assert!(same_x_smoke_verify(&key, &changed_descriptor, &circuit, &changed, &opening, &gkr_bytes)
        .is_err(), "descriptor mutation must reject at fresh GKR verification");

    let mut changed = statement.clone();
    changed.claims[0].point[0] += Fr::one();
    assert!(same_x_smoke_verify(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes)
        .is_err(), "projected point mutation must reject at the join");
    let mut changed = statement.clone();
    changed.claims[1].value += Fr::one();
    assert!(same_x_smoke_verify(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes)
        .is_err(), "projected value mutation must reject at the join");
    let mut changed = statement.clone();
    changed.claims[4].point[0] += Fr::one();
    assert!(same_x_smoke_verify(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes)
        .is_err(), "one deterministic duplicate mutation must reject");

    let (changed_pin_descriptor, changed_pin_circuit) = same_x_smoke_circuit(false);
    let mut changed = statement.clone();
    changed.corpus_id = Some(same_x_smoke_corpus_id(&changed_pin_descriptor));
    assert!(same_x_smoke_verify(&key, &changed_pin_descriptor, &changed_pin_circuit, &changed,
        &opening, &gkr_bytes).is_err(), "public pin mutation must reject in the fresh verifier");
    println!("SAME_X_SMOKE_FRESH_RECEIVER_PASS mutants=9 gkr_domain={} opening_domain={} corpus_domain={}",
        String::from_utf8_lossy(SAME_X_SMOKE_GKR_DOMAIN), String::from_utf8_lossy(DOMAIN),
        String::from_utf8_lossy(SAME_X_SMOKE_CORPUS_DOMAIN));
}

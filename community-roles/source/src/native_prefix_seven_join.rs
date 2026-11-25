//! Fixed-fixture, test-only composition of seven independently verified native roles.
//! The byte consumer has no witness, source, setup or caller-claimed point input.
use super::*;
use ark_serialize::CanonicalSerialize;
use blake2::{digest::consts::U32, Blake2b, Digest};
use dory_pcs::backends::arkworks::{ArkG1, ArkG2, ArkworksVerifierSetup};
use serde_json::{json, Value};
use std::{fs::{File, OpenOptions}, io::{Read, Seek, SeekFrom, Write}, mem::{size_of, size_of_val},
    path::{Path, PathBuf}};
use std::os::windows::{fs::{OpenOptionsExt, MetadataExt}, io::AsRawHandle};
use crate::{gkr, native_prefix_auth_plan::{Candidate, NativePrefixAuthPlan,
    NativeRole0DiagnosticContext, Selection, role0_sha256}, native_role4_join,
    verifier_key::AdmittedVerifierKey, work_tree_history_plan::WorkTreeHistoryPlan};

const PACKAGE_CAP: usize = 256*1024;
const REPORT_CAP: usize = 16384;
const META_CAP: usize = 8*1024*1024;
const PRODUCER_CAP: usize = 512*1024*1024;
const EXTENTS: [usize;7] = [7264,7264,7264,5696,7264,7264,7264];
const MEMBERS: [&str;10] = ["verifier-key.bin","commitment.bin","role0.gkr","role1.gkr",
    "role2.gkr","role3.gkr","role4.gkr","role5.gkr","role6.gkr","common-opening.bin"];
const KEY_SHA: &str = "D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2";
const C_SHA: &str = "2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90";
const SETUP: &str = "1AE7BADC1E529C7A5CDA709AD1B418AF6AE2EFB6B7B4D909816D091C3260A51B";
const CORPUS: &str = "725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";
const ROOT: &str = "DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913";
const TOTAL: &str = "000000000000000000000000000000000000000000564F0B9B000000";
const TIP: &str = "CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC";
const CONTINUATION: &[u8] = b"native-seven-distinct-join-continuation-v1";

fn need(ok:bool,error:&str)->Result<(),String>{if ok{Ok(())}else{Err(error.into())}}
fn plus(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("seven join capacity overflow".into())}
fn cap<T>(v:&Vec<T>)->Result<usize,String>{v.capacity().checked_mul(size_of::<T>()).ok_or("seven join vector capacity overflow".into())}
fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02X}")).collect()}
fn fixed<const N:usize>(text:&str)->Result<[u8;N],String>{
    need(text.len()==2*N&&text.bytes().all(|b|b.is_ascii_digit()||(b'A'..=b'F').contains(&b)),"seven join fixed canonical hex")?;
    let mut out=[0;N];for (i,b) in out.iter_mut().enumerate(){*b=u8::from_str_radix(&text[2*i..2*i+2],16).map_err(|e|e.to_string())?;}Ok(out)
}
fn scalar_hex(value:&Fr)->Result<String,String>{let mut b=[0;32];value.serialize_compressed(&mut b[..]).map_err(|e|e.to_string())?;Ok(hex(&b))}
fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
fn candidate()->Result<Candidate,String>{Ok(Candidate{n:3073,root:fixed(ROOT)?,total:fixed(TOTAL)?,tip:fixed(TIP)?,tip_time:1562018269889})}

struct Packet<'a>{role:usize,bytes:&'a [u8]}
fn roster(packets:&[Packet<'_>])->Result<(),String>{
    need(packets.len()==7,"seven join exact roster count")?;
    for (role,p) in packets.iter().enumerate(){
        need(p.role==role,"seven join ordered role identity")?;
        need(p.bytes.len()==EXTENTS[role],"seven join exact role packet extent")?;
    }Ok(())
}
fn admit_global(key:&[u8],commitment:&[u8])->Result<AdmittedVerifierKey,String>{
    // Exact historical C is fixed independently before any retained role2 data.
    let admitted=NativeRole0DiagnosticContext::admit(key,commitment)?;
    need(admitted.setup_id_for_report()==fixed(SETUP)?,"seven join expected setup")?;
    crate::verifier_key::admit_generated_test_key(32,key,fixed(SETUP)?)
}
struct Derived{statement:Statement,role_counters:[[u64;3];7],role_continuations:[String;7],
    packet_sha256:[String;7],prefix_counters:[[u64;3];7],prefix_continuations:[String;7],timing:Value}
fn derived(key:&[u8],commitment:&[u8],packets:&[Packet<'_>],controls:bool)->Result<Derived,String>{
    let admission_timer=Instant::now();
    let _key=admit_global(key,commitment)?;roster(packets)?;
    let admission_ns=admission_timer.elapsed().as_nanos();let mut verify_ns=[0u128;7];
    let role4_context_ns;let shared_plan_ns;
    let mut claims:[Option<Claim>;7]=std::array::from_fn(|_|None);
    let mut role_counters=[[0;3];7];let mut role_continuations:[String;7]=std::array::from_fn(|_|String::new());
    let mut prefix_counters=[[0;3];7];let mut prefix_continuations:[String;7]=std::array::from_fn(|_|String::new());
    // The opaque role4 verifier constructs/drops its own parent before the shared parent exists.
    {
        let timer=Instant::now();
        let statement=native_role4_join::expected_statement_bytes(commitment)?;
        let bound=native_role4_join::start_transcript(&statement,key,commitment)?;
        let prefix=bound.producer_transcript();prefix_counters[4]=counters(&prefix);
        prefix_continuations[4]=scalar_hex(&prefix.clone().challenge_scalar(CONTINUATION))?;
        role4_context_ns=timer.elapsed().as_nanos();let timer=Instant::now();
        let verified=bound.verify_gkr(packets[4].bytes)?;
        verify_ns[4]=timer.elapsed().as_nanos();
        claims[4]=Some(Claim{point:verified.claim().point.clone(),value:verified.claim().value});
        role_counters[4]=counters(verified.transcript());
        role_continuations[4]=scalar_hex(&verified.transcript().clone().challenge_scalar(CONTINUATION))?;
    }
    {
        let timer=Instant::now();
        let c=candidate()?;let parent=WorkTreeHistoryPlan::compile(3073,12,c.root,c.total)?;
        let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),c)?;
        shared_plan_ns=timer.elapsed().as_nanos();
        for role in [0,1,2,3,5,6]{
            let timer=Instant::now();
            let (claim,t)=plan.verify_native_role_packet_for_join(role,packets[role].bytes,key,commitment)?;
            verify_ns[role]=timer.elapsed().as_nanos();
            let projected=plan.project_claim(role,&claim.point)?;
            if role==3{need(projected.len()==32&&projected[..13]==claim.point[..13]
                &&projected[13..20]==[Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::one(),Fr::one()]
                &&projected[20..]==claim.point[13..],"seven join role3 bank96 projection")?;}
            claims[role]=Some(Claim{point:projected,value:claim.value});role_counters[role]=counters(&t);
            role_continuations[role]=scalar_hex(&t.clone().challenge_scalar(CONTINUATION))?;
            let (observed,continuation)=plan.native_role_prefix_control_for_join(role,key,commitment)?;
            prefix_counters[role]=observed;prefix_continuations[role]=scalar_hex(&continuation)?;
        }
        if controls{role_controls(&plan,key,commitment,packets)?;}
    }
    need(claims.iter().all(Option::is_some),"seven join all proof-derived claims")?;
    let statement=Statement{log_n:32,setup_id:fixed(SETUP)?,commitment:pcs::decode_commitment(commitment)?,
        corpus_id:Some(fixed(CORPUS)?),claims:claims.map(|x|x.expect("seven checked claim slots"))};
    let mut packet_sha256=std::array::from_fn(|_|String::new());
    for role in 0..7{packet_sha256[role]=hex(&role0_sha256(packets[role].bytes)?);}
    Ok(Derived{statement,role_counters,role_continuations,packet_sha256,prefix_counters,prefix_continuations,
        timing:json!({"admission_ns":admission_ns,"role4_context_including_template_ns":role4_context_ns,
            "shared_template_ns":shared_plan_ns,"role_verify_ns":verify_ns,"role4_verify_includes_template":true})})
}

// Crypto faults keep role IDs, geometry and all other bytes valid. No proof hash is an admission gate.
fn role_controls(plan:&NativePrefixAuthPlan<'_>,key:&[u8],commitment:&[u8],packets:&[Packet<'_>])->Result<(),String>{
    for fault in 0..5{let mut wrong=candidate()?;match fault{0=>wrong.n-=1,1=>wrong.root[0]^=1,
        2=>wrong.total[0]^=1,3=>wrong.tip[0]^=1,_=>wrong.tip_time+=1}
        need(plan.validate_candidate(&wrong).err().is_some_and(|e|e=="candidate changed after plan binding"),"seven join candidate policy fault accepted")?;}
    let general:Vec<Fr>=(0..25).map(|i|Fr::from(i as u64+2)).collect();let projected=plan.project_claim(3,&general)?;
    need(projected[..13]==general[..13]&&projected[20..]==general[13..]
        &&projected[13..20]==[Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::one(),Fr::one()],"seven join general-field bank projection")?;
    need(plan.project_claim(3,&general[..24]).is_err(),"seven join short bank projection accepted")?;
    for role in [0,1,2,3,5,6]{
        let dimension=if role==3{25}else{32};
        let original=gkr::decode_dimensions(&[dimension],packets[role].bytes)?;
        need(gkr::encode_proof(&original)?==packets[role].bytes,"seven join original GKR codec")?;
        let mut bad=original;bad.layers[0].rounds[0][0]+=Fr::one();
        let bytes=gkr::encode_proof(&bad)?;
        need(plan.verify_native_role_packet_for_join(role,&bytes,key,commitment).err().as_deref()==Some("GKR error: SumcheckIdentity"),
            "seven join canonical GKR polynomial fault did not reach SumcheckIdentity")?;
        let mut noncanonical=packets[role].bytes.to_vec();noncanonical[..32].fill(255);
        need(gkr::decode_dimensions(&[dimension],&noncanonical).is_err(),"seven join noncanonical GKR scalar accepted")?;
        need(gkr::decode_dimensions(&[dimension],&packets[role].bytes[..EXTENTS[role]-1]).is_err(),"seven join truncated GKR accepted")?;
        let mut trailing=packets[role].bytes.to_vec();trailing.push(0);
        need(gkr::decode_dimensions(&[dimension],&trailing).is_err(),"seven join trailing GKR accepted")?;
    }
    for (role,other) in [(0,1),(1,0),(2,5),(5,6),(6,2)]{
        need(plan.verify_native_role_packet_for_join(role,packets[other].bytes,key,commitment).is_err(),"seven join same-width cross-role substitution accepted")?;
    }
    Ok(())
}
struct Verified{derived:Derived,transcript:Transcript}
fn verify_common(derived:&Derived,key:&AdmittedVerifierKey,bytes:&[u8])->Result<Transcript,String>{
    need(bytes.len()==45501,"seven join common packet extent")?;
    let proof=decode_proof(bytes,32)?;need(encode_proof(&proof,32)?==bytes,"seven join common canonical codec")?;
    verify_admitted(&derived.statement,key,&proof)
}
fn consume(key:&[u8],commitment:&[u8],packets:&[Packet<'_>],common:&[u8])->Result<Verified,String>{
    let admitted=admit_global(key,commitment)?;
    let derived=derived(key,commitment,packets,false)?;
    let transcript=verify_common(&derived,&admitted,common)?;Ok(Verified{derived,transcript})
}

// Locked, bounded files are transport only. The consumer above never consults them.
#[repr(C)]
#[derive(Default,Debug,PartialEq,Eq)]
struct Identity{attributes:u32,created:[u32;2],accessed:[u32;2],written:[u32;2],volume:u32,
    size_high:u32,size_low:u32,links:u32,index_high:u32,index_low:u32}
fn identity(file:&File)->Result<Identity,String>{
    #[link(name="kernel32")] extern "system"{fn GetFileInformationByHandle(h:*mut std::ffi::c_void,p:*mut Identity)->i32;}
    let mut id=Identity::default();
    // ABI matches BY_HANDLE_FILE_INFORMATION; the borrowed File remains live.
    if unsafe{GetFileInformationByHandle(file.as_raw_handle(),&mut id)}==0{return Err(std::io::Error::last_os_error().to_string());}
    need(id.attributes&0x410==0&&id.links==1,"seven join regular single-link file")?;id.accessed=[0;2];Ok(id)
}
fn path_ok(path:&Path)->Result<(),String>{need(path.is_absolute()&&path.as_os_str().len()<=1024,"seven join bounded absolute path")}
struct Held{path:PathBuf,file:File,id:Identity,bytes:Vec<u8>,sha:String}
impl Held{
    fn open(path:PathBuf,length:usize,read:bool)->Result<Self,String>{
        path_ok(&path)?;let md=std::fs::symlink_metadata(&path).map_err(|e|e.to_string())?;
        need(md.is_file()&&md.file_attributes()&0x400==0&&md.len()==length as u64,"seven join input type/extent")?;
        let file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|e|e.to_string())?;
        let id=identity(&file)?;need(((u64::from(id.size_high)<<32)|u64::from(id.size_low))==length as u64,"seven join held extent")?;
        let mut bytes=Vec::new();let mut sha=String::new();
        if read{need(length<=PACKAGE_CAP,"seven join bounded byte input")?;bytes.try_reserve_exact(length).map_err(|e|e.to_string())?;
            file.try_clone().map_err(|e|e.to_string())?.take(length as u64+1).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
            need(bytes.len()==length,"seven join exact held read")?;sha=hex(&role0_sha256(&bytes)?);}
        let out=Self{path,file,id,bytes,sha};out.check()?;Ok(out)
    }
    fn env(name:&str,length:usize,read:bool)->Result<Self,String>{Self::open(PathBuf::from(std::env::var_os(name).ok_or_else(||format!("{name} absent"))?),length,read)}
    fn check(&self)->Result<(),String>{need(identity(&self.file)?==self.id,"seven join held identity changed")?;
        let reopened=OpenOptions::new().read(true).share_mode(1).open(&self.path).map_err(|e|e.to_string())?;
        need(identity(&reopened)?==self.id,"seven join path identity changed")}
    fn check_bytes(&self)->Result<(),String>{self.check()?;let mut reader=self.file.try_clone().map_err(|e|e.to_string())?;
        reader.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;let mut bytes=Vec::new();bytes.try_reserve_exact(self.bytes.len()).map_err(|e|e.to_string())?;
        reader.take(self.bytes.len() as u64+1).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
        need(bytes==self.bytes&&hex(&role0_sha256(&bytes)?)==self.sha,"seven join input bytes changed")}
}
fn packet_views(held:&[Held])->Vec<Packet<'_>>{(0..7).map(|role|Packet{role,bytes:&held[role+2].bytes}).collect()}
fn read_roster()->Result<Vec<Held>,String>{
    let mut held=Vec::with_capacity(9);held.push(Held::env("NIPOPOW_ROLE4_KEY_PATH",33264,true)?);
    held.push(Held::env("NIPOPOW_NATIVE_ROLE0_COMMITMENT_PATH",384,true)?);
    let _=admit_global(&held[0].bytes,&held[1].bytes)?;
    for role in 0..7{held.push(Held::env(&format!("NIPOPOW_SEVEN_ROLE{role}_PROOF_PATH"),EXTENTS[role],true)?);}
    Ok(held)
}
fn extent(name:&str)->Result<usize,String>{
    MEMBERS.iter().position(|x|*x==name).map(|i|match i{0=>33264,1=>384,9=>45501,_=>EXTENTS[i-2]}).ok_or("seven join unknown package member".into())
}
fn directory(path:&Path)->Result<(),String>{path_ok(path)?;let md=std::fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    need(md.is_dir()&&md.file_attributes()&0x400==0,"seven join regular artifact directory")}
fn member_roster(names:&[String])->Result<(),String>{
    need(names.len()==10,"seven join exact package member count")?;
    let mut total=0;for name in names{total=plus(total,extent(name)?)?;}
    need(MEMBERS.iter().all(|name|names.iter().filter(|x|x.as_str()==*name).count()==1)
        &&total==128429&&total<=PACKAGE_CAP,"seven join exact bounded package")
}
fn directory_roster(dir:&Path)->Result<(),String>{directory(dir)?;
    let mut names=Vec::with_capacity(10);let mut total=0usize;
    for entry in std::fs::read_dir(&dir).map_err(|e|e.to_string())?{let entry=entry.map_err(|e|e.to_string())?;
        let name=entry.file_name().into_string().map_err(|_|"seven join non-UTF8 member")?;
        need(names.len()<10,"seven join extra package member")?;total=plus(total,extent(&name)?)?;names.push(name);}
    need(total<=PACKAGE_CAP,"seven join directory package cap")?;member_roster(&names)
}
fn read_package()->Result<Vec<Held>,String>{
    let dir=PathBuf::from(std::env::var_os("NIPOPOW_SEVEN_JOIN_PACKAGE_DIR").ok_or("seven join package env absent")?);directory(&dir)?;
    let mut held=Vec::with_capacity(10);held.push(Held::open(dir.join(MEMBERS[0]),33264,true)?);
    held.push(Held::open(dir.join(MEMBERS[1]),384,true)?);let _=admit_global(&held[0].bytes,&held[1].bytes)?;
    directory_roster(&dir)?;
    for name in &MEMBERS[2..]{held.push(Held::open(dir.join(name),extent(name)?,true)?);}Ok(held)
}
fn source_check(held:&Held)->Result<(),String>{
    held.check()?;let mut reader=held.file.try_clone().map_err(|e|e.to_string())?;reader.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;
    let mut digest=Blake2b::<U32>::new();let mut scratch=vec![0;1<<20];
    for _ in 0..512{reader.read_exact(&mut scratch).map_err(|e|e.to_string())?;digest.update(&scratch);}
    need(hex(&digest.finalize())==CORPUS,"seven join held witness digest")?;held.check()
}
struct Limited(Vec<u8>);
impl Write for Limited{fn write(&mut self,bytes:&[u8])->std::io::Result<usize>{
    if bytes.len()>REPORT_CAP.saturating_sub(self.0.len()){return Err(std::io::Error::other("seven join report cap"));}
    self.0.extend_from_slice(bytes);Ok(bytes.len())}fn flush(&mut self)->std::io::Result<()>{Ok(())}}
fn report(value:&Value)->Result<(),String>{let mut out=Limited(Vec::with_capacity(REPORT_CAP));
    serde_json::to_writer(&mut out,value).map_err(|e|e.to_string())?;let mut stdout=std::io::stdout().lock();
    writeln!(stdout,"\nNATIVE_SEVEN_JOIN_REPORT {}",std::str::from_utf8(&out.0).map_err(|e|e.to_string())?).map_err(|e|e.to_string())?;
    stdout.flush().map_err(|e|e.to_string())}
struct Clock{start:Instant,mode:&'static str,phase:&'static str,index:usize,limit:u128,marks:Vec<Value>}
impl Clock{
    fn new(mode:&'static str,seconds:u128)->Self{Self{start:Instant::now(),mode,phase:"start",index:0,limit:seconds*1_000_000_000,marks:Vec::with_capacity(13)}}
    fn tick(&mut self,phase:&'static str)->Result<(),String>{self.phase=phase;let elapsed=self.start.elapsed().as_nanos();need(elapsed<=self.limit,"seven join deadline")?;
        let mut stderr=std::io::stderr().lock();writeln!(stderr,"NATIVE_SEVEN_JOIN_STAGE {} {} {} {}",self.mode,self.index,phase,elapsed).map_err(|e|e.to_string())?;
        stderr.flush().map_err(|e|e.to_string())?;self.marks.push(json!({"index":self.index,"phase":phase,"elapsed_ns":elapsed}));self.index+=1;Ok(())}
}
fn io(value:crate::packed::PackedIoSnapshot)->Result<Value,String>{
    need(value.write_calls==0&&value.write_bytes==0&&value.sync_calls==0,"seven join packed readonly")?;
    Ok(json!({"read_calls":value.read_calls,"read_bytes":value.read_bytes,"read_ns":value.read_ns,
        "write_calls":value.write_calls,"write_bytes":value.write_bytes,"sync_calls":value.sync_calls}))
}
fn key_capacity(key:&AdmittedVerifierKey)->Result<usize,String>{let v=key.verifier();let mut n=size_of_val(v);
    for x in [&v.delta_1l,&v.delta_1r,&v.delta_2l,&v.delta_2r,&v.chi]{n=plus(n,cap(x)?)?;}Ok(n)}
fn setup_capacity(setup:&Setup)->Result<usize,String>{let mut n=size_of::<Setup>();n=plus(n,cap(&setup.prover.g1_vec)?)?;
    n=plus(n,cap(&setup.prover.g2_vec)?)?;let v=&setup.verifier;
    for x in [&v.delta_1l,&v.delta_1r,&v.delta_2l,&v.delta_2r,&v.chi]{n=plus(n,cap(x)?)?;}Ok(n)}
fn retained_capacity(held:&Vec<Held>,d:&Derived,key:&AdmittedVerifierKey)->Result<usize,String>{
    let mut n=plus(cap(held)?,size_of::<Derived>())?;
    for h in held{n=plus(n,plus(h.bytes.capacity(),h.path.capacity().checked_mul(2).ok_or("seven join path capacity")?)?)?;n=plus(n,h.sha.capacity())?;}
    for c in &d.statement.claims{n=plus(n,cap(&c.point)?)?;}
    for s in d.role_continuations.iter().chain(d.prefix_continuations.iter()).chain(d.packet_sha256.iter()){n=plus(n,s.capacity())?;}
    // Reserve4MiB for simultaneous packet/codec copies, locked-file metadata,
    // the1MiB custody scratch, bounded report/JSON/marks and serializer locals.
    n=plus(n,key_capacity(key)?)?;n=plus(n,4*1024*1024)?;need(n<=META_CAP,"seven join metadata capacity")?;Ok(n)
}
fn claims_digest(d:&Derived)->Result<String,String>{let mut bytes=Vec::with_capacity(7*33*32);
    for c in &d.statement.claims{for x in c.point.iter().chain(std::iter::once(&c.value)){x.serialize_compressed(&mut bytes).map_err(|e|e.to_string())?;}}
    Ok(hex(&role0_sha256(&bytes)?))}
fn common_controls(d:&Derived,key:&AdmittedVerifierKey,bytes:&[u8],old:&[u8],ht:ArkGT)->Result<usize,String>{
    let proof=decode_proof(bytes,32)?;let mut count=0;
    let old_proof=decode_proof(old,32)?;need(encode_proof(&old_proof,32)?==old,"seven join old opening canonical codec")?;
    need(verify_common(d,key,old).is_err(),"seven join old repeated-role1 opening accepted")?;count+=1;
    for fault in 0..6{let mut wrong=d.statement.clone();match fault{
        0=>wrong.claims[0].value+=Fr::one(),1=>wrong.claims[0].point[0]+=Fr::one(),
        2=>wrong.claims[3].point[13]+=Fr::one(),3=>wrong.claims[3].point[20]+=Fr::one(),
        4=>wrong.corpus_id=Some([0;32]),_=>wrong.setup_id[0]^=1}
        need(verify_admitted(&wrong,key,&proof).is_err(),"seven join altered derived statement accepted")?;count+=1;}
    let bad=Proof{rounds:proof.rounds.clone(),terminal:proof.terminal+Fr::one(),pcs:proof.pcs.clone()};
    need(verify_admitted(&d.statement,key,&bad).err().as_deref()==Some("opening-batch terminal relation rejected"),
        "seven join altered terminal did not reach terminal relation")?;count+=1;
    let mut pcs=proof.pcs.clone();let prior=pcs.vmv_message.c;
    pcs.vmv_message.c=if prior==<ArkGT as dory_pcs::primitives::arithmetic::Group>::identity(){ht}else{<ArkGT as dory_pcs::primitives::arithmetic::Group>::identity()};
    need(pcs.vmv_message.c!=prior,"seven join nontrivial Dory mutant")?;
    let bad=Proof{rounds:proof.rounds.clone(),terminal:proof.terminal,pcs};let encoded=encode_proof(&bad,32)?;
    let canonical=decode_proof(&encoded,32)?;need(verify_admitted(&d.statement,key,&canonical).err()
        .is_some_and(|e|e.starts_with("opening-batch final PCS rejected:")),"seven join canonical Dory mutant did not reach final PCS")?;count+=1;
    need(decode_proof(&bytes[..bytes.len()-1],32).is_err(),"seven join truncated opening accepted")?;count+=1;
    let mut trailing=bytes.to_vec();trailing.push(0);need(decode_proof(&trailing,32).is_err(),"seven join trailing opening accepted")?;count+=1;Ok(count)
}
fn output_dir()->Result<PathBuf,String>{let path=PathBuf::from(std::env::var_os("NIPOPOW_SEVEN_JOIN_OUTPUT_DIR").ok_or("seven join output env absent")?);
    path_ok(&path)?;let parent=path.parent().ok_or("seven join output parent")?;directory(parent)?;
    need(!parent.canonicalize().map_err(|e|e.to_string())?.starts_with(std::env::temp_dir().canonicalize().map_err(|e|e.to_string())?),"seven join output under TEMP")?;
    std::fs::create_dir(&path).map_err(|e|format!("seven join create_new directory: {e}"))?;Ok(path)}
fn export(dir:&Path,held:&[Held],common:&[u8])->Result<Vec<Held>,String>{
    let mut outputs=Vec::with_capacity(10);let mut total=0;
    for (i,name) in MEMBERS.iter().enumerate(){let bytes=if i==9{common}else{&held[i].bytes};
        need(bytes.len()==extent(name)?,"seven join output exact extent")?;total=plus(total,bytes.len())?;need(total<=PACKAGE_CAP,"seven join output package cap")?;
        let path=dir.join(name);let mut f=OpenOptions::new().write(true).create_new(true).share_mode(1).open(&path).map_err(|e|e.to_string())?;
        f.write_all(bytes).map_err(|e|e.to_string())?;f.sync_all().map_err(|e|e.to_string())?;drop(f);
        let out=Held::open(path,bytes.len(),true)?;need(out.bytes==bytes,"seven join output readback")?;outputs.push(out);}
    need(total==128429,"seven join exported package extent")?;directory_roster(dir)?;Ok(outputs)
}
fn owned_bound(retained:usize,setup:usize,rows:usize,row_clone:usize)->Result<usize,String>{
    let n=plus(plus(plus(plus(plus(retained,setup)?,rows)?,row_clone)?,FRONTEND_CAPACITY_LIMIT)?,96*1024*1024)?;
    need(n<=PRODUCER_CAP,"seven join simultaneous producer owned payload")?;Ok(n)
}

fn producer(clock:&mut Clock)->Result<Value,String>{
    clock.tick("start")?;clock.phase="admission";need(rayon::current_num_threads()==4,"seven join exactly four Rayon workers")?;
    let held=read_roster()?;let old=Held::env("NIPOPOW_SEVEN_JOIN_OLD_OPENING_PATH",45501,true)?;
    let witness=Held::env("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS",536870912,false)?;source_check(&witness)?;
    let source=PackedFile::open_with_limit(&witness.path,32,32)?;need(source.input_len()==1usize<<32,"seven join source geometry")?;
    let output=output_dir()?;clock.tick("admission")?;
    clock.phase="roles";let phase=Instant::now();let packets=packet_views(&held);let d=derived(&held[0].bytes,&held[1].bytes,&packets,false)?;
    let roles_ns=phase.elapsed().as_nanos();clock.tick("roles")?;
    let key=admit_global(&held[0].bytes,&held[1].bytes)?;let retained=retained_capacity(&held,&d,&key)?;
    let setup_payload=65536usize.checked_mul(plus(size_of::<ArkG1>(),size_of::<ArkG2>())?).ok_or("seven join setup preflight overflow")?;
    let row_preflight=65536usize.checked_mul(size_of::<ArkG1>()).ok_or("seven join row preflight overflow")?;
    // Fixed32 geometry bounds allocations before setup/commit. Reserve96MiB:
    // commit's conservative262144*(G1Projective+G1Affine+Fq) table bound plus
    // windows,32MiB read batch and batch row outputs is below this reservation.
    // The later product uses that same batch plus bounded evaluation vectors.
    // Vendor internals remain separately constrained by the2GiB Job, not measured.
    let preflight=owned_bound(retained,plus(setup_payload,1024*1024)?,row_preflight,row_preflight)?;
    clock.phase="setup";let phase=Instant::now();let setup=pcs::generate_setup_for_scale_diagnostic(32)?;
    need(setup.id==fixed(SETUP)?&&pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))?==held[0].bytes,"seven join regenerated key/setup")?;
    let setup_bytes=setup_capacity(&setup)?;let setup_ns=phase.elapsed().as_nanos();clock.tick("setup")?;
    clock.phase="commit";source.reset_io_metrics();let phase=Instant::now();let committed=packed::commit(&source,&setup)?;
    need(committed.rows.len()==65536&&committed.nu==16&&committed.sigma==16
        &&pcs::encode_commitment(&committed.commitment)?==held[1].bytes,"seven join regenerated commitment/rows")?;
    let row_bytes=cap(&committed.rows)?;let row_clone=committed.rows.len().checked_mul(size_of::<ArkG1>()).ok_or("seven join row clone overflow")?;
    let producer_bound=owned_bound(retained,setup_bytes,row_bytes,row_clone)?;
    need(setup_bytes<=plus(setup_payload,1024*1024)?&&row_bytes==row_preflight&&producer_bound<=preflight&&producer_bound<=PRODUCER_CAP,
        "seven join simultaneous producer owned payload")?;
    let commit_io=io(source.io_metrics_snapshot())?;let commit_ns=phase.elapsed().as_nanos();clock.tick("commit")?;
    clock.phase="frontend";source.reset_io_metrics();let phase=Instant::now();let mut sender=Transcript::new(DOMAIN);
    let mut audit=FrontendAudit::new(&d.statement,retained,false)?;
    let frontend=prove_frontend_on_mode(&source,&d.statement,&mut sender,None,ProjectionMode::Fused,Some(&mut audit))?;
    let frontend_ns=phase.elapsed().as_nanos();let frontend_io=io(source.io_metrics_snapshot())?;
    let frontend_peak=audit.stats.state_peak_capacity_bytes;let frontend_bound=audit.stats.preflight_capacity_bound_bytes;
    need(frontend.point.len()==32&&frontend.rounds.len()==32,"seven join complete rectangular frontend")?;clock.tick("frontend")?;
    clock.phase="open";source.reset_io_metrics();let phase=Instant::now();let opening=packed::open(&committed,&source,&frontend.point,&setup,&mut sender)?;
    let open_ns=phase.elapsed().as_nanos();let open_io=io(source.io_metrics_snapshot())?;clock.tick("open")?;
    clock.phase="codec";let phase=Instant::now();let proof=Proof{rounds:frontend.rounds,terminal:frontend.terminal,pcs:opening};let common=encode_proof(&proof,32)?;
    need(common.len()==45501,"seven join canonical batch extent")?;let decoded=decode_proof(&common,32)?;
    need(encode_proof(&decoded,32)?==common,"seven join canonical batch reencode")?;drop(decoded);drop(proof);
    let codec_ns=phase.elapsed().as_nanos();clock.tick("codec")?;
    let ht=setup.prover.ht;drop(committed);drop(setup);drop(audit);drop(frontend.point);
    clock.phase="verify";let phase=Instant::now();let verified=consume(&held[0].bytes,&held[1].bytes,&packets,&common)?;
    need(counters(&sender)==counters(&verified.transcript)
        &&sender.clone().challenge_scalar(CONTINUATION)==verified.transcript.clone().challenge_scalar(CONTINUATION),"seven join sender/cold consumer replay")?;
    need(verified.derived.statement.claims==d.statement.claims,"seven join fresh proof-derived claims equality")?;
    let verify_ns=phase.elapsed().as_nanos();clock.tick("verify")?;
    clock.phase="negatives";let phase=Instant::now();let negatives=common_controls(&d,&key,&common,&old.bytes,ht)?;
    let negatives_ns=phase.elapsed().as_nanos();clock.tick("negatives")?;
    clock.phase="custody";for h in &held{h.check_bytes()?;}old.check_bytes()?;source_check(&witness)?;clock.tick("custody")?;
    clock.phase="export";let outputs=export(&output,&held,&common)?;for h in &outputs{h.check_bytes()?;}directory_roster(&output)?;clock.tick("export")?;
    let digest=claims_digest(&d)?;let proof_sha=hex(&role0_sha256(&common)?);let continuation=scalar_hex(&sender.clone().challenge_scalar(CONTINUATION))?;
    clock.tick("complete")?;
    Ok(json!({"schema":"native-seven-distinct-join-v1","state":"PASS","mode":"producer","error":null,
        "scope":{"roles":[0,1,2,3,4,5,6],"input_log":32,"fixed_commitment":true,"full_history":false,"production":false,"witness_free_consumer":true},
        "inputs":{"key_sha256":KEY_SHA,"commitment_sha256":C_SHA,"setup_id":SETUP,"corpus_id":CORPUS,"gkr_sha256":d.packet_sha256},
        "claims_sha256":digest,"role_counters":d.role_counters,"role_continuations":d.role_continuations,
        "prefix_counters":d.prefix_counters,"prefix_continuations":d.prefix_continuations,
        "role_timing":d.timing,"fresh_consumer_role_timing":verified.derived.timing,
        "common":{"bytes":common.len(),"sha256":proof_sha,"rounds":32,"pcs_invoked":true,"sender_counters":counters(&sender),"receiver_counters":counters(&verified.transcript),"continuation":continuation},
        "package":{"files":10,"bytes":128429,"cap":PACKAGE_CAP,"create_new":true,"readback":true},
        "memory":{"metadata_owned_bound":retained,"metadata_aux_reservation":4194304,"setup_owned_bytes":setup_bytes,"rows_owned_bytes":row_bytes,"row_clone_payload_bound":row_clone,
            "frontend_peak_owned_bytes":frontend_peak,"frontend_preflight_bound":frontend_bound,"producer_owned_payload_bound":producer_bound,
            "producer_preflight_bound":preflight,"packed_source_reservation":100663296,
            "producer_owned_cap":PRODUCER_CAP,"template_heap_measured":false,"vendor_scratch_measured":false,"job_limit":2147483648u64},
        "io":{"admission_payload_bytes":536870912u64,"final_custody_payload_bytes":536870912u64,"commit":commit_io,"frontend":frontend_io,"open":open_io},
        "checks":{"distinct_gkr":true,"fresh_consumer":true,"codec":true,"common_negatives":negatives,"custody":true},
        "phase_ns":{"roles":roles_ns,"setup":setup_ns,"commit":commit_ns,"frontend":frontend_ns,"open":open_ns,"codec":codec_ns,"verify":verify_ns,"negatives":negatives_ns},
        "marks":clock.marks,"elapsed_ns":clock.marks.last().ok_or("seven join complete marker")?["elapsed_ns"]}))
}
fn receiver(clock:&mut Clock)->Result<Value,String>{
    clock.tick("start")?;clock.phase="admission";let held=read_package()?;clock.tick("admission")?;
    clock.phase="roles";let phase=Instant::now();let packets=packet_views(&held);let d=derived(&held[0].bytes,&held[1].bytes,&packets,false)?;
    let roles_ns=phase.elapsed().as_nanos();clock.tick("roles")?;
    clock.phase="common";let phase=Instant::now();let key=admit_global(&held[0].bytes,&held[1].bytes)?;let t=verify_common(&d,&key,&held[9].bytes)?;
    let common_ns=phase.elapsed().as_nanos();clock.tick("common")?;
    clock.phase="custody";for h in &held{h.check_bytes()?;}directory_roster(held[0].path.parent().ok_or("seven join package parent")?)?;
    let retained=retained_capacity(&held,&d,&key)?;clock.tick("custody")?;
    let digest=claims_digest(&d)?;let continuation=scalar_hex(&t.clone().challenge_scalar(CONTINUATION))?;clock.tick("complete")?;
    Ok(json!({"schema":"native-seven-distinct-join-v1","state":"PASS","mode":"receiver","error":null,
        "scope":{"roles":[0,1,2,3,4,5,6],"input_log":32,"fixed_commitment":true,"full_history":false,"production":false,"witness_free_consumer":true},
        "inputs":{"key_sha256":KEY_SHA,"commitment_sha256":C_SHA,"setup_id":SETUP,"corpus_id":CORPUS,"gkr_sha256":d.packet_sha256},
        "claims_sha256":digest,"role_counters":d.role_counters,"role_continuations":d.role_continuations,
        "prefix_counters":d.prefix_counters,"prefix_continuations":d.prefix_continuations,
        "role_timing":d.timing,
        "common":{"bytes":45501,"sha256":held[9].sha,"rounds":32,"pcs_invoked":true,"receiver_counters":counters(&t),"continuation":continuation},
        "package":{"files":10,"bytes":128429,"cap":PACKAGE_CAP,"readback":true},
        "memory":{"metadata_owned_bound":retained,"metadata_aux_reservation":4194304,"template_heap_measured":false,"vendor_scratch_measured":false,"job_limit":2147483648u64},
        "checks":{"distinct_gkr":true,"codec":true,"custody":true},"phase_ns":{"roles":roles_ns,"common":common_ns},
        "marks":clock.marks,"elapsed_ns":clock.marks.last().ok_or("seven join complete marker")?["elapsed_ns"]}))
}
fn run(mode:&'static str)->Result<(),String>{let mut clock=Clock::new(mode,if mode=="producer"{600}else{120});
    let result=if mode=="producer"{producer(&mut clock)}else{receiver(&mut clock)};
    match result{Ok(value)=>report(&value),Err(error)=>{let bounded:String=error.chars().take(512).collect();
        let _=report(&json!({"schema":"native-seven-distinct-join-v1","state":"HOLD","mode":mode,
            "phase":clock.phase,"index":clock.index,"error":bounded,"elapsed_ns":clock.start.elapsed().as_nanos()}));Err(error)}}}

#[test]
fn ordinary_boundaries(){
    // This ordinary gate intentionally requires bounded retained native packets; it is not a pure toy suite.
    let held=read_roster().unwrap();let packets=packet_views(&held);
    roster(&packets).unwrap();assert!(roster(&packets[..6]).unwrap_err().contains("count"));
    for fault in 0..4{let mut bad:Vec<Packet<'_>>=packets.iter().map(|p|Packet{role:p.role,bytes:p.bytes}).collect();
        match fault{0=>bad[6].role=5,1=>bad.swap(0,1),2=>bad[6].role=7,_=>bad.push(Packet{role:7,bytes:packets[0].bytes})}
        assert!(roster(&bad).is_err());}
    let mut key=held[0].bytes.clone();key[0]^=1;assert!(admit_global(&key,&held[1].bytes).err().unwrap().contains("verifier-key"));
    let mut commitment=held[1].bytes.clone();commitment[0]^=1;assert!(admit_global(&held[0].bytes,&commitment).is_err());
    let d=derived(&held[0].bytes,&held[1].bytes,&packets,true).unwrap();
    let statement=native_role4_join::expected_statement_bytes(&held[1].bytes).unwrap();
    let bound=native_role4_join::start_transcript(&statement,&held[0].bytes,&held[1].bytes).unwrap();
    let mut proof=gkr::decode_dimensions(&[32],packets[4].bytes).unwrap();proof.layers[0].rounds[0][0]+=Fr::one();
    assert_eq!(bound.verify_gkr(&gkr::encode_proof(&proof).unwrap()).err().as_deref(),Some("GKR error: SumcheckIdentity"));
    assert!(bound.verify_gkr(packets[0].bytes).is_err());
    for (field,value) in [("parent_root",json!("00".repeat(32))),("parent_total_work_be28",json!("00".repeat(28))),
        ("headers",json!(3072)),("slots",json!(4095)),("pcs_setup_id",json!("00".repeat(32))),
        ("native_profile",json!("other-role"))]{let mut changed:Value=serde_json::from_slice(&statement).unwrap();changed[field]=value;
        assert!(native_role4_join::start_transcript(&serde_json::to_vec(&changed).unwrap(),&held[0].bytes,&held[1].bytes).is_err());}
    for name in ["other.bin","../role0.gkr","ROLE0.GKR"]{assert!(extent(name).is_err());}
    let names:Vec<String>=MEMBERS.iter().map(|s|s.to_string()).collect();member_roster(&names).unwrap();
    assert!(member_roster(&names[..9]).is_err());
    let mut duplicate=names.clone();duplicate[9]=duplicate[0].clone();assert!(member_roster(&duplicate).is_err());
    let mut extra=names.clone();extra.push("other.bin".into());assert!(member_roster(&extra).is_err());
    assert!(owned_bound(usize::MAX,0,0,0).is_err());assert!(owned_bound(0,PRODUCER_CAP,0,0).is_err());
    for bad in [Path::new("relative"),Path::new("")]{assert!(path_ok(bad).is_err());}
    let mut limited=Limited(Vec::with_capacity(REPORT_CAP));assert!(limited.write_all(&vec![0;REPORT_CAP+1]).is_err());assert!(limited.0.is_empty());
    let old=Held::env("NIPOPOW_SEVEN_JOIN_OLD_OPENING_PATH",45501,true).unwrap();let key=admit_global(&held[0].bytes,&held[1].bytes).unwrap();
    let old_proof=decode_proof(&old.bytes,32).unwrap();assert_eq!(encode_proof(&old_proof,32).unwrap(),old.bytes);
    assert!(verify_common(&d,&key,&old.bytes).is_err());
    for h in &held{h.check_bytes().unwrap();}old.check_bytes().unwrap();
    report(&json!({"schema":"native-seven-distinct-ordinary-v1","state":"PASS","scope":"retained-seven-GKR-and-isolated-boundaries",
        "roles":[0,1,2,3,4,5,6],"claims_sha256":claims_digest(&d).unwrap(),"gkr_sha256":d.packet_sha256,
        "role_counters":d.role_counters,"role_continuations":d.role_continuations,
        "prefix_counters":d.prefix_counters,"prefix_continuations":d.prefix_continuations,"native_producer_run":false,"new_common_positive":false})).unwrap();
}
#[test]
#[ignore="one reviewed fixed-fixture seven-role common producer,600s/Job2GiB"]
fn native_distinct_producer(){run("producer").unwrap();}
#[test]
#[ignore="separate cold witness-free receiver,120s/Job2GiB"]
fn native_distinct_receiver(){run("receiver").unwrap();}

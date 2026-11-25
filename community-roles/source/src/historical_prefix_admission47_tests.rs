//! Admission/prefix diagnostic only: no GKR, PCS, setup or expanded witness.
use super::*;
use std::{fs::File,io::{Read,Seek,SeekFrom},path::PathBuf};
use std::os::windows::{fs::{MetadataExt,OpenOptionsExt},io::AsRawHandle};

const STAGES:[(&str,&str);14]=[("admission","begin"),("admission","end"),("native","begin"),("native","end"),
    ("historical","begin"),("historical","end"),("prefixes","begin"),("prefixes","end"),
    ("drop","end"),("public_bindings","begin"),("public_bindings","end"),
    ("custody","begin"),("custody","end"),("complete","end")];
const RAW_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const PACK_BLAKE:&str="725d7b1215e1185c52c1012d9294260612653acad53a02429b8eaafd0f0770c8";
const KEY_SHA:&str="D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2";
const C_SHA:&str="2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90";
const ID:&str="1AE7BADC1E529C7A5CDA709AD1B418AF6AE2EFB6B7B4D909816D091C3260A51B";
fn need(ok:bool,error:&str)->Result<(),String>{if ok{Ok(())}else{Err(error.into())}}
fn rejected(result:Result<(),String>,message:&str,activity:[u64;2])->Result<(),String>{
    need(result.err().as_deref()==Some(message),"admission47 negative attribution")?;
    need(historical47_activity()==activity,"admission47 negative FS activity")
}
fn synthetic_c()->Result<Vec<u8>,String>{
    pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero()))
}
fn policy_geometry()->Geometry{Geometry{headers:3073,slot_log:12,slots:4096,common_input:32,bank_bits:4,
    input_bits:H47_INPUTS,row_bits:H47_ROWS,height_row:18,daa_row:31,daa_row_base:1usize<<31,
    point_local_input:13,point_local_row:14}}
fn codec_controls()->Result<(),String>{
    let p=Public{headers:3073,root:[2;32],total:[3;28],tip:[4;32],tip_time:5};
    let frame=historical47_frame(&p)?;need(historical47_frame(&historical47_decode(&frame)?)?==frame,"admission47 codec golden")?;
    let activity=historical47_activity();
    for n in [0,570,572]{let mut b=frame.clone();b.resize(n,0);
        rejected(historical47_decode(&b).map(|_|()),"admission47 frame extent",activity)?;}
    for (at,error) in [(0,"admission47 frame profile"),(43,"admission47 genesis anchor"),(75,"admission47 genesis anchor"),
        (107,"admission47 frame geometry"),(115,"admission47 frame geometry"),(123,"admission47 frame geometry"),(131,"admission47 frame geometry")]{
        let mut b=frame.clone();b[at]^=1;rejected(historical47_decode(&b).map(|_|()),error,activity)?;}
    let mut at=239;
    for role in 0..7{
        for (offset,error) in [(at,"admission47 role roster"),(at+8,"admission47 role roster"),
            (at+16,"admission47 role domain"),(at+16+ROLES[role].len(),"admission47 role geometry"),
            (at+24+ROLES[role].len(),"admission47 role geometry")]{let mut b=frame.clone();b[offset]^=1;
            rejected(historical47_decode(&b).map(|_|()),error,activity)?;}
        at+=32+ROLES[role].len();
    }
    // Public fields are candidate bytes, not a retained expected-Public oracle.
    for offset in [139,171,199,231]{let mut b=frame.clone();b[offset]^=1;
        need(historical47_frame(&historical47_decode(&b)?)?==b && b!=frame,"admission47 public codec differential")?;}
    let c=synthetic_c()?;historical47_commitment(&c)?;
    for size in [0,383,385]{let mut bad=c.clone();bad.resize(size,0);
        rejected(historical47_commitment(&bad),"admission47 commitment extent",activity)?;}
    let bad=vec![255;384];rejected(historical47_commitment(&bad),"admission47 commitment decode",activity)?;
    // A canonical field encoding outside GT's subgroup fails the actual decoder.
    let finite=dory_pcs::backends::arkworks::ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>(ark_bn254::Fq12::from(2u64)));
    rejected(historical47_commitment(&pcs::encode_commitment(&finite)?),"admission47 commitment decode",activity)?;
    use ark_ff::{BigInteger,PrimeField};
    let mut noncanonical=c.clone();let modulus=ark_bn254::Fq::MODULUS.to_bytes_le();
    need(modulus.len()==32,"admission47 modulus extent")?;noncanonical[..32].copy_from_slice(&modulus);
    rejected(historical47_commitment(&noncanonical),"admission47 commitment decode",activity)?;
    // The strict decoder already reencodes: its noncanonical rejection precedes
    // our defensive second roundtrip check; no fabricated latter-branch fixture.
    let g=policy_geometry();historical47_geometry(&g)?;
    for i in 0..7{let mut bad=g.clone();bad.input_bits[i]+=1;
        rejected(historical47_geometry(&bad),"admission47 geometry",activity)?;
        let mut bad=g.clone();bad.row_bits[i]+=1;rejected(historical47_geometry(&bad),"admission47 geometry",activity)?;}
    for i in 0..6{let mut bad=g.clone();match i{0=>bad.bank_bits+=1,1=>bad.height_row+=1,2=>bad.daa_row+=1,
        3=>bad.daa_row_base+=1,4=>bad.point_local_input+=1,_=>bad.point_local_row+=1}
        rejected(historical47_geometry(&bad),"admission47 geometry",activity)?;}
    for tuple in [(3,12,4096,32),(3073,11,4096,32),(3073,12,2048,32),(3073,12,4096,31)]{
        rejected(historical47_policy(tuple.0,tuple.1,tuple.2,tuple.3),"admission47 closed policy",activity)?;}
    need(Public::native(3)?.profile().is_ok() && Public::native(4)?.profile().is_ok()
        && p.profile().is_err(),"admission47 old profile boundary")
}
fn identity_controls()->Result<(),String>{
    let p=Public{headers:5,root:[0;32],total:[0;28],tip:[0;32],tip_time:0};
    let consumer=historical41_consumer(&p)?;
    let parts=RelationParts::compile(consumer.layout_refs(),HeightBinding::HistoricalDiagnostic)?;
    historical47_refs(&consumer,parts.refs())?;let activity=historical47_activity();
    {let mut refs=parts.refs();refs.mode=HeightBinding::LegacyN3N4;
        rejected(historical47_refs(&consumer,refs),"admission47 historical mode",activity)?;}
    // One consumer plus one foreign parent, dropped before any foreign point template.
    {let foreign=WorkTreeHistoryPlan::compile(5,3,[1;32],[0;28])?;
        let mut refs=parts.refs();refs.layouts.parent=&foreign;
        rejected(historical47_refs(&consumer,refs),"admission47 parent identity",activity)?;
        {let h=HeightWork::compile_history(&foreign)?;let mut refs=parts.refs();refs.height=&h;
            rejected(historical47_refs(&consumer,refs),"admission47 height parent identity",activity)?;}
        {let d=DaaHistoryRoster::compile(&foreign)?;let mut refs=parts.refs();refs.daa=&d;
            rejected(historical47_refs(&consumer,refs),"admission47 DAA parent identity",activity)?;}}
    {let a=HeaderAdjacencyLayout::compile(5,3,[0;32],[0;32])?;let mut refs=parts.refs();refs.layouts.adjacency=&a;
        rejected(historical47_refs(&consumer,refs),"admission47 adjacency identity",activity)?;}
    {let m=HeaderMetadataOrderLayout::compile(5,3,0)?;let mut refs=parts.refs();refs.layouts.metadata=&m;
        rejected(historical47_refs(&consumer,refs),"admission47 metadata identity",activity)?;}
    {let point=point_membership::build()?;let mut refs=parts.refs();refs.layouts.points=&point;
        rejected(historical47_refs(&consumer,refs),"admission47 points identity",activity)?;
        let role=PointRole::dimensions(&point.circuit,3,16,17,23)?;let mut refs=parts.refs();refs.point_role=&role;
        rejected(historical47_refs(&consumer,refs),"admission47 point base identity",activity)?;}
    {let text=consumer.point_template.clone();let mut refs=parts.refs();refs.layouts.point_template=&text;
        rejected(historical47_refs(&consumer,refs),"admission47 fingerprint identity",activity)?;}
    let mut geometry=parts.geometry.clone();geometry.row_bits[2]+=1;let mut refs=parts.refs();refs.geometry=&geometry;
    rejected(historical47_refs(&consumer,refs),"geometry role 2 row mismatch",activity)
}

// Same Windows held/named identity ABI as native_prefix_seven_join, without a
// whole-file PACK allocation. Access time is intentionally non-authoritative.
#[repr(C)]
#[derive(Default,PartialEq,Eq)]
struct Identity{attributes:u32,created:[u32;2],accessed:[u32;2],written:[u32;2],volume:u32,
    high:u32,low:u32,links:u32,index_high:u32,index_low:u32}
fn identity(file:&File)->Result<Identity,String>{
    #[link(name="kernel32")]extern "system"{fn GetFileInformationByHandle(h:*mut std::ffi::c_void,p:*mut Identity)->i32;}
    let mut id=Identity::default();
    // Identical BY_HANDLE_FILE_INFORMATION layout; File outlives this borrowed call.
    if unsafe{GetFileInformationByHandle(file.as_raw_handle(),&mut id)}==0{return Err("admission47 file identity".into());}
    need(id.attributes&0x410==0 && id.links==1,"admission47 ordinary single-link file")?;id.accessed=[0;2];Ok(id)
}
struct Held{file:File,path:PathBuf,id:Identity,bytes:Vec<u8>,digest:String}
impl Held{
    fn open(env:&str,size:usize,expected:&str,pack:bool)->Result<Self,String>{
        let path=PathBuf::from(std::env::var_os(env).ok_or("admission47 missing input")?);
        need(path.is_absolute()&&path.as_os_str().len()<=1024,"admission47 input path")?;
        let md=generic37_metadata(&path,false)?;need(md.len()==size as u64,"admission47 input extent")?;
        let mut file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|_|"admission47 input open")?;
        let id=identity(&file)?;need((u64::from(id.high)<<32)|u64::from(id.low)==size as u64,"admission47 held extent")?;
        let mut bytes=Vec::new();let digest;
        if pack{let mut state=Blake2b::<U32>::new();let mut scratch=[0u8;65536];let mut total=0usize;
            loop{let n=file.read(&mut scratch).map_err(|_|"admission47 PACK read")?;if n==0{break;}
                total=total.checked_add(n).ok_or("admission47 PACK overflow")?;
                need(total<=size,"admission47 PACK trailing")?;state.update(&scratch[..n]);}
            need(total==size,"admission47 PACK truncated")?;digest=h41_hex(&state.finalize());
        }else{need(size<=869449,"admission47 bounded input")?;bytes.resize(size,0);
            file.read_exact(&mut bytes).map_err(|_|"admission47 input read")?;
            let mut tail=[0;1];need(file.read(&mut tail).map_err(|_|"admission47 input tail")?==0,"admission47 input trailing")?;
            digest=h41_sha(&bytes)?;}
        need(digest==expected,"admission47 input digest")?;
        let held=Self{file,path,id,bytes,digest};held.check()?;Ok(held)
    }
    fn check(&self)->Result<(),String>{
        generic37_metadata(&self.path,false)?;need(identity(&self.file)?==self.id,"admission47 held custody")?;
        let named=OpenOptions::new().read(true).share_mode(1).open(&self.path).map_err(|_|"admission47 custody reopen")?;
        need(identity(&named)?==self.id,"admission47 named custody")
    }
    fn rehash(&mut self,pack:bool)->Result<(),String>{
        self.check()?;self.file.seek(SeekFrom::Start(0)).map_err(|_|"admission47 custody seek")?;
        let mut state=Blake2b::<U32>::new();let mut scratch=[0;65536];let mut total=0usize;
        if pack{loop{let n=self.file.read(&mut scratch).map_err(|_|"admission47 custody read")?;if n==0{break;}
            total=total.checked_add(n).ok_or("admission47 custody overflow")?;need(total<=536870912,"admission47 custody extent")?;state.update(&scratch[..n]);}
            need(total==536870912&&h41_hex(&state.finalize())==self.digest,"admission47 PACK custody hash")?;
        }else{let mut actual=vec![0;self.bytes.len()];self.file.read_exact(&mut actual).map_err(|_|"admission47 custody read")?;
            let mut tail=[0;1];need(self.file.read(&mut tail).map_err(|_|"admission47 custody tail")?==0
                &&actual==self.bytes&&h41_sha(&actual)?==self.digest,"admission47 buffer custody")?;}
        self.check()
    }
}
fn raw_input(bytes:&[u8])->Result<crate::packed_owner_assembly::NativePrefix,String>{
    let mut at=0usize;let mut raws=Vec::with_capacity(3073);
    for _ in 0..3073{let n=u32::from_le_bytes(historical47_take(bytes,&mut at)?) as usize;
        need((1..=514).contains(&n),"admission47 RAW record extent")?;
        let end=at.checked_add(n).ok_or("admission47 RAW overflow")?;
        raws.push(bytes.get(at..end).ok_or("admission47 RAW truncated")?.to_vec());at=end;}
    need(at==bytes.len(),"admission47 RAW trailing")?;
    crate::packed_owner_assembly::NativePrefix::from_raw_iter(3073,raws.into_iter().map(Ok))
}
fn probe_label(role:usize)->&'static [u8]{match role{2=>b"native-role2-direct-full-continuation-v1",
    4=>b"native-seven-distinct-join-continuation-v1",5=>b"native-role5-common-control",
    6=>b"native-role6-direct-full-continuation-v1",_=>b"native-role-join-prefix-control-v1"}}
fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
fn key_controls(a:&Historical47Admission,key:&[u8],meta:&[u8])->Result<(),String>{
    let activity=historical47_activity();
    let check=|k:&[u8],m:&[u8]|Historical47Admission::new(&a.frame,k,m,&a.commitment).map(|_|());
    for size in [0,39,41]{let mut bad=meta.to_vec();bad.resize(size,0);
        rejected(check(key,&bad),"admission47 key metadata extent",activity)?;}
    let mut bad=meta.to_vec();bad[0]=31;rejected(check(key,&bad),"admission47 key dimension",activity)?;
    let mut bad=meta.to_vec();bad[8]^=1;rejected(check(key,&bad),"admission47 key id",activity)?;
    rejected(check(&key[..key.len()-1],meta),"admission47 key extent",activity)?;
    let mut bad=key.to_vec();bad[100]^=1;rejected(check(&bad,meta),"admission47 key hash",activity)
}
fn census_controls(ctx:&ProofContext<'_>,a:&Historical47Admission,u:Historical47Units)->Result<(),String>{
    let before=historical47_activity();let mut bad=ctx.relation_refs();bad.composite_terms+=1;
    rejected(historical47_prefix(ctx.consumer,bad,&a.frame,&a.commitment,&mut PreparationObservation::default()).map(|_|()),
        "admission47 composite census",before)?;
    for i in 0..4{let mut bad=u;match i{0=>bad.initial-=1,1=>bad.equal-=1,2=>bad.alias2-=1,_=>bad.complement-=1}
        rejected(bad.total().map(|_|()),match i{0|1=>"admission47 numeric units",2=>"admission47 alias units",_=>"admission47 inactive units"},before)?;}
    rejected(historical47_check_count(u.total()?.checked_sub(1375137).ok_or("admission47 numeric omission fixture")?,
        ctx.composite_terms),"admission47 composite census",before)?;
    need(u.zero_occurrences>0&&u.a1>0,"admission47 zero occurrence reached")?;
    // Fault only the independent counting sink, not the immutable canonical visitor.
    // Omit the first actually reached M1/lane0 term with a zero coefficient.
    let mut omitted=false;let mut observed=0usize;
    let returned=ctx.daa.visit_s12_local_endpoint_terms(2048,0,|term|{
        if !omitted && (term.gate.c0.is_zero()||term.gate.c1.is_zero()||term.gate.c2.is_zero()||term.gate.c3.is_zero()){
            omitted=true;return Ok(());}observed+=1;Ok(())})?;
    need(omitted&&returned==u.a1&&observed.checked_add(1)==Some(returned),"admission47 reached zero omission")?;
    let mut bad=u;bad.a1=observed;
    rejected(historical47_check_count(bad.total()?,ctx.composite_terms),"admission47 composite census",before)
}
fn report(public:&Public,units:Historical47Units,native:&[([u64;3],String);7],historical:&[([u64;3],String);7],
    times:[u64;6],activity:[u64;2],frame_sha:String)->Result<serde_json::Value,String>{
    Ok(serde_json::json!({"schema":"historical32-admission47-v1","result":"PASS","headers":3073,"slot_log":12,"slots":4096,
        "common_input":32,"input_bits":H47_INPUTS,"row_bits":H47_ROWS,"full_roster":[26,6,32,32,40],
        "public":h41_public(public),"frame_bytes":571,"frame_sha256":frame_sha,
        "census":{"height_unit":units.height,"initial":units.initial,"equal":units.equal,"m1":units.a1,"m2":units.a2,
            "alias_m1":units.alias1,"alias_m2":units.alias2,"inactive_full":units.full,"inactive_m1":units.complement,
            "zero_occurrences":units.zero_occurrences,"total":units.total()?},
        "native_prefixes":native,"historical_prefixes":historical,"timings_ns":times,"activity":activity,
        "key":{"bytes":33264,"metadata_bytes":40,"log_n":32,"sha256":KEY_SHA,"setup_id":ID},
        "custody":{"raw_sha256":RAW_SHA,"pack_blake2b256":PACK_BLAKE,"commitment_sha256":C_SHA,"post":true},
        "checks":{"raw_plan":true,"geometry":true,"same_parent":true,"count":true,"canonical_c":true,"alternate_c_binding":true,
            "old_prefixes_incompatible":true,"public_field_bindings":true,"parents_sequential":true},
        "new_gkr":0,"pcs_invoked":false,"setup_generated":false,"witness_generated":false,"full_history":false,"production":false}))
}
struct Trace{start:Instant,next:usize}
impl Trace{
    fn mark(&mut self,phase:&str,event:&str)->Result<(),String>{
        need(STAGES.get(self.next)==Some(&(phase,event)),"admission47 stage order")?;
        eprintln!("HISTORICAL32_ADMISSION47_STAGE {phase} {event} {}",self.start.elapsed().as_nanos());self.next+=1;Ok(())
    }
}
fn run(t:&mut Trace)->Result<(),String>{
    let mut times=[0u64;6];t.mark("admission","begin")?;let started=Instant::now();
    let mut raw=Held::open("NIPOPOW_ADMISSION47_RAW_PATH",869449,RAW_SHA,false)?;
    let mut pack=Held::open("NIPOPOW_ADMISSION47_PACK_PATH",536870912,PACK_BLAKE,true)?;
    let mut key=Held::open("NIPOPOW_ADMISSION47_KEY_PATH",33264,KEY_SHA,false)?;
    let mut c=Held::open("NIPOPOW_ADMISSION47_COMMITMENT_PATH",384,C_SHA,false)?;
    let mut metadata=Held::open("NIPOPOW_ADMISSION47_KEY_METADATA_PATH",40,
        "E44408DC018E99711273794DF3575BE7D180CF347448A021AA7EEC6BD0143401",false)?;
    let input=raw_input(&raw.bytes)?;
    let public=Public{headers:3073,root:input.root(),total:input.total_be28(),
        tip:ergo_header_core::blake2b256(input.raw(3073)?),tip_time:input.timestamp(3073)?};
    need(public.root==historical47_hex::<32>("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913")?
        &&public.total==historical47_hex::<28>("000000000000000000000000000000000000000000564F0B9B000000")?
        &&public.tip==historical47_hex::<32>("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC")?
        &&public.tip_time==1562018269889,"admission47 retained candidate")?;
    let admitted=Historical47Admission::new(&historical47_frame(&public)?,&key.bytes,&metadata.bytes,&c.bytes)?;
    key_controls(&admitted,&key.bytes,&metadata.bytes)?;
    times[0]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"admission47 clock")?;t.mark("admission","end")?;
    let mut native:[([u64;3],String);7]=std::array::from_fn(|_|([0;3],String::new()));
    t.mark("native","begin")?;let started=Instant::now();
    {let statement=crate::native_role4_join::expected_statement_bytes(&c.bytes)?;
        let bound=crate::native_role4_join::start_transcript(&statement,&key.bytes,&c.bytes)?;
        let prefix=bound.producer_transcript();native[4]=(counters(&prefix),h41_fr(prefix.clone().try_challenge_scalar(probe_label(4))?));}
    {use crate::native_prefix_auth_plan::{Candidate,NativePrefixAuthPlan,Selection};
        let parent=WorkTreeHistoryPlan::compile(3073,12,public.root,public.total)?;
        crate::packed_owner_assembly::validate_native_plan_input(&parent,&input)?;
        let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),Candidate{n:3073,root:public.root,total:public.total,tip:public.tip,tip_time:public.tip_time})?;
        for role in [0,1,2,3,5,6]{let (counts,continuation)=plan.native_role_prefix_control_for_join(role,&key.bytes,&c.bytes)?;
            native[role]=(counts,h41_fr(continuation));}}
    times[1]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"admission47 clock")?;t.mark("native","end")?;
    t.mark("historical","begin")?;let started=Instant::now();
    let consumer=historical47_consumer(&admitted)?;crate::packed_owner_assembly::validate_native_plan_input(&consumer.parent,&input)?;
    drop(input);
    let (context,units)=ProofContext::historical_h12(&consumer,&admitted)?;
    need(work_tree_wiring::full_roster_shape(consumer.parent.topology())?==(26,6,32,32)
        &&consumer.parent.topology().families.len()==34,"admission47 native roster shape")?;
    census_controls(&context,&admitted,units)?;
    times[2]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"admission47 clock")?;t.mark("historical","end")?;
    t.mark("prefixes","begin")?;let started=Instant::now();
    let mut historical:[([u64;3],String);7]=std::array::from_fn(|_|([0;3],String::new()));
    for role in 0..7{let prefix=context.historical47_role_prefix(role,&admitted)?;
        historical[role]=(counters(&prefix),h41_fr(prefix.clone().try_challenge_scalar(probe_label(role))?));
        need(native[role].0[0]==0&&native[role].0[1]==0&&historical[role].0[0]==0&&historical[role].0[1]==0
            &&native[role].1!=historical[role].1,"admission47 actual prefix compatibility")?;}
    // Independent canonical C, outside the retained fixture hash authority.
    let alternate=Historical47Admission::new(&admitted.frame,&key.bytes,&metadata.bytes,&synthetic_c()?)?;
    need(alternate.commitment!=admitted.commitment,"admission47 alternate C reached")?;
    for role in 0..7{let prefix=context.historical47_role_prefix(role,&alternate)?;
        need(h41_fr(prefix.clone().try_challenge_scalar(probe_label(role))?)!=historical[role].1,"admission47 alternate C binding")?;}
    let activity=historical47_activity();need(activity==[1,14],"admission47 actual activity")?;
    times[3]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"admission47 clock")?;t.mark("prefixes","end")?;
    drop(alternate);drop(context);drop(consumer);t.mark("drop","end")?;
    t.mark("public_bindings","begin")?;let started=Instant::now();
    // Four distinct complete factory operations, each dropped before the next.
    // Observe role0's actual fork: all seven roles clone this same BASE.
    for field in 0..4{let mut changed=public.clone();match field{0=>changed.root[0]^=1,1=>changed.total[0]^=1,
        2=>changed.tip[0]^=1,_=>changed.tip_time^=1}
        let variant=Historical47Admission::new(&historical47_frame(&changed)?,&key.bytes,&metadata.bytes,&c.bytes)?;
        let variant_consumer=historical47_consumer(&variant)?;
        let (variant_context,_)=ProofContext::historical_h12(&variant_consumer,&variant)?;
        let fork=variant_context.historical47_role_prefix(0,&variant)?;
        need(h41_fr(fork.clone().try_challenge_scalar(probe_label(0))?)!=historical[0].1,"admission47 public field binding")?;
        drop(fork);drop(variant_context);drop(variant_consumer);drop(variant);
    }
    let activity=historical47_activity();need(activity==[5,18],"admission47 differential activity")?;
    times[4]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"admission47 clock")?;t.mark("public_bindings","end")?;
    t.mark("custody","begin")?;let started=Instant::now();
    raw.rehash(false)?;pack.rehash(true)?;key.rehash(false)?;c.rehash(false)?;metadata.rehash(false)?;
    times[5]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"admission47 clock")?;t.mark("custody","end")?;
    let value=report(&public,units,&native,&historical,times,activity,h41_sha(&admitted.frame)?)?;
    let bytes=serde_json::to_vec(&value).map_err(|_|"admission47 report encoding")?;
    need(bytes.len()<=16384,"admission47 report cap")?;t.mark("complete","end")?;
    println!("\nHISTORICAL32_ADMISSION47 {}",String::from_utf8(bytes).map_err(|_|"admission47 report UTF8")?);Ok(())
}
fn size_control()->Result<(),String>{
    let p=Public{headers:3073,root:[255;32],total:[255;28],tip:[255;32],tip_time:i64::MIN};
    let m=usize::MAX;let units=Historical47Units{height:32,initial:225,equal:448,a1:m/4,a2:m/4,alias1:192,alias2:288,
        full:81920,complement:73728,zero_occurrences:m};
    let prefixes=std::array::from_fn(|_|([u64::MAX;3],"f".repeat(64)));
    let v=report(&p,units,&prefixes,&prefixes,[u64::MAX;6],[u64::MAX;2],"F".repeat(64))?;
    let b=serde_json::to_vec(&v).map_err(|_|"admission47 report encoding")?;
    need(b.len()<16384,"admission47 maximal report")?;
    // Worst escaped HOLD reason is separately bounded, not a successful report.
    let hold=serde_json::to_vec(&serde_json::json!({"result":"HOLD","reason":"\"\\".repeat(100)})).map_err(|_|"admission47 HOLD encoding")?;
    need(b.len()+hold.len()+4096<65536,"admission47 diagnostic envelope")
}
#[test]
fn admission47_ordinary()->Result<(),String>{codec_controls()?;identity_controls()?;size_control()}
#[test]
#[ignore]
fn admission47_native32_prefixes(){
    let mut t=Trace{start:Instant::now(),next:0};
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(&mut t)));
    let error=match result{Ok(Ok(()))=>return,Ok(Err(e))=>e,Err(_)=>"admission47 panic".into()};
    let reason:String=error.chars().filter(|v|v.is_ascii_graphic()||*v==' ').take(160).collect();
    eprintln!("HISTORICAL32_ADMISSION47_HOLD {} {} {reason}",t.next,t.start.elapsed().as_nanos());panic!("admission47 HOLD");
}

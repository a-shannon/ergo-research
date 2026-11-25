//! Focused geometry, semantic omission and persisted-byte consumer gates.
use super::*;
use std::{fs::File, io::Read};

#[path = "historical_prefix_stream39_tests.rs"]
mod stream39_tests;

#[path = "historical_prefix_witness_stream40_tests.rs"]
mod stream40_tests;

#[path = "historical_prefix_aggregation44_tests.rs"]
mod aggregation44_tests;

#[path = "historical_prefix_boolean_fold45_tests.rs"]
mod boolean_fold45_tests;

#[path = "historical_prefix_admission47_tests.rs"]
mod admission47_tests;

#[path = "historical_prefix_role0_historical48_tests.rs"]
mod role0_historical48_tests;

#[path = "historical_prefix_role246_historical49_tests.rs"]
mod role246_historical49_tests;

#[path = "historical_prefix_role6_packed_line52_tests.rs"]
mod role6_packed_line52_tests;

#[path = "historical_prefix_role135_historical50_tests.rs"]
mod role135_historical50_tests;

// Source41 private H3 experiment. Key policy is trusted only in the reviewed
// parent invocation; candidate/public transport never supplies that authority.
const H41_MEMBERS:[(&str,usize);10]=[("statement.bin",568),("commitment.bin",384),
    ("role-0.gkr",5248),("role-1.gkr",5248),("role-2.gkr",5248),("role-3.gkr",3680),
    ("role-4.gkr",5248),("role-5.gkr",5248),("role-6.gkr",5248),("openings.bin",34269)];
fn h41_hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02x}")).collect()}
fn h41_sha(bytes:&[u8])->Result<String,String>{Ok(h41_hex(&crate::native_prefix_auth_plan::role0_sha256(bytes)?).to_uppercase())}
fn h41_fr(value:Fr)->String{use ark_ff::{BigInteger,PrimeField};let mut b=value.into_bigint().to_bytes_le();b.resize(32,0);h41_hex(&b)}
fn h41_claim(value:&Claim)->serde_json::Value{serde_json::json!({"point":value.point.iter().map(|v|h41_fr(*v)).collect::<Vec<_>>(),"value":h41_fr(value.value)})}
fn h41_env(name:&str,limit:usize)->Result<String,String>{let v=std::env::var(name).map_err(|_|format!("scaling41 missing {name}"))?;
    if v.is_empty()||v.len()>limit{return Err("scaling41 transport extent".into());}Ok(v)}
fn h41_hex32(text:&str)->Result<[u8;32],String>{
    if text.len()!=64||!text.bytes().all(|v|v.is_ascii_digit()||(b'A'..=b'F').contains(&v)){return Err("scaling41 transport hex".into());}
    let mut out=[0;32];for(i,pair)in text.as_bytes().chunks_exact(2).enumerate(){out[i]=u8::from_str_radix(std::str::from_utf8(pair).map_err(|_|"scaling41 transport hex")?,16).map_err(|_|"scaling41 transport hex")?;}Ok(out)
}
fn h41_names(names:&mut Vec<String>)->Result<(),String>{let mut expected:Vec<_>=H41_MEMBERS.iter().map(|v|v.0.to_owned()).collect();expected.sort();names.sort();
    if *names!=expected{return Err("scaling41 package roster".into());}Ok(())}
fn h41_pins(pins:&[(String,String)])->Result<(),String>{
    if pins.len()!=10||pins.iter().zip(H41_MEMBERS).any(|((name,pin),(expected,_))|name!=expected||pin.len()!=64
        ||!pin.bytes().all(|v|v.is_ascii_digit()||(b'a'..=b'f').contains(&v))){return Err("scaling41 pin roster".into());}Ok(())
}
fn h41_loaded(pins:&[(String,String)],name:&str,bytes:&[u8])->Result<(),String>{h41_pins(pins)?;
    let i=H41_MEMBERS.iter().position(|v|v.0==name).ok_or("scaling41 member name")?;
    if bytes.len()!=H41_MEMBERS[i].1{return Err("scaling41 member extent".into());}
    if layout::hash_bytes(bytes)!=pins[i].1{return Err("scaling41 consumed member hash".into());}Ok(())
}
fn h41_snapshot(dir:&Path)->Result<Vec<(String,String)>,String>{
    if !dir.is_absolute(){return Err("scaling41 package directory".into());}generic37_metadata(dir,true)?;
    let mut names=Vec::with_capacity(10);for e in dir.read_dir().map_err(|e|e.to_string())?{
        if names.len()==10{return Err("scaling41 package roster".into());}
        names.push(e.map_err(|e|e.to_string())?.file_name().into_string().map_err(|_|"scaling41 package name")?);}
    h41_names(&mut names)?;let mut pins=Vec::with_capacity(10);
    for(name,size)in H41_MEMBERS{pins.push((name.to_string(),layout::hash_bytes(&generic37_read(&dir.join(name),size)?)));}Ok(pins)
}
fn h41_read(dir:&Path,name:&str,pins:&[(String,String)])->Result<Vec<u8>,String>{
    h41_pins(pins)?;generic37_metadata(dir,true)?;let size=H41_MEMBERS.iter().find(|v|v.0==name).ok_or("scaling41 member name")?.1;
    let bytes=generic37_read(&dir.join(name),size)?;h41_loaded(pins,name,&bytes)?;Ok(bytes)
}
fn h41_load(dir:&Path,pins:&[(String,String)])->Result<(Vec<u8>,Artifact),String>{
    let frame=h41_read(dir,"statement.bin",pins)?;historical41_decode(&frame)?;
    let commitment=h41_read(dir,"commitment.bin",pins)?;let mut roles=Vec::with_capacity(7);
    for role in 0..7{roles.push(RoleProof{role,bytes:h41_read(dir,&format!("role-{role}.gkr"),pins)?});}
    let artifact=Artifact{commitment,roles,batch:h41_read(dir,"openings.bin",pins)?};historical41_package(&artifact)?;Ok((frame,artifact))
}
fn h41_headers(n:usize)->Result<Vec<ergo_header_core::Header>,String>{
    if !matches!(n,5|8){return Err("scaling41 fixture headers".into());}
    let value:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).map_err(|e|e.to_string())?;
    let mut out=Vec::with_capacity(n);for i in 0..n{let text=value["networks"]["mainnet"]["source_headers_hex"][i].as_str().ok_or("scaling41 retained header")?;
        if text.is_empty()||text.len()>1028||text.len()%2!=0{return Err("scaling41 retained raw extent".into());}
        let raw=text.as_bytes().chunks_exact(2).map(|b|u8::from_str_radix(std::str::from_utf8(b).map_err(|_|"scaling41 raw hex")?,16).map_err(|_|"scaling41 raw hex")).collect::<Result<Vec<_>,_>>()?;
        let h=ergo_header_core::Header::decode(&raw,None).map_err(|e|format!("{e:?}"))?;
        if h.encode().map_err(|e|format!("{e:?}"))?!=raw{return Err("scaling41 retained canonical header".into());}out.push(h);
    }Ok(out)
}
struct H41Key {policy:Historical41KeyPolicy,key:Vec<u8>,metadata:Vec<u8>,dir:std::path::PathBuf}
fn h41_key_roster(dir:&Path)->Result<(),String>{generic37_metadata(dir,true)?;let mut names=Vec::with_capacity(2);
    for e in dir.read_dir().map_err(|e|e.to_string())?{if names.len()==2{return Err("scaling41 key roster".into());}
        names.push(e.map_err(|e|e.to_string())?.file_name().into_string().map_err(|_|"scaling41 key name")?);}
    names.sort();if names!=["key-metadata.bin","verifier-key.bin"]{return Err("scaling41 key roster".into());}Ok(())}
impl H41Key{
    fn load()->Result<Self,String>{
        let dir=std::path::PathBuf::from(h41_env("NIPOPOW_SCALING41_KEY_DIR",240)?);
        if !dir.is_absolute(){return Err("scaling41 key directory".into());}h41_key_roster(&dir)?;
        if h41_env("NIPOPOW_SCALING41_KEY_BYTES",6)?!="25584"||h41_env("NIPOPOW_SCALING41_KEY_LOG",2)?!="23"{
            return Err("scaling41 key policy shape".into());}
        let policy=Historical41KeyPolicy::transport(25584,h41_hex32(&h41_env("NIPOPOW_SCALING41_KEY_SHA256",64)?)?,
            h41_hex32(&h41_env("NIPOPOW_SCALING41_SETUP_ID",64)?)?,23,h41_hex32(&h41_env("NIPOPOW_SCALING41_KEY_REVIEW",64)?)?)?;
        let key=generic37_read(&dir.join("verifier-key.bin"),25584)?;let metadata=generic37_read(&dir.join("key-metadata.bin"),40)?;
        policy.admit(&key,&metadata)?;Ok(Self{policy,key,metadata,dir})
    }
    fn custody(&self)->Result<(),String>{h41_key_roster(&self.dir)?;
        let key=generic37_read(&self.dir.join("verifier-key.bin"),25584)?;let meta=generic37_read(&self.dir.join("key-metadata.bin"),40)?;
        if key!=self.key||meta!=self.metadata{return Err("scaling41 key custody".into());}self.policy.admit(&key,&meta)?;Ok(())}
}
const H41_KEY_STAGES:&[(&str,&str)]=&[("admission","begin"),("admission","end"),("setup","begin"),("setup","end"),
    ("export","begin"),("export","end"),("complete","end")];
const H41_FULL_STAGES:&[(&str,&str)]=&[("admission","begin"),("admission","end"),("writer","begin"),("writer","end"),
    ("commit","begin"),("commit","end"),("context","begin"),("context","end"),
    ("role0","begin"),("role0","end"),("role1","begin"),("role1","end"),("role2","begin"),("role2","end"),
    ("role3","begin"),("role3","end"),("role4","begin"),("role4","end"),("role5","begin"),("role5","end"),
    ("role6","begin"),("role6","end"),("opening","begin"),("opening","end"),("producer_drop","end"),
    ("export","begin"),("export","end"),("consumer","begin"),("consumer","end"),("custody","begin"),("custody","end"),("complete","end")];
struct H41Trace{case:&'static str,start:Instant,events:Vec<(&'static str,&'static str,u64)>}
impl H41Trace{
    fn stamp(&self)->Result<u64,String>{u64::try_from(self.start.elapsed().as_nanos()).map_err(|_|"scaling41 clock".into())}
    fn at(&mut self,phase:&'static str,event:&'static str,ns:u64)->Result<(),String>{
        let schedule=if self.case=="key"{H41_KEY_STAGES}else{H41_FULL_STAGES};
        if schedule.get(self.events.len())!=Some(&(phase,event))||ns>if self.case=="key"{120_000_000_000}else{360_000_000_000}{return Err("scaling41 stage/deadline".into());}
        eprintln!("HISTORY_SCALING41_STAGE {} {phase} {event} {ns}",self.case);self.events.push((phase,event,ns));Ok(())}
    fn mark(&mut self,p:&'static str,e:&'static str)->Result<(),String>{let ns=self.stamp()?;self.at(p,e,ns)}
    fn phases(&self)->std::collections::BTreeMap<&str,u64>{self.events.windows(2).filter(|w|w[0].0==w[1].0&&w[0].1=="begin"&&w[1].1=="end")
        .map(|w|(w[0].0,w[1].2-w[0].2)).collect()}
}
fn h41_encode(value:&serde_json::Value)->Result<Vec<u8>,String>{let b=serde_json::to_vec(value).map_err(|e|e.to_string())?;
    if b.len()>16384{return Err("scaling41 report cap".into());}Ok(b)}
fn h41_print(value:&serde_json::Value)->Result<(),String>{let b=h41_encode(value)?;let mut out=std::io::stdout().lock();
    out.write_all(b"\nHISTORY_SCALING41_REPORT ").map_err(|e|e.to_string())?;out.write_all(&b).map_err(|e|e.to_string())?;
    out.write_all(b"\n").map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())}
fn h41_complete(t:&mut H41Trace,mut value:serde_json::Value)->Result<(),String>{let ns=t.stamp()?;
    value["elapsed_ns"]=serde_json::json!(ns);value["phase_ns"]=serde_json::json!(t.phases());let _=h41_encode(&value)?;
    t.at("complete","end",ns)?;h41_print(&value)}
fn h41_execute(case:&'static str,run:impl FnOnce(&mut H41Trace)->Result<(),String>){
    let mut t=H41Trace{case,start:Instant::now(),events:Vec::with_capacity(32)};
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(&mut t)));
    let error=match result{Ok(Ok(()))=>return,Ok(Err(e))=>e,Err(_)=>"scaling41 panic".into()};
    let reason:String=error.chars().filter(|v|v.is_ascii_graphic()||*v==' ').take(200).collect();
    let phase=t.events.last().map(|(p,e,_)|format!("{p}:{e}")).unwrap_or_else(||"entry".into());
    eprintln!("HISTORY_SCALING41_HOLD {case} {phase} {} {reason}",t.start.elapsed().as_nanos());panic!("scaling41 HOLD");
}
fn h41_public(p:&Public)->serde_json::Value{serde_json::json!({"headers":p.headers,"root":h41_hex(&p.root),"total":h41_hex(&p.total),"tip":h41_hex(&p.tip),"tip_time":p.tip_time})}
fn h41_full_report(case:&str,p:&Public,writer:&witness::stream40::WriterStats,key:&Historical41KeyPolicy,roles:Vec<serde_json::Value>,claims:&[Claim;7])->serde_json::Value{
    serde_json::json!({"schema":"scaling41-v1","case":case,"result":"PASS","public":h41_public(p),"writer":writer,
        "key":{"bytes":25584,"log_n":23,"sha256":h41_hex(&key.sha).to_uppercase(),"id":h41_hex(&key.id),"review":h41_hex(&key.review).to_uppercase()},
        "roles":roles,"claims":claims.iter().map(h41_claim).collect::<Vec<_>>(),"files":10,"public_bytes":70389,"opening_bytes":34269,
        "gkr_regenerated":7,"gkr_reused":0,"checks":{"held_mle":true,"producer_verified":true,"fresh_claims":true,"canonical_codecs":true,"custody":true,"producer_dropped":true},
        "full_history":false,"production":false})
}
fn h41_size_controls()->Result<(),String>{
    let p=Public{headers:8,root:[255;32],total:[255;28],tip:[255;32],tip_time:i64::MIN};let m=usize::MAX;
    let w=witness::stream40::WriterStats{sink_calls:m,written_bytes:m,finish_observed:true,output_capacity_peak:m,seen_capacity_peak:m,
        mask_capacity:m,header_capacity_peak:m,local_map_peak:m,frontier_peak:m,native_scans:m,scan_leaf_hashes:m,scan_node_hashes:m};
    let key=Historical41KeyPolicy::transport(25584,[255;32],[255;32],23,[255;32])?;
    let claims=std::array::from_fn(|_|Claim{point:vec![-Fr::one();23],value:-Fr::one()});let mut roles=Vec::new();
    for role in 0..7{roles.push(serde_json::json!({"role":role,"proof_sha256":"F".repeat(64),"producer_ns":u64::MAX,
        "terms":if matches!(role,2|4|5|6){Some(u64::MAX)}else{None},"sender":if matches!(role,2|4|5|6){Some(serde_json::json!([u64::MAX,u64::MAX,u64::MAX,"f".repeat(64)]))}else{None},
        "loads":if matches!(role,2|4|5|6){Some(u64::MAX)}else{None},"fields":if matches!(role,2|4|5|6){Some(u64::MAX)}else{None},
        "counts":if matches!(role,2|4|5|6){Some([u64::MAX;4])}else{None}}));}
    let mut v=h41_full_report("n8",&p,&w,&key,roles,&claims);v["elapsed_ns"]=serde_json::json!(u64::MAX);
    let phases:std::collections::BTreeMap<_,_>=H41_FULL_STAGES.iter().filter(|v|v.1=="begin").map(|v|(v.0,u64::MAX)).collect();v["phase_ns"]=serde_json::json!(phases);
    let b=h41_encode(&v)?;if b.len()+32*100+2048>65536{return Err("scaling41 source output envelope".into());}
    if h41_encode(&serde_json::json!({"oversize":"x".repeat(16384)})).err().as_deref()!=Some("scaling41 report cap"){return Err("scaling41 serializer attribution".into());}Ok(())
}

#[test]
fn scaling41_admission_boundaries(){
    let rejects=|result:Result<(),String>,expected:&str|assert_eq!(result.err().as_deref(),Some(expected));
    let initialized_iv:[u64;8]=[0x6a09e667f2bdc928,0xbb67ae8584caa73b,0x3c6ef372fe94f82b,0xa54ff53a5f1d36f1,
        0x510e527fade682d1,0x9b05688c2b3e6c1f,0x1f83d9abfb41bd6b,0x5be0cd19137e2179];
    let actual_iv=crate::circuit::blake2b256_initial_state();assert_eq!(actual_iv,initialized_iv,"scaling42 initialized IV words");
    assert_eq!(actual_iv.map(u64::count_ones),[33,35,38,38,32,31,38,32],"scaling42 initialized IV popcounts");
    assert_eq!(actual_iv.iter().map(|v|v.count_ones()).sum::<u32>(),277,"scaling42 initialized IV census");
    for tuple in [(3,2,4),(4,2,4),(5,3,8),(8,3,8)]{
        witness::stream40::assignment_mask_profile(tuple.0,tuple.1,tuple.2).unwrap();}
    // Mutate each tuple coordinate independently from an admitted profile.
    for tuple in [(2,2,4),(5,2,4),(3,3,4),(3,2,8),(4,3,4),(4,2,8),
        (4,3,8),(6,3,8),(7,3,8),(9,3,8),(5,2,8),(5,3,4),(8,2,8),(8,3,4)]{
        rejects(witness::stream40::assignment_mask_profile(tuple.0,tuple.1,tuple.2),"scaling43 assignment mask profile");}
    for n in [0,3,4,6,7,9]{assert_eq!(Historical41Policy::new(n).err().unwrap(),"scaling41 headers");}
    for n in [5,8]{let p=Public{headers:n,root:[1;32],total:[2;28],tip:[3;32],tip_time:4};let frame=historical41_frame(&p).unwrap();assert_eq!(frame.len(),568);
        assert_eq!(historical41_frame(&historical41_decode(&frame).unwrap()).unwrap(),frame);
        assert!(crate::historical_prefix_public::decode_tiny_candidate(&frame).is_err());assert!(p.profile().is_err());
        for extent in [567,569]{let mut b=frame.clone();b.resize(extent,0);assert_eq!(historical41_decode(&b).err().unwrap(),"scaling41 frame extent");}
        for (at,error) in [(0,"scaling41 frame profile"),(40,"scaling41 genesis anchor"),(72,"scaling41 genesis anchor"),
            (112,"scaling41 frame geometry"),(120,"scaling41 frame geometry"),(128,"scaling41 frame geometry")]{let mut b=frame.clone();b[at]^=1;assert_eq!(historical41_decode(&b).err().unwrap(),error);}
        let mut at=236;for role in 0..7{for offset in [at,at+8,at+16]{let mut b=frame.clone();b[offset]^=1;
            assert_eq!(historical41_decode(&b).err().unwrap(),if offset==at+16{"scaling41 role domain"}else{"scaling41 role roster"});}
            at+=16+ROLES[role].len();for offset in [at,at+8]{let mut b=frame.clone();b[offset]^=1;assert_eq!(historical41_decode(&b).err().unwrap(),"scaling41 role geometry");}at+=16;}
        // Untrusted candidate fields are canonically accepted, never compared to RAW truth here.
        for at in [136,168,196,228]{let mut b=frame.clone();b[at]^=1;assert!(historical41_decode(&b).is_ok());}
    }
    let bytes=vec![0;25584];let mut metadata=23u64.to_le_bytes().to_vec();metadata.extend([7;32]);
    let key=Historical41KeyPolicy::transport(25584,crate::native_prefix_auth_plan::role0_sha256(&bytes).unwrap(),[7;32],23,[9;32]).unwrap();
    for shape in [(25583,23),(25584,22),(25584,24)]{assert_eq!(Historical41KeyPolicy::transport(shape.0,[0;32],[7;32],shape.1,[9;32]).err().unwrap(),"scaling41 key policy shape");}
    for fault in 0..5{let mut b=bytes.clone();let mut meta=metadata.clone();let expected=match fault{
        0=>{meta.pop();"scaling41 key metadata extent"},1=>{meta[..8].copy_from_slice(&24u64.to_le_bytes());"scaling41 key dimension"},
        2=>{meta[8]^=1;"scaling41 key id"},3=>{b.pop();"scaling41 key extent"},_=>{b[0]^=1;"scaling41 key bytes"}};
        assert_eq!(key.admit(&b,&meta).err().unwrap(),expected);}
    assert!(key.admit(&bytes,&metadata).err().unwrap().contains("before allocation"));
    rejects(h41_hex32(&"f".repeat(64)).map(|_|()),"scaling41 transport hex");
    historical41_point_shape(3,8,1<<23,7).unwrap();
    for(stage,slots,length,owner)in [(2,8,1<<23,0),(3,4,1<<23,0),(3,8,1<<22,0),(3,8,1<<23,8)]{
        assert_eq!(historical41_point_shape(stage,slots,length,owner).err(),Some(GkrError::InvalidInputWidth));}
    for n in [5u64,8]{let layout=HeaderAdjacencyLayout::compile(n,3,[0;32],[0;32]).unwrap();
        let d=layout.historical_h3_descriptor_for_test().unwrap();d.validate(1<<23,16).unwrap();
        assert_eq!((d.active(),d.padded(),d.input_log(),d.row_log(),d.ids()),(n as usize,8,23,12,256));
        for(length,chunk)in [(1<<22,16),(1<<23,15),(1<<23,17)]{
            assert_eq!(d.validate(length,chunk).err().as_deref(),Some("linear diagnostic geometry/source rejected before activity"));}
        let mut t=Transcript::new(b"scaling41-linear-admission");let before=(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(crate::segment_adjacency::linear_for_test::prove(&d,1<<22,0,|_|panic!("wrong source reached loader"),&mut t)
            .err().map(|e|e.to_string()).as_deref(),Some("linear diagnostic geometry/source rejected before activity"));
        assert_eq!(before,(t.challenges(),t.raw_queries(),t.bytes_absorbed()));}
    {let layout=HeaderAdjacencyLayout::compile(7,3,[0;32],[0;32]).unwrap();
        assert_eq!(layout.historical_h3_descriptor_for_test().err().map(|e|e.to_string()).as_deref(),Some("scaling41 adjacency canonical H3 layout"));
        layout.cache_eviction_descriptor_for_test().unwrap().validate(1<<23,16).unwrap();}
    let terms=100u64;let upper=21*terms+344;let counts=[352,44*terms,22*terms,22*terms];
    for loads in [8u64,16,upper]{let io=packed::PackedIoSnapshot{read_calls:16*loads,read_bytes:131072*loads,..Default::default()};
        historical41_edge_census(terms,counts,loads,loads*layout::WIDTH as u64,&io).unwrap();}
    for fault in 0..12{let mut c=counts;let mut loads=16u64;let mut fields=loads*layout::WIDTH as u64;
        let mut io=packed::PackedIoSnapshot{read_calls:16*loads,read_bytes:131072*loads,..Default::default()};
        match fault{0..=3=>c[fault]+=1,4=>loads=7,5=>loads=upper+1,6=>fields-=1,7=>fields+=1,
            8=>io.read_calls-=1,9=>io.read_calls+=1,10=>io.read_bytes-=1,_=>io.read_bytes+=1}
        if matches!(fault,4|5){fields=loads*layout::WIDTH as u64;io.read_calls=16*loads;io.read_bytes=131072*loads;}
        assert_eq!(historical41_edge_census(terms,c,loads,fields,&io).err().as_deref(),
            Some(if fault<4{"scaling41 edge census"}else{"scaling41 edge load census"}));}
    assert_eq!(witness::stream40::h3_writer_controls().unwrap(),6);
    let core=Circuit{input_len:65536,row_count:131072,terms:Vec::new()};let banks:Vec<_>=layout::CORE_OFFSETS.iter().map(|v|v/layout::CORE).collect();
    for fault in 0..3{let mut t=Transcript::new(b"scaling41-admission");let before=(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        let mut changed=banks.clone();if fault==2{changed[0]=changed[1];}
        let r=core_pool_boolean::prove_h3_for_test(&core,if fault==0{3}else{4},&changed,if fault==1{2}else{3},
            |_|panic!("invalid H3 core reached loader"),&mut t,|_|panic!("invalid H3 core reached bind"),|_,_,_|panic!("invalid H3 core reached wiring"));
        assert_eq!(r.err().unwrap(),"scaling41 core policy");assert_eq!(before,(t.challenges(),t.raw_queries(),t.bytes_absorbed()));}
    let mut names=H41_MEMBERS.iter().map(|v|v.0.to_string()).collect::<Vec<_>>();h41_names(&mut names).unwrap();names.pop();rejects(h41_names(&mut names),"scaling41 package roster");
    let good=vec![0u8;568];let mut pins=H41_MEMBERS.iter().map(|(n,size)|(n.to_string(),layout::hash_bytes(&vec![0u8;*size]))).collect::<Vec<_>>();
    h41_loaded(&pins,"statement.bin",&good).unwrap();let mut bad=good.clone();bad[5]=1;rejects(h41_loaded(&pins,"statement.bin",&bad),"scaling41 consumed member hash");
    rejects(h41_loaded(&pins,"statement.bin",&good[..567]),"scaling41 member extent");pins[0]=pins[1].clone();rejects(h41_pins(&pins),"scaling41 pin roster");
    let pins=H41_MEMBERS.iter().map(|(name,size)|(name.to_string(),layout::hash_bytes(&vec![0u8;*size]))).collect::<Vec<_>>();
    for(name,size)in H41_MEMBERS{let good=vec![0u8;size];h41_loaded(&pins,name,&good).unwrap();
        let mut changed=good.clone();changed[0]^=1;rejects(h41_loaded(&pins,name,&changed),"scaling41 consumed member hash");
        rejects(h41_loaded(&pins,name,&good[..size-1]),"scaling41 member extent");}
    rejects(generic37_type(true,false,false,0x400,false),"generic37 public type/reparse");h41_size_controls().unwrap();
}

fn h41_eq(point:&[Fr],index:usize)->Fr{point.iter().enumerate().fold(Fr::one(),|v,(i,z)|v*if(index>>i)&1==1{*z}else{Fr::one()-z})}
fn h41_accumulate(out:&mut[Fr;4],term:Term,r:&[Fr],u:&[Fr],v:&[Fr]){let factor=h41_eq(r,term.row)*h41_eq(u,term.gate.left)*h41_eq(v,term.gate.right);
    for(a,b)in out.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]){*a+=factor*b;}}
fn h41_prefix_rejected(consumer:&Consumer,refs:RelationRefs<'_, '_>,frame:&[u8],expected:&str)->Result<(),String>{
    let mut observation=PreparationObservation::default();
    if historical41_prefix(consumer,refs,frame,&mut observation).err().as_deref()!=Some(expected)
        ||observation.transcript_created||observation.challenges!=0||observation.queries!=0{
        return Err("scaling41 identity guard attribution".into());}Ok(())
}
#[test]
#[ignore="private H3 shape/census/nonboolean checks; no setup or private witness input"]
fn scaling41_h3_shape_census()->Result<(),String>{
    let mut records=Vec::with_capacity(2);
    for n in [5u64,8]{let public=Public{headers:n,root:[0;32],total:[0;28],tip:[0;32],tip_time:0};let frame=historical41_frame(&public)?;
        let consumer=historical41_consumer(&public)?;
        {let mask=witness::stream40::assignment_mask(&consumer.parent)?;
            if mask.len()!=layout::WIDTH||mask.capacity()!=layout::WIDTH
                ||mask.iter().filter(|v|**v).count()!=401362||mask[991232..999424].iter().any(|v|*v){
                return Err("scaling43 assignment mask contract".into());}
            for owner in 0..8{let physical=consumer.parent.physical_assignment_replacement_mask(owner)?;
                if mask!=physical{return Err("scaling43 assignment mask owner equality".into());}}
            if consumer.parent.assignment_replacement_mask().err().as_deref()!=Some("prefix assignment overlay requires an N3/N4 four-slot plan"){
                return Err("scaling43 old mask admission".into());}}
        let parts=RelationParts::compile(consumer.layout_refs(),HeightBinding::HistoricalDiagnostic)?;
        Historical41Policy::new(n)?.geometry(&parts.geometry)?;let count=historical41_visit(parts.refs(),|_|Ok(()))?;
        if count!=32*n as usize+2*(225+448*(n as usize-2))+8*81920 || count!=parts.composite_terms{return Err("scaling41 independent class census".into());}
        for fault in 0..2{let mut refs=parts.refs();if fault==0{refs.mode=HeightBinding::LegacyN3N4;}else{refs.composite_terms+=1;}
            let mut observed=PreparationObservation::default();let e=historical41_prefix(&consumer,refs,&frame,&mut observed).err().ok_or("scaling41 prefix mutant accepted")?;
            if e!=if fault==0{"scaling41 historical mode"}else{"composite census differs from admitted profile"}
                ||observed.transcript_created||observed.challenges!=0||observed.queries!=0{return Err("scaling41 prefix mutant attribution".into());}}
        for role in 0..7{for rows in [false,true]{let mut g=parts.geometry.clone();if rows{g.row_bits[role]+=1;}else{g.input_bits[role]+=1;}
            let mut refs=parts.refs();refs.geometry=&g;let mut obs=PreparationObservation::default();let e=historical41_prefix(&consumer,refs,&frame,&mut obs).err().ok_or("scaling41 dimension mutant accepted")?;
            if e!=format!("geometry role {role} {} mismatch",if rows{"row"}else{"input"})||obs.transcript_created{return Err("scaling41 dimension attribution".into());}}}
        {let parent=WorkTreeHistoryPlan::compile(n,3,public.root,public.total)?;
            let mut refs=parts.refs();refs.layouts.parent=&parent;h41_prefix_rejected(&consumer,refs,&frame,"next36 parent layout identity")?;
            let height=HeightWork::compile_history(&parent)?;let mut refs=parts.refs();refs.height=&height;
            h41_prefix_rejected(&consumer,refs,&frame,"composite height parent identity")?;
            let daa=DaaHistoryRoster::compile(&parent)?;let mut refs=parts.refs();refs.daa=&daa;
            h41_prefix_rejected(&consumer,refs,&frame,"composite DAA parent identity")?;}
        {let adjacency=HeaderAdjacencyLayout::compile(n,3,[0;32],public.tip)?;let mut refs=parts.refs();refs.layouts.adjacency=&adjacency;
            h41_prefix_rejected(&consumer,refs,&frame,"next36 adjacency layout identity")?;}
        {let metadata=HeaderMetadataOrderLayout::compile(n,3,public.tip_time)?;let mut refs=parts.refs();refs.layouts.metadata=&metadata;
            h41_prefix_rejected(&consumer,refs,&frame,"next36 metadata layout identity")?;}
        {let points=point_membership::build()?;let mut refs=parts.refs();refs.layouts.points=&points;
            h41_prefix_rejected(&consumer,refs,&frame,"next36 points layout identity")?;
            let point_role=PointRole::dimensions(&points.circuit,3,16,17,23)?;let mut refs=parts.refs();refs.point_role=&point_role;
            h41_prefix_rejected(&consumer,refs,&frame,"next36 point base identity")?;}
        {let template=consumer.point_template.clone();let mut refs=parts.refs();refs.layouts.point_template=&template;
            h41_prefix_rejected(&consumer,refs,&frame,"next36 fingerprint owner identity")?;}
        {let mut other=public.clone();other.headers=if n==5{8}else{5};
            h41_prefix_rejected(&consumer,parts.refs(),&historical41_frame(&other)?,"scaling41 candidate identity")?;}
        drop(parts);let context=ProofContext::historical_h3(&consumer,&frame)?;let mut terms2=0;
        if historical41_admit(&context,1<<22,2).err().as_deref()!=Some("scaling41 source extent")
            ||historical41_admit(&context,1<<23,7).err().as_deref()!=Some("scaling41 role"){
            return Err("scaling41 wrapper admission attribution".into());}
        for role in [2usize,4]{let g=&context.geometry;let r=dense(g.row_bits[role],31+role as u64);let u=dense(g.input_bits[role],71);let v=dense(g.input_bits[role],113);
            let mut reference=[Fr::zero();4];if role==2{let c=context.small_circuit(2)?;terms2=c.terms.len();
                let shape=historical41_admit(&context,1<<23,2)?;
                if shape.terms!=terms2 as u64{return Err(format!("scaling41 role2 API/emission n={n} api={} canonical={terms2}",shape.terms));}
                let expected=if n==5{223651}else{265891};
                if terms2!=expected{return Err(format!("scaling41 role2 golden n={n} canonical={terms2} expected={expected}"));}
                let b1=consumer.parent.topology().families.len();let expected_b1=if n==5{14}else{16};
                if b1!=expected_b1{return Err(format!("scaling41 role2 B1 families n={n} actual={b1} expected={expected_b1}"));}
                let members=shape.strides.len();let expected_members=if n==5{20}else{22};
                if members!=expected_members{return Err(format!("scaling41 role2 members n={n} actual={members} expected={expected_members}"));}
                for term in c.terms{h41_accumulate(&mut reference,term,&r,&u,&v);}}
            else{historical41_visit(context.relation_refs(),|term|{h41_accumulate(&mut reference,term,&r,&u,&v);Ok(())})?;}
            if context.coefficients(role,&r,&u,&v)?!=reference{return Err("scaling41 nonboolean coefficient differential".into());}}
        records.push(serde_json::json!({"headers":n,"inputs":context.geometry.input_bits,"rows":context.geometry.row_bits,
            "families":consumer.parent.topology().families.len()+6,"role2_terms":terms2,"composite_terms":count,"coefficients_equal":true}));
    }
    h41_print(&serde_json::json!({"schema":"scaling41-v1","case":"shape","records":records,"full_history":false,"production":false}))
}

#[test]
#[ignore="two actual H2 historical packages plus distinct Legacy positive/prefix paths"]
fn scaling41_h2_compatibility()->Result<(),String>{
    let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;let mut historical=0;let mut legacy=0;let mut prefixes=0;
    let mut package_digests:[String;4]=std::array::from_fn(|_|String::new());
    for n in [3u64,4]{let dir=std::path::PathBuf::from(h41_env(if n==3{"NIPOPOW_SCALING41_H2_N3_DIR"}else{"NIPOPOW_SCALING41_H2_N4_DIR"},240)?);
        let pins=generic37_snapshot(&dir)?;let(frame,artifact)=generic37_load(&dir,&pins)?;
        if crate::historical_prefix_public::decode_tiny_candidate(&frame)?.headers!=n{return Err("scaling41 historical H2 directory".into());}
        let claims=verify_historical_tiny_bytes(&frame,&artifact)?;if claims.len()!=7{return Err("scaling41 H2 historical claims".into());}historical+=1;
        package_digests[(n-3) as usize]=h41_sha(&serde_json::to_vec(&pins).map_err(|e|e.to_string())?)?;
        if generic37_snapshot(&dir)?!=pins{return Err("scaling41 H2 historical custody".into());}
        let dir=std::path::PathBuf::from(h41_env(if n==3{"NIPOPOW_CANDIDATE_BINDING_N3_DIR"}else{"NIPOPOW_CANDIDATE_BINDING_N4_DIR"},240)?);
        let public=Public::native(n)?;let consumer=Consumer::new(&public)?;let context=ProofContext::new(&consumer)?;
        let pins=generic37_snapshot(&dir)?;let(frame,artifact)=generic37_load(&dir,&pins)?;
        if frame!=context.public_bytes{return Err("scaling41 Legacy statement custody".into());}
        context.verify(&artifact,&key).map_err(|e|format!("scaling41 Legacy {e:?}"))?;legacy+=1;
        package_digests[2+(n-3) as usize]=h41_sha(&serde_json::to_vec(&pins).map_err(|e|e.to_string())?)?;
        for role in 0..7{let mut actual=context.transcript(role,&key,&artifact.commitment);
            let mut literal=fresh_prefix(&context,&public,role,&key,&artifact.commitment,PrefixFault::NoFault)?;
            if [actual.challenges(),actual.raw_queries(),actual.bytes_absorbed()]!=[literal.challenges(),literal.raw_queries(),literal.bytes_absorbed()]
                ||actual.try_challenge_scalar(b"scaling41-legacy-prefix")?!=literal.try_challenge_scalar(b"scaling41-legacy-prefix")?{return Err("scaling41 Legacy NoFault prefix".into());}prefixes+=1;}
        if generic37_snapshot(&dir)?!=pins{return Err("scaling41 Legacy custody".into());}
    }
    if(historical,legacy,prefixes)!=(2,2,14){return Err("scaling41 H2 replay census".into());}
    h41_print(&serde_json::json!({"schema":"scaling41-v1","case":"h2","historical":historical,"legacy":legacy,"prefixes":prefixes,
        "package_digests":package_digests,"full_history":false,"production":false}))
}

#[test]
#[ignore="separate setup23 verifier-key export; no headers witness C or GKR"]
fn scaling41_key_export(){h41_execute("key",|t|{
    t.mark("admission","begin")?;let dir=std::path::PathBuf::from(h41_env("NIPOPOW_SCALING41_KEY_EXPORT_DIR",240)?);
    if !dir.is_absolute(){return Err("scaling41 export directory".into());}generic37_metadata(&dir,true)?;
    if dir.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("scaling41 key output not empty".into());}t.mark("admission","end")?;
    t.mark("setup","begin")?;let setup=pcs::generate_setup(23)?;let id=setup.id;
    let bytes=pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier))?;
    if bytes.len()!=25584{return Err("scaling41 key serializer".into());}
    let mut metadata=23u64.to_le_bytes().to_vec();metadata.extend(id);
    let policy=Historical41KeyPolicy::transport(25584,crate::native_prefix_auth_plan::role0_sha256(&bytes)?,id,23,[0;32])?;
    policy.admit(&bytes,&metadata)?;t.mark("setup","end")?;t.mark("export","begin")?;
    generic37_metadata(&dir,true)?;write_new(&dir.join("verifier-key.bin"),&bytes)?;write_new(&dir.join("key-metadata.bin"),&metadata)?;
    h41_key_roster(&dir)?;if generic37_read(&dir.join("verifier-key.bin"),25584)?!=bytes||generic37_read(&dir.join("key-metadata.bin"),40)?!=metadata{return Err("scaling41 key export custody".into());}
    t.mark("export","end")?;h41_complete(t,serde_json::json!({"schema":"scaling41-v1","case":"key","result":"PASS","log_n":23,
        "key_bytes":25584,"metadata_bytes":40,"internal_capacity":24,"id":h41_hex(&id),"sha256":h41_sha(&bytes)?,"full_history":false,"production":false}))
});}

fn h41_observation(role:usize,p:&History39Produced,bytes:&[u8])->Result<serde_json::Value,String>{
    let sender=match p.sender{Some((c,z))=>Some(serde_json::json!([c[0],c[1],c[2],h41_fr(z)])),None=>None};
    let counts=if let Some(e)=&p.edge{Some([e.endpoint_calls,e.callbacks,e.left_terms,e.right_terms])}
        else{p.linear.as_ref().map(|s|s.read_calls)};
    Ok(serde_json::json!({"role":role,"proof_sha256":h41_sha(bytes)?,"producer_ns":p.elapsed_ns,
        "terms":if matches!(role,2|4|5|6){Some(p.terms)}else{None},"sender":sender,
        "loads":if matches!(role,2|4|5|6){Some(p.load_calls)}else{None},"fields":if matches!(role,2|4|5|6){Some(p.loaded_fields)}else{None},"counts":counts}))
}
fn h41_full(n:u64){h41_execute(if n==5{"n5"}else{"n8"},|t|{
    t.mark("admission","begin")?;Historical41Policy::new(n)?;h41_size_controls()?;let material=H41Key::load()?;
    let output=artifact_directory()?;if !output.is_absolute(){return Err("scaling41 output directory".into());}generic37_metadata(&output,true)?;
    if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("scaling41 output not empty".into());}
    let private=std::env::temp_dir().join(format!("scaling41-n{n}-{}.bits",std::process::id()));if private.exists(){return Err("scaling41 private target exists".into());}t.mark("admission","end")?;
    t.mark("writer","begin")?;let headers=h41_headers(n as usize)?;
    if witness::stream40::h3_prepared_controls(&headers)?!=if n==5{9}else{10}{return Err("scaling41 prepared negative census".into());}
    let(source,summary,writer)=witness::stream40::write_h3_packed(&headers,&private)?;drop(headers);
    if source.input_len()!=1<<23||writer.written_bytes!=1048576||writer.sink_calls!=8||!writer.finish_observed{return Err("scaling41 writer extent".into());}
    let public=Public{headers:n,root:summary.root,total:summary.total,tip:summary.tip,tip_time:summary.tip_time};let frame=historical41_frame(&public)?;t.mark("writer","end")?;
    let(artifact,claims,observations)={
        t.mark("commit","begin")?;let key=material.policy.admit(&material.key,&material.metadata)?;let setup=pcs::generate_setup(23)?;
        if setup.id!=material.policy.id||pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier.clone()))?!=material.key{return Err("scaling41 setup identity".into());}
        let committed=packed::commit(&source,&setup)?;let commitment=pcs::encode_commitment(&committed.commitment)?;t.mark("commit","end")?;
        t.mark("context","begin")?;let(roles,claims,observations,corpus)={let consumer=historical41_consumer(&public)?;let context=ProofContext::historical_h3(&consumer,&frame)?;t.mark("context","end")?;
            let mut roles=Vec::with_capacity(7);let mut claims=Vec::with_capacity(7);let mut observations=Vec::with_capacity(7);
            for role in 0..7{let stage=["role0","role1","role2","role3","role4","role5","role6"][role];t.mark(stage,"begin")?;
                let p=prove_historical_h3(&context,&source,&key,&commitment,role)?;let bytes=gkr::encode_proof(&p.proof)?;
                let packet=RoleProof{role,bytes};let verified=context.verify_role(&packet,&key,&commitment).map_err(|e|format!("scaling41 fresh role {e:?}"))?;
                let point=if role==3{context.point_role.project(&p.claim.point)?}else{p.claim.point.clone()};let claim=Claim{point,value:p.claim.value};
                if claim!=verified.claim||claim.point.len()!=23||source.evaluate(&claim.point)?!=claim.value{return Err("scaling41 terminal/held MLE".into());}
                if role==3{let mut wrong=claim.point.clone();wrong[18]=Fr::zero();
                    if source.evaluate(&wrong)?==claim.value{return Err("scaling41 point bank differential".into());}}
                if matches!(role,2|4|5|6){let(c,z)=p.sender.ok_or("scaling41 sender missing")?;
                    if c!=verified.counters||z!=verified.continuation||c[0]!=[0,0,69,0,70,59,62][role]{return Err("scaling41 sender equality".into());}}
                let mut corrupt=p.proof.clone();corrupt.layers[0].rounds[0][0]+=Fr::one();let bad=RoleProof{role,bytes:gkr::encode_proof(&corrupt)?};
                let error=context.verify_role(&bad,&key,&commitment).err().ok_or("scaling41 bad GKR accepted")?;
                if error.stage!=RoleStage::Gkr||error.message!=GkrError::SumcheckIdentity.to_string(){return Err("scaling41 GKR negative attribution".into());}
                observations.push(h41_observation(role,&p,&packet.bytes)?);claims.push(claim);roles.push(packet);t.mark(stage,"end")?;
            }
            (roles,<[Claim;7]>::try_from(claims).map_err(|_|"scaling41 seven claims")?,observations,context.corpus_id)
        }; // No graph overlaps the common opening.
        t.mark("opening","begin")?;let statement=opening_batch::Statement{log_n:23,setup_id:setup.id,commitment:committed.commitment,corpus_id:Some(corpus),claims:claims.clone()};
        let(proof,_,_)=opening_batch::prove(&source,&committed,&setup,&statement)?;let batch=opening_batch::encode_proof(&proof,23)?;
        if batch.len()!=34269||opening_batch::encode_proof(&opening_batch::decode_proof(&batch,23)?,23)?!=batch{return Err("scaling41 common codec extent".into());}t.mark("opening","end")?;
        (Artifact{commitment,roles,batch},claims,observations)
    };drop(source);t.mark("producer_drop","end")?;
    t.mark("export","begin")?;generic37_metadata(&output,true)?;
    if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("scaling41 output drift".into());}
    write_new(&output.join("statement.bin"),&frame)?;write_new(&output.join("commitment.bin"),&artifact.commitment)?;
    for packet in &artifact.roles{write_new(&output.join(format!("role-{}.gkr",packet.role)),&packet.bytes)?;}write_new(&output.join("openings.bin"),&artifact.batch)?;
    let pins=h41_snapshot(&output)?;drop(artifact);drop(frame);t.mark("export","end")?;t.mark("consumer","begin")?;
    let(frame,artifact)=h41_load(&output,&pins)?;let actual=verify_historical_h3_bytes(&frame,&artifact,&material.key,&material.metadata,&material.policy)?;
    if actual!=claims{return Err("scaling41 atomic fresh claims".into());}
    // Binding mutations are classified as FS/public binding checks, not a new false-public theorem.
    for at in [136,168,196,228]{let mut changed=frame.clone();changed[at]^=1;
        if verify_historical_h3_bytes(&changed,&artifact,&material.key,&material.metadata,&material.policy).err().as_deref()!=Some("scaling41 atomic verification: Role(0)"){
            return Err("scaling41 public binding negative attribution".into());}}
    {let key=material.policy.admit(&material.key,&material.metadata)?;let consumer=historical41_consumer(&public)?;let context=ProofContext::historical_h3(&consumer,&frame)?;
        let verified=context.verified_roles(&artifact,&key).map_err(|e|format!("scaling41 negative baseline {e:?}"))?;
        let mut projected=verified.clone();projected.claims[3].point[0]+=Fr::one();common_verification_rejection(context.verify_common(&artifact,&key,&projected),None);
        let mut wrong=artifact.clone();wrong.commitment.fill(255);
        if historical41_package(&wrong).err().as_deref()!=Some("scaling41 canonical C"){return Err("scaling41 C negative attribution".into());}
        let mut proof=opening_batch::decode_proof(&artifact.batch,23)?;proof.terminal+=Fr::one();let mut wrong=artifact.clone();wrong.batch=opening_batch::encode_proof(&proof,23)?;
        common_verification_rejection(context.verify_common(&wrong,&key,&verified),Some("opening-batch terminal relation rejected"));
        use ark_ec::AffineRepr;use dory_pcs::backends::arkworks::ArkG1;
        let mut proof=opening_batch::decode_proof(&artifact.batch,23)?;let end=proof.pcs.final_message.as_mut().ok_or("scaling41 PCS final message")?;
        let one=ArkG1(ark_bn254::G1Affine::generator().into_group());end.e1=if end.e1!=one{one}else{ArkG1(ark_bn254::G1Affine::generator()*Fr::from(2u64))};
        let mut wrong=artifact.clone();wrong.batch=opening_batch::encode_proof(&proof,23)?;
        common_verification_rejection(context.verify_common(&wrong,&key,&verified),Some("opening-batch final PCS rejected:"));
    }
    t.mark("consumer","end")?;t.mark("custody","begin")?;if h41_snapshot(&output)?!=pins{return Err("scaling41 exported custody".into());}
    let _=h41_load(&output,&pins)?;material.custody()?;std::fs::remove_file(&private).map_err(|e|e.to_string())?;t.mark("custody","end")?;
    h41_complete(t,h41_full_report(if n==5{"n5"}else{"n8"},&public,&writer,&material.policy,observations,&actual))
});}
#[test]
#[ignore="private N5/H3 all-seven producer and fresh byte consumer; key admission required"]
fn scaling41_n5_complete(){h41_full(5);}
#[test]
#[ignore="private N8/H3 all-seven producer and fresh byte consumer; N5 acceptance required"]
fn scaling41_n8_complete(){h41_full(8);}

// New helpers are kept in this child: neither manifests nor fixture truth are
// inputs to the private historical byte consumer.
const GENERIC37_MEMBERS: [(&str,usize);10] = [("statement.bin",568),("commitment.bin",384),
    ("role-0.gkr",5024),("role-1.gkr",5024),("role-2.gkr",5024),("role-3.gkr",3456),
    ("role-4.gkr",5024),("role-5.gkr",5024),("role-6.gkr",5024),("openings.bin",31581)];

fn generic37_public(decoded: crate::historical_prefix_public::NativePublic) -> Public {
    Public { headers: decoded.headers, root: decoded.root, total: decoded.total,
        tip: decoded.tip, tip_time: decoded.tip_time }
}

fn generic37_type(is_file:bool,is_dir:bool,symlink:bool,attributes:u32,directory:bool)->Result<(),String> {
    if symlink || attributes & 0x400 !=0 || (if directory {!is_dir} else {!is_file}) {
        return Err("generic37 public type/reparse".into());
    }
    Ok(())
}

fn generic37_metadata(path:&Path,directory:bool)->Result<std::fs::Metadata,String> {
    let metadata=std::fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    #[cfg(windows)] let attributes={use std::os::windows::fs::MetadataExt;metadata.file_attributes()};
    #[cfg(not(windows))] let attributes=0;
    generic37_type(metadata.is_file(),metadata.is_dir(),metadata.file_type().is_symlink(),attributes,directory)?;
    Ok(metadata)
}

fn generic37_read(path: &Path, size: usize) -> Result<Vec<u8>, String> {
    let before = generic37_metadata(path,false)?;
    if before.len()!=size as u64 {return Err("generic37 public member extent".into());}
    let mut options = OpenOptions::new(); options.read(true);
    #[cfg(windows)] {
        use std::os::windows::fs::OpenOptionsExt;
        options.share_mode(1); // Read sharing only; deny writes/deletes while held.
    }
    let mut file=options.open(path).map_err(|e|e.to_string())?;
    let held=file.metadata().map_err(|e|e.to_string())?;
    let held_time=held.modified().map_err(|e|e.to_string())?;
    if held.len()!=before.len() || held_time!=before.modified().map_err(|e|e.to_string())? {
        return Err("generic37 public open drift".into());
    }
    let mut bytes=vec![0u8;size]; file.read_exact(&mut bytes).map_err(|e|e.to_string())?;
    let mut tail=[0u8;1]; if file.read(&mut tail).map_err(|e|e.to_string())?!=0 {
        return Err("generic37 public trailing member".into());
    }
    let after=file.metadata().map_err(|e|e.to_string())?;
    let named=generic37_metadata(path,false)?;
    if after.len()!=held.len() || after.modified().map_err(|e|e.to_string())?!=held_time
        || named.len()!=held.len() || named.modified().map_err(|e|e.to_string())?!=held_time {
        return Err("generic37 public read drift".into());
    }
    Ok(bytes)
}

fn generic37_snapshot(dir:&Path)->Result<Vec<(String,String)>,String> {
    if !dir.is_absolute() {return Err("generic37 public directory".into());}
    generic37_metadata(dir,true)?;
    let mut names=Vec::with_capacity(10);
    for entry in dir.read_dir().map_err(|e|e.to_string())? {
        let entry=entry.map_err(|e|e.to_string())?;
        if names.len()==10 {return Err("generic37 public roster".into());}
        names.push(entry.file_name().into_string().map_err(|_|"generic37 public member name")?);
    }
    names.sort(); let mut expected:Vec<_>=GENERIC37_MEMBERS.iter().map(|(name,_)|name.to_string()).collect();
    expected.sort(); if names!=expected {return Err("generic37 public roster".into());}
    let mut pins=Vec::with_capacity(10);
    for (name,size) in GENERIC37_MEMBERS {
        let bytes=generic37_read(&dir.join(name),size)?;
        pins.push((name.to_string(),layout::hash_bytes(&bytes)));
    }
    Ok(pins)
}

fn generic37_pin_roster(pins:&[(String,String)])->Result<(),String> {
    if pins.len()!=10 || pins.iter().zip(GENERIC37_MEMBERS).any(|((name,hash),(expected,_))|
        name!=expected || hash.len()!=64 || !hash.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b))) {
        return Err("generic37 loaded pin roster".into());
    }
    Ok(())
}

fn generic37_loaded_member(pins:&[(String,String)],name:&str,bytes:&[u8])->Result<(),String> {
    generic37_pin_roster(pins)?;
    let index=GENERIC37_MEMBERS.iter().position(|(member,_)|*member==name).ok_or("generic37 loaded member name")?;
    if bytes.len()!=GENERIC37_MEMBERS[index].1 {return Err("generic37 loaded member extent".into());}
    if layout::hash_bytes(bytes)!=pins[index].1 {return Err("generic37 loaded member digest".into());}
    Ok(())
}

fn generic37_bound_read(dir:&Path,name:&str,pins:&[(String,String)])->Result<Vec<u8>,String> {
    generic37_pin_roster(pins)?;
    generic37_metadata(dir,true)?;
    let size=GENERIC37_MEMBERS.iter().find(|(member,_)|*member==name).ok_or("generic37 loaded member name")?.1;
    let bytes=generic37_read(&dir.join(name),size)?;
    generic37_loaded_member(pins,name,&bytes)?;Ok(bytes)
}

fn generic37_load(dir:&Path,pins:&[(String,String)])->Result<(Vec<u8>,Artifact),String> {
    generic37_pin_roster(pins)?;
    let statement=generic37_bound_read(dir,"statement.bin",pins)?;
    crate::historical_prefix_public::decode_tiny_candidate(&statement)?;
    let commitment=generic37_bound_read(dir,"commitment.bin",pins)?;
    let mut roles=Vec::with_capacity(7);
    for role in 0..7 {roles.push(RoleProof {role,bytes:generic37_bound_read(dir,&format!("role-{role}.gkr"),pins)?});}
    let batch=generic37_bound_read(dir,"openings.bin",pins)?;
    Ok((statement,Artifact{commitment,roles,batch}))
}

fn generic37_join(headers:u64) {
    let started=Instant::now(); let location=std::cell::Cell::new("admission");
    let mark=|stage:&'static str,event:&str| {
        location.set(stage);
        eprintln!("HISTORY_GENERIC37_STAGE {stage} {event} {}",started.elapsed().as_nanos());
    };
    let operation=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||->Result<(),String> {
        if !matches!(headers,3|4) {return Err("generic37 trial profile".into());}
        let output=artifact_directory()?;
        generic37_metadata(&output,true)?;
        if !output.is_absolute() || !output.is_dir() || output.read_dir().map_err(|e|e.to_string())?.next().is_some() {
            return Err("generic37 fresh empty output".into());
        }
        let legacy_env=if headers==3 {"NIPOPOW_CANDIDATE_BINDING_N3_DIR"} else {"NIPOPOW_CANDIDATE_BINDING_N4_DIR"};
        let legacy_dir=std::env::var_os(legacy_env).map(std::path::PathBuf::from).ok_or("generic37 retained legacy input")?;
        let legacy_pins=generic37_snapshot(&legacy_dir)?;
        let (legacy_statement,legacy)=generic37_load(&legacy_dir,&legacy_pins)?;
        if crate::historical_prefix_public::decode_tiny_candidate(&legacy_statement)?.headers!=headers {
            return Err("generic37 retained history fixture".into());
        }
        let foreign_env=if headers==3 {"NIPOPOW_CANDIDATE_BINDING_N4_DIR"} else {"NIPOPOW_CANDIDATE_BINDING_N3_DIR"};
        let foreign_dir=std::env::var_os(foreign_env).map(std::path::PathBuf::from).ok_or("generic37 foreign C input")?;
        let foreign_pins=generic37_snapshot(&foreign_dir)?;
        let foreign_c=generic37_bound_read(&foreign_dir,"commitment.bin",&foreign_pins)?;
        if pcs::encode_commitment(&pcs::decode_commitment(&foreign_c)?)?!=foreign_c {
            return Err("generic37 foreign canonical C fixture".into());
        }
        let private_path=std::env::temp_dir().join(format!("generic37-n{headers}-{}.bits",std::process::id()));
        if private_path.exists() {return Err("generic37 private path exists".into());}
        mark("witness","begin");
        let public=Public::native(headers)?; // Fixture oracle; never passed to the fresh byte verifier.
        let bits={
            let w=witness::build(&witness::retained_headers_n(headers as usize)?)?;
            if (w.root,w.total,w.tip,w.tip_time)!=(public.root,public.total,public.tip,public.tip_time) {
                return Err("generic37 independent fixture agreement".into());
            }
            let mut bits=vec![0u8;(1<<22)/8];
            for (index,value) in w.values.iter().enumerate() {
                if !value.is_zero() && !value.is_one() {return Err("generic37 Boolean witness".into());}
                if value.is_one() {bits[index/8]|=1<<(index%8);}
            }
            bits
        }; // Dense witness dropped before setup/graph.
        mark("witness","end");
        let (artifact,claims,statement)={
            mark("setup_commit","begin");
            let source=packed_source(&private_path,&bits)?; drop(bits);
            let setup=pcs::generate_setup(22)?;
            let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
            if setup.id!=*key.id() {return Err("generic37 setup identity".into());}
            let committed=packed::commit(&source,&setup)?;
            let commitment=pcs::encode_commitment(&committed.commitment)?;
            if commitment.len()!=384 || pcs::encode_commitment(&pcs::decode_commitment(&commitment)?)?!=commitment {
                return Err("generic37 producer C codec".into());
            }
            mark("setup_commit","end");mark("producer","begin");
            let (roles,claims,statement,corpus_id)={
                let consumer=Consumer::new(&public)?;
                let encoded=literal_public_bytes(&public)?;
                let context=ProofContext::historical_tiny(&consumer,&encoded)?;
                let mut roles=Vec::with_capacity(7);let mut claims=Vec::with_capacity(7);
                for role in 0..7 {
                    let stage=["role0","role1","role2","role3","role4","role5","role6"][role];mark(stage,"begin");
                    let (proof,terminal)=if role==4 {
                        let circuit=context.tiny_historical_composite()?;
                        let input=read_all(&source,&context.geometry)?;
                        let mut t=context.transcript(4,&key,&commitment);
                        sparse::prove_with_binding(&circuit,&input,0,&mut t,|t|context.bind_role(4,t)).map_err(|e|e.to_string())?
                    } else {prove_role(&context,&source,&key,&commitment,role)?};
                    let bytes=gkr::encode_proof(&proof)?;
                    if bytes.len()!=(if role==3 {3456}else{5024})
                        || gkr::encode_proof(&gkr::decode_dimensions(&[context.geometry.input_bits[role]],&bytes)?)?!=bytes {
                        return Err("generic37 producer GKR codec".into());
                    }
                    let point=if role==3 {context.point_role.project(&terminal.point)?} else {terminal.point};
                    if source.evaluate(&point)?!=terminal.value {return Err("generic37 producer held MLE".into());}
                    claims.push(Claim{point,value:terminal.value});roles.push(RoleProof{role,bytes});mark(stage,"end");
                }
                (roles,<[Claim;7]>::try_from(claims).map_err(|_|"generic37 producer roster")?,
                    context.public_bytes.clone(),context.corpus_id)
            }; // Unique producer Consumer/context dropped before opening.
            mark("producer","end");mark("opening","begin");
            let common=opening_batch::Statement {log_n:22,setup_id:setup.id,commitment:committed.commitment,
                corpus_id:Some(corpus_id),claims:claims.clone()};
            let (proof,_,_)=opening_batch::prove(&source,&committed,&setup,&common)?;
            let batch=opening_batch::encode_proof(&proof,22)?;
            if batch.len()!=31581 || opening_batch::encode_proof(&opening_batch::decode_proof(&batch,22)?,22)?!=batch {
                return Err("generic37 producer common codec".into());
            }
            mark("opening","end");
            (Artifact{commitment,roles,batch},claims,statement)
        }; // ALL packed handles/setup/rows/prover/context heaps gone.
        drop(public); // No producer Public crosses into fresh verification.
        if statement.len()+artifact.commitment.len()+artifact.batch.len()
            +artifact.roles.iter().map(|p|p.bytes.len()).sum::<usize>()!=66133 {return Err("generic37 package total".into());}
        mark("export","begin");
        write_new(&output.join("statement.bin"),&statement)?;write_new(&output.join("commitment.bin"),&artifact.commitment)?;
        for packet in &artifact.roles {write_new(&output.join(format!("role-{}.gkr",packet.role)),&packet.bytes)?;}
        write_new(&output.join("openings.bin"),&artifact.batch)?;
        let pins=generic37_snapshot(&output)?;drop(artifact);drop(statement);
        mark("export","end");mark("receiver","begin");
        let (statement,artifact)=generic37_load(&output,&pins)?;
        let received=verify_historical_tiny_bytes(&statement,&artifact)?;
        if received!=claims {return Err("generic37 producer/receiver claims".into());}
        mark("receiver","end");mark("controls","begin");
        let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
        let decoded=generic37_public(crate::historical_prefix_public::decode_tiny_candidate(&statement)?);
        let retained_decoded=generic37_public(crate::historical_prefix_public::decode_tiny_candidate(&legacy_statement)?);
        let same_c=artifact.commitment==legacy.commitment;
        if !same_c || statement!=legacy_statement {return Err("generic37 isolated mode fixture identity".into());}
        // Honest retained packets verified first; one legacy graph, then fully dropped.
        {
            let consumer=Consumer::new(&retained_decoded)?;let context=ProofContext::new(&consumer)?;
            context.verify(&legacy,&key).map_err(|e|format!("generic37 retained legacy positive: {e:?}"))?;
            for role in 0..7 {target_gkr_rejection(context.verify_role(&artifact.roles[role],&key,&artifact.commitment),role,"historical in legacy");}
        }
        {
            let consumer=Consumer::new(&decoded)?;let context=ProofContext::historical_tiny(&consumer,&statement)?;
            let verified=context.verified_roles(&artifact,&key).map_err(|e|format!("generic37 fresh controls positive: {e:?}"))?;
            for role in 0..7 {
                let actual=context.transcript(role,&key,&artifact.commitment);
                let literal=fresh_prefix(&context,&decoded,role,&key,&artifact.commitment,PrefixFault::NoFault)?;
                if prefix_snapshot(&actual)!=prefix_snapshot(&literal) {return Err("generic37 historical prefix differential".into());}
                target_gkr_rejection(context.verify_role(&legacy.roles[role],&key,&legacy.commitment),role,"legacy in historical");
                let mut changed=artifact.roles[role].clone();
                let mut proof=gkr::decode_dimensions(&[context.geometry.input_bits[role]],&changed.bytes)?;
                proof.layers[0].rounds[0][0]+=Fr::one();changed.bytes=gkr::encode_proof(&proof)?;
                let failure=context.verify_role(&changed,&key,&artifact.commitment).err().ok_or("generic37 corrupt GKR accepted")?;
                if failure.stage!=RoleStage::Gkr || failure.message!=GkrError::SumcheckIdentity.to_string()
                    || !failure.observation.canonical_decode || !failure.observation.verifier_entered {
                    return Err("generic37 corrupt GKR attribution".into());
                }
            }
            // Existing exact terminal/final-PCS and derived-claim mutations, no second graph.
            if common_binding_controls(&context,&artifact,&key,&verified)!=32 {return Err("generic37 common controls census".into());}
            if structural_binding_controls(&context,&artifact,&key)!=9 {return Err("generic37 structural controls census".into());}
        }
        // Freshly reconstructed candidate relations, then replay old packets:
        // this is FS binding evidence, distinct from fresh-witness residuals.
        for field in 0..5 {
            let mut changed=decoded.clone();
            match field {0=>changed.root[0]^=1,1=>changed.total[0]^=1,2=>changed.tip[0]^=1,
                3=>changed.tip_time^=1,_=>changed.headers=if headers==3 {4}else{3}}
            let frame=literal_public_bytes(&changed)?;
            let candidate=generic37_public(crate::historical_prefix_public::decode_tiny_candidate(&frame)?);
            let consumer=Consumer::new(&candidate)?;let context=ProofContext::historical_tiny(&consumer,&frame)?;
            for role in 0..7 {target_gkr_rejection(context.verify_role(&artifact.roles[role],&key,&artifact.commitment),role,"single candidate field");}
        }
        // A separately retained canonical same-key C; no synthetic whitelist or
        // claim that the recomputed honest C is distinct from its legacy C.
        if foreign_c==artifact.commitment {
            return Err("generic37 foreign canonical C fixture".into());
        }
        {
            let consumer=Consumer::new(&decoded)?;let context=ProofContext::historical_tiny(&consumer,&statement)?;
            for role in 0..7 {target_gkr_rejection(context.verify_role(&artifact.roles[role],&key,&foreign_c),role,"valid foreign C");}
        }
        // No accepted atomic result may survive a late common-proof failure.
        let mut changed=artifact.clone();let mut common=opening_batch::decode_proof(&changed.batch,22)?;
        common.terminal+=Fr::one();changed.batch=opening_batch::encode_proof(&common,22)?;
        let mut accepted=None;
        if let Ok(result)=verify_historical_tiny_bytes(&statement,&changed) {accepted=Some(result);}
        if accepted.is_some() {return Err("generic37 late atomic rollback".into());}
        mark("controls","end");mark("custody","begin");
        if generic37_snapshot(&output)?!=pins || generic37_snapshot(&legacy_dir)?!=legacy_pins
            || generic37_snapshot(&foreign_dir)?!=foreign_pins {
            return Err("generic37 public custody drift".into());
        }
        if generic37_bound_read(&foreign_dir,"commitment.bin",&foreign_pins)?!=foreign_c {
            return Err("generic37 foreign C custody drift".into());
        }
        std::fs::remove_file(&private_path).map_err(|e|e.to_string())?; // Exact create-new private file, handles closed.
        mark("custody","end");
        let elapsed=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"generic37 elapsed overflow")?;
        let report=serde_json::json!({"schema":"generic37-historical-tiny-v1","result":"PASS","headers":headers,
            "mode":"historical_tiny_testonly","roles":7,"files":10,"public_bytes":66133,"statement_bytes":568,
            "gkr_bytes":33600,"commitment_bytes":384,"opening_bytes":31581,"quadratic_rounds":294,
            "producer_claims_equal":true,"sender_transcript_observed":false,"retained_legacy_positive":true,
            "same_commitment_as_retained":same_c,"mode_cross_rejections":14,"corrupt_gkr_rejections":7,
            "public_replay_rejections":35,"foreign_c_rejections":7,"structural_controls":9,
            "prefix_differentials":7,"common_controls":32,"atomic_rollback":true,"expected_public_in_receiver":false,
            "expected_c_in_receiver":false,"private_witness_in_receiver":false,"setup_in_receiver":false,
            "full_history":false,"production":false,"elapsed_ns":elapsed});
        let encoded=serde_json::to_string(&report).map_err(|e|e.to_string())?;
        if encoded.len()>16384 || elapsed>180_000_000_000 {return Err("generic37 diagnostic bound".into());}
        eprintln!("HISTORY_GENERIC37_STAGE complete end {elapsed}");
        println!("\nHISTORY_GENERIC37_REPORT {encoded}");Ok(())
    }));
    match operation {Ok(Ok(()))=>(), other=>{
        let message=match other {Ok(Err(e))=>e,_=>"fixture assertion/panic".into()};
        eprintln!("HISTORY_GENERIC37_HOLD {} {} {}",location.get(),started.elapsed().as_nanos(),
            message.chars().filter(|c|c.is_ascii_graphic() || *c==' ').take(240).collect::<String>());
        panic!("generic37 historical tiny HOLD");
    }}
}

#[test]
#[ignore="fresh historical N3 proof/export/fresh byte consumer; separate bounded admission"]
fn generic37_historical_n3_join(){generic37_join(3);}

#[test]
#[ignore="fresh historical N4 proof/export/fresh byte consumer; separate bounded admission"]
fn generic37_historical_n4_join(){generic37_join(4);}

fn generic37_rows(circuit: &Circuit, input: &[Fr]) -> Result<Vec<usize>, String> {
    if input.len() != circuit.input_len || circuit.terms.len() >= 1 << 20 {
        return Err("generic37 residual extent".into());
    }
    sparse::validate(circuit, 0).map_err(|e| e.to_string())?;
    let mut order: Vec<usize> = (0..circuit.terms.len()).collect();
    order.sort_unstable_by_key(|&i| circuit.terms[i].row);
    let mut failed = Vec::new(); let mut row = None; let mut value = Fr::zero();
    for index in order {
        let term = &circuit.terms[index];
        if row != Some(term.row) {
            if let Some(previous) = row { if !value.is_zero() { failed.push(previous); } }
            row = Some(term.row); value = Fr::zero();
        }
        value += term.gate.evaluate(input);
    }
    if let Some(previous) = row { if !value.is_zero() { failed.push(previous); } }
    Ok(failed)
}

fn generic37_reference(context: &ProofContext<'_>) -> Circuit {
    // One small legacy height object borrows the SAME parent; no second graph.
    let legacy = HeightWork::new(&context.consumer.parent).unwrap();
    let mut circuit = legacy.circuit().unwrap();
    circuit.terms.reserve_exact(context.term_count()-circuit.terms.len());
    circuit.row_count = 1 << context.geometry.row_bits[4];
    for owner in 0..context.geometry.slots {
        context.daa.visit_owner_terms(owner as u64, |mut term| {
            term.row += context.geometry.daa_row_base; circuit.terms.push(term); Ok(())
        }).unwrap();
    }
    circuit
}

#[test]
fn generic37_codec_and_collector() {
    use crate::historical_prefix_public::decode_tiny_candidate;
    let mut rejected = 0usize;
    for n in [3u64,4] {
        let public = Public { headers:n, root:[17;32], total:[23;28], tip:[31;32], tip_time:-42 };
        let bytes = literal_public_bytes(&public).unwrap(); assert_eq!(bytes.len(), 568);
        assert_eq!(literal_public_bytes(&generic37_public(decode_tiny_candidate(&bytes).unwrap())).unwrap(), bytes);
        let policy = public.profile().unwrap().len();
        let mut faults = vec![(0,"generic37 profile policy"), (policy,"generic37 genesis policy"),
            (policy+32,"generic37 parent anchor"), (policy+64,"generic37 tiny header policy"),
            (policy+72,"generic37 cheap geometry"), (policy+80,"generic37 cheap geometry"),
            (policy+88,"generic37 cheap geometry")];
        let mut cursor = policy + 196;
        for role in 0..7 {
            faults.extend([(cursor,"generic37 role order"), (cursor+8,"generic37 role tag extent"),
                (cursor+16,"generic37 role tag"), (cursor+16+ROLES[role].len(),"generic37 role geometry"),
                (cursor+24+ROLES[role].len(),"generic37 role geometry")]);
            cursor += 32 + ROLES[role].len();
        }
        assert_eq!(cursor, 568);
        for (offset, error) in faults {
            let mut changed = bytes.clone();
            if offset == policy+64 { changed[offset] = 5; } else { changed[offset] ^= 128; }
            let before = next36_constructions();
            assert_eq!(decode_tiny_candidate(&changed).err().unwrap(), error);
            assert_eq!(next36_constructions(), before); rejected += 1;
        }
        for length in [0,567,569] {
            let mut changed = bytes.clone(); changed.resize(length,0);
            assert_eq!(decode_tiny_candidate(&changed).err().unwrap(), "generic37 frame extent"); rejected += 1;
        }
        let mut pairing = bytes.clone(); pairing[policy+64] = if n==3 {4} else {3};
        assert_eq!(decode_tiny_candidate(&pairing).err().unwrap(), "generic37 profile/header pairing"); rejected += 1;
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::historical_tiny(&consumer, &bytes).unwrap();
        assert_eq!(context.height.circuit().err().unwrap(), "generic height/work requires owner streaming, not materialization");
        let mut actual = context.tiny_historical_composite().unwrap();
        let reference = generic37_reference(&context);
        assert!(actual==reference,"generic37 ordered collector mismatch");
        assert_eq!(actual.terms.len(), if n==3 {329122} else {330050});
        let (r,u,v) = (dense(22,3),dense(22,29),dense(22,71));
        let mut independent = [Fr::zero();4];
        for term in &reference.terms {
            let weight = adapters35_eq(&r,term.row)*adapters35_eq(&u,term.gate.left)*adapters35_eq(&v,term.gate.right);
            for (sum,c) in independent.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]) { *sum += weight*c; }
        }
        assert_eq!(context.composite_coefficients(&r,&u,&v).unwrap(), independent);
        // Each occurrence/coordinate/channel fault is tested against the retained reference.
        for field in 0..9 {
            let last=if field==0 {actual.terms.pop()} else {None};
            match field { 0=>(), 1=>actual.terms[1]=actual.terms[0].clone(),
                2=>actual.terms[0].row ^=1, 3=>actual.terms[0].gate.left ^=1,
                4=>actual.terms[0].gate.right ^=1, 5=>actual.terms[0].gate.c0 +=Fr::one(),
                6=>actual.terms[0].gate.c1 +=Fr::one(), 7=>actual.terms[0].gate.c2 +=Fr::one(),
                _=>actual.terms[0].gate.c3 +=Fr::one() }
            assert!(actual!=reference,"generic37 occurrence mutation {field}"); rejected += 1;
            if let Some(term)=last {actual.terms.push(term);}
            actual.terms[0]=reference.terms[0].clone();actual.terms[1]=reference.terms[1].clone();
            assert!(actual==reference,"generic37 restored collector {field}");
        }
        drop(actual); drop(reference);
        let mut observed = PreparationObservation::default();
        assert_eq!(ProofContext::prepare_prefix(&consumer, context.relation_refs(), &mut observed).err().unwrap(),
            "next36 legacy binding mode"); assert!(!observed.transcript_created);
        let mut bad_count = context.relation_refs(); bad_count.composite_terms -=1;
        assert_eq!(ProofContext::prepare_prefix_mode(&consumer,bad_count,HeightBinding::HistoricalDiagnostic,&mut observed)
            .err().unwrap(),"composite census differs from admitted profile"); assert!(!observed.transcript_created);
        // Canonical frame from a different candidate cannot reach prefix construction.
        let mut changed = bytes.clone(); changed[policy+96] ^=1;
        assert_eq!(ProofContext::historical_tiny(&consumer,&changed).err().unwrap(),"generic37 candidate identity");
    }
    assert_eq!(rejected, 110);
    // Real loader gates, with all other transport fields valid. Synthetic
    // bytes are not proofs; no negative public artifact is exported.
    let pins:Vec<_>=GENERIC37_MEMBERS.iter().map(|(name,size)|
        (name.to_string(),layout::hash_bytes(&vec![0u8;*size]))).collect();
    generic37_pin_roster(&pins).unwrap();let mut custody_rejections=0;
    for (name,size) in GENERIC37_MEMBERS {
        let mut bytes=vec![0u8;size];generic37_loaded_member(&pins,name,&bytes).unwrap();
        bytes[size-1]^=1;
        assert_eq!(generic37_loaded_member(&pins,name,&bytes).err().unwrap(),"generic37 loaded member digest");
        bytes[size-1]^=1;bytes.pop();
        assert_eq!(generic37_loaded_member(&pins,name,&bytes).err().unwrap(),"generic37 loaded member extent");
        bytes.push(0);bytes.push(0);
        assert_eq!(generic37_loaded_member(&pins,name,&bytes).err().unwrap(),"generic37 loaded member extent");
        custody_rejections+=3;
    }
    for fault in 0..5 {
        let mut changed=pins.clone();
        match fault {0=>{changed.pop();},1=>changed.push(pins[0].clone()),2=>changed[1]=pins[0].clone(),
            3=>changed.swap(0,1),_=>changed[0].0="unknown.bin".into()}
        assert_eq!(generic37_pin_roster(&changed).err().unwrap(),"generic37 loaded pin roster");custody_rejections+=1;
    }
    for directory in [false,true] {
        generic37_type(!directory,directory,false,0,directory).unwrap();
        for fault in 0..3 {
            let (file,dir,link,attrs)=match fault {0=>(directory,!directory,false,0),
                1=>(!directory,directory,true,0),_=>(!directory,directory,false,0x400)};
            assert_eq!(generic37_type(file,dir,link,attrs,directory).err().unwrap(),"generic37 public type/reparse");
            custody_rejections+=1;
        }
    }
    assert_eq!(custody_rejections,41);
}

#[test]
fn generic37_fresh_public_residuals() {
    // Rebuild an altered header's hash/serializer/order first: only the enabled
    // code-owned genesis boundary rejects, rather than a stale hash assignment.
    {
        use ergo_header_core::PowSolution;
        let mut header = witness::retained_headers_n(3).unwrap().remove(0);
        match &mut header.pow { PowSolution::V2{nonce,..}|PowSolution::V1{nonce,..}=>nonce[0]^=1 }
        let fields = crate::serializer::Fields::from_header(&header).unwrap();
        let mut joined = crate::header_order::build(Some(&fields)).unwrap();
        crate::header_order::assign_order(&mut joined,&fields,0,0,true).unwrap();
        let input = joined.base.base.input.as_ref().unwrap();
        let rows = generic37_rows(&joined.base.base.boundary,input).unwrap();
        assert!(!rows.is_empty() && rows.iter().all(|r|joined.genesis_rows.contains(r)));
    }
    // Independently valid metadata endpoint, with one serializer/order alias stale.
    {
        let header = witness::retained_headers_n(3).unwrap().remove(0);
        let fields = crate::serializer::Fields::from_header(&header).unwrap();
        let mut joined = crate::header_order::build(Some(&fields)).unwrap();
        crate::header_order::assign_order(&mut joined,&fields,0,0,true).unwrap();
        joined.base.base.input.as_mut().unwrap()[crate::header_order::ORDER_OFFSET+288+5] =
            Fr::one()-joined.base.base.input.as_ref().unwrap()[crate::header_order::ORDER_OFFSET+288+5];
        let input=joined.base.base.input.as_ref().unwrap();
        assert_eq!(generic37_rows(&joined.base.base.boundary,input).unwrap(),vec![joined.alias_rows.start+4]);
        assert!(crate::header_order::metadata_relation(1,header.timestamp^(1i64<<5)).unwrap()
            .residuals(input).unwrap().iter().all(Zero::is_zero));
    }
    let honest = witness::build(&witness::retained_headers_n(3).unwrap()).unwrap();
    let public = Public { headers:3,root:honest.root,total:honest.total,tip:honest.tip,tip_time:honest.tip_time };
    for field in 0..5 {
        let mut changed=public.clone();
        let role=match field {0=>{changed.root[0]^=1;2},1=>{changed.total[0]^=1;2},
            2=>{changed.tip[0]^=1;5},3=>{changed.tip_time^=1;6},_=>{changed.headers=4;4}};
        // Fresh semantic public/context; no comparison with fixture expected().
        let bytes=literal_public_bytes(&changed).unwrap();
        let decoded=generic37_public(crate::historical_prefix_public::decode_tiny_candidate(&bytes).unwrap());
        let consumer=Consumer::new(&decoded).unwrap();
        let context=ProofContext::historical_tiny(&consumer,&bytes).unwrap();
        let circuit=if role==4 {context.tiny_historical_composite().unwrap()} else {context.small_circuit(role).unwrap()};
        let failed=generic37_rows(&circuit,&honest.values).unwrap();
        assert!(!failed.is_empty(),"fresh semantic field {field}, enforcing role {role}");
        let prefix=context.transcript(role,&verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap(),&[0;384]);
        assert_eq!((prefix.challenges(),prefix.raw_queries()),(0,0));
    }
    let bytes=literal_public_bytes(&public).unwrap();
    let consumer=Consumer::new(&public).unwrap();let context=ProofContext::historical_tiny(&consumer,&bytes).unwrap();
    for role in [2,4,5,6] {
        let circuit=if role==4 {context.tiny_historical_composite().unwrap()} else {context.small_circuit(role).unwrap()};
        assert!(generic37_rows(&circuit,&honest.values).unwrap().is_empty(),"restored positive role {role}");
    }
}

// Independent old-profile oracle. Production/normal consumer code never reads these.
const INPUT_BITS: [usize; 7] = [22, 22, 22, 15, 22, 22, 22];
const ROW_BITS: [usize; 7] = [23, 21, 21, 16, 22, 11, 14];
const DAA_ROW_BASE: usize = 1 << 21;

fn literal_public_bytes(public: &Public) -> Result<Vec<u8>, String> {
    let mut bytes = public.profile()?.to_vec();
    bytes.extend(crate::header_order::MAINNET_GENESIS); bytes.extend([0u8; 32]);
    for n in [public.headers, 4, 2, 22] { bytes.extend(n.to_le_bytes()); }
    bytes.extend(public.root); bytes.extend(public.total); bytes.extend(public.tip);
    bytes.extend(public.tip_time.to_le_bytes());
    for role in 0..7 {
        bytes.extend((role as u64).to_le_bytes());
        bytes.extend((ROLES[role].len() as u64).to_le_bytes()); bytes.extend(ROLES[role]);
        bytes.extend((INPUT_BITS[role] as u64).to_le_bytes()); bytes.extend((ROW_BITS[role] as u64).to_le_bytes());
    }
    Ok(bytes)
}

fn literal_composite_binding(context: &ProofContext<'_>, t: &mut Transcript) {
    t.append_bytes(b"height-daa-composition", b"complete-height-and-four-daa-lanes-v2");
    for n in [2u64, context.consumer.public.headers, 22, 22, 8, 21, 0, 1, 13] {
        t.append_u64(b"height-daa-fixed-dimension", n);
    }
    t.append_u64(b"height-daa-row-base", 1 << 21);
    let terms = match context.consumer.public.headers { 3 => 329122, 4 => 330050, _ => panic!("literal profile") };
    t.append_u64(b"height-daa-total-terms", terms);
    context.height.bind(t); context.daa.bind(t);
}

fn reject_geometry(context: &ProofContext<'_>, geometry: &Geometry, expected: &str) {
    let mut observation = PreparationObservation::default();
    let error = match ProofContext::prepare_prefix(context.consumer,
        RelationRefs { geometry, ..context.relation_refs() }, &mut observation) {
        Err(error) => error, Ok(_) => panic!("invalid geometry reached a transcript"),
    };
    assert_eq!(error, expected);
    assert!(!observation.transcript_created);
    assert_eq!((observation.challenges, observation.queries), (0, 0));
}

#[test]
fn geometry34_boundaries() {
    let mut n3_geometry = None;
    for headers in [3u64, 4] {
        let public = Public::native(headers).unwrap();
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        let g = &context.geometry;
        assert_eq!((g.headers, g.slot_log, g.slots, g.common_input), (headers, 2, 4, 22));
        assert_eq!(g.input_bits, INPUT_BITS); assert_eq!(g.row_bits, ROW_BITS);
        assert_eq!(g.bank_bits, 4);
        assert_eq!(Geometry::domain(g.bank_bits).unwrap() * layout::CORE, layout::WIDTH);
        assert_eq!((g.height_row, g.daa_row, g.daa_row_base), (8, 21, 1 << 21));
        assert_eq!(context.public_bytes, literal_public_bytes(&public).unwrap());
        let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
        // Prefix-only fixture; actual retained GKR/common positives remain separate gates.
        for role in 0..7 {
            let actual = context.transcript(role, &key, &[0u8; 384]);
            let literal = fresh_prefix(&context, &public, role, &key, &[0u8; 384], PrefixFault::NoFault).unwrap();
            assert_eq!(prefix_snapshot(&actual), prefix_snapshot(&literal));
            assert_eq!((actual.challenges(), actual.raw_queries()), (0, 0));
        }
        let mut faults = Vec::new();
        for role in 0..7 {
            let mut changed = g.clone(); changed.input_bits[role] += 1;
            faults.push((changed, format!("geometry role {role} input mismatch")));
            let mut changed = g.clone(); changed.row_bits[role] += 1;
            faults.push((changed, format!("geometry role {role} row mismatch")));
        }
        for fault in 0..10 {
            let mut changed = g.clone();
            let error = match fault {
                0 => { changed.headers += 1; "geometry layout headers mismatch" }
                1 => { changed.slot_log += 1; "geometry layout H mismatch" }
                2 => { changed.slots += 1; "geometry layout slots mismatch" }
                3 => { changed.common_input += 1; "geometry common input mismatch" }
                4 => { changed.height_row += 1; "geometry height split mismatch" }
                5 => { changed.daa_row += 1; "geometry DAA split mismatch" }
                6 => { changed.daa_row_base += 1; "geometry DAA base mismatch" }
                7 => { changed.point_local_input += 1; "geometry point local mismatch" }
                8 => { changed.point_local_row += 1; "geometry point local mismatch" }
                _ => { changed.bank_bits += 1; "geometry core bank bits mismatch" }
            };
            faults.push((changed, error.to_string()));
        }
        assert_eq!(faults.len(), 24);
        for (changed, error) in faults { reject_geometry(&context, &changed, &error); }
        let mut changed = g.clone(); changed.slots += 1;
        assert_eq!(public.bytes_with_geometry(&changed).err().unwrap(), "geometry public H/slots mismatch");
        if headers == 3 { n3_geometry = Some(g.clone()); }
        else {
            let public3 = Public::native(3).unwrap();
            assert_eq!(public3.bytes_with_geometry(g).err().unwrap(), "geometry public headers mismatch");
            assert_eq!(public.bytes_with_geometry(n3_geometry.as_ref().unwrap()).err().unwrap(), "geometry public headers mismatch");
        }
        // Exact occurrence order and coefficients, not merely a conserved count.
        let circuit = context.composite_circuit().unwrap();
        let height = context.height.circuit().unwrap();
        assert_eq!(&circuit.terms[..height.terms.len()], height.terms.as_slice());
        let mut cursor = height.terms.len();
        for owner in 0..4 {
            context.daa.visit_owner_terms(owner, |term| {
                let actual = &circuit.terms[cursor];
                assert_eq!(actual.row, (1 << 21) + term.row); assert_eq!(actual.gate, term.gate);
                cursor += 1; Ok(())
            }).unwrap();
        }
        assert_eq!(cursor, circuit.terms.len());
        assert_eq!(cursor, if headers == 3 { 329122 } else { 330050 });
    }
    assert_eq!(Geometry::domain(usize::BITS as usize).err().unwrap(), "geometry shift overflow");
    assert_eq!(Geometry::domain(usize::MAX).err().unwrap(), "geometry shift overflow");
    assert_eq!(Geometry::log(0).err().unwrap(), "geometry non-power-of-two domain");
    assert_eq!(Geometry::log(3).err().unwrap(), "geometry non-power-of-two domain");
    let mut overflow = n3_geometry.unwrap(); overflow.input_bits[0] = usize::MAX;
    assert_eq!(overflow.proof_bytes(0).err().unwrap(), "geometry proof extent overflow");
    assert_eq!(overflow.proof_bytes(7).err().unwrap(), "geometry role index");
    for n in [2, 5] {
        assert_eq!(Geometry::profile_terms(n).err().unwrap(), "geometry unsupported profile terms");
        let mut public = Public::native(3).unwrap(); public.headers = n;
        assert_eq!(Consumer::new(&public).err().unwrap(), "common prefix requires N3 or N4");
    }
    // Genuine foreign layouts share final widths; their N/H still must agree.
    for fault in 0..4 {
        let public = Public::native(3).unwrap();
        let mut consumer = Consumer::new(&public).unwrap();
        if fault < 2 {
            consumer.adjacency = HeaderAdjacencyLayout::compile(if fault == 0 {4} else {3},
                if fault == 0 {2} else {3}, [0; 32], public.tip).unwrap();
        } else {
            consumer.metadata = HeaderMetadataOrderLayout::compile(if fault == 2 {4} else {3},
                if fault == 2 {2} else {3}, public.tip_time).unwrap();
        }
        let error = match ProofContext::new(&consumer) { Err(e) => e, Ok(_) => panic!("foreign layout accepted") };
        assert_eq!(error, if fault % 2 == 0 { "geometry layout history mismatch" } else { "geometry layout owner mismatch" });
    }
}

#[test]
fn geometry34_h3_shape_only() {
    // No admitted Consumer/ProofContext, key, setup, witness or proof is constructed.
    let public = Public { headers: 5, root: [0; 32], total: [0; 28], tip: [0; 32], tip_time: 0 };
    assert!(public.profile().is_err()); assert!(Geometry::profile_terms(5).is_err());
    let consumer = Consumer {
        public: public.clone(),
        parent: WorkTreeHistoryPlan::compile(5, 3, public.root, public.total).unwrap(),
        adjacency: HeaderAdjacencyLayout::compile(5, 3, [0; 32], public.tip).unwrap(),
        metadata: HeaderMetadataOrderLayout::compile(5, 3, public.tip_time).unwrap(),
        points: point_membership::build().unwrap(), point_template: String::new(),
    };
    let parts = RelationParts::compile(consumer.layout_refs(), HeightBinding::HistoricalDiagnostic).unwrap();
    let geometry = &parts.geometry;
    assert_eq!((geometry.headers, geometry.slot_log, geometry.slots, geometry.common_input), (5, 3, 8, 23));
    assert_eq!(geometry.bank_bits, 4); assert_ne!(geometry.bank_bits, geometry.slots);
    assert_eq!(geometry.input_bits, [23, 23, 23, 16, 23, 23, 23]);
    // N5 has four leaves/two levels: ten fixed B1 families plus four child
    // families, then six roster additions. Twenty tags need five bits;
    // local row14+H3 plus those five gives role2 row22, independently.
    assert_eq!(consumer.parent.topology().families.len(), 14);
    assert_eq!(geometry.row_bits, [24, 22, 22, 17, 23, 12, 15]);
    assert_eq!((geometry.height_row, geometry.daa_row, geometry.daa_row_base), (9, 22, 1 << 22));
    assert_ne!(geometry.input_bits, INPUT_BITS);
    let mut observation = PreparationObservation::default();
    let error = match ProofContext::prepare_prefix(&consumer, parts.refs(), &mut observation) {
        Err(e) => e, Ok(_) => panic!("shape-only profile reached transcript"),
    };
    assert_eq!(error, "geometry unsupported profile terms");
    assert!(!observation.transcript_created); assert_eq!((observation.challenges, observation.queries), (0, 0));
}

fn dense(bits: usize, seed: u64) -> Vec<Fr> {
    (0..bits)
        .map(|bit| Fr::from(seed + 17 * bit as u64))
        .collect()
}

fn enumerate(circuit: &Circuit, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let rows = gkr::eq_weights(r);
    let left = gkr::eq_weights(u);
    let right = gkr::eq_weights(v);
    let mut result = [Fr::zero(); 4];
    for term in &circuit.terms {
        let weight = rows[term.row] * left[term.gate.left] * right[term.gate.right];
        for (value, coefficient) in
            result
                .iter_mut()
                .zip([term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3])
        {
            *value += weight * coefficient;
        }
    }
    result
}

fn residuals(circuit: &Circuit, input: &[Fr]) -> Vec<Fr> {
    assert_eq!(input.len(), circuit.input_len);
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        rows[term.row] += term.gate.evaluate(input);
    }
    rows
}

fn geometry(headers: u64) -> Result<(), String> {
    let public = Public::native(headers)?;
    let consumer = Consumer::new(&public)?;
    let context = ProofContext::new(&consumer)?;
    let circuit = context.composite_circuit()?;
    let height = context.height.circuit()?;
    assert_eq!((circuit.input_len, circuit.row_count), (1 << 22, 1 << 22));
    assert_eq!(
        circuit.terms.len(),
        if headers == 3 { 329122 } else { 330050 }
    );
    assert_eq!(
        &circuit.terms[..height.terms.len()],
        height.terms.as_slice()
    );
    assert!(circuit.terms[..height.terms.len()]
        .iter()
        .all(|t| t.row < 256));
    assert!(circuit.terms[height.terms.len()..]
        .iter()
        .all(|t| t.row >= DAA_ROW_BASE));
    let mut cursor = height.terms.len();
    for owner in 0..4 {
        context.daa.visit_owner_terms(owner, |term| {
            let actual = &circuit.terms[cursor];
            assert_eq!(actual.row, DAA_ROW_BASE + term.row);
            assert_eq!(actual.gate, term.gate); // Keep global endpoints, including GLOBAL0.
            cursor += 1;
            Ok(())
        })?;
    }
    assert_eq!(cursor, circuit.terms.len());
    let r = dense(22, 3);
    let u = dense(22, 29);
    let v = dense(22, 71);
    let expected = enumerate(&circuit, &r, &u, &v);
    assert!(!expected[1].is_zero(), "oracle must not be vacuous");
    assert_eq!(context.composite_coefficients(&r, &u, &v)?, expected);
    for axis in 0..3 {
        for wrong_length in [21usize, 23] {
            let mut points = [r.clone(), u.clone(), v.clone()];
            points[axis] = dense(wrong_length, 113);
            assert!(context
                .composite_coefficients(&points[0], &points[1], &points[2])
                .is_err());
        }
    }
    // Both outer Boolean slices and the unused height padding are explicit.
    let mut padded = r.clone();
    padded[21] = Fr::zero();
    padded[8] = Fr::one();
    assert_eq!(
        context.composite_coefficients(&padded, &u, &v)?,
        [Fr::zero(); 4]
    );
    let mut lower = vec![Fr::zero(); 22];
    lower[..8].clone_from_slice(&r[..8]);
    assert_eq!(
        context.composite_coefficients(&lower, &u, &v)?,
        context.height.coefficients(&r[..8], &u, &v)?
    );
    let mut upper = r.clone();
    upper[21] = Fr::one();
    assert_eq!(
        context.composite_coefficients(&upper, &u, &v)?,
        context.daa.coefficients(&r[..21], &u, &v)?
    );

    // No short release applies in this authentic prefix. Compare exact terms,
    // retaining the parent's existing work-tree retirement and padding.
    for owner in 0..4 {
        let mut parent = Vec::new();
        let parent_counts = consumer.parent.visit_slot_terms(owner, |t| {
            parent.push(t);
            Ok(())
        })?;
        let mut paired = Vec::new();
        let counts = context.daa.visit_header_terms(owner, |t| {
            paired.push(t);
            Ok(())
        })?;
        assert_eq!(parent, paired);
        assert_eq!(counts.emitted, parent_counts.emitted);
        assert_eq!((counts.omitted_mature_a4, counts.omitted_short_a4), (0, 0));
    }
    println!(
        "{}",
        serde_json::json!({"result":"PASS","headers":headers,"terms":circuit.terms.len(),"input_log":22,"row_log":22,"roles":7,"proof":false})
    );
    Ok(())
}

#[test]
fn n3_complete_height_daa_geometry_and_nonboolean_coefficients() {
    geometry(3).unwrap();
}
#[test]
fn n4_complete_height_daa_geometry_and_nonboolean_coefficients() {
    geometry(4).unwrap();
}

fn valid_witness(context: &ProofContext<'_>, public: &Public) -> Result<Vec<Fr>, String> {
    let witness = witness::build(&witness::retained_headers_n(public.headers as usize)?)?;
    if witness.root != public.root
        || witness.total != public.total
        || witness.tip != public.tip
        || witness.tip_time != public.tip_time
    {
        return Err("native authority and field witness disagree".into());
    }
    let circuit = context.composite_circuit()?;
    assert!(residuals(&circuit, &witness.values).iter().all(Fr::is_zero));
    Ok(witness.values)
}

#[test]
fn complete_relation_rejects_isolated_height_and_unused_daa_cell_faults() {
    let public = Public::native(4).unwrap();
    let consumer = Consumer::new(&public).unwrap();
    let context = ProofContext::new(&consumer).unwrap();
    let circuit = context.composite_circuit().unwrap();
    let mut input = valid_witness(&context, &public).unwrap();
    let height_wire = context.height.circuit().unwrap().terms[0].gate.left;
    let saved = input[height_wire];
    assert!(saved.is_zero() || saved.is_one());
    input[height_wire] = Fr::one() - saved;
    let failed = residuals(&circuit, &input);
    assert!(failed[..256].iter().any(|x| !x.is_zero()));
    assert!(failed[DAA_ROW_BASE..].iter().all(Fr::is_zero));
    drop(failed);
    let mut t = Transcript::new(b"complete-height-fault-v2");
    assert!(matches!(
        sparse::prove_with_binding(&circuit, &input, 0, &mut t, |t| context.bind_role(4, t)),
        Err(GkrError::NonzeroOutput)
    ));
    input[height_wire] = saved;
    let inactive = circuit
        .terms
        .iter()
        .find(|t| t.row >= DAA_ROW_BASE && t.gate.left == 663552 && t.gate.c1.is_one())
        .unwrap();
    assert!(input[inactive.gate.left].is_zero());
    input[inactive.gate.left] = Fr::one();
    let failed = residuals(&circuit, &input);
    assert!(failed[..DAA_ROW_BASE].iter().all(Fr::is_zero));
    assert!(!failed[inactive.row].is_zero());
    drop(failed);
    let mut t = Transcript::new(b"complete-inactive-fault-v2");
    assert!(matches!(
        sparse::prove_with_binding(&circuit, &input, 0, &mut t, |t| context.bind_role(4, t)),
        Err(GkrError::NonzeroOutput)
    ));
}

fn read_bounded(path: &Path, limit: usize) -> Result<Vec<u8>, String> {
    let file = File::open(path).map_err(|e| e.to_string())?;
    let mut bytes = Vec::new();
    file.take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > limit {
        return Err("prefix artifact exceeds fixed byte bound".into());
    }
    Ok(bytes)
}
fn read_exact(path: &Path, length: usize) -> Result<Vec<u8>, String> {
    let bytes = read_bounded(path, length)?;
    if bytes.len() != length {
        return Err("prefix artifact exact length mismatch".into());
    }
    Ok(bytes)
}
fn artifact_directory() -> Result<std::path::PathBuf, String> {
    std::env::var_os("NIPOPOW_COMMON_PREFIX_DIR")
        .map(std::path::PathBuf::from)
        .ok_or("missing persisted common artifact directory".into())
}
fn load_artifact(dir: &Path, context: &ProofContext<'_>) -> Result<Artifact, String> {
    let expected = &context.public_bytes;
    if read_exact(&dir.join("statement.bin"), expected.len())?.as_slice() != expected.as_slice() {
        return Err("persisted statement differs from native expected public".into());
    }
    load_artifact_body(dir, &context.geometry)
}
fn load_artifact_body(dir: &Path, geometry: &Geometry) -> Result<Artifact, String> {
    let commitment = read_bounded(&dir.join("commitment.bin"), 1024)?;
    pcs::decode_commitment(&commitment)?;
    let mut roles = Vec::with_capacity(7);
    for role in 0..7 {
        roles.push(RoleProof {
            role,
            bytes: read_exact(
                &dir.join(format!("role-{role}.gkr")),
                geometry.proof_bytes(role)?,
            )?,
        });
    }
    let batch = read_bounded(&dir.join("openings.bin"), 65536)?;
    opening_batch::decode_proof(&batch, geometry.common_input)?;
    Ok(Artifact {
        commitment,
        roles,
        batch,
    })
}

#[test]
#[ignore = "requires a fresh directory for bounded reader negative fixtures"]
fn bounded_reader_rejects_truncated_trailing_and_wrong_public_statements() {
    let output = std::env::var_os("NIPOPOW_COMMON_READER_DIR").unwrap();
    let dir = Path::new(&output);
    let public = Public::native(4).unwrap();
    let consumer = Consumer::new(&public).unwrap();
    let context = ProofContext::new(&consumer).unwrap();
    let bytes = context.public_bytes.clone();
    let path = dir.join("valid-statement.bin");
    write_new(&path, &bytes).unwrap();
    assert_eq!(read_exact(&path, bytes.len()).unwrap(), bytes);
    for kind in ["truncated", "trailing", "wrong-public"] {
        let sub = dir.join(kind);
        std::fs::create_dir(&sub).unwrap();
        let mut wrong = bytes.clone();
        let expected = match kind {
            "truncated" => {
                wrong.pop();
                "prefix artifact exact length mismatch"
            }
            "trailing" => {
                wrong.push(0);
                "prefix artifact exceeds fixed byte bound"
            }
            _ => {
                wrong[public.profile().unwrap().len() + 96] ^= 1;
                "persisted statement differs from native expected public"
            }
        };
        write_new(&sub.join("statement.bin"), &wrong).unwrap();
        assert_eq!(load_artifact(&sub, &context).err().unwrap(), expected);
    }
    assert!(read_bounded(&dir.join("missing.bin"), 1024).is_err());
}

#[test]
#[ignore = "requires pinned prior N4 public artifacts, no producer witness"]
fn legacy_n4_profile_artifacts_reject_against_the_complete_new_consumer() {
    let output = std::env::var_os("NIPOPOW_OLD_COMMON_PREFIX_DIR").unwrap();
    let dir = Path::new(&output);
    let public = Public::native(4).unwrap();
    // Independently encode the former fixed statement using today's native
    // expected anchors. The old file is checked for equality, not authority.
    let mut old = b"historical-prefix-n4-common-seven-v1".to_vec();
    old.extend(crate::header_order::MAINNET_GENESIS);
    old.extend([0u8; 32]);
    for n in [4u64, 4, 2, 22] {
        old.extend(n.to_le_bytes());
    }
    old.extend(public.root);
    old.extend(public.total);
    old.extend(public.tip);
    old.extend(public.tip_time.to_le_bytes());
    let mut roles = ROLES;
    roles[4] = b"height-numeric";
    let mut rows = ROW_BITS;
    rows[4] = 8;
    for i in 0..7 {
        old.extend((i as u64).to_le_bytes());
        old.extend((roles[i].len() as u64).to_le_bytes());
        old.extend(roles[i]);
        old.extend((INPUT_BITS[i] as u64).to_le_bytes());
        old.extend((rows[i] as u64).to_le_bytes());
    }
    assert_eq!(
        read_exact(&dir.join("statement.bin"), old.len()).unwrap(),
        old
    );
    let consumer = Consumer::new(&public).unwrap();
    let context = ProofContext::new(&consumer).unwrap();
    assert_ne!(old, context.public_bytes);
    let artifact = load_artifact_body(dir, &context.geometry).unwrap();
    let key =
        verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    assert_eq!(context.verify(&artifact, &key), Err(Reject::Role(0)));
}

#[test]
#[ignore = "requires persisted N4 public artifacts and a bounded fresh process"]
fn fresh_n4_consumer_replays_only_public_artifacts_and_native_authority() {
    let started = Instant::now();
    let public = Public::native(4).unwrap();
    phase("native-expected-public", started);
    let started = Instant::now();
    let consumer = Consumer::new(&public).unwrap();
    let context = ProofContext::new(&consumer).unwrap();
    let key =
        verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    phase("fresh-consumer-and-admitted-key", started);
    let started = Instant::now();
    let artifact = load_artifact(&artifact_directory().unwrap(), &context).unwrap();
    phase("bounded-public-artifact-decode", started);
    let started = Instant::now();
    assert_eq!(context.verify(&artifact, &key).unwrap().len(), 7);
    phase("fresh-seven-roles-and-one-opening-verify", started);
    println!(
        "{}",
        serde_json::json!({"result":"PASS","headers":4,"roles":7,"private_witness_read":false,"setup_generated":false,"full_history":false,"production":false})
    );
}

#[derive(Clone, Copy, Debug)]
enum Omission {
    Daa,
    Height,
    OuterTag,
}

fn semantic_omission(kind: Omission) -> Result<(), String> {
    let public = Public::native(4)?;
    let consumer = Consumer::new(&public)?;
    let context = ProofContext::new(&consumer)?;
    let complete = context.composite_circuit()?;
    let height_len = context.height.circuit()?.terms.len();
    let mut input = valid_witness(&context, &public)?;
    let mut mutant = complete.clone();
    match kind {
        Omission::Daa => {
            mutant.terms.truncate(height_len);
            assert!(input[663552].is_zero());
            input[663552] = Fr::one();
        }
        Omission::Height => {
            mutant.terms.drain(..height_len);
            let wire = complete.terms[0].gate.left;
            assert!(input[wire].is_zero() || input[wire].is_one());
            input[wire] = Fr::one() - input[wire];
        }
        Omission::OuterTag => {
            for term in &mut mutant.terms[height_len..] {
                term.row -= DAA_ROW_BASE;
            }
        }
    }
    assert_eq!((mutant.input_len, mutant.row_count), (1 << 22, 1 << 22));
    assert!(residuals(&mutant, &input).iter().all(Fr::is_zero));
    let full = residuals(&complete, &input);
    match kind {
        Omission::OuterTag => assert!(full.iter().all(Fr::is_zero)),
        _ => assert!(full.iter().any(|x| !x.is_zero())),
    }
    drop(full);
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    // Keep the genuine complete baseline's commitment and expected public
    // statement. These falsifiers exercise role wiring before any PCS opening.
    let commitment = read_bounded(&artifact_directory()?.join("commitment.bin"), 1024)?;
    pcs::decode_commitment(&commitment)?;
    let mut producer_t = context.transcript(4, &key, &commitment);
    let (proof, producer_terminal) =
        sparse::prove_with_binding(&mutant, &input, 0, &mut producer_t, |t| {
            context.bind_role(4, t)
        })
        .map_err(|e| e.to_string())?;
    let bytes = gkr::encode_proof(&proof)?;
    assert_eq!(bytes.len(), (7 * 22 + 3) * 32);
    let decoded = gkr::decode_dimensions(&[22], &bytes)?;
    let mut own_t = context.transcript(4, &key, &commitment);
    let own_terminal = gkr::verify_with_wiring(
        &[22],
        1 << 22,
        &decoded,
        &mut own_t,
        |t| context.bind_role(4, t),
        |_, r, u, v| Ok(enumerate(&mutant, r, u, v)),
    )
    .map_err(|e| {
        format!("mutant must verify against its independently enumerated relation: {e:?}")
    })?;
    assert_eq!(own_terminal.point, producer_terminal.point);
    assert_eq!(own_terminal.value, producer_terminal.value);
    let mut verifier_t = context.transcript(4, &key, &commitment);
    let rejection = gkr::verify_with_wiring(
        &[22],
        1 << 22,
        &decoded,
        &mut verifier_t,
        |t| context.bind_role(4, t),
        |_, r, u, v| {
            context
                .composite_coefficients(r, u, v)
                .map_err(|_| GkrError::InvalidWireIndex)
        },
    );
    assert!(
        matches!(rejection, Err(GkrError::TerminalExpression)),
        "semantic omission must fail at complete wiring: {rejection:?}"
    );
    let output = std::env::var_os("NIPOPOW_COMMON_MUTANT_DIR")
        .ok_or("missing fresh mutant artifact directory")?;
    let dir = Path::new(&output);
    write_new(&dir.join("mutant-role-4.gkr"), &bytes)?;
    write_new(&dir.join("expected-statement.bin"), &context.public_bytes)?;
    println!(
        "{}",
        serde_json::json!({"result":"PASS","omission":format!("{kind:?}"),"input_log":22,"row_log":22,"complete_terms":complete.terms.len(),"mutant_terms":mutant.terms.len(),"proof_bytes":bytes.len(),"complete_binding":true,"reject":"TerminalExpression","pcs_opening_produced":false,"full_history":false})
    );
    Ok(())
}

#[test]
#[ignore = "requires genuine N4 commitment, fresh mutant directory and bounded process"]
fn genuine_omitted_daa_proof_rejects_with_complete_binding() {
    semantic_omission(Omission::Daa).unwrap();
}
#[test]
#[ignore = "requires genuine N4 commitment, fresh mutant directory and bounded process"]
fn genuine_omitted_height_proof_rejects_with_complete_binding() {
    semantic_omission(Omission::Height).unwrap();
}
#[test]
#[ignore = "requires genuine N4 commitment, fresh mutant directory and bounded process"]
fn genuine_wrong_outer_tag_proof_rejects_with_complete_binding() {
    semantic_omission(Omission::OuterTag).unwrap();
}

// These alternatives exist only inside the private cfg(test) consumer module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PrefixFault {
    NoFault, ProfileDomain, SerializedProfile, Genesis, ParentAnchor, Owners,
    SlotLog, WitnessInputLog, SetupId, AppendedRoleIndex, AppendedRoleDomain,
    RosterOrdinal(usize), RosterDomain(usize), RosterInputLog(usize), RosterRowLog(usize),
}

fn prefix_faults() -> Vec<PrefixFault> {
    use PrefixFault::*;
    let mut faults = vec![ProfileDomain, SerializedProfile, Genesis, ParentAnchor, Owners,
        SlotLog, WitnessInputLog, SetupId, AppendedRoleIndex, AppendedRoleDomain];
    for member in 0..7 {
        faults.extend([RosterOrdinal(member), RosterDomain(member), RosterInputLog(member), RosterRowLog(member)]);
    }
    assert_eq!(faults.len(), 38);
    faults
}

pub(super) fn fresh_prefix(context: &ProofContext<'_>, public: &Public, role: usize,
    key: &verifier_key::AdmittedVerifierKey, commitment: &[u8], fault: PrefixFault)
    -> Result<Transcript, String> {
    use PrefixFault::*;
    let profile = public.profile()?;
    let mut domain = profile.to_vec();
    if fault == ProfileDomain { domain[0] ^= 1; }
    let mut serialized_profile = profile.to_vec();
    if fault == SerializedProfile { serialized_profile[0] ^= 1; }
    let mut bytes = serialized_profile;
    let mut genesis = crate::header_order::MAINNET_GENESIS;
    if fault == Genesis { genesis[0] ^= 1; }
    bytes.extend(genesis);
    let mut anchor = [0u8; 32];
    if fault == ParentAnchor { anchor[0] = 1; }
    bytes.extend(anchor);
    for (index, value) in [public.headers, 4, 2, 22].into_iter().enumerate() {
        let changed = match (index, fault) {
            (1, Owners) | (2, SlotLog) | (3, WitnessInputLog) => value + 1,
            _ => value,
        };
        bytes.extend(changed.to_le_bytes());
    }
    bytes.extend(public.root); bytes.extend(public.total); bytes.extend(public.tip);
    bytes.extend(public.tip_time.to_le_bytes());
    for member in 0..7 {
        let ordinal = member + usize::from(fault == RosterOrdinal(member));
        bytes.extend((ordinal as u64).to_le_bytes());
        let mut name = ROLES[member].to_vec();
        if fault == RosterDomain(member) { name[0] ^= 1; }
        bytes.extend((name.len() as u64).to_le_bytes()); bytes.extend(name);
        bytes.extend(((INPUT_BITS[member] + usize::from(fault == RosterInputLog(member))) as u64).to_le_bytes());
        bytes.extend(((ROW_BITS[member] + usize::from(fault == RosterRowLog(member))) as u64).to_le_bytes());
    }
    if fault == NoFault && bytes != public.bytes_with_geometry(&context.geometry)? { return Err("NoFault public encoding drift".into()); }
    let mut t = Transcript::new(&domain);
    t.append_bytes(b"public-statement-and-roster", &bytes);
    context.consumer.parent.bind(&mut t);
    context.consumer.adjacency.bind(&mut t);
    context.consumer.metadata.bind(&mut t);
    t.append_bytes(b"point-template", context.consumer.point_template.as_bytes());
    literal_composite_binding(context, &mut t);
    let mut setup_id = *key.id();
    if fault == SetupId { setup_id[0] ^= 1; }
    t.append_bytes(b"setup-id", &setup_id);
    t.append_bytes(b"commitment", commitment);
    t.append_u64(b"role-index", (role + usize::from(fault == AppendedRoleIndex)) as u64);
    let mut role_domain = ROLES[role].to_vec();
    if fault == AppendedRoleDomain { role_domain[0] ^= 1; }
    t.append_bytes(b"role-domain", &role_domain);
    if t.challenges() != 0 || t.raw_queries() != 0 { return Err("control prefix not fresh".into()); }
    Ok(t)
}

fn prefix_snapshot(t: &Transcript) -> ([u64; 3], Fr) {
    ([t.challenges(), t.raw_queries(), t.bytes_absorbed()],
        t.clone().try_challenge_scalar(b"candidate-binding-prefix-control-v1").unwrap())
}

fn target_gkr_rejection(result: Result<VerifiedRole, RoleFailure>, role: usize, case: &str) {
    let error = match result { Ok(_) => panic!("{case}: role {role} unexpectedly accepted"), Err(e) => e };
    assert_eq!(error.role, role, "{case}: {error:?}");
    assert_eq!(error.stage, RoleStage::Gkr, "{case}: {error:?}");
    assert!(error.observation.canonical_decode && error.observation.verifier_entered, "{case}: {error:?}");
    assert_eq!(error.observation.prefix_challenges, 0, "{case}: {error:?}");
    assert_eq!(error.observation.prefix_raw_queries, 0, "{case}: {error:?}");
    assert!(error.observation.prefix_bytes > 0 && !error.message.is_empty(), "{case}: {error:?}");
}

fn common_verification_rejection(result: Result<(), CommonFailure>, expected: Option<&str>) {
    match result {
        Err(CommonFailure::Verification(message)) => {
            if let Some(prefix) = expected { assert!(message.starts_with(prefix), "{message}"); }
        }
        other => panic!("expected common verifier rejection, got {other:?}"),
    }
}

fn common_binding_controls(context: &ProofContext<'_>, artifact: &Artifact,
    key: &verifier_key::AdmittedVerifierKey, verified: &VerifiedClaims) -> usize {
    use ark_ec::AffineRepr;
    use dory_pcs::backends::arkworks::ArkG1;
    context.verify_common(artifact, key, verified).unwrap();
    let mut count = 0;
    for role in 0..7 {
        for field in 0..4 {
            let mut changed = verified.clone();
            match field {
                0 => changed.claims[role].value += Fr::one(),
                1 => changed.claims[role].point[role % 22] += Fr::one(),
                2 => changed.claims.swap(role, (role + 1) % 7),
                _ => changed.claims[role] = changed.claims[(role + 1) % 7].clone(),
            }
            assert_ne!(changed.claims, verified.claims);
            common_verification_rejection(context.verify_common(artifact, key, &changed), None);
            count += 1;
        }
    }
    for field in 0..2 {
        let mut decoded = opening_batch::decode_proof(&artifact.batch, 22).unwrap();
        if field == 0 { decoded.terminal += Fr::one(); }
        else {
            let final_message = decoded.pcs.final_message.as_mut().expect("honest PCS final message");
            let generator = ArkG1(ark_bn254::G1Affine::generator().into_group());
            let replacement = if final_message.e1 != generator { generator }
                else { ArkG1(ark_bn254::G1Affine::generator() * Fr::from(2u64)) };
            assert!(!replacement.0.is_zero()); assert_ne!(replacement, final_message.e1);
            final_message.e1 = replacement;
        }
        let mut changed = artifact.clone();
        changed.batch = opening_batch::encode_proof(&decoded, 22).unwrap();
        let canonical = opening_batch::decode_proof(&changed.batch, 22).unwrap();
        assert_eq!(opening_batch::encode_proof(&canonical, 22).unwrap(), changed.batch);
        common_verification_rejection(context.verify_common(&changed, key, verified), Some(if field == 0 {
            "opening-batch terminal relation rejected"
        } else { "opening-batch final PCS rejected:" }));
        count += 1;
    }
    for trailing in [false, true] {
        let mut changed = artifact.clone();
        if trailing { changed.batch.push(0); } else { changed.batch.pop(); }
        assert!(matches!(context.verify_common(&changed, key, verified), Err(CommonFailure::Codec(_))));
        count += 1;
    }
    assert_eq!(count, 32);
    count
}

fn structural_binding_controls(context: &ProofContext<'_>, artifact: &Artifact,
    key: &verifier_key::AdmittedVerifierKey) -> usize {
    for fault in 0..6 {
        let mut changed = artifact.clone();
        match fault {
            0 => { changed.roles.pop(); }
            1 => changed.roles.push(artifact.roles[0].clone()),
            2 => changed.roles[2] = artifact.roles[1].clone(),
            3 => changed.roles.swap(0, 1),
            4 => changed.roles[2].role = 7,
            _ => { changed.roles[2].bytes.pop(); }
        }
        assert!(matches!(context.verified_roles(&changed, key), Err(Reject::Shape)));
    }
    let wrong_key = verifier_key::admit(18, include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert!(matches!(context.verified_roles(artifact, &wrong_key), Err(Reject::Shape)));
    assert!(verifier_key::admit(23, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).is_err());
    let mut packet = artifact.roles[2].clone();
    packet.bytes[..32].fill(0xff);
    let failure = match context.verify_role(&packet, key, &artifact.commitment) {
        Err(error) => error, Ok(_) => panic!("noncanonical GKR accepted"),
    };
    assert_eq!(failure.stage, RoleStage::Decode);
    assert!(!failure.observation.canonical_decode && !failure.observation.verifier_entered);
    9
}

fn local_binding_controls(headers: u64) {
    let started = Instant::now();
    let public = Public::native(headers).unwrap();
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    let mut prefix_count = 0usize;
    let (artifact, geometry, common_count, structural_count) = {
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        let artifact = load_artifact(&artifact_directory().unwrap(), &context).unwrap();
        let verified = context.verified_roles(&artifact, &key).unwrap();
        for role in 0..7 {
            let actual = context.transcript(role, &key, &artifact.commitment);
            let rebuilt = fresh_prefix(&context, &public, role, &key, &artifact.commitment, PrefixFault::NoFault).unwrap();
            assert_eq!(actual.challenges(), 0); assert_eq!(actual.raw_queries(), 0);
            assert_eq!(prefix_snapshot(&actual), prefix_snapshot(&rebuilt));
            let normal = context.verify_role(&artifact.roles[role], &key, &artifact.commitment).unwrap();
            let no_fault = context.verify_role_control(&artifact.roles[role], &key, &artifact.commitment,
                &public, PrefixFault::NoFault).unwrap();
            assert_eq!(normal.claim, no_fault.claim);
            assert_eq!(normal.counters, no_fault.counters);
            assert_eq!(normal.continuation, no_fault.continuation);
            assert!(no_fault.observation.canonical_decode && no_fault.observation.verifier_entered);
            for fault in prefix_faults() {
                let altered = fresh_prefix(&context, &public, role, &key, &artifact.commitment, fault).unwrap();
                assert_ne!(prefix_snapshot(&actual).1, prefix_snapshot(&altered).1, "{fault:?}/{role}");
                target_gkr_rejection(context.verify_role_control(&artifact.roles[role], &key,
                    &artifact.commitment, &public, fault), role, &format!("prefix {fault:?}"));
                prefix_count += 1;
            }
        }
        let common_count = common_binding_controls(&context, &artifact, &key, &verified);
        let structural_count = structural_binding_controls(&context, &artifact, &key);
        (artifact, context.geometry.clone(), common_count, structural_count)
    }; // No context survives into a different public/layout construction.
    assert_eq!(prefix_count, 266);
    let mut public_count = 0;
    for fault in 0..5 {
        let mut changed = public.clone();
        match fault {
            0 => changed.root[0] ^= 1,
            1 => changed.total[27] ^= 1,
            2 => changed.tip[0] ^= 1,
            3 => changed.tip_time ^= 1,
            _ => changed.headers = if headers == 3 { 4 } else { 3 },
        }
        let consumer = Consumer::new(&changed).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        for role in 0..7 {
            target_gkr_rejection(context.verify_role(&artifact.roles[role], &key, &artifact.commitment),
                role, &format!("public field {fault}"));
            public_count += 1;
        }
    }
    for n in [2, 5] {
        let mut changed = public.clone(); changed.headers = n;
        assert!(changed.bytes_with_geometry(&geometry).is_err()); assert!(Consumer::new(&changed).is_err());
    }
    assert_eq!(public_count, 35);
    println!("{}", serde_json::json!({"schema":"candidate-binding-isolated-v1","result":"PASS",
        "headers":headers,"roles":7,"no_fault_roles":7,"prefix_rejections":prefix_count,
        "public_rejections":public_count,"common_rejections":common_count,"structural_rejections":structural_count+2,
        "producer_observed":false,"private_witness_read":false,"setup_generated":false,
        "full_history":false,"production":false,"elapsed_ns":started.elapsed().as_nanos()}));
}

#[test]
#[ignore = "retained N4 artifacts; separate bounded consumer admission required"]
fn candidate_binding_n4_isolated() { local_binding_controls(4); }

#[test]
#[ignore = "compatible fresh N3 artifacts; separate bounded consumer admission required"]
fn candidate_binding_n3_isolated() { local_binding_controls(3); }

#[test]
#[ignore = "two compatible public artifact directories; no producer state"]
fn candidate_binding_two_histories() {
    let started = Instant::now();
    let public3 = Public::native(3).unwrap(); let public4 = Public::native(4).unwrap();
    let dir3 = std::env::var_os("NIPOPOW_CANDIDATE_BINDING_N3_DIR").expect("N3 artifacts");
    let dir4 = std::env::var_os("NIPOPOW_CANDIDATE_BINDING_N4_DIR").expect("N4 artifacts");
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    // Establish both positives first, never keeping both heavyweight contexts.
    let load_positive = |public: &Public, dir: &Path| {
        let consumer = Consumer::new(public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        let artifact = load_artifact(dir, &context).unwrap();
        assert_eq!(context.verify(&artifact, &key).unwrap().len(), 7);
        artifact
    };
    let artifact4 = load_positive(&public4, Path::new(&dir4));
    let artifact3 = load_positive(&public3, Path::new(&dir3));
    assert_ne!(artifact3.commitment, artifact4.commitment);
    let mut c_count = 0; let mut packet_count = 0; let mut common_count = 0;
    for (public, artifact, foreign) in [(&public4, &artifact4, &artifact3), (&public3, &artifact3, &artifact4)] {
        let consumer = Consumer::new(public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        let verified = context.verified_roles(artifact, &key).unwrap();
        for role in 0..7 {
            target_gkr_rejection(context.verify_role(&artifact.roles[role], &key, &foreign.commitment),
                role, "valid foreign same-setup C"); c_count += 1;
            target_gkr_rejection(context.verify_role(&foreign.roles[role], &key, &artifact.commitment),
                role, "other history packet"); packet_count += 1;
        }
        let mut changed = artifact.clone(); changed.batch = foreign.batch.clone();
        common_verification_rejection(context.verify_common(&changed, &key, &verified), None);
        common_count += 1;
    }
    assert_eq!((c_count, packet_count, common_count), (14, 14, 2));
    println!("{}", serde_json::json!({"schema":"candidate-binding-paired-v1","result":"PASS",
        "histories":[3,4],"roles":7,"positive_histories":2,"foreign_c_rejections":c_count,
        "foreign_packet_rejections":packet_count,"foreign_common_rejections":common_count,
        "private_witness_read":false,"setup_generated":false,"full_history":false,"production":false,
        "elapsed_ns":started.elapsed().as_nanos()}));
}

#[test]
#[ignore = "fresh N3 production; separate bounded producer admission required"]
fn candidate_binding_n3_producer() {
    let started = Instant::now();
    let public = Public::native(3).unwrap();
    let output = artifact_directory().unwrap();
    assert!(output.is_dir() && output.read_dir().unwrap().next().is_none(), "fresh empty output required");
    let private_path = std::env::temp_dir().join(format!("candidate-binding-n3-{}.bits", std::process::id()));
    assert!(!private_path.exists(), "private TEMP path must be fresh");
    let (artifact, producer_claims, public_bytes) = {
        let w = witness::build(&witness::retained_headers_n(3).unwrap()).unwrap();
        assert_eq!((w.root, w.total, w.tip, w.tip_time), (public.root, public.total, public.tip, public.tip_time));
        let mut bits = vec![0u8; (1 << 22) / 8];
        for (index, value) in w.values.iter().enumerate() {
            assert!(value.is_zero() || value.is_one());
            if value.is_one() { bits[index / 8] |= 1 << (index % 8); }
        }
        drop(w); // The 2^22-Fr witness never overlaps a layout context.
        let source = packed_source(&private_path, &bits).unwrap(); drop(bits);
        let setup = pcs::generate_setup(22).unwrap();
        let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
        assert_eq!(setup.id, *key.id());
        let committed = packed::commit(&source, &setup).unwrap();
        let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
        let (roles, claims, geometry, public_bytes, corpus_id) = {
            let consumer = Consumer::new(&public).unwrap();
            let context = ProofContext::new(&consumer).unwrap();
            let mut roles = Vec::with_capacity(7); let mut claims = Vec::with_capacity(7);
            for role in 0..7 {
                let (proof, terminal) = prove_role(&context, &source, &key, &commitment, role).unwrap();
                let bytes = gkr::encode_proof(&proof).unwrap();
                assert_eq!(gkr::encode_proof(&gkr::decode_dimensions(&[context.geometry.input_bits[role]], &bytes).unwrap()).unwrap(), bytes);
                let point = if role == 3 { segment_points::embed(3, context.geometry.slot_log, &terminal.point).unwrap() }
                    else { terminal.point };
                assert_eq!(source.evaluate(&point).unwrap(), terminal.value);
                claims.push(Claim { point, value: terminal.value }); roles.push(RoleProof { role, bytes });
            }
            (roles, <[Claim; 7]>::try_from(claims).expect("producer roster"), context.geometry.clone(),
                context.public_bytes.clone(), context.corpus_id)
        }; // Producer layout context is gone before common-opening production.
        let statement = opening_batch::Statement { log_n:geometry.common_input, setup_id:setup.id,
            commitment:committed.commitment, corpus_id:Some(corpus_id),
            claims:claims.clone() };
        let (proof, _, _) = opening_batch::prove(&source, &committed, &setup, &statement).unwrap();
        let batch = opening_batch::encode_proof(&proof, geometry.common_input).unwrap();
        let decoded = opening_batch::decode_proof(&batch, geometry.common_input).unwrap();
        assert_eq!(opening_batch::encode_proof(&decoded, geometry.common_input).unwrap(), batch);
        (Artifact { commitment, roles, batch }, claims, public_bytes)
    }; // All setup, committed/source handles and prover heaps dropped.
    {
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
        assert_eq!(context.verify(&artifact, &key).unwrap(), producer_claims);
    }
    write_new(&output.join("statement.bin"), &public_bytes).unwrap();
    write_new(&output.join("commitment.bin"), &artifact.commitment).unwrap();
    write_new(&output.join("openings.bin"), &artifact.batch).unwrap();
    for packet in &artifact.roles { write_new(&output.join(format!("role-{}.gkr", packet.role)), &packet.bytes).unwrap(); }
    assert_eq!(output.read_dir().unwrap().count(), 10);
    std::fs::remove_file(&private_path).unwrap(); // Only the create-new owned file after successful closure.
    println!("{}", serde_json::json!({"schema":"candidate-binding-n3-producer-v1","result":"PASS",
        "headers":3,"roles":7,"files":10,"gkr_bytes":artifact.roles.iter().map(|p|p.bytes.len()).sum::<usize>(),
        "opening_bytes":artifact.batch.len(),"commitment_bytes":artifact.commitment.len(),
        "producer_claims_equal":true,"sender_transcript_observed":false,"full_history":false,"production":false,
        "elapsed_ns":started.elapsed().as_nanos()}));
}

fn adapters35_eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |a, (bit, x)| {
        a * if index >> bit & 1 == 0 { Fr::one() - x } else { *x }
    })
}

#[test]
fn adapters35_point_shape_and_coefficients() {
    let compiled = point_membership::build().unwrap();
    let base = &compiled.circuit;
    let base_shape = sparse::validate(base, 0).unwrap();
    for h in [0usize, 1, 2, 3, 12, 20, 21] {
        let adapter = PointRole::dimensions(base, h, 13 + h, 14 + h, 20 + h).unwrap();
        let r = dense(14 + h, 3); let u = dense(13 + h, 29); let v = dense(13 + h, 71);
        let actual = adapter.coefficients(&r, &u, &v).unwrap();
        let low = sparse::wiring(base, &base_shape, &r[..14], &u[..13], &v[..13]).unwrap();
        assert!(low.iter().any(|x| !x.is_zero()), "nonvacuous canonical coefficient oracle");
        // Two Boolean choices per bit, never an H-domain table or owner traversal.
        let mut factor = Fr::one();
        for bit in 0..h {
            factor *= (0..2).map(|choice| adapters35_eq(&r[14 + bit..15 + bit], choice)
                * adapters35_eq(&u[13 + bit..14 + bit], choice)
                * adapters35_eq(&v[13 + bit..14 + bit], choice)).sum::<Fr>();
        }
        assert_eq!(actual, low.map(|x| x * factor));
        if h <= 3 {
            let legacy_shape = sparse::validate(base, h).unwrap();
            assert_eq!(actual, sparse::wiring(base, &legacy_shape, &r, &u, &v).unwrap());
        }
        if h > 0 { assert_ne!(actual, low, "omitted copy factor must be observable"); }
        if h >= 2 {
            let mut wrong = u.clone(); wrong.swap(13, 14);
            assert_ne!(adapter.coefficients(&r, &wrong, &v).unwrap(), actual, "one high axis permutation");
        }
        for axis in 0..3 {
            for extra in [false, true] {
                let mut points = [r.clone(), u.clone(), v.clone()];
                if extra { points[axis].push(Fr::one()); } else { points[axis].pop(); }
                assert_eq!(adapter.coefficients(&points[0], &points[1], &points[2]), Err(GkrError::PointDimension));
            }
        }
        for owner in [0, (1usize << h) - 1] {
            for wire in [0usize, 1, 8191] {
                let point: Vec<_> = (0..13).map(|bit| Fr::from(((wire >> bit) & 1) as u64))
                    .chain((0..h).map(|bit| Fr::from(((owner >> bit) & 1) as u64))).collect();
                let projected = adapter.project(&point).unwrap();
                let index = projected.iter().enumerate().fold(0usize, |a, (bit, x)| {
                    assert!(x.is_zero() || x.is_one()); a | ((x.is_one() as usize) << bit)
                });
                assert_eq!(index, owner * layout::WIDTH + 786432 + wire);
                if h == 2 { assert_eq!(projected, segment_points::embed(3, h, &point).unwrap()); }
                let mut wrong_bank = projected.clone(); wrong_bank[18] = Fr::zero();
                assert_ne!(wrong_bank, projected);
                if h > 0 {
                    let mut wrong_owner = projected.clone(); wrong_owner[20] = Fr::one() - wrong_owner[20];
                    assert_ne!(wrong_owner, projected);
                }
            }
        }
        assert!(adapter.project(&vec![Fr::zero(); 12 + h]).is_err());
        assert!(adapter.project(&vec![Fr::zero(); 14 + h]).is_err());
        let projected = adapter.project(&u).unwrap();
        assert_eq!(&projected[..13], &u[..13]); assert_eq!(&projected[20..], &u[13..]);
    }
    for h in [22usize, usize::MAX] {
        assert_eq!(PointRole::dimensions(base, h, 13, 14, 20).err().unwrap(), "point adapter copy dimension");
    }
    for (input, row, common) in [(16, 16, 22), (15, 17, 22), (15, 16, 23)] {
        assert_eq!(PointRole::dimensions(base, 2, input, row, common).err().unwrap(), "point adapter joined geometry");
    }
    assert_eq!(sparse::validate(base, 4).err().unwrap(), GkrError::RepetitionLimit);
    assert!(segment_points::embed(3, 3, &vec![Fr::zero(); 16]).is_err());

    // Test-only bounded algebra fixture: it cannot enter the canonical constructor.
    // All channels are isolated even when a canonical point channel is identically zero.
    let toy = Circuit { input_len: 4, row_count: 2, terms: vec![Term { row: 1,
        gate: crate::gkr::Gate { left: 2, right: 3, c0: Fr::from(2u64), c1: Fr::from(3u64),
            c2: Fr::from(5u64), c3: Fr::from(7u64) } }, Term { row: 0,
        gate: crate::gkr::Gate { left: 0, right: 0, c0: Fr::zero(), c1: Fr::zero(), c2: Fr::zero(), c3: Fr::zero() } }] };
    assert_eq!(PointRole::dimensions(&toy, 2, 15, 16, 22).err().unwrap(), "point adapter canonical base geometry");
    assert_eq!(PointRole::toy_coefficients_for_test(&toy, 4).err().unwrap(), "point legacy toy fixture geometry");
    let mut wrong_input = toy.clone(); wrong_input.input_len = 8;
    assert_eq!(PointRole::toy_coefficients_for_test(&wrong_input, 2).err().unwrap(), "point legacy toy fixture geometry");
    let mut wrong_rows = toy.clone(); wrong_rows.row_count = 4;
    assert_eq!(PointRole::toy_coefficients_for_test(&wrong_rows, 2).err().unwrap(), "point legacy toy fixture geometry");
    for h in 0..=3 {
        let adapter = PointRole::toy_coefficients_for_test(&toy,h).unwrap();
        let r = dense(1 + h, 5); let u = dense(2 + h, 19); let v = dense(2 + h, 43);
        let mut expected = [Fr::zero(); 4];
        for copy in 0..1usize << h {
            for term in &toy.terms {
                let weight = adapters35_eq(&r, term.row + (copy << 1))
                    * adapters35_eq(&u, term.gate.left + (copy << 2))
                    * adapters35_eq(&v, term.gate.right + (copy << 2));
                for (target, coefficient) in expected.iter_mut().zip([term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]) {
                    *target += weight * coefficient;
                }
            }
        }
        assert_eq!(adapter.coefficients(&r, &u, &v).unwrap(), expected);
        for field in 0..7 {
            let mut changed = toy.clone();
            match field {
                0 => changed.terms[0].gate.c0 += Fr::one(), 1 => changed.terms[0].gate.c1 += Fr::one(),
                2 => changed.terms[0].gate.c2 += Fr::one(), 3 => changed.terms[0].gate.c3 += Fr::one(),
                4 => changed.terms[0].gate.left ^= 1, 5 => changed.terms[0].gate.right ^= 1,
                _ => changed.terms[0].row ^= 1,
            }
            let mutant = PointRole::toy_coefficients_for_test(&changed,h).unwrap();
            assert_ne!(mutant.coefficients(&r, &u, &v).unwrap(), expected, "isolated toy field {field}");
        }
    }
}

#[test]
fn adapters35_small_composite_census() {
    for (n, h, golden) in [(3u64, 2usize, 329122usize), (4, 2, 330050), (5, 3, 658658)] {
        let parent = WorkTreeHistoryPlan::compile(n, h, [0; 32], [0; 28]).unwrap();
        let height = HeightWork::compile_history(&parent).unwrap();
        let daa = DaaHistoryRoster::compile(&parent).unwrap();
        let census = daa.term_census().unwrap();
        let mut emitted_lanes = [0usize; 4]; let mut emitted_height = 0usize;
        for owner in 0..parent.slots() {
            let mut sink_count = 0;
            let counts = daa.visit_owner_terms(owner as u64, |_| { sink_count += 1; Ok(()) }).unwrap();
            assert_eq!(counts.lanes.iter().sum::<usize>(), sink_count);
            for lane in 0..4 { emitted_lanes[lane] += counts.lanes[lane]; }
            height.visit_owner_terms(owner as u64, |_| { emitted_height += 1; Ok(()) }).unwrap();
        }
        assert_eq!(census.lanes, emitted_lanes);
        assert_eq!(emitted_height + emitted_lanes.iter().sum::<usize>(), golden);
        assert_eq!(ProofContext::composite_census(&parent, &height, &daa).unwrap(), golden);
        assert_eq!(ProofContext::census_total(n, 32, census.lanes).unwrap(), golden);
        if n <= 4 {
            assert_eq!(ProofContext::admit_census(Geometry::profile_terms(n).unwrap(), golden).unwrap(), golden);
            for fault in [golden - census.lanes[2], golden - 81920, golden - 1, golden + 1] {
                assert_eq!(ProofContext::admit_census(Geometry::profile_terms(n).unwrap(), fault).err().unwrap(),
                    "composite census differs from admitted profile");
            }
        } else { assert!(Geometry::profile_terms(n).is_err()); }
    }
    assert_eq!(ProofContext::census_total(3, usize::MAX, [0; 4]).err().unwrap(), "composite census height overflow");
    assert_eq!(ProofContext::census_total(3, 1, [usize::MAX, 0, 0, 0]).err().unwrap(), "composite census total overflow");
}

#[test]
fn adapters35_same_parent_before_prefix() {
    let public = Public::native(3).unwrap();
    for foreign_height in [true, false] {
        let consumer = Consumer::new(&public).unwrap();
        let mut root = public.root; root[0] ^= 1;
        let foreign = WorkTreeHistoryPlan::compile(3, 2, root, public.total).unwrap();
        let height = HeightWork::new(if foreign_height { &foreign } else { &consumer.parent }).unwrap();
        let daa = DaaHistoryRoster::compile(if foreign_height { &consumer.parent } else { &foreign }).unwrap();
        // Equal N/H/domain arrays cannot detect the foreign immutable parent.
        let geometry = Geometry::derive(&consumer, &height, &daa).unwrap();
        let point_role = PointRole::new(&consumer, &geometry).unwrap();
        let mut observation = PreparationObservation::default();
        let refs = RelationRefs { layouts: consumer.layout_refs(), mode: HeightBinding::LegacyN3N4,
            height: &height, daa: &daa, geometry: &geometry, point_role: &point_role,
            composite_terms: Geometry::profile_terms(public.headers).unwrap() };
        let error = ProofContext::prepare_prefix(&consumer, refs, &mut observation).err().unwrap();
        assert_eq!(error, if foreign_height { "composite height parent identity" } else { "composite DAA parent identity" });
        assert!(!observation.transcript_created);
        assert_eq!((observation.challenges, observation.queries), (0, 0));
    }
}

#[test]
#[ignore = "retained N3/N4 public directories; bounded verifier differential only"]
fn adapters35_retained_point_old_new() {
    let dir3 = std::env::var_os("NIPOPOW_CANDIDATE_BINDING_N3_DIR").expect("N3 artifacts");
    let dir4 = std::env::var_os("NIPOPOW_CANDIDATE_BINDING_N4_DIR").expect("N4 artifacts");
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    for (headers, directory) in [(3, dir3), (4, dir4)] {
        let public = Public::native(headers).unwrap();
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        let artifact = load_artifact(Path::new(&directory), &context).unwrap();
        let packet = &artifact.roles[3];
        let proof = gkr::decode_dimensions(&[context.geometry.input_bits[3]], &packet.bytes).unwrap();
        assert_eq!(gkr::encode_proof(&proof).unwrap(), packet.bytes);
        let mut legacy_t = context.transcript(3, &key, &artifact.commitment);
        let mut analytic_t = context.transcript(3, &key, &artifact.commitment);
        assert_eq!(prefix_snapshot(&legacy_t), prefix_snapshot(&analytic_t));
        assert_eq!((legacy_t.challenges(), legacy_t.raw_queries()), (0, 0));
        let legacy = sparse::verify(&consumer.points.circuit, context.geometry.slot_log, &proof, &mut legacy_t).unwrap();
        let analytic = context.point_role.verify(&proof, &mut analytic_t).unwrap();
        assert_eq!(legacy, analytic);
        assert_eq!(prefix_snapshot(&legacy_t), prefix_snapshot(&analytic_t));
        let old_projection = segment_points::embed(3, context.geometry.slot_log, &legacy.point).unwrap();
        assert_eq!(old_projection, context.point_role.project(&analytic.point).unwrap());
        let normal = context.verify_role(packet, &key, &artifact.commitment).unwrap();
        assert_eq!(normal.claim, Claim { point: old_projection, value: legacy.value });
        assert_eq!(normal.counters, [legacy_t.challenges(), legacy_t.raw_queries(), legacy_t.bytes_absorbed()]);
        assert_eq!(normal.continuation, legacy_t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1").unwrap());
        assert_eq!(gkr::encode_proof(&proof).unwrap(), packet.bytes);
    }
}

fn next36_request(headers: u64, slot_log: usize) -> LayoutRequest {
    LayoutRequest { headers, slot_log, root: [0x5a; 32], total: [0x33; 28], tip: [0xa5; 32], tip_time: 1700000000 }
}
fn next36_reject(consumer: &Consumer, refs: RelationRefs<'_, '_>, expected: &str) {
    let before = next36_constructions();
    let mut observation = PreparationObservation::default();
    let error = ProofContext::prepare_prefix(consumer, refs, &mut observation).err().expect("isolated prefix rejection");
    assert_eq!(error, expected);
    assert!(!observation.transcript_created);
    assert_eq!((observation.challenges, observation.queries), (0, 0));
    assert_eq!(next36_constructions(), before, "views and prefix must not reconstruct or census");
}

#[test]
fn next36_preflight_and_shared_path() {
    for (n, h, error) in [(0, 2, "next36 header extent"), (2, 2, "next36 header extent"),
        ((1u64 << 21) + 1, 22, "next36 header extent"), (u64::MAX, 21, "next36 header padding overflow"),
        (3, 3, "next36 canonical owner dimension"), (4, usize::MAX, "next36 canonical owner dimension")] {
        let before = next36_constructions();
        assert_eq!(compile_layouts(&next36_request(n, h)).err().unwrap(), error);
        assert_eq!(next36_constructions(), before, "reject before first template factory");
    }
    let before = next36_constructions();
    assert_eq!(next36_request(3, 2).preflight_abi(32).err().unwrap(), "next36 requires 64-bit ABI");
    assert_eq!(next36_constructions(), before);
    next36_request((1 << 20) + 1, 21).preflight().unwrap();
    for n in [3u64, 4] {
        let public = Public::native(n).unwrap();
        let before = next36_constructions();
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        assert_eq!(next36_constructions(), [before[0] + 1, before[1] + 1]);
        assert_eq!(context.height_binding, HeightBinding::LegacyN3N4);
        assert_eq!(context.composite_terms, Geometry::profile_terms(n).unwrap());
        assert_eq!(context.public_bytes, literal_public_bytes(&public).unwrap());
        let counts = next36_constructions();
        for _ in 0..2 {
            let (mut prefix, bytes, corpus, count) = ProofContext::prepare_prefix(&consumer, context.relation_refs(),
                &mut PreparationObservation::default()).unwrap();
            context.bind_composite(&mut prefix);
            assert_eq!(prefix_snapshot(&prefix), prefix_snapshot(&context.base));
            assert_eq!((bytes, corpus, count), (context.public_bytes.clone(), context.corpus_id, context.composite_terms));
        }
        assert_eq!(next36_constructions(), counts, "prefix count is stored, not recomputed");
        let callback_before = next36_callback_calls();
        for role in 0..7 {
            let r = dense(context.geometry.row_bits[role], 3 + 101 * role as u64);
            let u = dense(context.geometry.input_bits[role], 29 + 101 * role as u64);
            let v = dense(context.geometry.input_bits[role], 71 + 101 * role as u64);
            let direct = match role {
                0 => consumer.parent.core_pool().coefficients(&r, &u, &v).unwrap(),
                1 => context.daa.header_coefficients(&r, &u, &v).unwrap(),
                2 => work_tree_wiring::full_roster_coefficients(consumer.parent.topology(), fixed::engine().unwrap(),
                    consumer.parent.fixed_profile(), consumer.parent.leaf_boundary(), consumer.parent.work_boundary(), &r, &u, &v).unwrap(),
                3 => context.point_role.coefficients(&r, &u, &v).unwrap(),
                4 => crate::native_prefix_auth_plan::composite_coefficients(&context.height, &context.daa, &r, &u, &v).unwrap(),
                5 => consumer.adjacency.coefficients(&r, &u, &v).unwrap(),
                6 => consumer.metadata.coefficients(&r, &u, &v).unwrap(),
                _ => unreachable!(),
            };
            assert_eq!(context.coefficients(role, &r, &u, &v).unwrap(), direct);
            let calls = next36_callback_calls();
            for axis in 0..3 {
                for extra in [false, true] {
                    let mut points = [r.clone(), u.clone(), v.clone()];
                    if extra { points[axis].push(Fr::one()); } else { points[axis].pop(); }
                    assert_eq!(context.coefficients(role, &points[0], &points[1], &points[2]).err().unwrap(),
                        "next36 coefficient point dimensions");
                    assert_eq!(next36_callback_calls(), calls, "dimension guard precedes callback dispatch");
                }
            }
        }
        assert_eq!(context.coefficients(7, &[], &[], &[]).err().unwrap(), "next36 coefficient role");
        assert_eq!(next36_callback_calls(), callback_before + 7);
        assert_eq!(next36_constructions(), counts, "callbacks do not rerun census");
        let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
        for role in 0..7 {
            let actual = context.transcript(role, &key, &[0; 384]);
            let reference = fresh_prefix(&context, &public, role, &key, &[0; 384], PrefixFault::NoFault).unwrap();
            assert_eq!(prefix_snapshot(&actual), prefix_snapshot(&reference));
            assert_eq!((actual.challenges(), actual.raw_queries()), (0, 0));
        }
    }
}

#[test]
fn next36_prefix_identity_mode_count() {
    let public = Public::native(3).unwrap();
    let consumer = Consumer::new(&public).unwrap();
    {
        let mut parts = RelationParts::compile(consumer.layout_refs(), HeightBinding::LegacyN3N4).unwrap();
        let baseline = next36_constructions();
        ProofContext::prepare_prefix(&consumer, parts.refs(), &mut PreparationObservation::default()).unwrap();
        assert_eq!(next36_constructions(), baseline);
        {
            let mut root = public.root; root[0] ^= 1;
            let foreign = WorkTreeHistoryPlan::compile(3, 2, root, public.total).unwrap();
            let layouts = LayoutRefs { parent: &foreign, ..parts.layouts };
            next36_reject(&consumer, RelationRefs { layouts, ..parts.refs() }, "next36 parent layout identity");
        }
        {
            let foreign = HeaderAdjacencyLayout::compile(3, 2, [0; 32], public.tip).unwrap();
            let layouts = LayoutRefs { adjacency: &foreign, ..parts.layouts };
            next36_reject(&consumer, RelationRefs { layouts, ..parts.refs() }, "next36 adjacency layout identity");
        }
        {
            let foreign = HeaderMetadataOrderLayout::compile(3, 2, public.tip_time).unwrap();
            let layouts = LayoutRefs { metadata: &foreign, ..parts.layouts };
            next36_reject(&consumer, RelationRefs { layouts, ..parts.refs() }, "next36 metadata layout identity");
        }
        {
            let foreign = point_membership::build().unwrap();
            let layouts = LayoutRefs { points: &foreign, ..parts.layouts };
            next36_reject(&consumer, RelationRefs { layouts, ..parts.refs() }, "next36 points layout identity");
            let point_role = PointRole::dimensions(&foreign.circuit, 2, 15, 16, 22).unwrap();
            next36_reject(&consumer, RelationRefs { point_role: &point_role, ..parts.refs() }, "next36 point base identity");
        }
        {
            let foreign = consumer.point_template.clone();
            let layouts = LayoutRefs { point_template: &foreign, ..parts.layouts };
            next36_reject(&consumer, RelationRefs { layouts, ..parts.refs() }, "next36 fingerprint owner identity");
        }
        let golden = parts.composite_terms;
        for count in [golden - 1, golden + 1] {
            parts.composite_terms = count;
            next36_reject(&consumer, parts.refs(), "composite census differs from admitted profile");
        }
        parts.composite_terms = golden;
        ProofContext::prepare_prefix(&consumer, parts.refs(), &mut PreparationObservation::default()).unwrap();
    }
    // Same N/H/geometry/count and correct original references; only binder mode differs.
    let diagnostic = RelationParts::compile(consumer.layout_refs(), HeightBinding::HistoricalDiagnostic).unwrap();
    assert_eq!(diagnostic.geometry.input_bits, INPUT_BITS);
    assert_eq!(diagnostic.geometry.row_bits, ROW_BITS);
    assert_eq!(diagnostic.composite_terms, 329122);
    next36_reject(&consumer, diagnostic.refs(), "next36 legacy binding mode");
}

fn next36_ns(started: Instant) -> Result<u64, String> {
    u64::try_from(started.elapsed().as_nanos()).map_err(|_| "next36 nanosecond overflow".into())
}
fn next36_mark(stage: &str, boundary: &str, started: Instant) -> Result<(), String> {
    let elapsed = next36_ns(started)?;
    if elapsed > 120000000000 { return Err("next36 diagnostic deadline".into()); }
    eprintln!("HISTORY_NEXT36_STAGE {stage} {boundary} {elapsed}");
    Ok(())
}
fn next36_scalar_hex(value: Fr) -> Result<String, String> {
    use ark_ff::{BigInteger, PrimeField};
    let bytes = value.into_bigint().to_bytes_le();
    if bytes.len() != 32 { return Err("next36 scalar extent".into()); }
    Ok(bytes.iter().map(|byte| format!("{byte:02x}")).collect())
}
fn next36_point_box_bytes(compiled: &point_membership::Compiled) -> Result<usize, String> {
    let mut total = 0usize;
    for point in &compiled.layout.points {
        for bits in [&point.x, &point.y, &point.u, &point.v].into_iter()
            .chain(point.quotients.iter()).chain(point.comparisons.iter()) {
            total = total.checked_add(std::mem::size_of_val(bits.as_ref())).ok_or("next36 point box ledger overflow")?;
        }
        for row in &point.carries {
            for bits in row {
                total = total.checked_add(std::mem::size_of_val(bits.as_ref())).ok_or("next36 point box ledger overflow")?;
            }
        }
    }
    Ok(total)
}

#[test]
#[ignore = "H21 joined construction and seven callbacks; separate bounded cold-process admission"]
fn next36_h21_joined_callbacks() {
    let started = Instant::now();
    let location = std::cell::Cell::new("layout");
    let operation = (|| -> Result<(), String> {
        let initial = next36_constructions();
        let callbacks_before = next36_callback_calls();
        let request = next36_request((1 << 20) + 1, 21);
        next36_mark("layout", "begin", started)?;
        let clock = Instant::now();
        let layouts = compile_layouts(&request)?;
        let layout_ns = next36_ns(clock)?;
        next36_mark("layout", "end", started)?;
        location.set("relation"); next36_mark("relation", "begin", started)?;
        let clock = Instant::now();
        let parts = RelationParts::compile(layouts.layout_refs(), HeightBinding::HistoricalDiagnostic)?;
        let relation_ns = next36_ns(clock)?;
        next36_mark("relation", "end", started)?;
        if parts.geometry.headers != request.headers || parts.geometry.slot_log != 21
            || parts.geometry.slots != 2097152 || parts.geometry.common_input != 41
            || parts.mode != HeightBinding::HistoricalDiagnostic { return Err("next36 joined geometry".into()); }
        location.set("projection"); next36_mark("projection", "begin", started)?;
        let clock = Instant::now();
        let local_point = dense(parts.geometry.input_bits[3], 29);
        let projected = parts.point_role.project(&local_point)?;
        let bank = [0u64, 0, 0, 0, 0, 1, 1].map(Fr::from);
        if projected.len() != 41 || projected[..13] != local_point[..13]
            || projected[13..20] != bank[..] || projected[20..] != local_point[13..] {
            return Err("next36 joined point projection".into());
        }
        let projection_ns = next36_ns(clock)?;
        next36_mark("projection", "end", started)?;
        let projection_bytes = local_point.capacity().checked_add(projected.capacity())
            .and_then(|n| n.checked_mul(std::mem::size_of::<Fr>())).ok_or("next36 point ledger overflow")?;
        drop(projected); drop(local_point);
        let mut results = Vec::with_capacity(7);
        let mut small_point_peak_bytes = projection_bytes;
        for (role, name) in ["role0", "role1", "role2", "role3", "role4", "role5", "role6"].into_iter().enumerate() {
            location.set(name); next36_mark(name, "begin", started)?;
            let r = dense(parts.geometry.row_bits[role], 3 + 101 * role as u64);
            let u = dense(parts.geometry.input_bits[role], 29 + 101 * role as u64);
            let v = dense(parts.geometry.input_bits[role], 71 + 101 * role as u64);
            let point_bytes = r.capacity().checked_add(u.capacity()).and_then(|n| n.checked_add(v.capacity()))
                .and_then(|n| n.checked_mul(std::mem::size_of::<Fr>())).ok_or("next36 point ledger overflow")?;
            small_point_peak_bytes = small_point_peak_bytes.max(point_bytes);
            let clock = Instant::now();
            let coefficients = role_coefficients(parts.refs(), role, &r, &u, &v)?;
            let callback_ns = next36_ns(clock)?;
            results.push((role, coefficients, callback_ns));
            next36_mark(name, "end", started)?;
        }
        location.set("closure");
        let final_counts = next36_constructions();
        if final_counts != [initial[0].checked_add(1).ok_or("next36 factory counter overflow")?,
            initial[1].checked_add(1).ok_or("next36 census counter overflow")?] || results.len() != 7
            || next36_callback_calls() != callbacks_before.checked_add(7).ok_or("next36 callback counter overflow")? {
            return Err("next36 construction/callback closure".into());
        }
        let point_terms_bytes = layouts.points.circuit.terms.capacity().checked_mul(std::mem::size_of::<Term>())
            .ok_or("next36 template ledger overflow")?;
        let point_box_bytes = next36_point_box_bytes(&layouts.points)?;
        let results_bytes = results.capacity().checked_mul(std::mem::size_of::<(usize, [Fr; 4], u64)>())
            .ok_or("next36 result ledger overflow")?;
        let outputs = results.iter().map(|(role, coefficients, callback_ns)| {
            let coefficients = coefficients.iter().map(|value| next36_scalar_hex(*value)).collect::<Result<Vec<_>, _>>()?;
            Ok(serde_json::json!({"role":role,"coefficients":coefficients,"callback_ns":callback_ns}))
        }).collect::<Result<Vec<_>, String>>()?;
        let elapsed_ns = next36_ns(started)?;
        let report = serde_json::json!({"schema":"history-next36-joined-v1","state":"PASS",
            "headers":request.headers,"slot_log":21,"slots":2097152,"diagnostic_only":true,
            "public_profile_admitted":false,"proof_verified":false,"private_input_read":false,"setup_generated":false,
            "full_history":false,"production":false,"input_bits":parts.geometry.input_bits,"row_bits":parts.geometry.row_bits,
            "composite_terms":parts.composite_terms,"recipe":{"r_offset":3,"u_offset":29,"v_offset":71,
                "role_step":101,"coordinate_step":17,"index_origin":0},
            "projection":{"input_log":34,"common_input_log":41,"low_coordinates":13,"bank":96,"owner_coordinates":21,"checked":true},
            "construction_observations":{"layout_factories":1,"census":1,"callbacks":7},
            "phase_ns":{"layout":layout_ns,"relation":relation_ns,"projection":projection_ns},"results":outputs,
            "known_payload":{"owned_inline_bytes":std::mem::size_of_val(&layouts),"relation_inline_bytes":std::mem::size_of_val(&parts),
                "point_terms_capacity":layouts.points.circuit.terms.capacity(),"point_terms_bytes":point_terms_bytes,
                "point_box_bytes":point_box_bytes,
                "point_fingerprint_capacity_bytes":layouts.point_template.capacity(),"small_point_peak_bytes":small_point_peak_bytes,"results_bytes":results_bytes},
            "resource_unknowns":["other_layout_heap","other_relation_heap","callback_internal_scratch","allocator_and_vendor"],"elapsed_ns":elapsed_ns});
        let encoded = serde_json::to_string(&report).map_err(|e| e.to_string())?;
        if encoded.len() > 16384 { return Err("next36 report extent".into()); }
        if next36_ns(started)? > 120000000000 { return Err("next36 diagnostic deadline".into()); }
        // Semantic closure timestamp; serialization/transport are outside elapsed_ns.
        eprintln!("HISTORY_NEXT36_STAGE complete end {elapsed_ns}");
        println!("\nHISTORY_NEXT36_JOINED_REPORT {encoded}");
        Ok(())
    })();
    if let Err(error) = operation {
        eprintln!("HISTORY_NEXT36_HOLD {} {} {}", location.get(), next36_ns(started).unwrap_or(u64::MAX), error.chars().take(240).collect::<String>());
        panic!("next36 joined diagnostic HOLD");
    }
}

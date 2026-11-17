//! Local five-role transport; C is untrusted and no history-ready token exists.
use super::*;
use ark_ff::{One,Zero};
use std::{io::{Read,Write},path::{Path,PathBuf}};
use crate::point_role::{PointPublicStatement,PointPublicVerifier};
use crate::global_producer_endpoint_plan::{NativeHeaderPublicStatement,NativeHeaderPublicVerifier};

const C573_PACKET_BYTES:usize=171201;
const C573_GKR:[usize;5]=[5024,3456,5024,5024,5024];
const C573_PCS:usize=29421;
#[derive(Clone,PartialEq,Eq)]
struct C573Request{root:[u8;32],total:[u8;28],key_id:[u8;32]}
fn c573_key()->AdmittedVerifierKey{crate::verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap()}
fn c573_request(b:&[u8])->Result<C573Request,String>{
    if b.len()!=112||&b[..8]!=b"C573REQ1"||u16::from_le_bytes(b[8..10].try_into().unwrap())!=1
        ||u64::from_le_bytes(b[10..18].try_into().unwrap())!=3||b[18]!=2||b[79]!=22
    {return Err("C573 request format/profile".into());}
    let r=C573Request{root:b[19..51].try_into().unwrap(),total:b[51..79].try_into().unwrap(),key_id:b[80..112].try_into().unwrap()};
    if &r.key_id!=c573_key().id(){return Err("C573 request release key".into());}Ok(r)
}
struct C573Packet<'a>{common:&'a[u8],gkr:[&'a[u8];5],pcs:[&'a[u8];5]}
fn c573_packet<'a>(b:&'a[u8],r:&C573Request)->Result<C573Packet<'a>,String>{
    if b.len()!=C573_PACKET_BYTES{return Err("C573 packet extent".into());}
    if &b[..8]!=b"C573N3V1"||u16::from_le_bytes(b[8..10].try_into().unwrap())!=1
        ||u16::from_le_bytes(b[10..12].try_into().unwrap())!=1||b[498]!=5
    {return Err("C573 packet format/version/cardinality".into());}
    if u64::from_le_bytes(b[12..20].try_into().unwrap())!=3||b[20]!=2||b[81]!=22
        ||b[21..53]!=r.root||b[53..81]!=r.total||b[82..114]!=r.key_id
    {return Err("C573 packet/request mismatch".into());}
    let(mut gkr,mut pcs)=([&[][..];5],[&[][..];5]);let mut at=499usize;
    for role in 0..5{
        let end=at.checked_add(9).ok_or("C573 header offset overflow")?;
        let h=b.get(at..end).ok_or("C573 missing entry")?;
        if h[0]as usize!=role||u32::from_le_bytes(h[1..5].try_into().unwrap())as usize!=C573_GKR[role]
            ||u32::from_le_bytes(h[5..9].try_into().unwrap())as usize!=C573_PCS
        {return Err("C573 entry order/tag/extent".into());}at=end;
        let end=at.checked_add(C573_GKR[role]).ok_or("C573 GKR offset overflow")?;gkr[role]=b.get(at..end).ok_or("C573 GKR missing")?;at=end;
        let end=at.checked_add(C573_PCS).ok_or("C573 PCS offset overflow")?;pcs[role]=b.get(at..end).ok_or("C573 PCS missing")?;at=end;
    }
    if at!=b.len(){return Err("C573 trailing bytes".into());}
    let common=&b[114..498];pcs::decode_commitment(common).map_err(|e|format!("C573 C encoding: {e}"))?;
    Ok(C573Packet{common,gkr,pcs})
}

fn c573_verify(r:&C573Request,b:&[u8])->Result<(),String>{
    let packet=c573_packet(b,r)?;let key=c573_key();
    if &r.key_id!=key.id(){return Err("C573 request release key".into());}
    let parent=WorkTreeHistoryPlan::compile(3,2,r.root,r.total)?;
    // Construct ALL expected public contexts from ONE immutable candidate-C
    // slice before any role challenges. Defensive role re-decoding stays.
    let work=NativeWorkVerifier::new(&parent,&key,packet.common)?;
    let point=PointPublicVerifier::new(PointPublicStatement::new(&parent,&key,packet.common)
        .map_err(|e|format!("C573 POINT context: {e:?}"))?,&key).map_err(|e|format!("C573 POINT context: {e:?}"))?;
    let header=NativeHeaderPublicVerifier::new(&parent,NativeHeaderPublicStatement::new(r.root,r.total,&key,packet.common)?,&key)
        .map_err(|e|format!("C573 HEADER context: {e:?}"))?;
    let core=super::native_core_pool_real_join_tests::C573CoreVerifier::expected(&parent,&key,packet.common)?;
    let tree=super::native_tree_real_join_tests::C573TreeVerifier::expected(&parent,&key,packet.common)?;
    work.verify(packet.gkr[0],packet.pcs[0]).map_err(|e|format!("C573 role0 Work: {e}"))?;
    point.verify_encoded_on(packet.gkr[1],packet.pcs[1],&mut Transcript::new(b"c569-POINT-semantic"))
        .map_err(|e|format!("C573 role1 POINT: {e:?}"))?;
    header.verify_encoded_on(packet.gkr[2],packet.pcs[2],&mut Transcript::new(b"c569-HEADER-semantic"))
        .map_err(|e|format!("C573 role2 HEADER: {e:?}"))?;
    core.verify_on(packet.gkr[3],packet.pcs[3],&mut Transcript::new(b"nipopow-native-core-pool-diagnostic-v1"))
        .map_err(|e|format!("C573 role3 Core: {e}"))?;
    tree.verify_on(packet.gkr[4],packet.pcs[4],&mut Transcript::new(b"nipopow-native-tree-diagnostic-v1"))
        .map_err(|e|format!("C573 role4 Tree: {e}"))?;
    Ok(()) // No partial collection acceptance or producer-issued token.
}
fn c573_encode(r:&C573Request,c:&[u8],bodies:&[(Vec<u8>,Vec<u8>);5])->Result<Vec<u8>,String>{
    if c.len()!=384{return Err("C573 encode C extent".into());}pcs::decode_commitment(c)?;
    for(i,(g,p))in bodies.iter().enumerate(){
        if g.len()!=C573_GKR[i]||p.len()!=C573_PCS{return Err("C573 encode role extent".into());}
        gkr::decode_dimensions(&[if i==1{15}else{22}],g)?;pcs::decode_proof(p,22)?;
    }
    let mut out=Vec::new();out.try_reserve_exact(C573_PACKET_BYTES).map_err(|_|"C573 envelope allocation")?;
    out.extend_from_slice(b"C573N3V1");out.extend_from_slice(&1u16.to_le_bytes());out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&3u64.to_le_bytes());out.push(2);out.extend_from_slice(&r.root);out.extend_from_slice(&r.total);out.push(22);
    out.extend_from_slice(&r.key_id);out.extend_from_slice(c);out.push(5);
    for(i,(g,p))in bodies.iter().enumerate(){out.push(i as u8);out.extend_from_slice(&(g.len()as u32).to_le_bytes());
        out.extend_from_slice(&(p.len()as u32).to_le_bytes());out.extend_from_slice(g);out.extend_from_slice(p);}
    if out.len()!=C573_PACKET_BYTES{return Err("C573 encoded total".into());}c573_packet(&out,r)?;Ok(out)
}
fn c573_path(name:&str)->PathBuf{
    let p=PathBuf::from(std::env::var_os(name).expect("controller supplies exact path"));
    assert!(p.is_absolute()&&!p.components().any(|c|matches!(c,std::path::Component::ParentDir)));p
}
fn c573_read(path:&Path,bytes:usize)->Result<Vec<u8>,String>{
    let m=std::fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !m.is_file()||m.file_type().is_symlink()||!m.permissions().readonly()||m.len()!=bytes as u64{return Err("C573 immutable input extent/path".into());}
    let mut file=std::fs::File::open(path).map_err(|e|e.to_string())?;let mut out=Vec::new();
    out.try_reserve_exact(bytes).map_err(|_|"C573 bounded read allocation")?;out.resize(bytes,0);
    file.read_exact(&mut out).map_err(|e|e.to_string())?;let mut tail=[0u8;1];
    if file.read(&mut tail).map_err(|e|e.to_string())?!=0||file.metadata().map_err(|e|e.to_string())?.len()!=bytes as u64{return Err("C573 input changed".into());}Ok(out)
}
fn c573_mark(t:&Transcript)->((u64,u64,u64),[Fr;2]){let mut c=t.clone();((t.challenges(),t.raw_queries(),t.bytes_absorbed()),
    [c.challenge_scalar(b"c573-continuation-a"),c.challenge_scalar(b"c573-continuation-b")])}

#[test]
#[ignore="C573 one-owner five-role generation/export; separate controller and source custody"]
fn c573_produce_local_five_role_collection(){
    let request=c573_read(&c573_path("C573_REQUEST"),112).unwrap();let r=c573_request(&request).unwrap();
    let parent=WorkTreeHistoryPlan::compile(3,2,r.root,r.total).unwrap();
    let source=c573_path("C573_SOURCE");let metadata=std::fs::metadata(&source).unwrap();
    assert!(metadata.is_file()&&metadata.permissions().readonly());assert_eq!(metadata.len(),524288);
    let output=c573_path("C573_PACKET_OUT");assert!(!output.exists());
    let mut audit=WorkPreparationAudit::default();
    let owner=NativeWorkProducer::create(&parent,&source,c573_key(),Some(&mut audit)).unwrap();
    assert_eq!((audit.opens,audit.setups,audit.commits),(1,1,1));
    assert_eq!((audit.relations,audit.chunks,audit.residuals),(1,64,1));
    let lease=owner.c573_lease().unwrap();lease.check().unwrap();
    // Rejected challenged adapters reach no helper/opening; caller state stays.
    let mut challenged=Transcript::new(b"c573-challenged");challenged.challenge_scalar(b"already");
    let before=c573_mark(&challenged);
    assert!(crate::point_role::c573_prove_owned_on(&lease,&mut challenged).is_err());assert_eq!(c573_mark(&challenged),before);
    assert!(crate::global_producer_endpoint_plan::c573_prove_packed_header_on(&lease,&mut challenged).is_err());assert_eq!(c573_mark(&challenged),before);
    assert!(super::native_core_pool_real_join_tests::c573_prove(&lease,&mut challenged).is_err());assert_eq!(c573_mark(&challenged),before);
    assert!(super::native_tree_real_join_tests::c573_prove(&lease,&mut challenged).is_err());assert_eq!(c573_mark(&challenged),before);
    let work=owner.prove().unwrap();let work_bytes=(work.gkr_bytes().to_vec(),work.pcs_bytes().to_vec());
    NativeWorkVerifier::new(&parent,lease.key(),lease.commitment_bytes()).unwrap().verify(&work_bytes.0,&work_bytes.1).unwrap();
    println!("C573_COLLECTION_STAGE|Work_ready");
    let mut point_t=Transcript::new(b"c569-POINT-semantic");let point=crate::point_role::c573_prove_owned_on(&lease,&mut point_t).unwrap();
    let public_point=PointPublicVerifier::new(PointPublicStatement::new(&parent,lease.key(),lease.commitment_bytes()).unwrap(),lease.key()).unwrap();
    let mut point_v=Transcript::new(b"c569-POINT-semantic");public_point.verify_encoded_on(&point.0,&point.1,&mut point_v).unwrap();
    assert_eq!(c573_mark(&point_t),c573_mark(&point_v));println!("C573_COLLECTION_STAGE|POINT_ready");
    let mut header_t=Transcript::new(b"c569-HEADER-semantic");let header=crate::global_producer_endpoint_plan::c573_prove_packed_header_on(&lease,&mut header_t).unwrap();
    let public_header=NativeHeaderPublicVerifier::new(&parent,NativeHeaderPublicStatement::new(r.root,r.total,lease.key(),lease.commitment_bytes()).unwrap(),lease.key()).unwrap();
    let mut header_v=Transcript::new(b"c569-HEADER-semantic");public_header.verify_encoded_on(&header.0,&header.1,&mut header_v).unwrap();
    assert_eq!(c573_mark(&header_t),c573_mark(&header_v));println!("C573_COLLECTION_STAGE|HEADER_ready");
    let mut core_t=Transcript::new(b"nipopow-native-core-pool-diagnostic-v1");let core=super::native_core_pool_real_join_tests::c573_prove(&lease,&mut core_t).unwrap();
    let public_core=super::native_core_pool_real_join_tests::C573CoreVerifier::expected(&parent,lease.key(),lease.commitment_bytes()).unwrap();
    let mut core_v=Transcript::new(b"nipopow-native-core-pool-diagnostic-v1");public_core.verify_on(&core.0,&core.1,&mut core_v).unwrap();
    assert_eq!(c573_mark(&core_t),c573_mark(&core_v));println!("C573_COLLECTION_STAGE|Core_ready");
    let mut tree_t=Transcript::new(b"nipopow-native-tree-diagnostic-v1");let tree=super::native_tree_real_join_tests::c573_prove(&lease,&mut tree_t).unwrap();
    let public_tree=super::native_tree_real_join_tests::C573TreeVerifier::expected(&parent,lease.key(),lease.commitment_bytes()).unwrap();
    let mut tree_v=Transcript::new(b"nipopow-native-tree-diagnostic-v1");public_tree.verify_on(&tree.0,&tree.1,&mut tree_v).unwrap();
    assert_eq!(c573_mark(&tree_t),c573_mark(&tree_v));println!("C573_COLLECTION_STAGE|Tree_ready");
    assert_eq!((audit.opens,audit.setups,audit.commits),(1,1,1));
    let packet=c573_encode(&r,lease.commitment_bytes(),&[work_bytes,point,header,core,tree]).unwrap();c573_verify(&r,&packet).unwrap();
    let mut file=std::fs::OpenOptions::new().write(true).create_new(true).open(&output).unwrap();file.write_all(&packet).unwrap();
    file.flush().unwrap();file.sync_all().unwrap();drop(file);
    let mut permissions=std::fs::metadata(&output).unwrap().permissions();permissions.set_readonly(true);std::fs::set_permissions(&output,permissions).unwrap();
    assert_eq!(c573_read(&output,C573_PACKET_BYTES).unwrap(),packet);
    println!("C573_COLLECTION_STAGE|packet_ready");
}

fn c573_offsets(role:usize)->(usize,usize,usize){
    assert!(role<5);let mut h=499;for n in C573_GKR.iter().take(role){h+=9+n+C573_PCS;}(h,h+9,h+9+C573_GKR[role])
}
fn c573_fail(r:&C573Request,b:&[u8],prefix:&str){
    let e=c573_verify(r,b).err().expect("mutant accepted");assert!(e.starts_with(prefix),"expected {prefix}, got {e}");
}
fn c573_role_fail(r:&C573Request,b:&[u8],role:usize,pcs:bool){
    let e=c573_verify(r,b).err().expect("semantic mutant accepted");
    assert!(e.starts_with(&format!("C573 role{role} ")),"wrong rejection role: {e}");
    if pcs{assert!(e.contains("PCS")||e.contains("Pcs("),"not PCS rejection: {e}");}
    else{assert!(e.contains("GKR")||e.contains("Gkr("),"not GKR rejection: {e}");}
}
#[test]
#[ignore="C573 fresh-process source-free collection consumer; producer must already be known closed"]
fn c573_cold_verify_local_five_role_collection(){
    for name in ["C573_SOURCE","C573_PACKET_OUT","C572_SOURCE","C571_SOURCE","C570_SOURCE","C569_RETAINED_SOURCE",
        "C569_OUTPUT_DIR","C568_POINT_SOURCE","NIPOPOW_H21_FRAME","NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR","NIPOPOW_CORE_POOL_EVIDENCE"]{
        assert!(std::env::var_os(name).is_none(),"cold source/output environment present: {name}");
    }
    let request=c573_read(&c573_path("C573_REQUEST"),112).unwrap();let r=c573_request(&request).unwrap();
    let bytes=c573_read(&c573_path("C573_PACKET"),C573_PACKET_BYTES).unwrap();
    c573_verify(&r,&bytes).unwrap();
    for id in 1..=67{c579_run_case(id,&request,&r,&bytes);}
    c573_verify(&r,&bytes).unwrap();
    println!("C573_COLLECTION_COLD_PASS|roles=5");
}

// Independent public requester stage. Never reachable from packet/cold parsing.
#[test]
#[ignore="C573 public-only request preparation; separate bounded requester process"]
fn c573_prepare_public_request(){
    for name in ["C573_SOURCE","C573_PACKET","C573_PACKET_OUT","C573_REQUEST","C572_SOURCE","C571_SOURCE","C570_SOURCE",
        "C569_RETAINED_SOURCE","C569_OUTPUT_DIR","C568_POINT_SOURCE","NIPOPOW_H21_FRAME","NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR"]{
        assert!(std::env::var_os(name).is_none(),"requester must not inherit source/prover/request input: {name}");
    }
    let output=c573_path("C573_REQUEST_OUT");assert!(!output.exists());
    let headers=crate::historical_prefix_witness::retained_headers().unwrap();
    let public=crate::packed_owner_assembly::NativePrefix::from_raw_iter(3,
        headers.iter().map(|h|h.encode().map_err(|e|format!("{e:?}")))).unwrap();
    let key=c573_key();require_work_key22(&key).unwrap();
    let mut bytes=Vec::new();bytes.try_reserve_exact(112).unwrap();
    bytes.extend_from_slice(b"C573REQ1");bytes.extend_from_slice(&1u16.to_le_bytes());bytes.extend_from_slice(&3u64.to_le_bytes());bytes.push(2);
    bytes.extend_from_slice(&public.root());bytes.extend_from_slice(&public.total_be28());bytes.push(22);bytes.extend_from_slice(key.id());
    assert_eq!(bytes.len(),112);let parsed=c573_request(&bytes).unwrap();
    assert_eq!(parsed.root,public.root());assert_eq!(parsed.total,public.total_be28());assert_eq!(&parsed.key_id,key.id());
    let mut file=std::fs::OpenOptions::new().write(true).create_new(true).open(&output).unwrap();
    file.write_all(&bytes).unwrap();file.flush().unwrap();file.sync_all().unwrap();drop(file);
    let mut permissions=std::fs::metadata(&output).unwrap().permissions();permissions.set_readonly(true);std::fs::set_permissions(&output,permissions).unwrap();
    let readback=c573_read(&output,112).unwrap();assert_eq!(readback,bytes);assert!(c573_request(&readback).unwrap()==parsed);
    println!("C573_REQUEST_READY");
}


fn c573_cold_once_emit(line:&'static str){println!("{line}");std::io::stdout().flush().unwrap();}
fn c573_verify_once_staged(r:&C573Request,b:&[u8])->Result<(),String>{
    let packet=c573_packet(b,r)?;c573_cold_once_emit("C573_COLD_ONCE_STAGE|envelope_ready");let key=c573_key();
    if &r.key_id!=key.id(){return Err("C573 request release key".into());}
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|key_ready");
    let parent=WorkTreeHistoryPlan::compile(3,2,r.root,r.total)?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|parent_ready");
    // Construct ALL expected public contexts from ONE immutable candidate-C
    // slice before any role challenges. Defensive role re-decoding stays.
    let work=NativeWorkVerifier::new(&parent,&key,packet.common)?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|Work_context_ready");
    let point=PointPublicVerifier::new(PointPublicStatement::new(&parent,&key,packet.common)
        .map_err(|e|format!("C573 POINT context: {e:?}"))?,&key).map_err(|e|format!("C573 POINT context: {e:?}"))?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|POINT_context_ready");
    let header=NativeHeaderPublicVerifier::new(&parent,NativeHeaderPublicStatement::new(r.root,r.total,&key,packet.common)?,&key)
        .map_err(|e|format!("C573 HEADER context: {e:?}"))?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|HEADER_context_ready");
    let core=super::native_core_pool_real_join_tests::C573CoreVerifier::expected(&parent,&key,packet.common)?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|Core_context_ready");
    let tree=super::native_tree_real_join_tests::C573TreeVerifier::expected(&parent,&key,packet.common)?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|Tree_context_ready");
    work.verify(packet.gkr[0],packet.pcs[0]).map_err(|e|format!("C573 role0 Work: {e}"))?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|Work_verified");
    point.verify_encoded_on(packet.gkr[1],packet.pcs[1],&mut Transcript::new(b"c569-POINT-semantic"))
        .map_err(|e|format!("C573 role1 POINT: {e:?}"))?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|POINT_verified");
    header.verify_encoded_on(packet.gkr[2],packet.pcs[2],&mut Transcript::new(b"c569-HEADER-semantic"))
        .map_err(|e|format!("C573 role2 HEADER: {e:?}"))?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|HEADER_verified");
    core.verify_on(packet.gkr[3],packet.pcs[3],&mut Transcript::new(b"nipopow-native-core-pool-diagnostic-v1"))
        .map_err(|e|format!("C573 role3 Core: {e}"))?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|Core_verified");
    tree.verify_on(packet.gkr[4],packet.pcs[4],&mut Transcript::new(b"nipopow-native-tree-diagnostic-v1"))
        .map_err(|e|format!("C573 role4 Tree: {e}"))?;
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|Tree_verified");
    Ok(()) // No partial collection acceptance or producer-issued token.
}

#[test]
#[ignore="C573 retained-packet positive-only cold diagnostic; fresh process and reviewed custody required"]
fn c573_cold_verify_once_with_stages(){
    for name in ["C573_SOURCE","C573_REQUEST_OUT","C573_PACKET_OUT","C572_SOURCE","C571_SOURCE","C570_SOURCE","C569_RETAINED_SOURCE",
        "C569_OUTPUT_DIR","C568_POINT_SOURCE","NIPOPOW_H21_FRAME","NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR","NIPOPOW_CORE_POOL_EVIDENCE"]{
        assert!(std::env::var_os(name).is_none(),"cold-once source/output environment present: {name}");
    }
    let request=c573_read(&c573_path("C573_REQUEST"),112).unwrap();
    let packet=c573_read(&c573_path("C573_PACKET"),C573_PACKET_BYTES).unwrap();
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|inputs_read");
    let r=c573_request(&request).unwrap();
    c573_cold_once_emit("C573_COLD_ONCE_STAGE|request_ready");
    c573_verify_once_staged(&r,&packet).unwrap();
    c573_cold_once_emit("C573_COLD_ONCE_PASS|roles=5");
}

// The fixed case identities retain the legacy mutation order and oracles.
fn c579_run_case(id:u8,request:&Vec<u8>,pristine:&C573Request,bytes:&Vec<u8>){
    let r=(*pristine).clone();
    match id{
        1..=4=>{
            let at=[8usize,18,79,80][usize::from(id-1)];
            let mut bad=request.clone();bad[at]^=1;assert!(c573_request(&bad).is_err());
        }
        5=>{let mut short=bytes.clone();short.pop();c573_fail(&r,&short,"C573 packet extent");}
        6=>{let mut extra=bytes.clone();extra.push(0);c573_fail(&r,&extra,"C573 packet extent");}
        7..=10=>{
            let at=[0usize,8,10,498][usize::from(id-7)];
            let mut bad=bytes.clone();bad[at]^=1;c573_fail(&r,&bad,"C573 packet format/");
        }
        11..=16=>{
            let at=[12usize,20,21,53,81,82][usize::from(id-11)];
            let mut bad=bytes.clone();bad[at]^=1;c573_fail(&r,&bad,"C573 packet/request mismatch");
        }
        17..=41=>{
            let role=usize::from((id-17)/5);let field=(id-17)%5;
            let(h,_,_)=c573_offsets(role);
            match field{
                0..=2=>{
                    let field=[0usize,1,5][usize::from(field)];
                    let mut bad=bytes.clone();bad[h+field]^=1;c573_fail(&r,&bad,"C573 entry order/tag/extent");
                }
                3=>{let mut duplicate=bytes.clone();duplicate[h]=if role==0{4}else{(role-1)as u8};c573_fail(&r,&duplicate,"C573 entry order/tag/extent");}
                4=>{let mut unknown=bytes.clone();unknown[h]=255;c573_fail(&r,&unknown,"C573 entry order/tag/extent");}
                _=>unreachable!(),
            }
        }
        42..=44=>{
            let(a,b)=[(0usize,2usize),(0,3),(3,4)][usize::from(id-42)];
            let(_,ag,ap)=c573_offsets(a);let(_,bg,bp)=c573_offsets(b);assert_eq!(C573_GKR[a],C573_GKR[b]);
            let mut bad=bytes.clone();bad[ag..ap+C573_PCS].copy_from_slice(&bytes[bg..bp+C573_PCS]);
            bad[bg..bp+C573_PCS].copy_from_slice(&bytes[ag..ap+C573_PCS]);assert_ne!(bad.as_slice(),bytes.as_slice());
            c573_packet(&bad,&r).unwrap();let e=c573_verify(&r,&bad).err().unwrap();assert!(e.starts_with(&format!("C573 role{} ",a.min(b))));
        }
        45=>{
            let candidate=pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(
                ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap();
            assert_ne!(candidate.as_slice(),&bytes[114..498]);let mut changed_c=bytes.clone();changed_c[114..498].copy_from_slice(&candidate);
            c573_packet(&changed_c,&r).unwrap();c573_role_fail(&r,&changed_c,0,false);
        }
        46..=47=>{
            let total=id==47;let mut expected=r.clone();let mut bad=bytes.clone();
            if total{expected.total[27]^=1;bad[53..81].copy_from_slice(&expected.total);}else{expected.root[0]^=1;bad[21..53].copy_from_slice(&expected.root);}
            assert!(expected!=r);c573_packet(&bad,&expected).unwrap();c573_role_fail(&expected,&bad,0,false);
        }
        48..=67=>{
            let role=usize::from((id-48)/4);let field=(id-48)%4;
            let(_,g,p)=c573_offsets(role);let log=if role==1{15}else{22};
            match field{
                0=>{
                    let mut decoded=gkr::decode_dimensions(&[log],&bytes[g..p]).unwrap();decoded.layers[0].rounds[0][0]+=Fr::one();
                    let canonical=gkr::encode_proof(&decoded).unwrap();assert_eq!(canonical.len(),C573_GKR[role]);assert_ne!(canonical.as_slice(),&bytes[g..p]);
                    gkr::decode_dimensions(&[log],&canonical).unwrap();let mut bad=bytes.clone();bad[g..p].copy_from_slice(&canonical);c573_role_fail(&r,&bad,role,false);
                }
                1=>{
                    let mut opening=pcs::decode_proof(&bytes[p..p+C573_PCS],22).unwrap();opening.vmv_message.e1.0=-opening.vmv_message.e1.0;
                    let canonical=pcs::encode_proof(&opening).unwrap();assert_eq!(canonical.len(),C573_PCS);assert_ne!(canonical.as_slice(),&bytes[p..p+C573_PCS]);
                    pcs::decode_proof(&canonical,22).unwrap();let mut bad=bytes.clone();bad[p..p+C573_PCS].copy_from_slice(&canonical);c573_role_fail(&r,&bad,role,true);
                }
                2=>{
                    let mut malformed=bytes.clone();malformed[g..g+32].fill(255);let e=c573_verify(&r,&malformed).err().unwrap();
                    assert!(e.starts_with(&format!("C573 role{role} ")));assert!(gkr::decode_dimensions(&[log],&malformed[g..p]).is_err());
                }
                3=>{
                    let mut wrong_rounds=bytes.clone();assert_eq!(u32::from_le_bytes(wrong_rounds[p+800..p+804].try_into().unwrap()),11);
                    wrong_rounds[p+800..p+804].copy_from_slice(&12u32.to_le_bytes());let e=c573_verify(&r,&wrong_rounds).err().unwrap();
                    assert!(e.starts_with(&format!("C573 role{role} ")));assert!(e.contains("round count rejected before allocation"));
                }
                _=>unreachable!(),
            }
        }
        _=>panic!("C579 unknown case ID"),
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum C579Selection{Structural41,Case(u8)}
impl C579Selection{
    fn ids(self)->std::ops::RangeInclusive<u8>{
        match self{
            Self::Structural41=>1..=41,
            Self::Case(id)=>{assert!((42..=67).contains(&id));id..=id}
        }
    }
    fn count(self)->usize{match self{Self::Structural41=>41,Self::Case(_)=>1}}
}
fn c579_parse_selection(value:Option<&str>)->Result<C579Selection,&'static str>{
    let value=value.ok_or("C579_COLD_SELECTION required")?;
    if value=="structural41"{return Ok(C579Selection::Structural41);}
    let b=value.as_bytes();
    if b.len()==6 && &b[..4]==b"case" && b[4].is_ascii_digit() && b[5].is_ascii_digit(){
        let id=(b[4]-b'0')*10+(b[5]-b'0');
        if (42..=67).contains(&id){return Ok(C579Selection::Case(id));}
    }
    Err("C579 closed selection spelling required")
}
fn c579_emit_start(id:u8){println!("C579_COLD_START|id={id:02}");std::io::stdout().flush().unwrap();}
fn c579_emit_reject(id:u8){println!("C579_COLD_REJECT|id={id:02}");std::io::stdout().flush().unwrap();}
fn c579_emit_done(selected:usize){println!("C579_COLD_DONE|selected={selected}");std::io::stdout().flush().unwrap();}

#[test]
#[ignore="C579 fixed retained-input negative selection; same-final-binary positive and independent admission required"]
fn c579_cold_verify_selected_cases(){
    let value=std::env::var("C579_COLD_SELECTION").ok();
    let selection=c579_parse_selection(value.as_deref()).expect("C579 closed selection before input/key/context work");
    for name in ["C573_SOURCE","C573_REQUEST_OUT","C573_PACKET_OUT","C572_SOURCE","C571_SOURCE","C570_SOURCE","C569_RETAINED_SOURCE",
        "C569_OUTPUT_DIR","C568_POINT_SOURCE","NIPOPOW_H21_FRAME","NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR","NIPOPOW_CORE_POOL_EVIDENCE"]{
        assert!(std::env::var_os(name).is_none(),"cold source/output environment present: {name}");
    }
    let ids=selection.ids();let first=*ids.start();
    c579_emit_start(first);
    let request=c573_read(&c573_path("C573_REQUEST"),112).unwrap();let r=c573_request(&request).unwrap();
    let bytes=c573_read(&c573_path("C573_PACKET"),C573_PACKET_BYTES).unwrap();c573_packet(&bytes,&r).unwrap();
    let mut count=0;
    for id in ids{
        if id!=first{c579_emit_start(id);}
        c579_run_case(id,&request,&r,&bytes);
        c579_emit_reject(id);count+=1;
    }
    assert_eq!(count,selection.count());c579_emit_done(count);
}

#[test]
fn c579_no_frame_selection_is_closed_and_complete(){
    let structural=c579_parse_selection(Some("structural41")).unwrap();
    assert_eq!(structural,C579Selection::Structural41);assert_eq!(structural.count(),41);
    assert_eq!(structural.ids().collect::<Vec<_>>(),(1u8..=41).collect::<Vec<_>>());
    let mut seen=[0u8;68];for id in structural.ids(){seen[usize::from(id)]+=1;}
    for id in 42u8..=67{
        let text=format!("case{id:02}");let selected=c579_parse_selection(Some(&text)).unwrap();
        assert_eq!(selected,C579Selection::Case(id));assert_eq!(selected.count(),1);
        assert_eq!(selected.ids().collect::<Vec<_>>(),vec![id]);
        for actual in selected.ids(){seen[usize::from(actual)]+=1;}
    }
    assert_eq!(seen[0],0);assert!(seen[1..].iter().all(|n|*n==1));
    assert!(c579_parse_selection(None).is_err());
    for bad in ["","structural41 "," structural41","STRUCTURAL41","structural41,case42","case41","case68","case042","case4","Case42",
        "case42 "," case42","case42\n","case42,case43","case42;case43","case4\u{200b}2","case\u{ff14}2","case42\0"]{
        assert!(c579_parse_selection(Some(bad)).is_err(),"accepted foreign selection: {bad:?}");
    }
}

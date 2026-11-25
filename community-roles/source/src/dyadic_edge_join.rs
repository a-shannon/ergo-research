//! One dyadic B1 child edge, streamed through sparse GKR and two mandatory PCS openings.
use std::time::Instant;
use ark_bn254::{Fr,G1Projective,G2Projective,Bn254};
use ark_ff::{One,Zero};
use ark_serialize::{CanonicalDeserialize,CanonicalSerialize};
use blake2::{Blake2b,Digest,digest::consts::U32};
use dory_pcs::backends::arkworks::{ArkDoryProof,ArkGT};
use serde::{Serialize,Deserialize};
use crate::{gkr::{self,Gate,GkrProof,InputClaim},sparse::{self,Circuit,Term},sparse_stream_boolean,
    packed::{self,PackedFile,PackedCommitted},pcs::{self,Setup},transcript::Transcript,verifier_key,
    work_tree_layout::{self as layout,Endpoints,WIDTH,ENDPOINT_BASE,ENDPOINT_WIDTH},work_tree_wiring::Descriptor};

pub const DOMAIN:&[u8]=b"nipopow-dyadic-edge-gkr-two-pcs-v1";
const MAGIC:&[u8;8]=b"DYEDGE01";
const VERSION:u8=1;
pub const STATEMENT_CAP:usize=16384;
pub const PAIR_WIDTH:usize=16384;
pub const CONTRACT_SHA256:&str="D4626BE65B0A94436C1F6E70529E48D8A954F68714D0F7F6E247E9D78CB1326D";

#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
#[serde(deny_unknown_fields)]
pub struct Geometry {
    pub headers:usize,pub leaves:usize,pub slots:usize,pub level:usize,pub branch:usize,
    pub copies:usize,pub log_copies:usize,pub parent_base:usize,pub child_base:usize,
    pub bank_offset:usize,pub bank_width:usize,pub header_width:usize,pub global_log:usize,
    pub coordinate_order:String,
}
impl Geometry {
    pub fn new(headers:usize,level:usize,branch:usize)->Result<Self,String>{
        if !matches!(headers,3|5){return Err("dyadic edge admits only H3/H5".into());}
        let d=Descriptor::new(headers,[0;32])?;
        if level==0||level>d.leaves.trailing_zeros() as usize||branch>1{return Err("dyadic level/branch rejected".into());}
        let copies=d.leaves>>level;if !matches!(copies,1|2){return Err("dyadic copy cap".into());}
        Ok(Self {headers,leaves:d.leaves,slots:d.slots,level,branch,copies,log_copies:copies.trailing_zeros() as usize,
            parent_base:d.leaves-2*copies,child_base:if level==1{0}else {d.leaves-4*copies},
            bank_offset:ENDPOINT_BASE,bank_width:ENDPOINT_WIDTH,header_width:WIDTH,global_log:20+d.slot_log(),
            coordinate_order:"LSB: bank13, side1, copy-high; PCS bank13, bank-prefix7, slot-high".into()})
    }
    pub fn validate(&self)->Result<(),String>{if *self!=Self::new(self.headers,self.level,self.branch)?{return Err("dyadic geometry mismatch".into());}Ok(())}
    pub fn indices(&self,copy:usize)->Result<(usize,usize),String>{self.validate()?;if copy>=self.copies{return Err("dyadic copy index".into());}
        Ok((self.parent_base+copy,self.child_base+2*copy+self.branch))}
}
pub fn local_circuit(g:&Geometry)->Result<Circuit,String>{g.validate()?;let e=Endpoints::new();
    if ENDPOINT_BASE!=983040||ENDPOINT_WIDTH!=8192||[e.leaf[0],e.node_left[0],e.node_right[0],e.node[0]].map(|w|w-ENDPOINT_BASE)!=[5338,5594,5850,6106]{return Err("B1 endpoint layout drift".into());}
    let left=if g.branch==0{&e.node_left}else{&e.node_right};let right=if g.level==1{&e.leaf}else{&e.node};
    let terms=(0..256).map(|bit|Term {row:bit,gate:Gate {left:left[bit]-ENDPOINT_BASE,
        right:ENDPOINT_WIDTH+right[bit]-ENDPOINT_BASE,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}}).collect();
    Ok(Circuit {input_len:PAIR_WIDTH,row_count:256,terms})
}
fn load_pair_measured(source:&PackedFile,g:&Geometry,copy:usize)->Result<(Vec<Fr>,usize),String>{
    let (parent,child)=g.indices(copy)?;if source.input_len()!=g.slots*WIDTH{return Err("dyadic packed dimension".into());}
    let index=|slot|slot*(WIDTH/ENDPOINT_WIDTH)+ENDPOINT_BASE/ENDPOINT_WIDTH;
    let mut left=source.read_copy(ENDPOINT_WIDTH,index(parent))?;left.reserve_exact(ENDPOINT_WIDTH);
    let right=source.read_copy(ENDPOINT_WIDTH,index(child))?;
    let peak_fields=left.capacity().checked_add(right.capacity()).ok_or("pair loader capacity overflow")?;
    left.extend(right);Ok((left,peak_fields))
}
pub fn load_pair(source:&PackedFile,g:&Geometry,copy:usize)->Result<Vec<Fr>,String>{Ok(load_pair_measured(source,g,copy)?.0)}
pub fn derive_points(g:&Geometry,point:&[Fr])->Result<[Vec<Fr>;2],String>{
    g.validate()?;if point.len()!=14+g.log_copies{return Err("dyadic GKR terminal dimension".into());}
    let h=g.global_log-20;let m=g.log_copies;let mut left=point[..13].to_vec();let mut right=left.clone();
    let bank=(0..7).map(|bit|Fr::from(((ENDPOINT_BASE/ENDPOINT_WIDTH>>bit)&1) as u64)).collect::<Vec<_>>();
    left.extend_from_slice(&bank);right.extend_from_slice(&bank);
    left.extend_from_slice(&point[14..]);left.extend((m..h).map(|bit|Fr::from(((g.parent_base>>bit)&1) as u64)));
    right.push(Fr::from(g.branch as u64));right.extend_from_slice(&point[14..]);
    right.extend((m+1..h).map(|bit|Fr::from(((g.child_base>>bit)&1) as u64)));
    if left.len()!=g.global_log||right.len()!=g.global_log{return Err("dyadic PCS embedding dimension".into());}Ok([left,right])
}

#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
#[serde(deny_unknown_fields)]
pub struct ExpectedStatement {
    pub profile:String,pub version:u8,pub tree:Descriptor,pub geometry:Geometry,pub setup_mode:String,
    pub setup_id:[u8;32],pub commitment:Vec<u8>,pub corpus_blake2b256:[u8;32],pub circuit_blake2b256:String,
}
impl ExpectedStatement {
    pub fn new(g:Geometry,root:[u8;32],setup:&Setup,commitment:&ArkGT,corpus_blake2b256:[u8;32])->Result<Self,String>{
        let circuit=local_circuit(&g)?;let out=Self {profile:"dyadic-edge-gkr-two-pcs-v1".into(),version:VERSION,
            tree:Descriptor::new(g.headers,root)?,setup_mode:if g.headers==3{"release-admitted-log22"}else{"independently-regenerated-log23-diagnostic"}.into(),
            geometry:g,setup_id:setup.id,commitment:pcs::encode_commitment(commitment)?,corpus_blake2b256,circuit_blake2b256:layout::hash_terms(&circuit.terms)};
        out.validate()?;if setup.log_n!=out.geometry.global_log{return Err("edge setup dimension".into());}Ok(out)
    }
    pub fn validate(&self)->Result<(),String>{
        self.geometry.validate()?;self.tree.validate()?;let c=local_circuit(&self.geometry)?;
        let mode=if self.geometry.headers==3{"release-admitted-log22"}else{"independently-regenerated-log23-diagnostic"};
        if self.profile!="dyadic-edge-gkr-two-pcs-v1"||self.version!=VERSION||self.tree.headers!=self.geometry.headers
            ||self.setup_mode!=mode||self.circuit_blake2b256!=layout::hash_terms(&c.terms){return Err("expected edge statement mismatch".into());}
        pcs::decode_commitment(&self.commitment)?;Ok(())
    }
}
pub fn encode_statement(s:&ExpectedStatement)->Result<Vec<u8>,String>{s.validate()?;let bytes=serde_json::to_vec_pretty(s).map_err(|e|e.to_string())?;
    if bytes.len()>STATEMENT_CAP{return Err("expected statement cap".into());}Ok(bytes)}
pub fn decode_statement(bytes:&[u8])->Result<ExpectedStatement,String>{if bytes.len()>STATEMENT_CAP{return Err("expected statement cap".into());}
    let s:ExpectedStatement=serde_json::from_slice(bytes).map_err(|e|e.to_string())?;s.validate()?;Ok(s)}
fn bind(s:&ExpectedStatement,t:&mut Transcript)->Result<(),String>{s.validate()?;
    t.append_bytes(b"dyadic-expected-statement",&serde_json::to_vec(s).map_err(|e|e.to_string())?);
    t.append_u64(b"dyadic-opening-count",2);t.append_bytes(b"dyadic-opening-order",b"parent-L,child-R");Ok(())
}
fn new_transcript(s:&ExpectedStatement)->Result<Transcript,String>{let mut t=Transcript::new(DOMAIN);bind(s,&mut t)?;Ok(t)}
fn bind_tail(t:&mut Transcript,claim:&InputClaim,points:&[Vec<Fr>;2],values:&[Fr;2])->Result<(),String>{
    if claim.point.len()<14{return Err("edge terminal too short".into());}
    let s=claim.point[13];if (Fr::one()-s)*values[0]+s*values[1]!=claim.value{return Err("edge split relation rejected".into());}
    t.append_bytes(b"dyadic-two-pcs",b"split-at-local-bit13-no-reset-v1");t.append_scalar(b"dyadic-gkr-terminal",&claim.value);
    for side in 0..2{t.append_u64(b"dyadic-opening-role",side as u64);t.append_u64(b"dyadic-point-length",points[side].len() as u64);
        for x in &points[side]{t.append_scalar(b"dyadic-point-coordinate",x);}t.append_scalar(b"dyadic-value",&values[side]);}Ok(())
}
fn verify_openings(context:&VerifierContext,expected:&ExpectedStatement,claim:&InputClaim,points:&[Vec<Fr>;2],
    values:&[Fr;2],openings:&[ArkDoryProof;2],t:&mut Transcript)->Result<[f64;2],String>{
    bind_tail(t,claim,points,values)?;let c=pcs::decode_commitment(&expected.commitment)?;let mut seconds=[0.0;2];
    for side in 0..2{let now=Instant::now();context.verify_one(c.clone(),values[side],&points[side],&openings[side],t)
        .map_err(|e|format!("edge PCS {} rejected: {e}",if side==0{"L"}else{"R"}))?;seconds[side]=now.elapsed().as_secs_f64();}
    Ok(seconds)
}

enum Key {Admitted(verifier_key::AdmittedVerifierKey),Regenerated(Setup)}
pub struct VerifierContext {key:Key}
impl VerifierContext {
    pub fn load(expected:&ExpectedStatement)->Result<Self,String>{expected.validate()?;
        let key=if expected.geometry.global_log==22 {Key::Admitted(verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?)}
            else {Key::Regenerated(pcs::generate_setup(23)?)};
        let out=Self {key};out.admit(expected)?;Ok(out)
    }
    fn admit(&self,s:&ExpectedStatement)->Result<(),String>{let (log,id)=match &self.key {Key::Admitted(k)=>(k.log_n(),*k.id()),Key::Regenerated(k)=>(k.log_n,k.id)};
        if log!=s.geometry.global_log||id!=s.setup_id{return Err("edge verifier setup identity mismatch".into());}Ok(())}
    fn verify_one(&self,c:ArkGT,value:Fr,point:&[Fr],proof:&ArkDoryProof,t:&mut Transcript)->Result<(),String>{match &self.key{
        Key::Admitted(k)=>pcs::verify_admitted(c,value,point,proof,k,t),Key::Regenerated(k)=>pcs::verify(c,value,point,proof,k,t),}}
}
pub struct Proof {pub gkr:GkrProof,pub values:[Fr;2],pub openings:[ArkDoryProof;2]}
#[derive(Default,Debug,Serialize)]
pub struct Metrics {
    pub gkr_seconds:f64,pub packed_evaluation_seconds:f64,pub opening_seconds:[f64;2],pub verification_seconds:[f64;2],
    pub load_pair_reads:usize,pub maximum_pair_and_second_bank_fields:usize,pub global_packed_bits:usize,pub proof_bytes:usize,
    pub transcript_challenges:u64,pub transcript_raw_queries:u64,pub transcript_bytes:u64,
}
pub fn prove(source:&PackedFile,committed:&PackedCommitted,setup:&Setup,expected:&ExpectedStatement)->Result<(Proof,Metrics),String>{
    expected.validate()?;if source.input_len()!=1usize<<expected.geometry.global_log||setup.log_n!=expected.geometry.global_log
        ||setup.id!=expected.setup_id||pcs::encode_commitment(&committed.commitment)?!=expected.commitment{return Err("edge source/commitment/setup mismatch".into());}
    let mut t=new_transcript(expected)?;let circuit=local_circuit(&expected.geometry)?;let mut metrics=Metrics {global_packed_bits:source.input_len(),..Metrics::default()};
    let now=Instant::now();let mut load_error=None;
    let (gkr,claim)=sparse_stream_boolean::prove(&circuit,expected.geometry.log_copies,|copy|{
        match load_pair_measured(source,&expected.geometry,copy){Ok((pair,peak_fields))=>{metrics.load_pair_reads+=1;
            metrics.maximum_pair_and_second_bank_fields=metrics.maximum_pair_and_second_bank_fields.max(peak_fields);Ok(pair)},
            Err(e)=>{load_error=Some(e);Err(gkr::GkrError::InvalidInputWidth)}}
    },&mut t).map_err(|e|load_error.unwrap_or_else(||e.to_string()))?;metrics.gkr_seconds=now.elapsed().as_secs_f64();
    let points=derive_points(&expected.geometry,&claim.point)?;let now=Instant::now();let values=[source.evaluate(&points[0])?,source.evaluate(&points[1])?];
    metrics.packed_evaluation_seconds=now.elapsed().as_secs_f64();bind_tail(&mut t,&claim,&points,&values)?;
    let now=Instant::now();let left=packed::open(committed,source,&points[0],setup,&mut t)?;metrics.opening_seconds[0]=now.elapsed().as_secs_f64();
    let now=Instant::now();let right=packed::open(committed,source,&points[1],setup,&mut t)?;metrics.opening_seconds[1]=now.elapsed().as_secs_f64();
    let proof=Proof {gkr,values,openings:[left,right]};metrics.proof_bytes=encode_proof(expected,&proof)?.len();
    metrics.transcript_challenges=t.challenges();metrics.transcript_raw_queries=t.raw_queries();metrics.transcript_bytes=t.bytes_absorbed();Ok((proof,metrics))
}
pub fn verify(expected:&ExpectedStatement,proof:&Proof,context:&VerifierContext)->Result<Metrics,String>{
    expected.validate()?;context.admit(expected)?;let mut t=new_transcript(expected)?;let circuit=local_circuit(&expected.geometry)?;
    let now=Instant::now();let claim=sparse::verify(&circuit,expected.geometry.log_copies,&proof.gkr,&mut t).map_err(|e|e.to_string())?;
    let mut metrics=Metrics {gkr_seconds:now.elapsed().as_secs_f64(),global_packed_bits:1usize<<expected.geometry.global_log,..Metrics::default()};
    let points=derive_points(&expected.geometry,&claim.point)?;
    metrics.verification_seconds=verify_openings(context,expected,&claim,&points,&proof.values,&proof.openings,&mut t)?;
    metrics.proof_bytes=encode_proof(expected,proof)?.len();metrics.transcript_challenges=t.challenges();metrics.transcript_raw_queries=t.raw_queries();metrics.transcript_bytes=t.bytes_absorbed();Ok(metrics)
}
fn dory_bytes(k:usize)->usize{let g1=G1Projective::zero().compressed_size();let g2=G2Projective::zero().compressed_size();let gt=ark_ec::pairing::PairingOutput::<Bn254>::zero().compressed_size();
    2*gt+g1+4+k.div_ceil(2)*(6*gt+3*g1+3*g2)+1+g1+g2+8}
pub fn proof_bytes(g:&Geometry)->Result<usize,String>{g.validate()?;Ok(9+32*(7*(14+g.log_copies)+3)+64+2*dory_bytes(g.global_log))}
pub fn encode_proof(expected:&ExpectedStatement,p:&Proof)->Result<Vec<u8>,String>{expected.validate()?;let g=&expected.geometry;
    if p.openings.iter().any(|proof|proof.nu!=g.global_log/2||proof.sigma!=g.global_log.div_ceil(2)
        ||proof.first_messages.len()!=proof.sigma||proof.second_messages.len()!=proof.sigma){
        return Err("edge PCS proof shape".into());
    }
    let circuit=local_circuit(g)?;let gkr=gkr::encode_proof(&p.gkr)?;
    let decoded=sparse::decode_proof(&circuit,g.log_copies,&gkr)?;if decoded!=p.gkr{return Err("edge GKR proof shape".into());}
    if gkr.len()!=32*(7*(14+g.log_copies)+3){return Err("edge GKR encoding length".into());}
    let mut out=Vec::with_capacity(proof_bytes(g)?);out.extend_from_slice(MAGIC);out.push(VERSION);out.extend(gkr);
    for value in &p.values{out.extend(pcs::encode(value)?);}for opening in &p.openings{let bytes=pcs::encode_proof(opening)?;
        if bytes.len()!=dory_bytes(g.global_log){return Err("edge Dory encoding length".into());}out.extend(bytes);}
    if out.len()!=proof_bytes(g)?{return Err("edge packet size".into());}Ok(out)
}
fn decode_scalar(bytes:&[u8])->Result<Fr,String>{let mut reader=bytes;let scalar=Fr::deserialize_compressed(&mut reader).map_err(|e|e.to_string())?;
    if !reader.is_empty()||pcs::encode(&scalar)?!=bytes{return Err("edge noncanonical scalar".into());}Ok(scalar)}
pub fn decode_proof(expected:&ExpectedStatement,bytes:&[u8])->Result<Proof,String>{expected.validate()?;let g=&expected.geometry;
    if bytes.len()!=proof_bytes(g)?||&bytes[..8]!=MAGIC||bytes[8]!=VERSION{return Err("edge packet frame/length rejected before allocation".into());}
    let mut at=9;let size=32*(7*(14+g.log_copies)+3);let gkr=sparse::decode_proof(&local_circuit(g)?,g.log_copies,&bytes[at..at+size])?;at+=size;
    let values=[decode_scalar(&bytes[at..at+32])?,decode_scalar(&bytes[at+32..at+64])?];at+=64;let size=dory_bytes(g.global_log);
    let left=pcs::decode_proof(&bytes[at..at+size],g.global_log)?;at+=size;let right=pcs::decode_proof(&bytes[at..at+size],g.global_log)?;at+=size;
    let proof=Proof {gkr,values,openings:[left,right]};if at!=bytes.len()||encode_proof(expected,&proof)?!=bytes{return Err("edge noncanonical packet".into());}Ok(proof)
}

pub fn fixture_bytes(g:&Geometry)->Result<Vec<u8>,String>{g.validate()?;let mut out=Vec::with_capacity(g.slots*WIDTH/8);
    for block in 0..(g.slots*WIDTH/8).div_ceil(32){let mut h=Blake2b::<U32>::new();h.update(b"dyadic-edge-byte-envelope-v1");
        for n in [g.headers,g.level,g.branch,block]{h.update((n as u64).to_le_bytes());}out.extend_from_slice(&h.finalize());}
    out.truncate(g.slots*WIDTH/8);let c=local_circuit(g)?;
    for copy in 0..g.copies{let (parent,child)=g.indices(copy)?;for term in &c.terms{
        let source=child*WIDTH+ENDPOINT_BASE+term.gate.right-ENDPOINT_WIDTH;let target=parent*WIDTH+ENDPOINT_BASE+term.gate.left;
        let bit=(out[source/8]>>(source%8))&1;out[target/8]=(out[target/8]&!(1<<(target%8)))|(bit<<(target%8));
    }}Ok(out)
}
pub fn corpus_digest(bytes:&[u8])->[u8;32]{Blake2b::<U32>::digest(bytes).into()}
pub fn source_pins()->serde_json::Value{serde_json::json!({"contract_sha256":CONTRACT_SHA256,
    "dyadic_edge_join.rs":layout::hash_bytes(include_bytes!("dyadic_edge_join.rs")),"work_tree_layout.rs":layout::hash_bytes(include_bytes!("work_tree_layout.rs")),
    "work_tree_wiring.rs":layout::hash_bytes(include_bytes!("work_tree_wiring.rs")),"sparse.rs":layout::hash_bytes(include_bytes!("sparse.rs")),
    "gkr.rs":layout::hash_bytes(include_bytes!("gkr.rs")),"sparse_stream.rs":layout::hash_bytes(include_bytes!("sparse_stream.rs")),
    "sparse_stream_boolean.rs":layout::hash_bytes(include_bytes!("sparse_stream_boolean.rs")),"packed.rs":layout::hash_bytes(include_bytes!("packed.rs")),
    "pcs.rs":layout::hash_bytes(include_bytes!("pcs.rs")),"transcript.rs":layout::hash_bytes(include_bytes!("transcript.rs")),
    "verifier_key.rs":layout::hash_bytes(include_bytes!("verifier_key.rs"))})}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{sparse_stream,work_tree_wiring::{Mapping,Topology}};
    use std::{fs::OpenOptions,io::Write,sync::atomic::{AtomicU64,Ordering}};
    static NEXT:AtomicU64=AtomicU64::new(0);

    fn open_fixture(g:&Geometry)->(std::path::PathBuf,Vec<u8>,PackedFile){
        let bytes=fixture_bytes(g).unwrap();
        open_bytes(g,bytes)
    }
    fn open_bytes(g:&Geometry,bytes:Vec<u8>)->(std::path::PathBuf,Vec<u8>,PackedFile){
        let path=std::env::temp_dir().join(format!("dyadic-edge-{}-{}.bin",std::process::id(),NEXT.fetch_add(1,Ordering::Relaxed)));
        let mut file=OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
        file.write_all(&bytes).unwrap();drop(file);
        let source=PackedFile::open(&path,g.global_log).unwrap();
        assert!(OpenOptions::new().write(true).open(&path).is_err());
        (path,bytes,source)
    }
    fn rows_under_statement(source:&PackedFile,honest_source:&PackedFile,honest:&PackedCommitted,
        setup:&Setup)->PackedCommitted{
        let rows=if std::ptr::eq(source,honest_source){
            PackedCommitted{rows:honest.rows.clone(),commitment:honest.commitment.clone(),nu:honest.nu,sigma:honest.sigma}
        }else{packed::commit(source,setup).unwrap()};
        PackedCommitted{commitment:honest.commitment.clone(),..rows}
    }
    fn mixed_openings(g:&Geometry,expected:&ExpectedStatement,committed:&PackedCommitted,setup:&Setup,
        gkr_source:&PackedFile,left_source:&PackedFile,right_source:&PackedFile,honest_source:&PackedFile)->(Proof,Transcript,Transcript){
        let circuit=local_circuit(g).unwrap();let mut t=starter(expected);
        let(gkr,claim)=sparse_stream_boolean::prove(&circuit,g.log_copies,
            |copy|load_pair(gkr_source,g,copy).map_err(|_|gkr::GkrError::InvalidInputWidth),&mut t).unwrap();
        let points=derive_points(g,&claim.point).unwrap();
        let values=[left_source.evaluate(&points[0]).unwrap(),right_source.evaluate(&points[1]).unwrap()];
        bind_tail(&mut t,&claim,&points,&values).unwrap();
        let left_committed=rows_under_statement(left_source,honest_source,committed,setup);
        let left=packed::open(&left_committed,left_source,&points[0],setup,&mut t).unwrap();
        let after_left=t.clone();
        let right_committed=rows_under_statement(right_source,honest_source,committed,setup);
        let right=packed::open(&right_committed,right_source,&points[1],setup,&mut t).unwrap();
        (Proof{gkr,values,openings:[left,right]},after_left,t)
    }
    fn verify_omitting_opening(context:&VerifierContext,expected:&ExpectedStatement,claim:&InputClaim,
        points:&[Vec<Fr>;2],values:&[Fr;2],openings:&[ArkDoryProof;2],omit:usize,t:&mut Transcript)->Result<(),String>{
        bind_tail(t,claim,points,values)?;let c=pcs::decode_commitment(&expected.commitment)?;
        for side in 0..2{let result=context.verify_one(c.clone(),values[side],&points[side],&openings[side],t);
            if side==omit{if result.is_ok(){return Err("omitted PCS unexpectedly passed".into());}}
            else{result.map_err(|e|format!("non-omitted PCS {} rejected: {e}",if side==0{"L"}else{"R"}))?;}}
        Ok(())
    }
    fn flip_unused_endpoint(bytes:&mut [u8],slot:usize){
        let bit=slot*WIDTH+ENDPOINT_BASE;bytes[bit/8]^=1<<(bit%8);
    }
    fn expected_for(g:&Geometry)->ExpectedStatement{
        let commitment=ArkGT(ark_ec::pairing::PairingOutput::<Bn254>::zero());let circuit=local_circuit(g).unwrap();
        ExpectedStatement {profile:"dyadic-edge-gkr-two-pcs-v1".into(),version:VERSION,
            tree:Descriptor::new(g.headers,[0x53;32]).unwrap(),geometry:g.clone(),
            setup_mode:if g.headers==3{"release-admitted-log22"}else{"independently-regenerated-log23-diagnostic"}.into(),
            setup_id:[0x27;32],commitment:pcs::encode_commitment(&commitment).unwrap(),
            corpus_blake2b256:[0x91;32],circuit_blake2b256:layout::hash_terms(&circuit.terms)}
    }
    fn reject_statement(s:ExpectedStatement){assert!(s.validate().is_err());}
    fn starter(s:&ExpectedStatement)->Transcript{new_transcript(s).unwrap()}
    fn geometries()->Vec<Geometry>{
        [(3,1,0),(3,1,1),(5,1,0),(5,1,1),(5,2,0),(5,2,1)]
            .into_iter().map(|(h,l,b)|Geometry::new(h,l,b).unwrap()).collect()
    }

    #[test]
    fn every_local_gate_matches_b1_child_enumeration_and_isolation(){
        let base=layout::shared_baseline().unwrap();
        for g in geometries(){
            let tree=Topology::new(base,g.headers,[0x53;32]).unwrap();
            let family_name=format!("level_{}_child_{}",g.level,g.branch);
            let family=tree.families.iter().find(|f|f.name==family_name).unwrap();
            assert_eq!(family.mapping,Mapping::Child{level:g.level,branch:g.branch});
            let full=family.enumerate(&tree.descriptor,256*g.copies).unwrap();
            let local=local_circuit(&g).unwrap();assert_eq!(full.terms.len(),256*g.copies);
            for copy in 0..g.copies{let(parent,child)=g.indices(copy).unwrap();
                for bit in 0..256{let actual=&full.terms[copy*256+bit];let wanted=&local.terms[bit];
                    assert_eq!(actual.row,parent*256+bit);
                    assert_eq!(actual.gate.left,parent*WIDTH+ENDPOINT_BASE+wanted.gate.left);
                    assert_eq!(actual.gate.right,child*WIDTH+ENDPOINT_BASE+wanted.gate.right-ENDPOINT_WIDTH);
                    assert_eq!(actual.gate.c0,wanted.gate.c0);assert_eq!(actual.gate.c1,wanted.gate.c1);
                    assert_eq!(actual.gate.c2,wanted.gate.c2);assert_eq!(actual.gate.c3,wanted.gate.c3);
                }
            }
            let mut omitted=local.clone();omitted.terms.pop();assert_ne!(omitted,local);
            let wrong=local_circuit(&Geometry::new(g.headers,g.level,g.branch^1).unwrap()).unwrap();assert_ne!(wrong,local);
        }
    }

    #[test]
    fn dense_virtual_mle_matches_both_embedded_global_openings(){
        for g in geometries(){
            let(path,_bytes,source)=open_fixture(&g);
            let pairs=(0..g.copies).map(|j|load_pair(&source,&g,j).unwrap()).collect::<Vec<_>>();
            let virtual_input=pairs.iter().flatten().copied().collect::<Vec<_>>();
            let virtual_point=(0..14+g.log_copies).map(|i|Fr::from((i*17+23) as u64)).collect::<Vec<_>>();
            for selector in [Fr::zero(),Fr::one(),Fr::from(37u64)]{
                let mut point=virtual_point.clone();point[13]=selector;
                let global=derive_points(&g,&point).unwrap();
                let left_mle_point=point[..13].iter().chain(&point[14..]).copied().collect::<Vec<_>>();
                let left_values=pairs.iter().map(|v|v[..ENDPOINT_WIDTH].to_vec()).flatten().collect::<Vec<_>>();
                let right_values=pairs.iter().map(|v|v[ENDPOINT_WIDTH..].to_vec()).flatten().collect::<Vec<_>>();
                let l=gkr::mle(&left_values,&left_mle_point).unwrap();let r=gkr::mle(&right_values,&left_mle_point).unwrap();
                assert_eq!(source.evaluate(&global[0]).unwrap(),l);
                assert_eq!(source.evaluate(&global[1]).unwrap(),r);
                let expected=(Fr::one()-selector)*l+selector*r;
                assert_eq!(gkr::mle(&virtual_input,&point).unwrap(),expected);
            }
            drop(source);std::fs::remove_file(path).unwrap();
        }
    }

    #[test]
    fn dense_generic_and_boolean_streaming_proofs_have_identical_claims_and_transcripts(){
        for g in geometries(){
            let(path,_bytes,source)=open_fixture(&g);let pairs=(0..g.copies).map(|j|load_pair(&source,&g,j).unwrap()).collect::<Vec<_>>();
            let input=pairs.iter().flatten().copied().collect::<Vec<_>>();let circuit=local_circuit(&g).unwrap();let statement=expected_for(&g);
            let mut dense_t=starter(&statement);let dense=sparse::prove(&circuit,&input,g.log_copies,&mut dense_t).unwrap();
            let mut stream_t=starter(&statement);let stream=sparse_stream::prove(&circuit,g.log_copies,|j|Ok(pairs[j].clone()),&mut stream_t).unwrap();
            let mut bool_t=starter(&statement);let boolean=sparse_stream_boolean::prove(&circuit,g.log_copies,|j|Ok(pairs[j].clone()),&mut bool_t).unwrap();
            assert_eq!(dense,stream);assert_eq!(stream,boolean);
            for t in [&stream_t,&bool_t]{assert_eq!(dense_t.challenges(),t.challenges());assert_eq!(dense_t.raw_queries(),t.raw_queries());assert_eq!(dense_t.bytes_absorbed(),t.bytes_absorbed());}
            assert_eq!(dense_t.clone().challenge_scalar(b"continuation"),stream_t.clone().challenge_scalar(b"continuation"));
            assert_eq!(dense_t.clone().challenge_scalar(b"continuation"),bool_t.clone().challenge_scalar(b"continuation"));
            let claim=sparse::verify(&circuit,g.log_copies,&boolean.0,&mut starter(&statement)).unwrap();assert_eq!(claim,boolean.1);
            drop(source);std::fs::remove_file(path).unwrap();
        }
    }

    #[test]
    fn h3_edge_exports_and_verifies_both_openings(){
        let g=Geometry::new(3,1,1).unwrap();let(path,_bytes,source)=open_fixture(&g);
        let setup=pcs::generate_setup(g.global_log).unwrap();
        let committed=packed::commit(&source,&setup).unwrap();
        let expected=ExpectedStatement::new(g.clone(),[0x53;32],&setup,&committed.commitment,corpus_digest(&_bytes)).unwrap();
        let statement_bytes=encode_statement(&expected).unwrap();let parsed=decode_statement(&statement_bytes).unwrap();assert_eq!(parsed,expected);
        let(proof,metrics)=prove(&source,&committed,&setup,&expected).unwrap();
        assert_eq!(metrics.load_pair_reads,(14+5)*g.copies);
        assert_eq!(metrics.maximum_pair_and_second_bank_fields,PAIR_WIDTH+ENDPOINT_WIDTH);
        let packet=encode_proof(&expected,&proof).unwrap();assert_eq!(packet.len(),proof_bytes(&g).unwrap());
        let decoded=decode_proof(&expected,&packet).unwrap();assert_eq!(encode_proof(&expected,&decoded).unwrap(),packet);
        assert!(decode_proof(&expected,&packet[..packet.len()-1]).is_err());
        let mut bad_magic=packet.clone();bad_magic[0]^=1;assert!(decode_proof(&expected,&bad_magic).is_err());
        let mut bad_version=packet.clone();bad_version[8]^=1;assert!(decode_proof(&expected,&bad_version).is_err());
        let mut trailing=packet.clone();trailing.push(0);assert!(decode_proof(&expected,&trailing).is_err());
        let value_at=9+32*(7*(14+g.log_copies)+3);let mut noncanonical=packet.clone();noncanonical[value_at..value_at+32].fill(0xff);
        assert!(decode_proof(&expected,&noncanonical).is_err());
        let context=VerifierContext::load(&expected).unwrap();let verified=verify(&expected,&decoded,&context).unwrap();
        assert_eq!(verified.transcript_challenges,metrics.transcript_challenges);
        assert_eq!(verified.transcript_raw_queries,metrics.transcript_raw_queries);
        let mut wrong=expected.clone();wrong.tree.root[0]^=1;assert!(verify(&wrong,&decoded,&context).is_err());
        let mut wrong_mapping=expected.clone();wrong_mapping.geometry.branch=0;
        wrong_mapping.circuit_blake2b256=layout::hash_terms(&local_circuit(&wrong_mapping.geometry).unwrap().terms);
        wrong_mapping.validate().unwrap();assert!(verify(&wrong_mapping,&decoded,&context).is_err(),"a coherently rehashed wrong branch must fail against the external statement");
        let mut wrong_bank=expected.clone();wrong_bank.geometry.bank_offset+=ENDPOINT_WIDTH;assert!(wrong_bank.validate().is_err());
        let mut wrong_shape=expected.clone();wrong_shape.geometry.copies+=1;assert!(wrong_shape.validate().is_err());
        let mut wrong_order=expected.clone();wrong_order.geometry.coordinate_order.push('x');assert!(wrong_order.validate().is_err());
        let mut wrong_setup=expected.clone();wrong_setup.setup_id[0]^=1;assert!(context.admit(&wrong_setup).is_err());
        let mut changed_value=decode_proof(&expected,&packet).unwrap();changed_value.values[0]+=Fr::one();assert!(verify(&expected,&changed_value,&context).is_err());
        let mut swapped=decode_proof(&expected,&packet).unwrap();swapped.openings.swap(0,1);assert!(verify(&expected,&swapped,&context).is_err());

        // A fresh Q changes only one unconstrained parent bit. Its edge equalities
        // remain true; PCS-L is false under C_P while PCS-R stays honest on P.
        let mut q_bytes=_bytes.clone();flip_unused_endpoint(&mut q_bytes,0);let(q_path,_q_bytes,q)=open_bytes(&g,q_bytes);
        let(q_left,q_producer_after_left,_) = mixed_openings(&g,&expected,&committed,&setup,&q,&q,&source,&source);
        let mut q_verify_t=starter(&expected);let q_claim=sparse::verify(&local_circuit(&g).unwrap(),g.log_copies,&q_left.gkr,&mut q_verify_t).unwrap();
        let q_points=derive_points(&g,&q_claim.point).unwrap();let p_left=source.evaluate(&q_points[0]).unwrap();
        assert_ne!(q_left.values[0],p_left,"fresh parent forgery must change the derived left MLE");
        assert!(((Fr::one()-q_claim.point[13])*q_left.values[0]+q_claim.point[13]*q_left.values[1]-q_claim.value).is_zero());
        assert!(verify(&expected,&q_left,&context).is_err());

        // Isolate the failed PCS-L predicate. If omitted, the same transcript
        // must continue exactly as the producer did and the honest PCS-R accepts.
        let mut omit_left_t=starter(&expected);let claim=sparse::verify(&local_circuit(&g).unwrap(),g.log_copies,&q_left.gkr,&mut omit_left_t).unwrap();
        let points=derive_points(&g,&claim.point).unwrap();bind_tail(&mut omit_left_t,&claim,&points,&q_left.values).unwrap();
        assert!(context.verify_one(pcs::decode_commitment(&expected.commitment).unwrap(),q_left.values[0],&points[0],
            &q_left.openings[0],&mut omit_left_t).is_err());
        assert_eq!(omit_left_t.challenges(),q_producer_after_left.challenges());
        assert_eq!(omit_left_t.raw_queries(),q_producer_after_left.raw_queries());
        assert_eq!(omit_left_t.bytes_absorbed(),q_producer_after_left.bytes_absorbed());
        assert_eq!(omit_left_t.clone().challenge_scalar(b"omission-continuation"),
            q_producer_after_left.clone().challenge_scalar(b"omission-continuation"));
        assert!(context.verify_one(pcs::decode_commitment(&expected.commitment).unwrap(),q_left.values[1],&points[1],
            &q_left.openings[1],&mut omit_left_t).is_ok(),"omitting PCS-L alone must accept this one-sided forgery");

        // A fresh Q on the child side reaches PCS-R after a valid PCS-L; omitting
        // only the right verifier predicate would accept the forged statement.
        let mut r_bytes=_bytes.clone();flip_unused_endpoint(&mut r_bytes,1);let(r_path,_r_bytes,r)=open_bytes(&g,r_bytes);
        let(r_forgery,_,_) = mixed_openings(&g,&expected,&committed,&setup,&r,&source,&r,&source);
        let mut right_t=starter(&expected);let right_claim=sparse::verify(&local_circuit(&g).unwrap(),g.log_copies,&r_forgery.gkr,&mut right_t).unwrap();
        let right_points=derive_points(&g,&right_claim.point).unwrap();assert!(((Fr::one()-right_claim.point[13])*r_forgery.values[0]+
            right_claim.point[13]*r_forgery.values[1]-right_claim.value).is_zero());
        assert_ne!(r_forgery.values[1],source.evaluate(&right_points[1]).unwrap(),"fresh child forgery must change the derived right MLE");
        bind_tail(&mut right_t,&right_claim,&right_points,&r_forgery.values).unwrap();
        assert!(context.verify_one(pcs::decode_commitment(&expected.commitment).unwrap(),r_forgery.values[0],&right_points[0],
            &r_forgery.openings[0],&mut right_t).is_ok());
        assert!(context.verify_one(pcs::decode_commitment(&expected.commitment).unwrap(),r_forgery.values[1],&right_points[1],
            &r_forgery.openings[1],&mut right_t).is_err());
        assert!(verify_right_omitted(&expected,&r_forgery,&context).is_ok(),"omitting PCS-R alone must accept this one-sided forgery");
        let other_commitment=packed::commit(&q,&setup).unwrap();let mut wrong_c=expected.clone();
        // Keep every statement byte but C fixed; only the authenticated commitment changes.
        wrong_c.commitment=pcs::encode_commitment(&other_commitment.commitment).unwrap();
        wrong_c.validate().unwrap();assert!(verify(&wrong_c,&decoded,&context).is_err(),"a valid but wrong external commitment must reject the packet");
        drop(source);drop(q);drop(r);std::fs::remove_file(path).unwrap();std::fs::remove_file(q_path).unwrap();std::fs::remove_file(r_path).unwrap();
    }

    #[test]
    fn external_statement_rejects_each_noncanonical_field(){
        let base=expected_for(&Geometry::new(3,1,1).unwrap());
        let mut s=base.clone();s.profile.push('x');reject_statement(s);
        let mut s=base.clone();s.version^=1;reject_statement(s);
        let mut s=base.clone();s.tree.headers=5;reject_statement(s);
        let mut s=base.clone();s.setup_mode.push('x');reject_statement(s);
        let mut s=base.clone();s.circuit_blake2b256.push('x');reject_statement(s);
        let mut s=base.clone();s.geometry.level=2;reject_statement(s);
        let mut s=base.clone();s.geometry.branch=2;reject_statement(s);
        let mut s=base.clone();s.geometry.copies+=1;reject_statement(s);
        let mut s=base.clone();s.geometry.log_copies^=1;reject_statement(s);
        let mut s=base.clone();s.geometry.parent_base+=1;reject_statement(s);
        let mut s=base.clone();s.geometry.child_base+=1;reject_statement(s);
        let mut s=base.clone();s.geometry.bank_offset+=ENDPOINT_WIDTH;reject_statement(s);
        let mut s=base.clone();s.geometry.bank_width^=1;reject_statement(s);
        let mut s=base.clone();s.geometry.header_width^=1;reject_statement(s);
        let mut s=base.clone();s.geometry.global_log+=1;reject_statement(s);
        let mut s=base.clone();s.geometry.coordinate_order.push('x');reject_statement(s);
        let mut s=base.clone();s.geometry.leaves+=1;reject_statement(s);
        let mut s=base;s.geometry.slots+=1;reject_statement(s);
    }

    fn verify_right_omitted(expected:&ExpectedStatement,proof:&Proof,context:&VerifierContext)->Result<(),String>{
        let mut t=starter(expected);let g=&expected.geometry;
        let claim=sparse::verify(&local_circuit(g)?,g.log_copies,&proof.gkr,&mut t).map_err(|e|e.to_string())?;
        let points=derive_points(g,&claim.point)?;bind_tail(&mut t,&claim,&points,&proof.values)?;
        context.verify_one(pcs::decode_commitment(&expected.commitment)?,proof.values[0],&points[0],&proof.openings[0],&mut t)
    }

    #[test]
    fn wrong_child_and_single_omitted_equality_have_isolated_witnesses(){
        let g=Geometry::new(3,1,1).unwrap();let circuit=local_circuit(&g).unwrap();
        let wrong_geometry=Geometry::new(3,1,0).unwrap();let(wrong_path,_wrong_bytes,wrong_source)=open_bytes(&g,fixture_bytes(&wrong_geometry).unwrap());
        let wrong_pair=load_pair(&wrong_source,&g,0).unwrap();
        assert!(sparse::prove(&circuit,&wrong_pair,g.log_copies,&mut starter(&expected_for(&g))).is_err(),"wrong child must violate the expected mapping");
        let(path,mutated_bytes,canonical_source)=open_fixture(&g);
        let(parent,child)=g.indices(0).unwrap();let wrong_bank_offset=ENDPOINT_BASE+ENDPOINT_WIDTH;
        let wrong_bank_index=|slot:usize|slot*(WIDTH/ENDPOINT_WIDTH)+wrong_bank_offset/ENDPOINT_WIDTH;
        let mut wrong_bank_pair=canonical_source.read_copy(ENDPOINT_WIDTH,wrong_bank_index(parent)).unwrap();
        wrong_bank_pair.extend(canonical_source.read_copy(ENDPOINT_WIDTH,wrong_bank_index(child)).unwrap());
        assert_ne!(wrong_bank_pair,load_pair(&canonical_source,&g,0).unwrap(),"the selected offset must read the other bank");
        assert!(sparse::prove(&circuit,&wrong_bank_pair,g.log_copies,&mut starter(&expected_for(&g))).is_err(),
            "a concrete pair read from the wrong endpoint bank must violate the canonical B1 equality family");
        let term=&circuit.terms[0];let constrained_bit=ENDPOINT_BASE+term.gate.left;
        let mut bytes=mutated_bytes.clone();bytes[constrained_bit/8]^=1<<(constrained_bit%8);
        let(mutant_path,_mutant_bytes,mutant_source)=open_bytes(&g,bytes);let input=load_pair(&mutant_source,&g,0).unwrap();
        assert!(sparse::prove(&circuit,&input,g.log_copies,&mut starter(&expected_for(&g))).is_err(),"the complete B1 family must reject one broken equality");
        let mut omitted=circuit.clone();omitted.terms.remove(0);
        let(mutant_proof,mutant_claim)=sparse::prove(&omitted,&input,g.log_copies,&mut starter(&expected_for(&g))).unwrap();
        assert_eq!(sparse::verify(&omitted,g.log_copies,&mutant_proof,&mut starter(&expected_for(&g))).unwrap(),mutant_claim,
            "removing only the broken equality must explain the acceptance");
        drop(wrong_source);drop(canonical_source);drop(mutant_source);std::fs::remove_file(wrong_path).unwrap();std::fs::remove_file(path).unwrap();std::fs::remove_file(mutant_path).unwrap();
    }

    #[test]
    fn zero_weight_opening_is_still_checked_at_selector_endpoints(){
        let g=Geometry::new(3,1,1).unwrap();let(path,bytes,source)=open_fixture(&g);let setup=pcs::generate_setup(g.global_log).unwrap();
        let committed=packed::commit(&source,&setup).unwrap();let expected=ExpectedStatement::new(g.clone(),[0x53;32],&setup,&committed.commitment,corpus_digest(&bytes)).unwrap();
        let context=VerifierContext::load(&expected).unwrap();
        for (selector,mutated_slot,bad_side) in [(Fr::zero(),1usize,1usize),(Fr::one(),0usize,0usize)]{
            let mut point=(0..14).map(|i|Fr::from((i+11) as u64)).collect::<Vec<_>>();point[13]=selector;
            let points=derive_points(&g,&point).unwrap();let p_values=[source.evaluate(&points[0]).unwrap(),source.evaluate(&points[1]).unwrap()];
            let mut q_bytes=bytes.clone();flip_unused_endpoint(&mut q_bytes,mutated_slot);let(q_path,_q_bytes,q)=open_bytes(&g,q_bytes);
            let values=if selector.is_zero(){[p_values[0],q.evaluate(&points[1]).unwrap()]}
                else{[q.evaluate(&points[0]).unwrap(),p_values[1]]};
            let claim=InputClaim{point,value:(Fr::one()-selector)*p_values[0]+selector*p_values[1]};
            if bad_side==0{assert_ne!(values[0],p_values[0]);}else{assert_ne!(values[1],p_values[1]);}
            let left_committed=rows_under_statement(if bad_side==0{&q}else{&source},&source,&committed,&setup);
            let right_committed=rows_under_statement(if bad_side==1{&q}else{&source},&source,&committed,&setup);
            let mut producer_t=starter(&expected);bind_tail(&mut producer_t,&claim,&points,&values).unwrap();
            let left=packed::open(&left_committed,if bad_side==0{&q}else{&source},&points[0],&setup,&mut producer_t).unwrap();
            let right=packed::open(&right_committed,if bad_side==1{&q}else{&source},&points[1],&setup,&mut producer_t).unwrap();
            let openings=[left,right];let mut verifier_t=starter(&expected);
            let error=verify_openings(&context,&expected,&claim,&points,&values,&openings,&mut verifier_t).unwrap_err();
            assert!(error.contains(if bad_side==0{"PCS L"}else{"PCS R"}),"wrong opening rejected: {error}");
            let mut omitted_t=starter(&expected);verify_omitting_opening(&context,&expected,&claim,&points,&values,&openings,bad_side,&mut omitted_t).unwrap();
            drop(q);std::fs::remove_file(q_path).unwrap();
        }
        drop(source);std::fs::remove_file(path).unwrap();
    }
}

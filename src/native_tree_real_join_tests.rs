//! C572 concrete N3 Tree diagnostic, not complete history authentication.
use super::*;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use crate::{work_tree_wiring as tree, work_tree_fixed_hash as fixed,
    sparse_stream_roster::{self as edge, EdgeTerm}};
use dory_pcs::backends::arkworks::{ArkDoryProof, ArkworksVerifierSetup};
use std::{cell::Cell, path::Path};

const C572_DOMAIN: &[u8] = b"nipopow-native-tree-diagnostic-v1";
#[derive(Clone, PartialEq, Eq)]
struct C572Member { name: String, width: usize, terms: usize }
struct C572Plan<'p> {
    parent: &'p WorkTreeHistoryPlan, engine: &'static fixed::Engine,
    members: Vec<C572Member>, widths: Vec<usize>,
}
impl<'p> C572Plan<'p> {
    fn expected(parent: &'p WorkTreeHistoryPlan, key: &AdmittedVerifierKey) -> Result<Self,String> {
        let d = parent.descriptor();
        if parent.headers()!=3 || parent.slot_log()!=2 || parent.slots()!=4 || key.log_n()!=22
            || d.genuine!=2 || d.leaves!=2 || d.slots!=4
            || &parent.topology().descriptor!=d || &parent.fixed_profile().tree!=d
            || &parent.leaf_profile().tree!=d || &parent.work_profile().tree!=d
        { return Err("C572 admission geometry".into()); }
        require_work_key22(key)?;
        if tree::full_roster_shape(parent.topology())? != (16,5,21,22)
            || parent.topology().families.len()!=12 || parent.work_boundary().links().len()!=3
        { return Err("C572 roster geometry".into()); }
        let engine = fixed::engine()?; let mut members = Vec::new();
        members.try_reserve_exact(18).map_err(|_|"C572 member allocation")?;
        let mut add = |name: String, width: usize, count: u64| -> Result<(),String> {
            if members.len()>=18 || width>14 { return Err("C572 local member bounds".into()); }
            members.push(C572Member { name, width, terms: usize::try_from(count).map_err(|_|"C572 gross count overflow")? }); Ok(())
        };
        for f in &parent.topology().families {
            let c=f.count(d)?;add(f.name.clone(),c.row_log.checked_sub(2).ok_or("C572 B1 local width")?,c.terms)?;
        }
        add("B2_fixed_hash".into(),11,fixed::count(engine,parent.fixed_profile())?.total_boundary_terms)?;
        add("B3_leaf_hash".into(),14,crate::work_tree_leaf_hash::count(engine,parent.leaf_boundary())?["new_boundary_terms"].as_u64().ok_or("C572 B3 gross count")?)?;
        add("B4_local_work".into(),11,crate::work_tree_work::count(parent.work_boundary())?["new_local_terms"].as_u64().ok_or("C572 B4 gross count")?)?;
        for f in parent.work_boundary().links() {
            let c=f.count(d)?;add(f.name.clone(),c.row_log.checked_sub(2).ok_or("C572 link local width")?,c.terms)?;
        }
        drop(add);
        let total=members.iter().try_fold(0usize,|n,m|n.checked_add(m.terms).ok_or("C572 gross sum overflow"))?;
        if members.len()!=18 || total!=111668 { return Err("C572 gross member census".into()); }
        let mut widths=Vec::new();widths.try_reserve_exact(18).map_err(|_|"C572 width allocation")?;
        widths.extend(members.iter().map(|m|m.width));
        Ok(Self {parent,engine,members,widths})
    }
    fn require(&self, key: &AdmittedVerifierKey) -> Result<(),String> {
        let expected=Self::expected(self.parent,key)?;self.require_members(&expected.members)?;
        if self.widths!=expected.widths || !std::ptr::eq(self.engine,expected.engine) {
            return Err("C572 canonical plan identity".into());
        } Ok(())
    }
    fn require_members(&self, members: &[C572Member]) -> Result<(),String> {
        if self.members!=members { return Err("C572 ordered member metadata".into()); } Ok(())
    }
    fn check_edge(&self, item: &EdgeTerm, left: bool, owner: usize) -> Result<usize,String> {
        if owner>=4 || item.term.row>=1usize<<21 {return Err("C572 edge global domain".into());}
        tree::check_role2_endpoint_edge(item,left,owner,2,&self.widths)
    }
    // Forward every unchanged canonical callback once; no selection/dedup/remap.
    fn visit(&self, left: bool, owner: usize, sink: &mut dyn FnMut(EdgeTerm)->Result<(),String>) -> Result<(),String> {
        tree::visit_full_roster_endpoint(self.parent.topology(),self.engine,self.parent.fixed_profile(),
            self.parent.leaf_boundary(),self.parent.work_boundary(),left,owner,&mut |item| {
                self.check_edge(&item,left,owner)?; sink(item)
            })
    }
    fn preflight(&self) -> Result<(),String> {
        for left in [true,false] {
            let mut counts=[0usize;18];
            for owner in 0..4 {self.visit(left,owner,&mut |item| {
                let tag=item.family_row>>14;counts[tag]=counts[tag].checked_add(1).ok_or("C572 census overflow")?;
                if counts[tag]>self.members[tag].terms{return Err("C572 member excess".into());} Ok(())
            })?;}
            for (m,n) in self.members.iter().zip(counts) {if m.terms!=n{return Err("C572 member missing count".into());}}
        } Ok(())
    }
    fn bind_roster(&self, t: &mut Transcript) {
        tree::bind_full_roster(self.parent.topology(),self.parent.fixed_profile(),self.parent.leaf_profile(),self.parent.work_profile(),t)
    }
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr;4],String> {
        tree::full_roster_coefficients(self.parent.topology(),self.engine,self.parent.fixed_profile(),self.parent.leaf_boundary(),self.parent.work_boundary(),r,u,v)
    }
    fn literal_coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
        if r.len()!=21||u.len()!=22||v.len()!=22{return Err("C572 terminal dimensions".into());}
        fn eq(p:&[Fr],mut n:usize)->Result<Fr,String>{
            let mut w=Fr::one();for x in p {w*=if n&1==0{Fr::one()-x}else{*x};n>>=1;}
            if n!=0{return Err("C572 literal coordinate".into());}Ok(w)
        }
        let mut out=[Fr::zero();4];let mut count=0usize;
        for owner in 0..4 {self.visit(true,owner,&mut |item|{
            let a=&item.term;let w=eq(r,a.row)?*eq(u,a.gate.left)?*eq(v,a.gate.right)?;
            for (sum,c) in out.iter_mut().zip([a.gate.c0,a.gate.c1,a.gate.c2,a.gate.c3]){*sum+=w*c;}
            count+=1;if count>111668{return Err("C572 literal count excess".into());}Ok(())
        })?;}
        if count!=111668{return Err("C572 literal count".into());}Ok(out)
    }
}

struct C572Bounds {c:usize,key:usize,gkr:usize,pcs:usize,rounds_at:usize}
fn c572_bounds()->Result<C572Bounds,String>{
    let gt=ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero().compressed_size();
    let g1=ark_bn254::G1Projective::zero().compressed_size();let g2=ark_bn254::G2Projective::zero().compressed_size();
    let sigma=22usize.div_ceil(2);let at=2*gt+g1;
    let b=C572Bounds{c:gt,key:1920*(sigma+1)+624,gkr:(7*22+3)*Fr::zero().compressed_size(),
        pcs:at+4+sigma*(6*gt+3*g1+3*g2)+1+g1+g2+8,rounds_at:at};
    if (b.c,b.key,b.gkr,b.pcs,sigma)!=(384,23664,5024,29421,11){return Err("C572 codec dimensions".into());}Ok(b)
}
struct C572Context<'p>{plan:C572Plan<'p>,key_id:[u8;32],key_bytes:Vec<u8>,c:ArkGT,c_bytes:Vec<u8>}
impl<'p>C572Context<'p>{
    fn expected(parent:&'p WorkTreeHistoryPlan,key:&AdmittedVerifierKey,c:&[u8])->Result<Self,String>{
        let plan=C572Plan::expected(parent,key)?;let b=c572_bounds()?;
        if c.len()!=b.c{return Err("C572 commitment extent".into());}
        let value=pcs::decode_commitment(c).map_err(|e|format!("C572 commitment encoding: {e}"))?;
        let bytes=pcs::encode(&ArkworksVerifierSetup(key.verifier().clone()))?;
        if bytes.len()!=b.key{return Err("C572 key extent".into());}
        Ok(Self{plan,key_id:*key.id(),key_bytes:bytes,c:value,c_bytes:c.to_vec()})
    }
    fn require(&self,key:&AdmittedVerifierKey)->Result<(),String>{
        self.plan.require(key)?;let b=c572_bounds()?;
        if self.key_id!=*key.id()||self.key_bytes.len()!=b.key
            ||self.key_bytes.as_slice()!=include_bytes!("../fixtures/verifier-keys-v1/log22.vk")
            ||self.c_bytes.len()!=b.c||pcs::encode_commitment(&self.c)?!=self.c_bytes
        {return Err("C572 expected identity".into());}pcs::decode_commitment(&self.c_bytes)?;Ok(())
    }
    fn bind(&self,key:&AdmittedVerifierKey,t:&mut Transcript)->Result<(),String>{
        self.require(key)?;if t.challenges()!=0{return Err("C572 context already challenged".into());}
        let p=self.plan.parent;let d=p.descriptor();
        t.append_u64(b"c572-tree-version",1);
        t.append_bytes(b"c572-tree-role",b"full-B1-B2-B3-B4");
        t.append_bytes(b"c572-tree-policy",b"native-N3-full-roster-18-gross-empty-ordinals-v1");
        for(label,n)in[(b"c572-tree-N".as_slice(),p.headers()),(b"c572-tree-H",p.slot_log()as u64),
            (b"c572-tree-slots",p.slots()as u64),(b"c572-tree-genuine",d.genuine as u64),(b"c572-tree-leaves",d.leaves as u64)]{t.append_u64(label,n);}
        t.append_bytes(b"c572-tree-root",&d.root);t.append_bytes(b"c572-tree-total",&p.work_profile().total_be28);
        for(label,n)in[(b"c572-tree-input-log".as_slice(),22u64),(b"c572-tree-row-log",21),(b"c572-tree-local-input",20),
            (b"c572-tree-slot-bits",2),(b"c572-tree-base-row",14),(b"c572-tree-family-bits",5),(b"c572-tree-members",18),(b"c572-tree-terms",111668)]{t.append_u64(label,n);}
        for(i,m)in self.plan.members.iter().enumerate(){
            t.append_u64(b"c572-tree-member-index",i as u64);t.append_bytes(b"c572-tree-member-name",m.name.as_bytes());
            t.append_u64(b"c572-tree-member-local-width",m.width as u64);t.append_u64(b"c572-tree-member-terms",m.terms as u64);
        }
        t.append_bytes(b"c572-tree-template",self.plan.engine.base.inventory.core.terms_blake2b256.as_bytes());
        t.append_bytes(b"c572-tree-inventory",self.plan.engine.base.inventory.descriptor_blake2b256.as_bytes());
        t.append_bytes(b"c572-tree-mode",b"Transparent-dory-v1");t.append_bytes(b"c572-tree-vendor",pcs::VENDOR_PIN);
        t.append_bytes(b"c572-tree-key-id",&self.key_id);t.append_bytes(b"c572-tree-key-bytes",&self.key_bytes);t.append_bytes(b"c572-tree-C",&self.c_bytes);
        Ok(()) // Only the helper/verifier callback adds bind_full_roster.
    }
}
fn c572_separator(t:&mut Transcript){t.append_bytes(b"c572-tree-authentication-boundary",b"gkr-to-pcs-v1");}
#[derive(Clone)]struct C572Proof{gkr:Vec<u8>,pcs:Vec<u8>}
fn c572_encode_publish(g:&gkr::GkrProof,o:&ArkDoryProof,next:Transcript,t:&mut Transcript)->Result<C572Proof,String>{
    let p=C572Proof{gkr:gkr::encode_proof(g)?,pcs:pcs::encode_proof(o)?};let b=c572_bounds()?;
    if p.gkr.len()!=b.gkr||p.pcs.len()!=b.pcs{return Err("C572 produced extent".into());}
    gkr::decode_dimensions(&[22],&p.gkr)?;pcs::decode_proof(&p.pcs,22)?;*t=next;Ok(p)
}
struct C572Verifier<'p,'k>{context:C572Context<'p>,key:&'k AdmittedVerifierKey}
impl<'p,'k>C572Verifier<'p,'k>{
    fn expected(p:&'p WorkTreeHistoryPlan,k:&'k AdmittedVerifierKey,c:&[u8])->Result<Self,String>{Ok(Self{context:C572Context::expected(p,k,c)?,key:k})}
    fn replay_gkr(&self,bytes:&[u8],prefix:&Transcript)->Result<(InputClaim,Transcript),String>{
        if bytes.len()!=c572_bounds()?.gkr{return Err("C572 GKR extent".into());}
        let proof=gkr::decode_dimensions(&[22],bytes).map_err(|e|format!("C572 GKR encoding: {e}"))?;
        if gkr::encode_proof(&proof)?!=bytes{return Err("C572 GKR canonical encoding".into());}
        let mut next=prefix.clone();self.context.bind(self.key,&mut next)?;
        let plan=&self.context.plan;
        let claim=gkr::verify_with_wiring(&[22],1usize<<21,&proof,&mut next,|t|plan.bind_roster(t),|layer,r,u,v|{
            if layer!=0{return Err(GkrError::ProofLayerCount);}plan.coefficients(r,u,v).map_err(|_|GkrError::PointDimension)
        }).map_err(|e|format!("C572 GKR: {e:?}"))?;
        if claim.point.len()!=22{return Err("C572 global claim dimension".into());}Ok((claim,next))
    }
    fn finish_pcs_on(&self,claim:&InputClaim,opening:&ArkDoryProof,t:&mut Transcript)->Result<(),String>{
        self.context.require(self.key)?;if claim.point.len()!=22{return Err("C572 global claim dimension".into());}
        let mut next=t.clone();c572_separator(&mut next);
        pcs::verify_admitted(self.context.c,claim.value,&claim.point,opening,self.key,&mut next).map_err(|e|format!("C572 PCS: {e}"))?;
        *t=next;Ok(())
    }
    fn verify_on(&self,p:&C572Proof,t:&mut Transcript)->Result<(),String>{
        self.context.require(self.key)?;let b=c572_bounds()?;
        if p.gkr.len()!=b.gkr{return Err("C572 GKR extent".into());}if p.pcs.len()!=b.pcs{return Err("C572 PCS extent".into());}
        let opening=pcs::decode_proof(&p.pcs,22).map_err(|e|format!("C572 PCS encoding: {e}"))?;
        let(claim,mut next)=self.replay_gkr(&p.gkr,t)?;self.finish_pcs_on(&claim,&opening,&mut next)?;*t=next;Ok(())
    }
    fn verify(&self,p:&C572Proof)->Result<Transcript,String>{let mut t=Transcript::new(C572_DOMAIN);self.verify_on(p,&mut t)?;Ok(t)}
}

struct C572HelperError{error:String,hits:usize,visits:usize,after_bind:usize,binds:usize,literal:usize,observed:[u64;3]}
struct C572Producer<'p>{work:NativeWorkProducer<'p>,plan:C572Plan<'p>}
impl<'p>C572Producer<'p>{
    fn new(p:&'p WorkTreeHistoryPlan,path:&Path,k:AdmittedVerifierKey)->Result<Self,String>{
        let plan=C572Plan::expected(p,&k)?;plan.preflight()?;
        Ok(Self{work:NativeWorkProducer::new(p,path,k)?,plan})
    }
    fn load(&self,owner:usize)->Result<Vec<Fr>,String>{ C573TreeBorrowed{work:&self.work,plan:&self.plan,legacy:true}.load(owner) }
    // Actual helper boundary: ONE normal proof plus ONE late-fault invocation.
    // Late mode emits no positive-path stage and never changes helper code.
    fn gkr_on(&self,t:&mut Transcript,late:bool)->Result<(gkr::GkrProof,InputClaim),C572HelperError>{ C573TreeBorrowed{work:&self.work,plan:&self.plan,legacy:true}.gkr_on(t,late) }
    fn prove_on(&self,t:&mut Transcript)->Result<C572Proof,String>{ C573TreeBorrowed{work:&self.work,plan:&self.plan,legacy:true}.prove_on(t) }
    fn prove(&self)->Result<(C572Proof,Transcript),String>{let mut t=Transcript::new(C572_DOMAIN);let p=self.prove_on(&mut t)?;Ok((p,t))}
}

fn c572_key()->AdmittedVerifierKey{crate::verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap()}
fn c572_mark(t:&Transcript)->((u64,u64,u64),[Fr;2]){
    let mut n=t.clone();((t.challenges(),t.raw_queries(),t.bytes_absorbed()),[n.challenge_scalar(b"c572-continuation-a"),n.challenge_scalar(b"c572-continuation-b")])
}
fn c572_reject(v:&C572Verifier<'_,'_>,p:&C572Proof,t:&mut Transcript,stage:&str){
    let before=c572_mark(t);let e=v.verify_on(p,t).err().expect("fault accepted");
    assert!(e.starts_with(stage),"expected {stage}, got {e}");assert_eq!(c572_mark(t),before);
}
// Literal framing differential: same fields/bytes, one final order or kind fault.
fn c572_reference_prefix(c:&C572Context<'_>,t:&mut Transcript,fault:usize){
    let p=c.plan.parent;let d=p.descriptor();
    if fault==2{t.append_bytes(b"c572-tree-version",&1u64.to_le_bytes());}else{t.append_u64(b"c572-tree-version",1);}
    t.append_bytes(b"c572-tree-role",b"full-B1-B2-B3-B4");
    t.append_bytes(b"c572-tree-policy",b"native-N3-full-roster-18-gross-empty-ordinals-v1");
    for(label,n)in[(b"c572-tree-N".as_slice(),p.headers()),(b"c572-tree-H",p.slot_log()as u64),
        (b"c572-tree-slots",p.slots()as u64),(b"c572-tree-genuine",d.genuine as u64),(b"c572-tree-leaves",d.leaves as u64)]{t.append_u64(label,n);}
    t.append_bytes(b"c572-tree-root",&d.root);t.append_bytes(b"c572-tree-total",&p.work_profile().total_be28);
    for(label,n)in[(b"c572-tree-input-log".as_slice(),22u64),(b"c572-tree-row-log",21),(b"c572-tree-local-input",20),
        (b"c572-tree-slot-bits",2),(b"c572-tree-base-row",14),(b"c572-tree-family-bits",5),(b"c572-tree-members",18),(b"c572-tree-terms",111668)]{t.append_u64(label,n);}
    for(i,m)in c.plan.members.iter().enumerate(){t.append_u64(b"c572-tree-member-index",i as u64);t.append_bytes(b"c572-tree-member-name",m.name.as_bytes());
        t.append_u64(b"c572-tree-member-local-width",m.width as u64);t.append_u64(b"c572-tree-member-terms",m.terms as u64);}
    t.append_bytes(b"c572-tree-template",c.plan.engine.base.inventory.core.terms_blake2b256.as_bytes());
    t.append_bytes(b"c572-tree-inventory",c.plan.engine.base.inventory.descriptor_blake2b256.as_bytes());
    t.append_bytes(b"c572-tree-mode",b"Transparent-dory-v1");t.append_bytes(b"c572-tree-vendor",pcs::VENDOR_PIN);
    t.append_bytes(b"c572-tree-key-id",&c.key_id);
    if fault==1{t.append_bytes(b"c572-tree-C",&c.c_bytes);t.append_bytes(b"c572-tree-key-bytes",&c.key_bytes);}
    else{t.append_bytes(b"c572-tree-key-bytes",&c.key_bytes);t.append_bytes(b"c572-tree-C",&c.c_bytes);}
}

#[test]
#[ignore="C572 genuine complete N3 Tree on held original4B53; separate controller/admission required"]
fn c572_real_n3_tree_same_x(){
    let headers=crate::historical_prefix_witness::retained_headers().unwrap();
    let native=crate::packed_owner_assembly::NativePrefix::from_raw_iter(3,headers.iter().map(|h|h.encode().map_err(|e|format!("{e:?}")))).unwrap();
    let p=WorkTreeHistoryPlan::compile(3,2,native.root(),native.total_be28()).unwrap();
    let poison=Path::new("Z:/c572-must-not-open.bits");
    let n4=WorkTreeHistoryPlan::compile(4,2,native.root(),native.total_be28()).unwrap();
    assert_eq!(C572Producer::new(&n4,poison,c572_key()).err().unwrap(),"C572 admission geometry");
    let k18=crate::verifier_key::admit(18,include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert_eq!(C572Producer::new(&p,poison,k18).err().unwrap(),"C572 admission geometry");
    let key=c572_key();let mut id=*key.id();id[0]^=1;
    let wrong=crate::verifier_key::admit_generated_test_key(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),id).unwrap();
    assert_eq!(C572Producer::new(&p,poison,wrong).err().unwrap(),"C569 pinned key22 identity/bytes");
    let mut foreign=key.verifier().clone();foreign.chi.swap(0,1);let bytes=pcs::encode(&ArkworksVerifierSetup(foreign)).unwrap();
    assert_eq!(bytes.len(),23664);assert_ne!(bytes.as_slice(),include_bytes!("../fixtures/verifier-keys-v1/log22.vk"));
    let foreign=crate::verifier_key::admit_generated_test_key(22,&bytes,*key.id()).unwrap();
    assert_eq!(C572Producer::new(&p,poison,foreign).err().unwrap(),"C569 pinned key22 identity/bytes");
    let plan=C572Plan::expected(&p,&key).unwrap();plan.preflight().unwrap();
    assert_eq!(plan.members.len(),18);assert_eq!(plan.widths.len(),18);
    assert_eq!(plan.members.iter().map(|m|m.terms).sum::<usize>(),111668);
    let empty=plan.members.iter().position(|m|m.terms==0).expect("N3 empty ordinal");
    for fault in 0..5{
        let mut bad=plan.members.clone();
        match fault{0=>bad[0].width+=1,1=>bad[0].terms+=1,2=>bad[12].name.push_str(".wrong"),3=>{bad.remove(empty);},_=>bad.swap(empty,(empty+1)%18)}
        assert!(bad!=plan.members);assert_eq!(plan.require_members(&bad).err().unwrap(),"C572 ordered member metadata");
    }
    let mut first=None;plan.visit(true,0,&mut|e|{if first.is_none(){first=Some(e);}Ok(())}).unwrap();let original=first.unwrap();
    assert!(plan.check_edge(&original,true,0).is_ok());
    for fault in 0..4{let mut bad=original.clone();match fault{
        0=>bad.source_slot=4,1=>bad.term.gate.left=1usize<<22,2=>bad.family_row=18usize<<14,_=>bad.term.row=1usize<<21}
        assert!(plan.check_edge(&bad,true,0).is_err());}
    let identity=pcs::encode_commitment(&ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap();
    assert_eq!(C572Context::expected(&p,&key,&identity[..383]).err().unwrap(),"C572 commitment extent");
    let mut extra=identity.clone();extra.push(0);assert_eq!(C572Context::expected(&p,&key,&extra).err().unwrap(),"C572 commitment extent");
    assert!(C572Context::expected(&p,&key,&[255u8;384]).err().unwrap().starts_with("C572 commitment encoding:"));
    let cheap=C572Context::expected(&p,&key,&identity).unwrap();let mut a=Transcript::new(C572_DOMAIN);cheap.bind(&key,&mut a).unwrap();
    let mut b=Transcript::new(C572_DOMAIN);c572_reference_prefix(&cheap,&mut b,0);assert_eq!(c572_mark(&a),c572_mark(&b));assert_eq!(a.challenges(),0);

    let path=std::path::PathBuf::from(std::env::var_os("C572_SOURCE").expect("controller pins BOTH original4B53 copies"));
    assert!(path.is_absolute());let meta=std::fs::metadata(&path).unwrap();assert!(meta.is_file()&&meta.permissions().readonly());assert_eq!(meta.len(),524288);
    println!("C572_REAL_STAGE|prepare_begin");
    let producer=C572Producer::new(&p,&path,c572_key()).unwrap();
    println!("C572_REAL_STAGE|commit_ready");
    let w=&producer.work;let verifier=C572Verifier::expected(&p,&w.prepared.key,w.commitment_bytes()).unwrap();
    assert_ne!(identity.as_slice(),w.commitment_bytes());
    let mut challenged=Transcript::new(C572_DOMAIN);challenged.challenge_scalar(b"already");let before=c572_mark(&challenged);
    assert_eq!(producer.prove_on(&mut challenged).err().unwrap(),"C572 context already challenged");assert_eq!(c572_mark(&challenged),before);
    let(proof,end)=producer.prove().unwrap();assert_eq!((proof.gkr.len(),proof.pcs.len()),(5024,29421));
    let verified=verifier.verify(&proof).unwrap();assert_eq!(c572_mark(&end),c572_mark(&verified));
    println!("C572_REAL_STAGE|proof_verified");
    let decoded=gkr::decode_dimensions(&[22],&proof.gkr).unwrap();let opening=pcs::decode_proof(&proof.pcs,22).unwrap();
    let(claim,post)=verifier.replay_gkr(&proof.gkr,&Transcript::new(C572_DOMAIN)).unwrap();
    assert_eq!(claim.point.len(),22);assert_eq!(w.prepared.source.evaluate(&claim.point).unwrap(),claim.value);
    let mut success=post.clone();verifier.finish_pcs_on(&claim,&opening,&mut success).unwrap();assert_eq!(c572_mark(&success),c572_mark(&end));

    // Initial eight census visits precede bind. Call9 is the first challenged
    // U visit: its first callback succeeds, then the second is the sole fault.
    let mut outer=Transcript::new(C572_DOMAIN);let before=c572_mark(&outer);
    let e=producer.gkr_on(&mut outer,true).err().expect("late helper failure absent");
    assert_eq!(e.error,"C572 isolated postchallenge endpoint");assert_eq!((e.hits,e.visits,e.after_bind,e.binds,e.literal),(1,9,1,1,0));
    assert!(e.observed[0]>=21&&e.observed[1]>=e.observed[0]&&e.observed[2]>outer.bytes_absorbed());assert_eq!(c572_mark(&outer),before);

    for field in 0..2{let(mut root,mut total)=(native.root(),native.total_be28());if field==0{root[0]^=1;}else{total[27]^=1;}
        let alternate=WorkTreeHistoryPlan::compile(3,2,root,total).unwrap();let v=C572Verifier::expected(&alternate,&w.prepared.key,w.commitment_bytes()).unwrap();
        c572_reject(&v,&proof,&mut Transcript::new(C572_DOMAIN),"C572 GKR:");}
    let wrong_c=C572Verifier::expected(&p,&w.prepared.key,&identity).unwrap();
    c572_reject(&wrong_c,&proof,&mut Transcript::new(C572_DOMAIN),"C572 GKR:");
    c572_reject(&verifier,&proof,&mut Transcript::new(b"c572-wrong-domain"),"C572 GKR:");
    c572_reject(&verifier,&proof,&mut challenged,"C572 context already challenged");
    let c=&verifier.context;let mut normal=Transcript::new(C572_DOMAIN);c.bind(&w.prepared.key,&mut normal).unwrap();
    let mut reference=Transcript::new(C572_DOMAIN);c572_reference_prefix(c,&mut reference,0);assert_eq!(c572_mark(&normal),c572_mark(&reference));
    for fault in [0,1,2]{let mut t=Transcript::new(C572_DOMAIN);c572_reference_prefix(c,&mut t,fault);
        let result=gkr::verify_with_wiring(&[22],1usize<<21,&decoded,&mut t,|t|c.plan.bind_roster(t),|_,r,u,v|c.plan.coefficients(r,u,v).map_err(|_|GkrError::PointDimension));
        if fault==0{assert_eq!(result.unwrap(),claim);assert_eq!(c572_mark(&t),c572_mark(&post));}else{assert!(result.is_err());}}

    for endpoint in [false,true]{let mut g=decoded.clone();if endpoint{g.layers[0].line_coefficients[0]+=Fr::one();}else{g.layers[0].rounds[0][0]+=Fr::one();}
        c572_reject(&verifier,&C572Proof{gkr:gkr::encode_proof(&g).unwrap(),pcs:proof.pcs.clone()},&mut Transcript::new(C572_DOMAIN),"C572 GKR:");}
    for gkr_side in [true,false]{for trailing in [true,false]{let mut bad=proof.clone();let bytes=if gkr_side{&mut bad.gkr}else{&mut bad.pcs};
        if trailing{bytes.push(0);}else{bytes.pop();}c572_reject(&verifier,&bad,&mut Transcript::new(C572_DOMAIN),if gkr_side{"C572 GKR extent"}else{"C572 PCS extent"});}}
    let mut noncanonical=proof.clone();noncanonical.gkr[..32].fill(255);c572_reject(&verifier,&noncanonical,&mut Transcript::new(C572_DOMAIN),"C572 GKR encoding:");
    let bounds=c572_bounds().unwrap();let mut rounds=proof.clone();assert_eq!(u32::from_le_bytes(rounds.pcs[bounds.rounds_at..bounds.rounds_at+4].try_into().unwrap()),11);
    rounds.pcs[bounds.rounds_at..bounds.rounds_at+4].copy_from_slice(&12u32.to_le_bytes());
    c572_reject(&verifier,&rounds,&mut Transcript::new(C572_DOMAIN),"C572 PCS encoding: Dory round count rejected before allocation");

    // Each private-finisher test uses the SAME exact successful post-GKR,
    // pre-separator prefix; no changed-context GKR error substitutes for PCS.
    for field in 0..3{let mut changed=claim.clone();let mut t=post.clone();let before=c572_mark(&t);
        let v=if field==2{assert_ne!(wrong_c.context.c_bytes,verifier.context.c_bytes);&wrong_c}else{&verifier};
        if field==0{changed.point[0]+=Fr::one();assert_ne!(changed.point,claim.point);}else if field==1{changed.value+=Fr::one();assert_ne!(changed.value,claim.value);}
        assert!(v.finish_pcs_on(&changed,&opening,&mut t).err().unwrap().starts_with("C572 PCS:"));assert_eq!(c572_mark(&t),before);
    }
    let mut drift=post.clone();drift.append_bytes(b"c572-pcs-drift",b"one-fault");let before=c572_mark(&drift);
    assert!(verifier.finish_pcs_on(&claim,&opening,&mut drift).err().unwrap().starts_with("C572 PCS:"));assert_eq!(c572_mark(&drift),before);

    let mut publish=Transcript::new(C572_DOMAIN);let before=c572_mark(&publish);
    for shape in 0..3{let mut bad=decoded.clone();match shape{0=>{bad.layers[0].rounds[0].pop();},1=>{bad.layers[0].rounds.pop();},_=>{bad.layers[0].line_coefficients.pop();}}
        assert!(c572_encode_publish(&bad,&opening,end.clone(),&mut publish).is_err());assert_eq!(c572_mark(&publish),before);}
    let mut bad_pcs=pcs::decode_proof(&proof.pcs,22).unwrap();bad_pcs.sigma+=1;
    assert!(c572_encode_publish(&decoded,&bad_pcs,end.clone(),&mut publish).is_err());assert_eq!(c572_mark(&publish),before);
    let published=c572_encode_publish(&decoded,&opening,end.clone(),&mut publish).unwrap();
    assert_eq!(published.gkr,proof.gkr);assert_eq!(published.pcs,proof.pcs);assert_eq!(c572_mark(&publish),c572_mark(&end));
    println!("C572_REAL_STAGE|controls_done");
}

struct C573TreeBorrowed<'o,'p>{work:&'o NativeWorkProducer<'p>,plan:&'o C572Plan<'p>,legacy:bool}
impl<'o,'p>C573TreeBorrowed<'o,'p>{
    fn load(&self,owner:usize)->Result<Vec<Fr>,String>{
        let view=self.work.prepared.source.h2_boolean_view()?;view.require_same_source(&self.work.prepared.source)?;
        let bits=view.read_copy(owner)?;
        if bits.len()!=1usize<<20||bits.capacity_bytes()>131072{return Err("C572 packed owner bounds".into());}
        let mut values=Vec::new();values.try_reserve_exact(1usize<<20).map_err(|_|"C572 owner allocation")?;
        if values.capacity()!=1usize<<20{return Err("C572 owner capacity".into());}
        for i in 0..1usize<<20{values.push(Fr::from(bits.bit_at(i)as u64));}Ok(values)
    }
    fn gkr_on(&self,t:&mut Transcript,late:bool)->Result<(gkr::GkrProof,InputClaim),C572HelperError>{
        let(hits,visits,after_bind,binds,literal)=(Cell::new(0),Cell::new(0),Cell::new(0),Cell::new(0),Cell::new(0));
        let failure=|error:String,next:&Transcript|C572HelperError{error,hits:hits.get(),visits:visits.get(),after_bind:after_bind.get(),binds:binds.get(),literal:literal.get(),
            observed:[next.challenges(),next.raw_queries(),next.bytes_absorbed()]};
        let mut next=t.clone();let w=self.work;
        let context=C572Context::expected(self.plan.parent,&w.prepared.key,w.commitment_bytes()).map_err(|e|failure(e,&next))?;
        context.bind(&w.prepared.key,&mut next).map_err(|e|failure(e,&next))?;
        if !late{if self.legacy { println!("C572_REAL_STAGE|gkr_begin"); }}
        let result=edge::prove_edge_terms_with_cache_limit_for_test(20,2,14,5,&self.plan.widths,0,
            |left,owner,sink|{
                visits.set(visits.get()+1);let call=visits.get();let mut callbacks=0usize;
                self.plan.visit(left,owner,&mut |item|{
                    callbacks+=1;
                    if late&&call==9&&callbacks==2{hits.set(hits.get()+1);return Err("C572 isolated postchallenge endpoint".into());}
                    sink(item)?;if binds.get()==1&&call>=9{after_bind.set(after_bind.get()+1);}Ok(())
                })
            },|owner|self.load(owner),&mut next,|t|{binds.set(binds.get()+1);self.plan.bind_roster(t)},
            |r,u,v|{literal.set(literal.get()+1);let c=self.plan.coefficients(r,u,v)?;
                if c!=self.plan.literal_coefficients(r,u,v)?{return Err("C572 actual-terminal literal differential".into());}Ok(c)});
        let(proof,claim,used_u,used_v)=result.map_err(|e|failure(e,&next))?;
        if used_u||used_v||binds.get()!=1||literal.get()!=1||claim.point.len()!=22
            ||self.work.prepared.source.evaluate(&claim.point).map_err(|e|failure(e,&next))?!=claim.value
        {return Err(failure("C572 helper/owned global claim".into(),&next));}
        *t=next;Ok((proof,claim))
    }
    fn prove_on(&self,t:&mut Transcript)->Result<C572Proof,String>{
        let w=self.work;self.plan.require(&w.prepared.key)?;
        if !std::ptr::eq(self.plan.parent,w.prepared.parent)||w.prepared.source.input_len()!=1usize<<22
            ||w.setup.log_n!=22||w.setup.id!=*w.prepared.key.id()
            ||pcs::encode(&ArkworksVerifierSetup(w.setup.verifier.clone()))?.as_slice()!=include_bytes!("../fixtures/verifier-keys-v1/log22.vk")
            ||pcs::encode_commitment(&w.committed.commitment)?!=w.commitment_bytes()
        {return Err("C572 owned producer identity".into());}
        let mut next=t.clone();let(g,claim)=self.gkr_on(&mut next,false).map_err(|e|e.error)?;
        if self.legacy { println!("C572_REAL_STAGE|gkr_ready"); }c572_separator(&mut next);
        let opening=crate::packed::open(&w.committed,&w.prepared.source,&claim.point,&w.setup,&mut next)?;
        if self.legacy { println!("C572_REAL_STAGE|primary_opening_ready"); }c572_encode_publish(&g,&opening,next,t)
    }
}

pub(super) fn c573_prove(lease:&C573PcsLease<'_,'_>,t:&mut Transcript)->Result<(Vec<u8>,Vec<u8>),String>{
    lease.check()?;let plan=C572Plan::expected(lease.parent(),lease.key())?;plan.preflight()?;
    let p=C573TreeBorrowed{work:lease.owner,plan:&plan,legacy:false}.prove_on(t)?;Ok((p.gkr,p.pcs))
}
pub(super) struct C573TreeVerifier<'p,'k>(C572Verifier<'p,'k>);
impl<'p,'k>C573TreeVerifier<'p,'k>{
    pub(super) fn expected(p:&'p WorkTreeHistoryPlan,k:&'k AdmittedVerifierKey,c:&[u8])->Result<Self,String>{Ok(Self(C572Verifier::expected(p,k,c)?))}
    pub(super) fn verify_on(&self,g:&[u8],p:&[u8],t:&mut Transcript)->Result<(),String>{
        let b=c572_bounds()?;if g.len()!=b.gkr||p.len()!=b.pcs{return Err("C573 Tree extent".into());}
        self.0.verify_on(&C572Proof{gkr:g.to_vec(),pcs:p.to_vec()},t)
    }
}

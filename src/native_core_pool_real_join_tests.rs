//! C571 diagnostic CorePool authentication; no Tree/history acceptance token.
use super::*;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use std::path::Path;

const C571_DOMAIN: &[u8] = b"nipopow-native-core-pool-diagnostic-v1";

fn c571_geometry(parent: &WorkTreeHistoryPlan, key: &AdmittedVerifierKey) -> Result<(), String> {
    let d = parent.descriptor(); let pool = parent.core_pool();
    if parent.headers() != 3 || parent.slot_log() != 2 || parent.slots() != 4
        || d.genuine != 2 || d.leaves != 2 || d.slots != 4 || key.log_n() != 22
        || &parent.topology().descriptor != d || &parent.fixed_profile().tree != d
        || &parent.leaf_profile().tree != d || &parent.work_profile().tree != d
        || pool.copy_bits() != 2 || pool.input_log() != 22 || pool.row_log() != 23
        || pool.input_len() != 1usize << 22 || pool.row_count() != 1usize << 23
        || pool.term_count() != 7_589_120 || work_tree_layout::CORE_OFFSETS.len() * parent.slots() != 44
    { return Err("C571 admission geometry".into()); }
    require_work_key22(key)
}

struct C571Bounds { commitment: usize, key: usize, gkr: usize, pcs: usize, rounds_at: usize, sigma: usize }
fn c571_bounds() -> Result<C571Bounds, String> {
    let scalar = Fr::zero().compressed_size();
    let gt = ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero().compressed_size();
    let g1 = ark_bn254::G1Projective::zero().compressed_size();
    let g2 = ark_bn254::G2Projective::zero().compressed_size();
    let sigma = 22usize.div_ceil(2); let rounds_at = 2 * gt + g1;
    let b = C571Bounds { commitment: gt, key: 1920 * (sigma + 1) + 624,
        gkr: (7 * 22 + 3) * scalar,
        pcs: rounds_at + 4 + sigma * (6 * gt + 3 * g1 + 3 * g2) + 1 + g1 + g2 + 8,
        rounds_at, sigma };
    if (b.commitment,b.key,b.gkr,b.pcs,b.sigma) != (384,23664,5024,29421,11) {
        return Err("C571 codec dimensions".into());
    }
    Ok(b)
}

// Expected public material only. No reference into the producer's owned key.
struct C571Context<'p> {
    parent: &'p WorkTreeHistoryPlan, key_id: [u8; 32], key_bytes: Vec<u8>,
    commitment: ArkGT, commitment_bytes: Vec<u8>,
}
impl<'p> C571Context<'p> {
    fn expected(parent: &'p WorkTreeHistoryPlan, key: &AdmittedVerifierKey, c: &[u8]) -> Result<Self, String> {
        c571_geometry(parent,key)?; let b = c571_bounds()?;
        if c.len() != b.commitment { return Err("C571 commitment extent".into()); }
        let commitment = pcs::decode_commitment(c).map_err(|e| format!("C571 commitment encoding: {e}"))?;
        let key_bytes = pcs::encode(&ArkworksVerifierSetup(key.verifier().clone()))?;
        if key_bytes.len() != b.key { return Err("C571 key extent".into()); }
        Ok(Self { parent, key_id: *key.id(), key_bytes, commitment, commitment_bytes: c.to_vec() })
    }
    fn require(&self, key: &AdmittedVerifierKey) -> Result<(), String> {
        c571_geometry(self.parent,key)?; let b = c571_bounds()?;
        if self.key_id != *key.id() || self.key_bytes.len() != b.key
            || self.key_bytes.as_slice() != include_bytes!("../fixtures/verifier-keys-v1/log22.vk")
            || self.commitment_bytes.len() != b.commitment
            || pcs::encode_commitment(&self.commitment)? != self.commitment_bytes
        { return Err("C571 expected context identity".into()); }
        pcs::decode_commitment(&self.commitment_bytes)?;
        Ok(())
    }
    fn bind(&self, key: &AdmittedVerifierKey, t: &mut Transcript) -> Result<(), String> {
        self.require(key)?;
        if t.challenges() != 0 { return Err("C571 context already challenged".into()); }
        let p = self.parent; let d = p.descriptor(); let pool = p.core_pool();
        t.append_u64(b"c571-core-pool-version",1);
        t.append_bytes(b"c571-core-pool-role",b"native-N3-all44-same-X");
        t.append_bytes(b"c571-core-pool-policy",b"native-N3-h2-original-X-all44-cores-only-v1");
        t.append_u64(b"c571-parent-N",p.headers());
        t.append_u64(b"c571-parent-H",p.slot_log() as u64);
        t.append_u64(b"c571-parent-slots",p.slots() as u64);
        t.append_u64(b"c571-parent-genuine",d.genuine as u64);
        t.append_u64(b"c571-parent-leaves",d.leaves as u64);
        t.append_bytes(b"c571-parent-root",&d.root);
        t.append_bytes(b"c571-parent-total",&p.work_profile().total_be28);
        t.append_u64(b"c571-input-log",pool.input_log() as u64);
        t.append_u64(b"c571-row-log",pool.row_log() as u64);
        t.append_u64(b"c571-core-terms",pool.term_count() as u64);
        t.append_u64(b"c571-core-embeddings",44);
        t.append_bytes(b"c571-input-axes",&[16,4,2]);
        t.append_bytes(b"c571-row-axes",&[17,2,4]);
        t.append_bytes(b"c571-pcs-mode",b"Transparent-dory-v1");
        t.append_bytes(b"c571-pcs-vendor",pcs::VENDOR_PIN);
        t.append_bytes(b"c571-key-id",&self.key_id);
        t.append_bytes(b"c571-key-bytes",&self.key_bytes);
        t.append_bytes(b"c571-C",&self.commitment_bytes);
        // The unchanged helper OR Plan::verify owns the sole Plan.bind.
        Ok(())
    }
}
fn c571_separator(t: &mut Transcript) {
    t.append_bytes(b"c571-core-pool-authentication-boundary",b"gkr-to-pcs-v1");
}

#[derive(Clone)]
struct C571Proof { gkr: Vec<u8>, pcs: Vec<u8> }
fn c571_encode_publish(g: &gkr::GkrProof, o: &dory_pcs::backends::arkworks::ArkDoryProof,
    next: Transcript, t: &mut Transcript) -> Result<C571Proof, String>
{
    let proof = C571Proof { gkr: gkr::encode_proof(g)?, pcs: pcs::encode_proof(o)? };
    let b = c571_bounds()?;
    if proof.gkr.len() != b.gkr || proof.pcs.len() != b.pcs { return Err("C571 produced extent".into()); }
    gkr::decode_dimensions(&[22],&proof.gkr)?; pcs::decode_proof(&proof.pcs,22)?;
    *t = next; Ok(proof)
}
struct C571Verifier<'p,'k> { context: C571Context<'p>, key: &'k AdmittedVerifierKey }
impl<'p,'k> C571Verifier<'p,'k> {
    fn expected(parent: &'p WorkTreeHistoryPlan, key: &'k AdmittedVerifierKey, c: &[u8]) -> Result<Self, String> {
        Ok(Self { context: C571Context::expected(parent,key,c)?, key })
    }
    // Private partial replay is used only inside full verification/derived tests.
    fn replay_gkr(&self, bytes: &[u8], prefix: &Transcript) -> Result<(InputClaim,Transcript), String> {
        let b = c571_bounds()?;
        if bytes.len() != b.gkr { return Err("C571 GKR extent".into()); }
        let proof = self.context.parent.core_pool().decode(bytes).map_err(|e| format!("C571 GKR encoding: {e}"))?;
        if gkr::encode_proof(&proof)? != bytes { return Err("C571 GKR canonical encoding".into()); }
        let mut next = prefix.clone(); self.context.bind(self.key,&mut next)?;
        let claim = self.context.parent.core_pool().verify(&proof,&mut next)
            .map_err(|e| format!("C571 GKR: {e:?}"))?;
        if claim.point.len() != 22 { return Err("C571 logical input claim".into()); }
        Ok((claim,next))
    }
    fn verify_on(&self, proof: &C571Proof, t: &mut Transcript) -> Result<(), String> {
        self.context.require(self.key)?; let b = c571_bounds()?;
        if proof.gkr.len() != b.gkr { return Err("C571 GKR extent".into()); }
        if proof.pcs.len() != b.pcs { return Err("C571 PCS extent".into()); }
        let opening = pcs::decode_proof(&proof.pcs,22).map_err(|e| format!("C571 PCS encoding: {e}"))?;
        let (claim,mut next) = self.replay_gkr(&proof.gkr,t)?;
        self.finish_pcs_on(&claim,&opening,&mut next)?;
        *t = next; Ok(())
    }
    fn finish_pcs_on(&self, claim: &InputClaim, opening: &dory_pcs::backends::arkworks::ArkDoryProof,
        t: &mut Transcript) -> Result<(), String>
    {
        self.context.require(self.key)?;
        if claim.point.len() != 22 { return Err("C571 logical input claim".into()); }
        let mut next = t.clone();
        c571_separator(&mut next);
        pcs::verify_admitted(self.context.commitment,claim.value,&claim.point,opening,self.key,&mut next)
            .map_err(|e| format!("C571 PCS: {e}"))?;
        *t = next; Ok(())
    }
    fn verify(&self, proof: &C571Proof) -> Result<Transcript, String> {
        let mut t = Transcript::new(C571_DOMAIN); self.verify_on(proof,&mut t)?; Ok(t)
    }
}

fn c571_key22() -> AdmittedVerifierKey {
    crate::verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap()
}
fn c571_mark(t: &Transcript) -> ((u64,u64,u64),[Fr;2]) {
    let mut next = t.clone();
    ((t.raw_queries(),t.challenges(),t.bytes_absorbed()),
        [next.challenge_scalar(b"c571-continuation-a"),next.challenge_scalar(b"c571-continuation-b")])
}
fn c571_reject(v: &C571Verifier<'_,'_>, proof: &C571Proof, t: &mut Transcript, stage: &str) {
    let before = c571_mark(t); let error = v.verify_on(proof,t).err().expect("fault accepted");
    assert!(error.starts_with(stage),"expected {stage}, got {error}"); assert_eq!(c571_mark(t),before);
}

// Independent literal-prefix fixture, including kind5 integers and binary axes.
// Only the order/type mutants below use the alternative frame; the producer
// and normal verifier always use the one fixed C571Context::bind above.
fn c571_reference_prefix(c: &C571Context<'_>, t: &mut Transcript, fault: usize) {
    let p = c.parent; let d = p.descriptor(); let pool = p.core_pool();
    if fault == 2 { t.append_bytes(b"c571-core-pool-version",&1u64.to_le_bytes()); }
    else { t.append_u64(b"c571-core-pool-version",1); }
    t.append_bytes(b"c571-core-pool-role",b"native-N3-all44-same-X");
    t.append_bytes(b"c571-core-pool-policy",b"native-N3-h2-original-X-all44-cores-only-v1");
    t.append_u64(b"c571-parent-N",p.headers());
    t.append_u64(b"c571-parent-H",p.slot_log() as u64);
    t.append_u64(b"c571-parent-slots",p.slots() as u64);
    t.append_u64(b"c571-parent-genuine",d.genuine as u64);
    t.append_u64(b"c571-parent-leaves",d.leaves as u64);
    t.append_bytes(b"c571-parent-root",&d.root);
    t.append_bytes(b"c571-parent-total",&p.work_profile().total_be28);
    t.append_u64(b"c571-input-log",pool.input_log() as u64);
    t.append_u64(b"c571-row-log",pool.row_log() as u64);
    t.append_u64(b"c571-core-terms",pool.term_count() as u64);
    t.append_u64(b"c571-core-embeddings",44);
    t.append_bytes(b"c571-input-axes",&[16,4,2]);
    t.append_bytes(b"c571-row-axes",&[17,2,4]);
    t.append_bytes(b"c571-pcs-mode",b"Transparent-dory-v1");
    t.append_bytes(b"c571-pcs-vendor",pcs::VENDOR_PIN);
    t.append_bytes(b"c571-key-id",&c.key_id);
    if fault == 1 {
        t.append_bytes(b"c571-C",&c.commitment_bytes);
        t.append_bytes(b"c571-key-bytes",&c.key_bytes);
    } else {
        t.append_bytes(b"c571-key-bytes",&c.key_bytes);
        t.append_bytes(b"c571-C",&c.commitment_bytes);
    }
}

#[test]
#[ignore = "C571 genuine N3 CorePool44 on controller-held original4B53; separate admission required"]
fn c571_real_n3_core_pool_same_x() {
    let headers = crate::historical_prefix_witness::retained_headers().unwrap();
    let native = crate::packed_owner_assembly::NativePrefix::from_raw_iter(3,
        headers.iter().map(|h| h.encode().map_err(|e| format!("{e:?}")))).unwrap();
    let p = WorkTreeHistoryPlan::compile(3,2,native.root(),native.total_be28()).unwrap();
    let poison = Path::new("Z:/c571-poison-source-must-not-open.bits");
    let n4 = WorkTreeHistoryPlan::compile(4,2,native.root(),native.total_be28()).unwrap();
    assert_eq!(C571Producer::new(&n4,poison,c571_key22()).err().unwrap(),"C571 admission geometry");
    let key18 = crate::verifier_key::admit(18,include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert_eq!(C571Producer::new(&p,poison,key18).err().unwrap(),"C571 admission geometry");
    let key = c571_key22(); let mut wrong_id = *key.id(); wrong_id[0] ^= 1;
    let wrong = crate::verifier_key::admit_generated_test_key(22,
        include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),wrong_id).unwrap();
    assert_eq!(C571Producer::new(&p,poison,wrong).err().unwrap(),"C569 pinned key22 identity/bytes");
    let mut other_key = key.verifier().clone(); other_key.chi.swap(0,1);
    let foreign_bytes = pcs::encode(&ArkworksVerifierSetup(other_key)).unwrap();
    assert_eq!(foreign_bytes.len(),23664); assert_ne!(foreign_bytes.as_slice(),include_bytes!("../fixtures/verifier-keys-v1/log22.vk"));
    let foreign = crate::verifier_key::admit_generated_test_key(22,&foreign_bytes,*key.id()).unwrap();
    assert_eq!(C571Producer::new(&p,poison,foreign).err().unwrap(),"C569 pinned key22 identity/bytes");

    let identity = pcs::encode_commitment(&ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap();
    let b = c571_bounds().unwrap(); assert_eq!(identity.len(),b.commitment);
    assert_eq!(C571Context::expected(&p,&key,&identity[..383]).err().unwrap(),"C571 commitment extent");
    let mut extra_c = identity.clone(); extra_c.push(0);
    assert_eq!(C571Context::expected(&p,&key,&extra_c).err().unwrap(),"C571 commitment extent");
    assert!(C571Context::expected(&p,&key,&[255u8;384]).err().unwrap().starts_with("C571 commitment encoding:"));
    let expected = C571Context::expected(&p,&key,&identity).unwrap();
    let mut actual_prefix = Transcript::new(C571_DOMAIN); expected.bind(&key,&mut actual_prefix).unwrap();
    let mut literal_prefix = Transcript::new(C571_DOMAIN); c571_reference_prefix(&expected,&mut literal_prefix,0);
    assert_eq!(c571_mark(&actual_prefix),c571_mark(&literal_prefix)); assert_eq!(actual_prefix.challenges(),0);

    let path = std::path::PathBuf::from(std::env::var_os("C571_SOURCE").expect("controller holds exact original4B53 pair"));
    assert!(path.is_absolute()); let meta = std::fs::metadata(&path).unwrap();
    assert!(meta.is_file() && meta.permissions().readonly()); assert_eq!(meta.len(),524288);
    println!("C571_REAL_STAGE|prepare_begin");
    let producer = C571Producer::new(&p,&path,c571_key22()).unwrap();
    println!("C571_REAL_STAGE|commit_ready");
    let w = &producer.work; let context = C571Context::expected(&p,&w.prepared.key,w.commitment_bytes()).unwrap();
    let verifier = C571Verifier::expected(&p,&w.prepared.key,w.commitment_bytes()).unwrap();
    assert_ne!(identity.as_slice(),w.commitment_bytes());
    assert_eq!(context.commitment_bytes,w.commitment_bytes());
    let mut challenged = Transcript::new(C571_DOMAIN); challenged.challenge_scalar(b"already");
    let before = c571_mark(&challenged);
    assert_eq!(producer.prove_on(&mut challenged).err().unwrap(),"C571 context already challenged");
    assert_eq!(c571_mark(&challenged),before);

    let (proof,producer_end) = producer.prove().unwrap();
    assert_eq!((proof.gkr.len(),proof.pcs.len()),(5024,29421));
    let verifier_end = verifier.verify(&proof).unwrap(); assert_eq!(c571_mark(&producer_end),c571_mark(&verifier_end));
    println!("C571_REAL_STAGE|proof_verified");
    let decoded = p.core_pool().decode(&proof.gkr).unwrap();
    let opened = pcs::decode_proof(&proof.pcs,22).unwrap();
    let (claim,post_gkr) = verifier.replay_gkr(&proof.gkr,&Transcript::new(C571_DOMAIN)).unwrap();
    assert_eq!(claim.point.len(),22); assert_eq!(w.prepared.source.evaluate(&claim.point).unwrap(),claim.value);

    // Valid expected N3 statements: the relation stays the same, its context changes.
    for field in 0..2 {
        let (mut root,mut total) = (native.root(),native.total_be28());
        if field == 0 { root[0] ^= 1; } else { total[27] ^= 1; }
        let alternate = WorkTreeHistoryPlan::compile(3,2,root,total).unwrap();
        let wrong = C571Verifier::expected(&alternate,&w.prepared.key,w.commitment_bytes()).unwrap();
        c571_reject(&wrong,&proof,&mut Transcript::new(C571_DOMAIN),"C571 GKR:");
    }
    let wrong = C571Verifier::expected(&p,&w.prepared.key,&identity).unwrap();
    c571_reject(&wrong,&proof,&mut Transcript::new(C571_DOMAIN),"C571 GKR:");
    c571_reject(&verifier,&proof,&mut Transcript::new(b"c571-wrong-domain"),"C571 GKR:");
    c571_reject(&verifier,&proof,&mut challenged,"C571 context already challenged");
    // Exact-order/type single faults preserve every field/value and total extent.
    let mut reference = Transcript::new(C571_DOMAIN); c571_reference_prefix(&context,&mut reference,0);
    assert_eq!(p.core_pool().verify(&decoded,&mut reference).unwrap(),claim);
    assert_eq!(c571_mark(&reference),c571_mark(&post_gkr));
    let mut correct_prefix = Transcript::new(C571_DOMAIN); context.bind(&w.prepared.key,&mut correct_prefix).unwrap();
    for fault in [1,2] {
        let mut prefix = Transcript::new(C571_DOMAIN); c571_reference_prefix(&context,&mut prefix,fault);
        assert_ne!(c571_mark(&prefix),c571_mark(&correct_prefix));
        assert!(p.core_pool().verify(&decoded,&mut prefix).is_err());
    }

    for endpoint in [false,true] {
        let mut g = decoded.clone();
        if endpoint { g.layers[0].line_coefficients[0] += Fr::one(); }
        else { g.layers[0].rounds[0][0] += Fr::one(); }
        let bad = C571Proof { gkr: gkr::encode_proof(&g).unwrap(), pcs: proof.pcs.clone() };
        c571_reject(&verifier,&bad,&mut Transcript::new(C571_DOMAIN),"C571 GKR:");
    }
    for gkr_side in [true,false] { for trailing in [true,false] {
        let mut bad = proof.clone(); let bytes = if gkr_side { &mut bad.gkr } else { &mut bad.pcs };
        if trailing { bytes.push(0); } else { bytes.pop(); }
        c571_reject(&verifier,&bad,&mut Transcript::new(C571_DOMAIN),if gkr_side { "C571 GKR extent" } else { "C571 PCS extent" });
    }}
    let mut noncanonical = proof.clone(); noncanonical.gkr[..32].fill(255);
    c571_reject(&verifier,&noncanonical,&mut Transcript::new(C571_DOMAIN),"C571 GKR encoding:");
    let mut wrong_rounds = proof.clone();
    assert_eq!(u32::from_le_bytes(wrong_rounds.pcs[b.rounds_at..b.rounds_at+4].try_into().unwrap()),b.sigma as u32);
    wrong_rounds.pcs[b.rounds_at..b.rounds_at+4].copy_from_slice(&((b.sigma+1) as u32).to_le_bytes());
    c571_reject(&verifier,&wrong_rounds,&mut Transcript::new(C571_DOMAIN),"C571 PCS encoding: Dory round count rejected before allocation");

    for point_fault in [true,false] {
        let mut wrong = claim.clone(); if point_fault { wrong.point[0] += Fr::one(); } else { wrong.value += Fr::one(); }
        let mut t = post_gkr.clone(); let before = c571_mark(&t);
        assert!(verifier.finish_pcs_on(&wrong,&opened,&mut t).err().unwrap().starts_with("C571 PCS:"));
        assert_eq!(c571_mark(&t),before);
    }
    let mut drift = post_gkr.clone(); drift.append_bytes(b"c571-pcs-drift",b"one-fault");
    let before = c571_mark(&drift);
    assert!(verifier.finish_pcs_on(&claim,&opened,&mut drift).err().unwrap().starts_with("C571 PCS:"));
    assert_eq!(c571_mark(&drift),before);

    // One actual foreign opening from the SAME exact post-GKR/PCS prefix.
    let mut pcs_prefix = post_gkr.clone(); c571_separator(&mut pcs_prefix);
    let mut q = claim.point.clone(); q[0] += Fr::one(); assert_ne!(q,claim.point);
    let q_value = w.prepared.source.evaluate(&q).unwrap(); let mut foreign_prover = pcs_prefix.clone();
    println!("C571_REAL_STAGE|foreign_opening_begin");
    let foreign_opening = crate::packed::open(&w.committed,&w.prepared.source,&q,&w.setup,&mut foreign_prover).unwrap();
    let foreign_bytes = pcs::encode_proof(&foreign_opening).unwrap(); assert_eq!(foreign_bytes.len(),b.pcs);
    let foreign_decoded = pcs::decode_proof(&foreign_bytes,22).unwrap(); let mut foreign_verifier = pcs_prefix.clone();
    pcs::verify_admitted(w.committed.commitment,q_value,&q,&foreign_decoded,&w.prepared.key,&mut foreign_verifier).unwrap();
    assert_eq!(c571_mark(&foreign_prover),c571_mark(&foreign_verifier));
    println!("C571_REAL_STAGE|foreign_verified");
    c571_reject(&verifier,&C571Proof { gkr: proof.gkr.clone(), pcs: foreign_bytes },&mut Transcript::new(C571_DOMAIN),"C571 PCS:");

    // Real producer completion boundary: failure in either encoder publishes nothing.
    let mut bad_gkr = decoded.clone(); bad_gkr.layers[0].rounds[0].pop();
    let mut t = Transcript::new(C571_DOMAIN); let before = c571_mark(&t);
    assert!(c571_encode_publish(&bad_gkr,&opened,producer_end.clone(),&mut t).is_err()); assert_eq!(c571_mark(&t),before);
    let mut bad_pcs = pcs::decode_proof(&proof.pcs,22).unwrap(); bad_pcs.sigma += 1;
    assert!(c571_encode_publish(&decoded,&bad_pcs,producer_end.clone(),&mut t).is_err()); assert_eq!(c571_mark(&t),before);
    let published = c571_encode_publish(&decoded,&opened,producer_end.clone(),&mut t).unwrap();
    assert_eq!(published.gkr,proof.gkr); assert_eq!(published.pcs,proof.pcs); assert_eq!(c571_mark(&t),c571_mark(&producer_end));
    println!("C571_REAL_STAGE|controls_done");
}

struct C571Producer<'p> { work: NativeWorkProducer<'p> }
impl<'p> C571Producer<'p> {
    fn new(parent: &'p WorkTreeHistoryPlan, path: &Path, key: AdmittedVerifierKey) -> Result<Self, String> {
        c571_geometry(parent,&key)?;
        Ok(Self { work: NativeWorkProducer::new(parent,path,key)? })
    }
    fn prove_on(&self, t: &mut Transcript) -> Result<C571Proof, String> { c571_prove_borrowed_on(&self.work,t,true) }
    fn prove(&self) -> Result<(C571Proof,Transcript), String> {
        let mut t = Transcript::new(C571_DOMAIN); let proof = self.prove_on(&mut t)?; Ok((proof,t))
    }
}

fn c571_prove_borrowed_on(work:&NativeWorkProducer<'_>,t:&mut Transcript,legacy:bool)->Result<C571Proof,String>{
        let w = work; let parent = w.prepared.parent; let key = &w.prepared.key;
        let context = C571Context::expected(parent,key,w.commitment_bytes())?;
        if w.prepared.source.input_len() != 1usize << 22 || w.setup.log_n != 22
            || w.setup.id != *key.id() || pcs::encode(&ArkworksVerifierSetup(w.setup.verifier.clone()))? != context.key_bytes
            || pcs::encode_commitment(&w.committed.commitment)? != context.commitment_bytes
        { return Err("C571 owned producer identity".into()); }
        w.prepared.source.h2_boolean_view()?.require_same_source(&w.prepared.source)?;
        let mut next = t.clone(); context.bind(key,&mut next)?;
        if legacy { println!("C571_REAL_STAGE|gkr_begin"); }
        let (gkr_proof,claim) = parent.core_pool().prove_packed_four_owners_for_test(&w.prepared.source,&mut next)?;
        if claim.point.len() != 22 || w.prepared.source.evaluate(&claim.point)? != claim.value {
            return Err("C571 owned original-X claim".into());
        }
        if legacy { println!("C571_REAL_STAGE|gkr_ready"); }
        c571_separator(&mut next);
        let opening = crate::packed::open(&w.committed,&w.prepared.source,&claim.point,&w.setup,&mut next)?;
        if legacy { println!("C571_REAL_STAGE|primary_opening_ready"); }
        c571_encode_publish(&gkr_proof,&opening,next,t)
    
}

pub(super) fn c573_prove(lease:&C573PcsLease<'_,'_>,t:&mut Transcript)->Result<(Vec<u8>,Vec<u8>),String>{
    lease.check()?;let p=c571_prove_borrowed_on(lease.owner,t,false)?;Ok((p.gkr,p.pcs))
}
pub(super) struct C573CoreVerifier<'p,'k>(C571Verifier<'p,'k>);
impl<'p,'k>C573CoreVerifier<'p,'k>{
    pub(super) fn expected(p:&'p WorkTreeHistoryPlan,k:&'k AdmittedVerifierKey,c:&[u8])->Result<Self,String>{Ok(Self(C571Verifier::expected(p,k,c)?))}
    pub(super) fn verify_on(&self,g:&[u8],p:&[u8],t:&mut Transcript)->Result<(),String>{
        let b=c571_bounds()?;if g.len()!=b.gkr||p.len()!=b.pcs{return Err("C573 Core extent".into());}
        self.0.verify_on(&C571Proof{gkr:g.to_vec(),pcs:p.to_vec()},t)
    }
}

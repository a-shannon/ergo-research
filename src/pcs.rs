//! Bounded Transparent Dory adapter. Final d-batching has Laurent powers -1..2,
//! hence the formal statistical bound is 3*q_D/(p-1), not 2*q_D/(p-1).
use crate::transcript::Transcript;
use ark_bn254::{Fr, G1Projective, G2Projective};
use ark_ec::pairing::Pairing;
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use blake2::{Blake2b512, Digest};
use dory_pcs::backends::arkworks::{
    ArkDoryProof, ArkFr, ArkG1, ArkG2, ArkGT, ArkworksPolynomial,
    ArkworksProverSetup, ArkworksVerifierSetup, BN254, G1Routines, G2Routines,
};
use dory_pcs::{Polynomial, ProverSetup, Transparent, VerifierSetup};
use rand_core::{Error as RngError, RngCore};
use std::collections::HashSet;
use std::io::{self, Write};

pub const MAX_LOG_N: usize = 24;
/// Maximum proof dimension accepted by the CPU verifier. Producer-side setup,
/// commitments, and packed witnesses retain the lower `MAX_LOG_N` bound.
pub const MAX_VERIFY_LOG_N: usize = 41;
pub const VENDOR_PIN: &[u8] = b"5246da503c3e2c6baa40ec00d714987c73a3e6eb";
const SETUP_DOMAIN: &[u8] = b"nipopow-gkr-dory-coordinate-setup-v1";

#[derive(Clone)]
pub struct Setup {
    pub prover: ProverSetup<BN254>,
    pub verifier: VerifierSetup<BN254>,
    pub id: [u8; 32],
    pub log_n: usize,
}

pub struct Committed {
    pub polynomial: ArkworksPolynomial,
    pub rows: Vec<ArkG1>,
    pub commitment: ArkGT,
    pub nu: usize,
    pub sigma: usize,
}

// Public randomness drives coordinate sampling, not a secret/public scalar
// multiplied by a fixed group generator. Each independent slot has its own stream.
struct CoordinateRng {
    prefix: Vec<u8>, block: [u8; 64], offset: usize, counter: u64,
}

impl CoordinateRng {
    fn new(log_n: usize, role: &[u8], index: usize) -> Self {
        let mut prefix = SETUP_DOMAIN.to_vec();
        prefix.extend_from_slice(VENDOR_PIN);
        prefix.extend_from_slice(&(log_n as u64).to_le_bytes());
        prefix.extend_from_slice(&(role.len() as u64).to_le_bytes());
        prefix.extend_from_slice(role);
        prefix.extend_from_slice(&(index as u64).to_le_bytes());
        Self { prefix, block: [0; 64], offset: 64, counter: 0 }
    }
}

impl RngCore for CoordinateRng {
    fn next_u32(&mut self) -> u32 {
        let mut bytes = [0; 4]; self.fill_bytes(&mut bytes); u32::from_le_bytes(bytes)
    }
    fn next_u64(&mut self) -> u64 {
        let mut bytes = [0; 8]; self.fill_bytes(&mut bytes); u64::from_le_bytes(bytes)
    }
    fn fill_bytes(&mut self, destination: &mut [u8]) {
        for byte in destination {
            if self.offset == 64 {
                let mut h = Blake2b512::new();
                h.update(&self.prefix);
                h.update(self.counter.to_le_bytes());
                self.block.copy_from_slice(&h.finalize());
                self.counter = self.counter.checked_add(1).expect("setup RNG counter overflow");
                self.offset = 0;
            }
            *byte = self.block[self.offset]; self.offset += 1;
        }
    }
    fn try_fill_bytes(&mut self, destination: &mut [u8]) -> Result<(), RngError> {
        self.fill_bytes(destination); Ok(())
    }
}

pub fn encode<T: CanonicalSerialize>(value: &T) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    value.serialize_compressed(&mut bytes).map_err(|e| e.to_string())?;
    Ok(bytes)
}

pub fn generate_setup(log_n: usize) -> Result<Setup, String> {
    generate_setup_with_limit(log_n,MAX_LOG_N)
}

/// Diagnostic prefix only: no G2, hiding points, pairing, verifier key or setup ID.
#[cfg(test)]
#[derive(Debug, Default)]
pub(crate) struct G1PrefixStats {
    pub points_capacity: usize,
    pub admission_capacity: usize,
    pub compressed_capacity_bytes: usize,
    pub sampling_attempts: usize,
}

#[cfg(test)]
pub(crate) fn g1_primary_prefix_for_width_test(
    log_n: usize, width: usize,
) -> Result<(Vec<ArkG1>, G1PrefixStats), String> {
    g1_primary_prefix_for_width_test_with(log_n, width, |_, _, _| {})
}

#[cfg(test)]
pub(crate) fn g1_primary_prefix_for_width_test_with(
    log_n: usize, width: usize, mut fault: impl FnMut(usize, usize, &mut G1Projective),
) -> Result<(Vec<ArkG1>, G1PrefixStats), String> {
    if log_n > MAX_VERIFY_LOG_N || width > (1usize << log_n.div_ceil(2)) {
        return Err("diagnostic G1 prefix exceeds dimension".into());
    }
    let mut points = Vec::new();
    points.try_reserve_exact(width).map_err(|_| "diagnostic G1 reservation failed")?;
    if points.capacity() != width { return Err("diagnostic G1 capacity mismatch".into()); }
    let mut seen = HashSet::new();
    seen.try_reserve(width).map_err(|_| "diagnostic G1 admission reservation failed")?;
    let mut stats = G1PrefixStats::default();
    let started = std::time::Instant::now();
    for index in 0..width {
        let mut rng = CoordinateRng::new(log_n, b"G1-primary", index);
        let mut admitted = None;
        for attempt in 0..4096 {
            stats.sampling_attempts += 1;
            let mut point = G1Projective::rand(&mut rng);
            fault(index, attempt, &mut point);
            if !point.is_zero() && seen.insert(encode(&point)?) {
                admitted = Some(ArkG1(point));
                break;
            }
        }
        points.push(admitted.ok_or("G1 generator admission failed")?);
        if (index + 1) % (1 << 15) == 0 {
            eprintln!("G1-primary prefix only: admitted={}/{} log_n={} seconds={:.3} attempts={}",
                index + 1, width, log_n, started.elapsed().as_secs_f64(), stats.sampling_attempts);
        }
    }
    stats.points_capacity = points.capacity();
    stats.admission_capacity = seen.capacity();
    stats.compressed_capacity_bytes = seen.iter().try_fold(0usize, |n, p| n.checked_add(p.capacity()))
        .ok_or("diagnostic G1 encoded capacity overflow")?;
    Ok((points, stats))
}

#[derive(Default)]
pub(crate) struct SetupConstructionStats {
    pub g1_capacity: usize,
    pub g2_capacity: usize,
    pub seen1_capacity: usize,
    pub seen2_capacity: usize,
    pub compressed_point_capacity_bytes: usize,
    pub prover_serialized_bytes: u64,
    pub verifier_serialized_bytes: u64,
}

struct CountedSetupWriter<W> { inner: W, accepted: u64, expected: u64 }
impl<W: Write> Write for CountedSetupWriter<W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let requested = u64::try_from(bytes.len()).map_err(|_| io::ErrorKind::InvalidData)?;
        let end = self.accepted.checked_add(requested).ok_or(io::ErrorKind::InvalidData)?;
        if end > self.expected { return Err(io::ErrorKind::InvalidData.into()); }
        let written = self.inner.write(bytes)?;
        if written > bytes.len() { return Err(io::ErrorKind::InvalidData.into()); }
        self.accepted = self.accepted.checked_add(written as u64).ok_or(io::ErrorKind::InvalidData)?;
        Ok(written)
    }
    fn flush(&mut self) -> io::Result<()> { self.inner.flush() }
}
struct SetupDigestWriter<'a>(&'a mut Blake2b512);
impl Write for SetupDigestWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> { self.0.update(bytes); Ok(bytes.len()) }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}
fn borrowed_setup_frame<T: dory_pcs::primitives::serialization::DorySerialize>(
    value: &T, hasher: &mut Blake2b512,
) -> Result<u64, String> {
    use dory_pcs::primitives::serialization::{Compress, DorySerialize};
    let invalid = || ark_serialize::SerializationError::InvalidData.to_string();
    let expected = u64::try_from(DorySerialize::serialized_size(value, Compress::Yes)).map_err(|_| invalid())?;
    hasher.update(expected.to_le_bytes());
    let mut writer = CountedSetupWriter { inner: SetupDigestWriter(hasher), accepted: 0, expected };
    write_borrowed_setup(value, &mut writer)
}
fn write_borrowed_setup<T:dory_pcs::primitives::serialization::DorySerialize,W:Write>(
    value:&T,writer:&mut CountedSetupWriter<W>)->Result<u64,String>{
    use dory_pcs::primitives::serialization::{Compress,DorySerialize};
    let invalid=||ark_serialize::SerializationError::InvalidData.to_string();
    DorySerialize::serialize_with_mode(value,&mut *writer,Compress::Yes).map_err(|_|invalid())?;
    if writer.accepted!=writer.expected{return Err(invalid());}
    Ok(writer.accepted)
}
fn streamed_setup_id(log_n: usize, prover: &ProverSetup<BN254>, verifier: &VerifierSetup<BN254>)
    -> Result<([u8;32],u64,u64),String> {
    let mut hasher = Blake2b512::new();
    hasher.update(SETUP_DOMAIN); hasher.update(VENDOR_PIN);
    hasher.update((log_n as u64).to_le_bytes());
    let prover_bytes = borrowed_setup_frame(prover, &mut hasher)?;
    let verifier_bytes = borrowed_setup_frame(verifier, &mut hasher)?;
    let mut id = [0;32]; id.copy_from_slice(&hasher.finalize()[..32]);
    Ok((id,prover_bytes,verifier_bytes))
}

// Frozen original generator and hash path, used only as a bounded independent
// oracle. It intentionally retains the former allocation order and wrappers.
#[cfg(test)]
pub(crate) fn original_setup_for_construction_test(log_n:usize)->Setup{
    assert!(log_n<=MAX_LOG_N);
    let width=1usize<<log_n.div_ceil(2);
    let mut seen1=HashSet::new();let mut seen2=HashSet::new();
    let mut sample1=|role:&[u8],index:usize|->Result<ArkG1,String>{
        let mut rng=CoordinateRng::new(log_n,role,index);
        for _ in 0..4096{let point=G1Projective::rand(&mut rng);
            if !point.is_zero()&&seen1.insert(encode(&point)?){return Ok(ArkG1(point));}}
        Err("G1 generator admission failed".into())
    };
    let mut sample2=|role:&[u8],index:usize|->Result<ArkG2,String>{
        let mut rng=CoordinateRng::new(log_n,role,index);
        for _ in 0..4096{let point=G2Projective::rand(&mut rng);
            if !point.is_zero()&&seen2.insert(encode(&point)?){return Ok(ArkG2(point));}}
        Err("G2 generator admission failed".into())
    };
    let g1_vec=(0..width).map(|i|sample1(b"G1-primary",i)).collect::<Result<Vec<_>,_>>().unwrap();
    let g2_vec=(0..width).map(|i|sample2(b"G2-primary",i)).collect::<Result<Vec<_>,_>>().unwrap();
    let h1=sample1(b"G1-hiding",0).unwrap();let h2=sample2(b"G2-hiding",0).unwrap();
    let ht=ArkGT(ark_bn254::Bn254::pairing(h1.0,h2.0));
    let prover=ProverSetup::<BN254>{g1_vec,g2_vec,h1,h2,ht};let verifier=prover.to_verifier_setup();
    let mut hasher=Blake2b512::new();hasher.update(SETUP_DOMAIN);hasher.update(VENDOR_PIN);
    hasher.update((log_n as u64).to_le_bytes());
    for bytes in [encode(&ArkworksProverSetup(prover.clone())).unwrap(),encode(&ArkworksVerifierSetup(verifier.clone())).unwrap()]{
        hasher.update((bytes.len()as u64).to_le_bytes());hasher.update(&bytes);}
    let mut id=[0;32];id.copy_from_slice(&hasher.finalize()[..32]);Setup{prover,verifier,id,log_n}
}

#[cfg(test)]
pub(crate) fn construction_setup22()->(Setup,SetupConstructionStats,usize){
    // Only the small canonical oracle buffers survive into the new generation.
    let (old_prover,old_verifier,old_id)={let old=original_setup_for_construction_test(22);
        (encode(&ArkworksProverSetup(old.prover)).unwrap(),encode(&ArkworksVerifierSetup(old.verifier)).unwrap(),old.id)};
    let mut stats=SetupConstructionStats::default();let setup=generate_setup_measured(22,MAX_LOG_N,&mut stats).unwrap();
    assert_eq!(encode(&ArkworksProverSetup(setup.prover.clone())).unwrap(),old_prover);
    let key_bytes=encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();assert_eq!(key_bytes,old_verifier);
    assert_eq!(key_bytes,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"));assert_eq!(setup.id,old_id);
    let key=crate::verifier_key::admit(22,&key_bytes).unwrap();assert_eq!(key.id(),&setup.id);
    assert_eq!((stats.g1_capacity,stats.g2_capacity),(2048,2048));
    assert_eq!((stats.prover_serialized_bytes,stats.verifier_serialized_bytes),(old_prover.len()as u64,old_verifier.len()as u64));
    let mut prover_writer=CountedSetupWriter{inner:Vec::new(),accepted:0,expected:stats.prover_serialized_bytes};
    write_borrowed_setup(&setup.prover,&mut prover_writer).unwrap();assert_eq!(prover_writer.inner,old_prover);
    let mut verifier_writer=CountedSetupWriter{inner:Vec::new(),accepted:0,expected:stats.verifier_serialized_bytes};
    write_borrowed_setup(&setup.verifier,&mut verifier_writer).unwrap();assert_eq!(verifier_writer.inner,old_verifier);
    (setup,stats,9)
}

#[cfg(test)]
pub(crate) fn construction_setup_controls()->(usize,usize,usize){
    use ark_ff::One;
    let mut math=0;let mut negatives=0;let mut proof_cases=0;
    let mut zero_case=None;
    for log_n in 0..=4{
        let old=original_setup_for_construction_test(log_n);let new=generate_setup(log_n).unwrap();
        assert_eq!(encode(&ArkworksProverSetup(old.prover.clone())).unwrap(),encode(&ArkworksProverSetup(new.prover.clone())).unwrap());
        assert_eq!(encode(&ArkworksVerifierSetup(old.verifier.clone())).unwrap(),encode(&ArkworksVerifierSetup(new.verifier.clone())).unwrap());
        assert_eq!(old.id,new.id);
        let values=(0..1usize<<log_n).map(|i|Fr::from((i*i+7)as u64)).collect::<Vec<_>>();
        let point=(0..log_n).map(|i|Fr::from((i+3)as u64)).collect::<Vec<_>>();
        let a=commit(&values,&old).unwrap();let b=commit(&values,&new).unwrap();
        let mut ta=Transcript::new(b"pcs-construction-tiny-v1");let mut tb=ta.clone();
        let pa=open(&a,&point,&old,&mut ta).unwrap();let pb=open(&b,&point,&new,&mut tb).unwrap();
        assert_eq!(encode_proof(&pa).unwrap(),encode_proof(&pb).unwrap());
        assert_eq!((ta.challenges(),ta.raw_queries(),ta.bytes_absorbed()),(tb.challenges(),tb.raw_queries(),tb.bytes_absorbed()));
        assert_eq!(ta.challenge_scalar(b"after-tiny"),tb.challenge_scalar(b"after-tiny"));math+=6;
        let value=b.polynomial.evaluate(&point.iter().copied().map(ArkFr).collect::<Vec<_>>()).0;
        verify(b.commitment,value,&point,&pb,&new,&mut Transcript::new(b"pcs-construction-tiny-v1")).unwrap();proof_cases+=1;
        let mut wrong=new.clone();wrong.id[0]^=1;
        assert!(verify(b.commitment,value,&point,&pb,&wrong,&mut Transcript::new(b"pcs-construction-tiny-v1")).is_err());negatives+=1;
        assert!(verify(b.commitment,value+Fr::one(),&point,&pb,&new,&mut Transcript::new(b"pcs-construction-tiny-v1")).is_err());negatives+=1;
        if log_n==0{zero_case=Some((new,b,pb,value));}
    }
    struct ShortWriter{bytes:Vec<u8>,fail_after:Option<usize>}
    impl Write for ShortWriter{
        fn write(&mut self,bytes:&[u8])->io::Result<usize>{
            let remain=self.fail_after.map(|n|n.saturating_sub(self.bytes.len())).unwrap_or(usize::MAX);
            if remain==0{return Err(io::ErrorKind::Other.into());}
            let n=bytes.len().min(3).min(remain);self.bytes.extend_from_slice(&bytes[..n]);Ok(n)
        }
        fn flush(&mut self)->io::Result<()>{Ok(())}
    }
    let (setup,positive_commitment,positive_proof,positive_value)=zero_case.unwrap();
    let expected=encode(&ArkworksProverSetup(setup.prover.clone())).unwrap();
    let mut positive=CountedSetupWriter{inner:ShortWriter{bytes:Vec::new(),fail_after:None},accepted:0,expected:expected.len()as u64};
    assert_eq!(write_borrowed_setup(&setup.prover,&mut positive).unwrap(),expected.len()as u64);
    assert_eq!(positive.inner.bytes,expected);math+=2;
    let invalid=ark_serialize::SerializationError::InvalidData.to_string();
    let mut failure=CountedSetupWriter{inner:ShortWriter{bytes:Vec::new(),fail_after:Some(17)},accepted:0,expected:expected.len()as u64};
    assert_eq!(write_borrowed_setup(&setup.prover,&mut failure).unwrap_err(),invalid);assert_eq!(failure.accepted,17);negatives+=1;
    let mut mismatch=CountedSetupWriter{inner:Vec::new(),accepted:0,expected:expected.len()as u64+1};
    assert_eq!(write_borrowed_setup(&setup.prover,&mut mismatch).unwrap_err(),invalid);negatives+=1;
    let mut overflow=CountedSetupWriter{inner:Vec::new(),accepted:u64::MAX,expected:u64::MAX};
    assert!(overflow.write(&[1]).is_err());assert!(overflow.inner.is_empty());negatives+=1;
    let mut excess=CountedSetupWriter{inner:Vec::new(),accepted:0,expected:0};
    assert!(excess.write(&[1]).is_err());assert!(excess.inner.is_empty());negatives+=1;
    let prover=encode(&ArkworksProverSetup(setup.prover.clone())).unwrap();let verifier=encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let mut preimage=SETUP_DOMAIN.to_vec();preimage.extend_from_slice(VENDOR_PIN);preimage.extend_from_slice(&0u64.to_le_bytes());
    let frame_start=preimage.len();preimage.extend_from_slice(&(prover.len()as u64).to_le_bytes());preimage.extend_from_slice(&prover);
    preimage.extend_from_slice(&(verifier.len()as u64).to_le_bytes());preimage.extend_from_slice(&verifier);
    let digest=Blake2b512::digest(&preimage);assert_eq!(&digest[..32],&setup.id);math+=1;
    let reject_derived_id=|id:[u8;32]|{
        assert_ne!(id,setup.id);
        let mut receiver=setup.clone();receiver.id=id;
        assert!(verify(positive_commitment.commitment,positive_value,&[],&positive_proof,&receiver,
            &mut Transcript::new(b"pcs-construction-tiny-v1")).is_err());
    };
    for index in [0,SETUP_DOMAIN.len(),frame_start]{let mut changed=preimage.clone();changed[index]^=1;
        let mut id=[0u8;32];id.copy_from_slice(&Blake2b512::digest(&changed)[..32]);
        reject_derived_id(id);negatives+=1;}
    let mut swapped=preimage[..frame_start].to_vec();swapped.extend_from_slice(&(verifier.len()as u64).to_le_bytes());swapped.extend_from_slice(&verifier);
    swapped.extend_from_slice(&(prover.len()as u64).to_le_bytes());swapped.extend_from_slice(&prover);
    let mut id=[0u8;32];id.copy_from_slice(&Blake2b512::digest(&swapped)[..32]);
    reject_derived_id(id);negatives+=1;
    for (role,index) in [(b"G1-primary".as_slice(),1usize),(b"G1-hiding".as_slice(),0usize)]{
        let replacement=ArkG1(G1Projective::rand(&mut CoordinateRng::new(0,role,index)));
        assert_ne!(replacement,setup.prover.g1_vec[0]);
        let mut altered=setup.clone();altered.prover.g1_vec[0]=replacement;
        assert_ne!(encode(&ArkworksProverSetup(altered.prover.clone())).unwrap(),prover);
        let (id,_,_)=streamed_setup_id(0,&altered.prover,&altered.verifier).unwrap();
        reject_derived_id(id);negatives+=1;}
    assert!(generate_setup(25).is_err());negatives+=1;
    assert!(decode_proof(&[],MAX_VERIFY_LOG_N).unwrap_err().contains("length"));math+=1;
    assert!(decode_proof(&[],MAX_VERIFY_LOG_N+1).is_err());negatives+=1;
    assert_eq!((math,negatives,proof_cases),(34,22,5));(math,negatives,proof_cases)
}

fn generate_setup_with_limit(log_n:usize,admitted_log_n:usize)->Result<Setup,String>{
    generate_setup_measured(log_n, admitted_log_n, &mut SetupConstructionStats::default())
}
fn generate_setup_measured(log_n:usize,admitted_log_n:usize,stats:&mut SetupConstructionStats)->Result<Setup,String>{
    if log_n>admitted_log_n||log_n>=usize::BITS as usize {
        return Err("setup dimension exceeds prototype bound".into());
    }
    let width = 1usize << log_n.div_ceil(2);
    let mut seen1 = HashSet::new();
    let mut seen2 = HashSet::new();
    let admitted_points = width.checked_add(1).ok_or("setup point count overflow")?;
    seen1.try_reserve(admitted_points).map_err(|_| "G1 admission reservation failed")?;
    seen2.try_reserve(admitted_points).map_err(|_| "G2 admission reservation failed")?;
    let mut sample1 = |role: &[u8], index: usize| -> Result<ArkG1, String> {
        let mut rng = CoordinateRng::new(log_n, role, index);
        for _ in 0..4096 {
            let point = G1Projective::rand(&mut rng);
            if !point.is_zero() && seen1.insert(encode(&point)?) { return Ok(ArkG1(point)); }
        }
        Err("G1 generator admission failed".into())
    };
    let mut sample2 = |role: &[u8], index: usize| -> Result<ArkG2, String> {
        let mut rng = CoordinateRng::new(log_n, role, index);
        for _ in 0..4096 {
            let point = G2Projective::rand(&mut rng);
            if !point.is_zero() && seen2.insert(encode(&point)?) { return Ok(ArkG2(point)); }
        }
        Err("G2 generator admission failed".into())
    };
    let mut g1_vec = Vec::new();
    g1_vec.try_reserve_exact(width).map_err(|_| "G1 generator reservation failed")?;
    if g1_vec.capacity() != width { return Err("G1 generator capacity exceeds reservation".into()); }
    for i in 0..width { g1_vec.push(sample1(b"G1-primary", i)?); }
    let mut g2_vec = Vec::new();
    g2_vec.try_reserve_exact(width).map_err(|_| "G2 generator reservation failed")?;
    if g2_vec.capacity() != width { return Err("G2 generator capacity exceeds reservation".into()); }
    for i in 0..width { g2_vec.push(sample2(b"G2-primary", i)?); }
    let h1 = sample1(b"G1-hiding", 0)?;
    let h2 = sample2(b"G2-hiding", 0)?;
    drop(sample1); drop(sample2);
    stats.g1_capacity = g1_vec.capacity(); stats.g2_capacity = g2_vec.capacity();
    stats.seen1_capacity = seen1.capacity(); stats.seen2_capacity = seen2.capacity();
    stats.compressed_point_capacity_bytes = seen1.iter().chain(seen2.iter())
        .try_fold(0usize, |sum, bytes| sum.checked_add(bytes.capacity()))
        .ok_or("setup encoded admission capacity overflow")?;
    drop(seen1); drop(seen2);
    let ht = ArkGT(ark_bn254::Bn254::pairing(h1.0, h2.0));
    let prover = ProverSetup::<BN254> { g1_vec, g2_vec, h1, h2, ht };
    let verifier = prover.to_verifier_setup();
    let (id, prover_bytes, verifier_bytes) = streamed_setup_id(log_n, &prover, &verifier)?;
    stats.prover_serialized_bytes = prover_bytes; stats.verifier_serialized_bytes = verifier_bytes;
    Ok(Setup { prover, verifier, id, log_n })
}

#[cfg(test)]
pub(crate) fn generate_setup_for_scale_diagnostic(log_n: usize) -> Result<Setup, String> {
    generate_setup_with_limit(log_n, log_n)
}

/// Diagnostic only: regenerate the exact log41 prover coordinates, then bind
/// them to the already admitted verifier bytes through the original setup ID.
/// This avoids recomputing the verifier's large pairing census. It does not
/// widen any production setup, commitment, or verifier admission limit.
#[cfg(test)]
pub(crate) fn regenerate_log41_prover_for_sparse_test(mark: impl Fn(&str)) -> Result<Setup, String> {
    const LOG_N: usize = 41;
    const WIDTH: usize = 1 << 21;
    let admitted = crate::verifier_key::admit(LOG_N,
        include_bytes!("../fixtures/verifier-keys-v1/log41.vk"))?;
    let expected = "ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6";
    let id_hex: String = admitted.id().iter().map(|b| format!("{b:02x}")).collect();
    if id_hex != expected { return Err("unexpected admitted log41 setup ID".into()); }

    mark("setup-g1-start");
    let mut seen1 = HashSet::new();
    seen1.try_reserve(WIDTH + 1).map_err(|_| "G1 admission reservation failed")?;
    let mut sample1 = |role: &[u8], index: usize| -> Result<ArkG1, String> {
        let mut rng = CoordinateRng::new(LOG_N, role, index);
        for _ in 0..4096 {
            let point = G1Projective::rand(&mut rng);
            if !point.is_zero() && seen1.insert(encode(&point)?) { return Ok(ArkG1(point)); }
        }
        Err("G1 generator admission failed".into())
    };
    let mut g1_vec = Vec::new();
    g1_vec.try_reserve_exact(WIDTH).map_err(|_| "G1 reservation failed")?;
    for i in 0..WIDTH {
        g1_vec.push(sample1(b"G1-primary", i)?);
        if (i + 1) % 65536 == 0 { mark(&format!("setup-g1-count={}", i + 1)); }
    }
    let h1 = sample1(b"G1-hiding", 0)?;
    drop(sample1); drop(seen1);
    mark("setup-g1-done");

    mark("setup-g2-start");
    let mut seen2 = HashSet::new();
    seen2.try_reserve(WIDTH + 1).map_err(|_| "G2 admission reservation failed")?;
    let mut sample2 = |role: &[u8], index: usize| -> Result<ArkG2, String> {
        let mut rng = CoordinateRng::new(LOG_N, role, index);
        for _ in 0..4096 {
            let point = G2Projective::rand(&mut rng);
            if !point.is_zero() && seen2.insert(encode(&point)?) { return Ok(ArkG2(point)); }
        }
        Err("G2 generator admission failed".into())
    };
    let mut g2_vec = Vec::new();
    g2_vec.try_reserve_exact(WIDTH).map_err(|_| "G2 reservation failed")?;
    for i in 0..WIDTH {
        g2_vec.push(sample2(b"G2-primary", i)?);
        if (i + 1) % 65536 == 0 { mark(&format!("setup-g2-count={}", i + 1)); }
    }
    let h2 = sample2(b"G2-hiding", 0)?;
    drop(sample2); drop(seen2);
    mark("setup-g2-done");
    let ht = ArkGT(ark_bn254::Bn254::pairing(h1.0, h2.0));
    let prover = ProverSetup::<BN254> { g1_vec, g2_vec, h1, h2, ht };
    let verifier = admitted.verifier().clone();
    mark("setup-id-start");
    let (id, _, _) = streamed_setup_id(LOG_N, &prover, &verifier)?;
    if &id != admitted.id() { return Err("regenerated prover differs from admitted setup ID".into()); }
    mark("setup-id-done");
    Ok(Setup { prover, verifier, id, log_n: LOG_N })
}

pub fn commit(values: &[Fr], setup: &Setup) -> Result<Committed, String> {
    if setup.log_n > MAX_LOG_N || values.len() != 1usize << setup.log_n {
        return Err("input length does not match admitted setup dimension".into());
    }
    let nu = setup.log_n / 2;
    let sigma = setup.log_n.div_ceil(2);
    let polynomial = ArkworksPolynomial::new(values.iter().copied().map(ArkFr).collect());
    let (commitment, rows, blind) = polynomial.commit::<BN254, Transparent, G1Routines>(nu, sigma, &setup.prover)
        .map_err(|e| e.to_string())?;
    if !blind.0.is_zero() { return Err("unexpected commitment blind".into()); }
    Ok(Committed { polynomial, rows, commitment, nu, sigma })
}

pub(crate) fn bind_statement(setup: &Setup, commitment: &ArkGT, value: &Fr, point: &[Fr], transcript: &mut Transcript) -> Result<(), String> {
    bind_statement_parts(setup.log_n, &setup.id, commitment, value, point, transcript)
}

fn bind_statement_parts(log_n: usize, id: &[u8;32], commitment: &ArkGT, value: &Fr, point: &[Fr], transcript: &mut Transcript) -> Result<(), String> {
    if point.len() != log_n { return Err("opening point dimension mismatch".into()); }
    transcript.append_bytes(b"pcs-mode", b"Transparent-dory-v1");
    transcript.append_bytes(b"pcs-vendor", VENDOR_PIN);
    transcript.append_bytes(b"pcs-setup", id);
    transcript.append_u64(b"pcs-nu", (log_n / 2) as u64);
    transcript.append_u64(b"pcs-sigma", log_n.div_ceil(2) as u64);
    transcript.append_bytes(b"pcs-commitment", &encode(commitment)?);
    transcript.append_u64(b"pcs-point-length", point.len() as u64);
    for coordinate in point { transcript.append_scalar(b"pcs-coordinate-lsb-first", coordinate); }
    transcript.append_scalar(b"pcs-value", value);
    Ok(())
}

pub fn open(committed: &Committed, point: &[Fr], setup: &Setup, transcript: &mut Transcript) -> Result<ArkDoryProof, String> {
    if point.len() != setup.log_n || committed.nu != setup.log_n / 2 || committed.sigma != setup.log_n.div_ceil(2) {
        return Err("opening dimensions differ from admitted setup".into());
    }
    let point_ark: Vec<_> = point.iter().copied().map(ArkFr).collect();
    let evaluation = committed.polynomial.evaluate(&point_ark).0;
    bind_statement(setup, &committed.commitment, &evaluation, point, transcript)?;
    let (proof, blind) = dory_pcs::prove::<_, BN254, G1Routines, G2Routines, _, _, Transparent>(
        &committed.polynomial, &point_ark, committed.rows.clone(), ArkFr(Fr::zero()),
        committed.nu, committed.sigma, &setup.prover, transcript,
    ).map_err(|e| e.to_string())?;
    if blind.is_some() { return Err("unexpected proof blind".into()); }
    Ok(proof)
}

pub fn verify(commitment: ArkGT, value: Fr, point: &[Fr], proof: &ArkDoryProof, setup: &Setup, transcript: &mut Transcript) -> Result<(), String> {
    verify_parts(commitment, value, point, proof, setup.log_n, &setup.id, &setup.verifier, transcript)
}

pub fn verify_admitted(commitment: ArkGT, value: Fr, point: &[Fr], proof: &ArkDoryProof,
    key: &crate::verifier_key::AdmittedVerifierKey, transcript: &mut Transcript) -> Result<(), String> {
    verify_parts(commitment, value, point, proof, key.log_n(), key.id(), key.verifier(), transcript)
}

fn verify_parts(commitment: ArkGT, value: Fr, point: &[Fr], proof: &ArkDoryProof, log_n: usize,
    id: &[u8;32], verifier: &VerifierSetup<BN254>, transcript: &mut Transcript) -> Result<(), String> {
    check_shape(proof, log_n)?;
    bind_statement_parts(log_n, id, &commitment, &value, point, transcript)?;
    let point_ark: Vec<_> = point.iter().copied().map(ArkFr).collect();
    dory_pcs::verify::<_, BN254, G1Routines, G2Routines, _>(
        commitment, ArkFr(value), &point_ark, proof, verifier.clone(), transcript,
    ).map_err(|e| e.to_string())
}

fn check_shape(proof: &ArkDoryProof, log_n: usize) -> Result<(), String> {
    if log_n > MAX_VERIFY_LOG_N || proof.nu != log_n / 2 || proof.sigma != log_n.div_ceil(2)
        || proof.first_messages.len() != proof.sigma || proof.second_messages.len() != proof.sigma {
        return Err("Dory proof dimension/round mismatch".into());
    }
    match proof.mode().map_err(|e| e.to_string())? {
        dory_pcs::ProofMode::Transparent(..) => Ok(()),
    }
}

pub fn encode_proof(proof: &ArkDoryProof) -> Result<Vec<u8>, String> {
    check_shape(proof, proof.nu.checked_add(proof.sigma).ok_or("dimension overflow")?)?;
    encode(proof)
}

pub fn decode_proof(bytes: &[u8], log_n: usize) -> Result<ArkDoryProof, String> {
    if log_n > MAX_VERIFY_LOG_N { return Err("proof dimension exceeds verifier bound".into()); }
    let sigma = log_n.div_ceil(2);
    let g1_size = G1Projective::zero().compressed_size();
    let g2_size = G2Projective::zero().compressed_size();
    let gt_size = ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero().compressed_size();
    let rounds_offset = 2 * gt_size + g1_size;
    let expected_size = rounds_offset + 4 + sigma * (6 * gt_size + 3 * g1_size + 3 * g2_size)
        + 1 + g1_size + g2_size + 8;
    if bytes.len() != expected_size { return Err("noncanonical or oversized Dory proof length".into()); }
    let rounds = u32::from_le_bytes(bytes[rounds_offset..rounds_offset + 4].try_into().unwrap()) as usize;
    if rounds != sigma { return Err("Dory round count rejected before allocation".into()); }
    let mut cursor = bytes;
    let proof = ArkDoryProof::deserialize_compressed(&mut cursor).map_err(|e| e.to_string())?;
    if !cursor.is_empty() { return Err("trailing Dory proof bytes".into()); }
    check_shape(&proof, log_n)?;
    if encode(&proof)? != bytes { return Err("noncanonical Dory proof encoding".into()); }
    Ok(proof)
}

pub fn encode_commitment(commitment: &ArkGT) -> Result<Vec<u8>, String> { encode(commitment) }

pub fn decode_commitment(bytes: &[u8]) -> Result<ArkGT, String> {
    let expected = ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero().compressed_size();
    if bytes.len() != expected { return Err("commitment length mismatch".into()); }
    let mut cursor = bytes;
    let commitment = ArkGT::deserialize_compressed(&mut cursor).map_err(|e| e.to_string())?;
    if !cursor.is_empty() || encode(&commitment)? != bytes { return Err("noncanonical commitment".into()); }
    Ok(commitment)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn c533_odd_padded_row_commitment() {
        use dory_pcs::primitives::arithmetic::{Group, PairingCurve};
        use dory_pcs::primitives::transcript::Transcript as _;
        const ANCHOR: &[u8] = b"c533-odd-padding-falsifier-v1";

        // Build through the existing group-state API, bypassing the honest
        // polynomial constructor, while retaining the public PCS verifier.
        fn group_witness_proof(setup: &Setup, point: &[Fr], row: usize) -> (ArkGT, ArkDoryProof) {
            let a = setup.prover.g1_vec[0];
            let commitment = BN254::pair(&a, &setup.prover.g2_vec[row]);
            let zero = ArkFr(Fr::zero());
            let one = Fr::from(1);
            let (x, y, r) = (point[0], point[1], point[2]);
            let s1 = vec![ArkFr((one-x)*(one-y)), ArkFr(x*(one-y)),
                ArkFr((one-x)*y), ArkFr(x*y)];
            let s2 = vec![ArkFr(one-r), ArkFr(r), zero, zero];
            let mut v1 = vec![ArkG1::identity(); 4];
            v1[row] = a;
            let mut state = dory_pcs::DoryProverState::<BN254, Transparent>::new(
                v1, vec![ArkG2::identity(); 4], None, s1, s2, &setup.prover);
            state.set_initial_blinds(zero, zero, zero, zero, zero);
            let vmv_message = dory_pcs::VMVMessage {
                c: ArkGT::identity(), d2: ArkGT::identity(), e1: ArkG1::identity(),
            };
            let mut t = Transcript::new(ANCHOR);
            bind_statement_parts(3, &setup.id, &commitment, &Fr::zero(), point, &mut t).unwrap();
            t.append_serde(b"vmv_c", &vmv_message.c);
            t.append_serde(b"vmv_d2", &vmv_message.d2);
            t.append_serde(b"vmv_e1", &vmv_message.e1);
            let mut first_messages = Vec::new();
            let mut second_messages = Vec::new();
            for _ in 0..2 {
                let first = state.compute_first_message::<G1Routines, G2Routines>();
                t.append_serde(b"d1_left", &first.d1_left);
                t.append_serde(b"d1_right", &first.d1_right);
                t.append_serde(b"d2_left", &first.d2_left);
                t.append_serde(b"d2_right", &first.d2_right);
                t.append_serde(b"e1_beta", &first.e1_beta);
                t.append_serde(b"e2_beta", &first.e2_beta);
                let beta = ArkFr(t.challenge_scalar(b"beta"));
                state.apply_first_challenge::<G1Routines, G2Routines>(&beta);
                first_messages.push(first);
                let second = state.compute_second_message::<G1Routines, G2Routines>();
                t.append_serde(b"c_plus", &second.c_plus);
                t.append_serde(b"c_minus", &second.c_minus);
                t.append_serde(b"e1_plus", &second.e1_plus);
                t.append_serde(b"e1_minus", &second.e1_minus);
                t.append_serde(b"e2_plus", &second.e2_plus);
                t.append_serde(b"e2_minus", &second.e2_minus);
                let alpha = ArkFr(t.challenge_scalar(b"alpha"));
                state.apply_second_challenge::<G1Routines, G2Routines>(&alpha);
                second_messages.push(second);
            }
            let gamma = ArkFr(t.challenge_scalar(b"gamma"));
            state.apply_fold_scalars(&gamma);
            let final_message = state.compute_final_message();
            t.append_serde(b"final_e1", &final_message.e1);
            t.append_serde(b"final_e2", &final_message.e2);
            let _d = t.challenge_scalar(b"d");
            (commitment, dory_pcs::DoryProof {
                vmv_message, first_messages, second_messages,
                final_message: Some(final_message), nu: 1, sigma: 2,
            })
        }

        fn public_roundtrip_verify(setup: &Setup, point: &[Fr], row: usize) -> Result<(), String> {
            let (commitment, proof) = group_witness_proof(setup, point, row);
            let decoded_commitment = decode_commitment(&encode_commitment(&commitment)?)?;
            let decoded_proof = decode_proof(&encode_proof(&proof)?, 3)?;
            verify(decoded_commitment, Fr::zero(), point, &decoded_proof, setup,
                &mut Transcript::new(ANCHOR))
        }

        let setup = generate_setup(3).unwrap();
        let canonical_zero = commit(&vec![Fr::zero(); 8], &setup).unwrap();
        assert_eq!(canonical_zero.commitment, ArkGT::identity());
        let padded_commitment = BN254::pair(&setup.prover.g1_vec[0], &setup.prover.g2_vec[2]);
        assert_ne!(padded_commitment, ArkGT::identity());
        assert_ne!(padded_commitment, canonical_zero.commitment);
        let mut padded_pass = 0;
        for vertex in 0..8usize {
            let point: Vec<_> = (0..3).map(|bit| Fr::from(((vertex >> bit) & 1) as u64)).collect();
            public_roundtrip_verify(&setup, &point, 2)
                .unwrap_or_else(|e| panic!("padded vertex {vertex} rejected: {e}"));
            padded_pass += 1;
        }
        let point = [Fr::from(2), Fr::from(3), Fr::from(5)];
        public_roundtrip_verify(&setup, &point, 2).expect("padded non-Boolean point rejected");
        padded_pass += 1;
        let active_error = public_roundtrip_verify(&setup, &point, 1)
            .expect_err("active-row zero-VMV control unexpectedly accepted");
        assert_eq!(active_error, "Invalid proof");
        assert_eq!(padded_pass, 9);
        println!("C533_PADDED_PASS=9 C533_ACTIVE_REJECT=1 C533_CANONICAL_ZERO_IDENTITY=true");
    }

    #[test]
    fn reproducible_setup_and_serialized_opening() {
        for log_n in [0, 3, 4] {
            let setup = generate_setup(log_n).unwrap();
            assert_eq!(setup.id, generate_setup(log_n).unwrap().id);
            let values: Vec<_> = (0..1usize << log_n).map(|i| Fr::from((i * i + 7) as u64)).collect();
            let committed = commit(&values, &setup).unwrap();
            let point: Vec<_> = (0..log_n).map(|i| Fr::from((i + 3) as u64)).collect();
            let value = committed.polynomial.evaluate(&point.iter().copied().map(ArkFr).collect::<Vec<_>>()).0;
            let expected: Fr = values.iter().enumerate().map(|(index, coefficient)| {
                point.iter().enumerate().fold(*coefficient, |acc, (bit, x)| {
                    acc * if (index >> bit) & 1 == 1 { *x } else { Fr::from(1) - *x }
                })
            }).sum();
            assert_eq!(value, expected, "Dory must use the GKR LSB-first MLE convention");
            let proof = open(&committed, &point, &setup, &mut Transcript::new(b"pcs-test")).unwrap();
            let bytes = encode_proof(&proof).unwrap();
            let decoded = decode_proof(&bytes, log_n).unwrap();
            let commitment = decode_commitment(&encode_commitment(&committed.commitment).unwrap()).unwrap();
            verify(commitment, value, &point, &decoded, &setup, &mut Transcript::new(b"pcs-test")).unwrap();
            assert!(verify(commitment, value + Fr::from(1), &point, &decoded, &setup, &mut Transcript::new(b"pcs-test")).is_err());
            assert!(verify(commitment, value, &point, &decoded, &setup, &mut Transcript::new(b"wrong-anchor")).is_err());
            if !point.is_empty() {
                let mut wrong_point = point.clone(); wrong_point[0] += Fr::from(1);
                assert!(verify(commitment, value, &wrong_point, &decoded, &setup, &mut Transcript::new(b"pcs-test")).is_err());
            }
            let mut trailing = bytes.clone(); trailing.push(0);
            assert!(decode_proof(&trailing, log_n).is_err());
            let mut bad_rounds = bytes;
            let offset = 2 * commitment.compressed_size() + G1Projective::zero().compressed_size();
            bad_rounds[offset..offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());
            assert!(decode_proof(&bad_rounds, log_n).is_err());
        }
    }

    #[test]
    fn generated_odd_key_admits_and_verifies_a_serialized_odd_proof() {
        let log_n=9;
        let setup=generate_setup(log_n).unwrap();
        let key_bytes=encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
        let key=crate::verifier_key::admit_generated_test_key(log_n,&key_bytes,setup.id).unwrap();
        let values=(0..1usize<<log_n).map(|i|Fr::from((i*i+17) as u64)).collect::<Vec<_>>();
        let committed=commit(&values,&setup).unwrap();
        let point=(0..log_n).map(|i|Fr::from((i*3+5) as u64)).collect::<Vec<_>>();
        let value:Fr=values.iter().enumerate().map(|(index,coefficient)|{
            point.iter().enumerate().fold(*coefficient,|acc,(bit,x)|{
                acc*if (index>>bit)&1==1 {*x} else {Fr::from(1)-*x}
            })
        }).sum();
        let proof=open(&committed,&point,&setup,&mut Transcript::new(b"odd-admitted-pcs")).unwrap();
        let proof_bytes=encode_proof(&proof).unwrap();
        let decoded=decode_proof(&proof_bytes,log_n).unwrap();
        verify_admitted(committed.commitment,value,&point,&decoded,&key,&mut Transcript::new(b"odd-admitted-pcs")).unwrap();
        assert!(verify_admitted(committed.commitment,value+Fr::from(1),&point,&decoded,&key,&mut Transcript::new(b"odd-admitted-pcs")).is_err());
        assert!(verify_admitted(committed.commitment,value,&point,&decoded,&key,&mut Transcript::new(b"wrong-odd-anchor")).is_err());
    }

    #[test]
    fn verifier_proof_dimension_cap_is_independent_of_producer_cap() {
        assert!(generate_setup(MAX_VERIFY_LOG_N).is_err());
        assert!(decode_proof(&[],MAX_VERIFY_LOG_N).unwrap_err().contains("length"));
        assert!(decode_proof(&[],MAX_VERIFY_LOG_N+1).unwrap_err().contains("verifier bound"));
    }

    #[test]
    #[ignore = "manual k=32 transparent setup scale diagnostic; does not build a witness or commitment"]
    fn diagnostic_generate_k32_transparent_setup_only() {
        diagnostic_generate_transparent_setup_only(32);
    }

    #[test]
    #[ignore = "manual k=41 transparent setup scale diagnostic; does not build a witness or commitment"]
    fn diagnostic_generate_k41_transparent_setup_only() {
        diagnostic_generate_transparent_setup_only(41);
    }

    fn diagnostic_generate_transparent_setup_only(log_n: usize) {
        let log_n = log_n;
        assert!(generate_setup(log_n).is_err(),"runtime admission must remain capped at 24 bits");
        let started=std::time::Instant::now();
        let setup=generate_setup_with_limit(log_n,log_n).unwrap();
        let prover_generators=setup.prover.g1_vec.len()*std::mem::size_of::<ArkG1>()
            +setup.prover.g2_vec.len()*std::mem::size_of::<ArkG2>();
        let verifier_precompute=(setup.verifier.delta_1l.len()+setup.verifier.delta_1r.len()
            +setup.verifier.delta_2l.len()+setup.verifier.delta_2r.len()+setup.verifier.chi.len())
            *std::mem::size_of::<ark_bn254::Fq12>();
        let setup_id=setup.id.iter().map(|byte|format!("{byte:02x}")).collect::<String>();
        println!("dory_setup_only log_n={log_n} g1_generators={} g2_generators={} prover_generator_bytes={} verifier_precompute_bytes={} elapsed_ms={} setup_id={}",
            setup.prover.g1_vec.len(),setup.prover.g2_vec.len(),prover_generators,verifier_precompute,
            started.elapsed().as_millis(),setup_id);
    }
}

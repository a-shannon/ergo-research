//! Release-pinned admission for exact deterministic verifier-key bytes.
//! Digests select the bytes; reproducible setup generation establishes their
//! provenance. A caller-supplied manifest or setup ID is never an authority.
use blake2::{Blake2b512,Digest};
use ark_serialize::{CanonicalDeserialize,Compress,Validate};
use dory_pcs::{VerifierSetup,backends::arkworks::{ArkworksVerifierSetup,BN254}};
use crate::pcs;

pub const MAX_PINNED_KEY_BYTES:usize=42_864;

pub struct AdmittedVerifierKey {
    id:[u8;32],log_n:usize,verifier:VerifierSetup<BN254>,
}
impl AdmittedVerifierKey {
    pub fn id(&self)->&[u8;32] {&self.id}
    pub fn log_n(&self)->usize {self.log_n}
    pub(crate) fn verifier(&self)->&VerifierSetup<BN254> {&self.verifier}
}

const fn hex<const N:usize>(text:&str)->[u8;N] {
    const fn digit(x:u8)->u8 {match x {b'0'..=b'9'=>x-b'0',b'a'..=b'f'=>x-b'a'+10,_=>panic!("invalid compile-time hex")}}
    let bytes=text.as_bytes();assert!(bytes.len()==2*N);let mut out=[0;N];let mut i=0;
    while i<N {out[i]=(digit(bytes[2*i])<<4)|digit(bytes[2*i+1]);i+=1;}out
}
struct Pin {digest:[u8;64],id:[u8;32]}
fn pin(log_n:usize)->Result<Pin,String> {
    match log_n {
        18=>Ok(Pin {
            digest:hex("7f5f23faa3518d67ea0527153be759a8f38776c3d8277629266499493ee3391f9c839797a18a3ff18905ac146179a0086ffae04515019e64bc70452060988f75"),
            id:hex("0eb06acc69c9a222000e3ab4640ea3892e587612011e9140464e25ef57e31d3a")}),
        22=>Ok(Pin {
            digest:hex("b9037bbb5452360e0f05f199f340f3cc8da6ee0276c2844cd0305a571c0a1e1cf4d508f2eefdc2aa6e3484544ca9cbfd8e9bb5910ce7f034323a71c192a9a96c"),
            id:hex("94f67a7bd4490c3c563a7e421b4dbfdbe88cc09d090bb85d9ac8226337b73955")}),
        41=>Ok(Pin {
            digest:hex("a599010d26a97d53a8759924f702a45f0bca47d65202107686c61eba2992f326c3cb91c1ced0be78a5278c1f214e62773bad60e74381b50660aa5c7e3fa6a226"),
            id:hex("ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6")}),
        _=>Err("unsupported verifier-key dimension".into()),
    }
}

// Dory's setup is square internally. For an odd polynomial log_n, it rounds
// the row dimension up to the next even square capacity while retaining the
// requested log_n in the outer transcript and proof statement.
fn dory_verifier_shape(log_n:usize)->Result<(usize,usize),String> {
    let rounds=log_n.div_ceil(2);
    let length=rounds.checked_add(1).ok_or("verifier-key shape overflow")?;
    let max_log_n=rounds.checked_mul(2).ok_or("verifier-key shape overflow")?;
    Ok((length,max_log_n))
}

fn check_frame(log_n:usize,bytes:&[u8])->Result<(),String> {
    let (length,max_log_n)=dory_verifier_shape(log_n)?;let expected=1920*length+624;
    if bytes.len()!=expected {return Err("verifier-key length mismatch".into());}
    let stride=8+384*length;
    for vector in 0..5 {
        let at=vector*stride;let count=u64::from_le_bytes(bytes[at..at+8].try_into().unwrap());
        if count!=length as u64 {return Err("verifier-key vector length rejected before allocation".into());}
    }
    let at=5*stride+576;
    if u64::from_le_bytes(bytes[at..at+8].try_into().unwrap())!=max_log_n as u64 {
        return Err("verifier-key serialized dimension mismatch".into());
    }
    Ok(())
}

// Private so tests can isolate parser checks behind the public digest boundary.
fn decode_bounded(log_n:usize,bytes:&[u8])->Result<VerifierSetup<BN254>,String> {
    check_frame(log_n,bytes)?;
    let mut cursor=bytes;
    // The wrapper's Valid::check is a no-op. Validation must be requested on
    // deserialization, which propagates it to each source/target group element.
    let decoded=ArkworksVerifierSetup::deserialize_with_mode(&mut cursor,Compress::Yes,Validate::Yes)
        .map_err(|e|format!("invalid verifier-key group encoding: {e}"))?;
    if !cursor.is_empty(){return Err("trailing verifier-key bytes".into());}
    if pcs::encode(&decoded)?!=bytes{return Err("noncanonical verifier-key encoding".into());}
    let (length,max_log_n)=dory_verifier_shape(log_n)?;let v=decoded.0;
    if [v.delta_1l.len(),v.delta_1r.len(),v.delta_2l.len(),v.delta_2r.len(),v.chi.len()]!=[length;5]
        ||v.max_log_n!=max_log_n {return Err("decoded verifier-key shape mismatch".into());}
    Ok(v)
}

pub fn admit(log_n:usize,bytes:&[u8])->Result<AdmittedVerifierKey,String> {
    let expected=pin(log_n)?;
    admit_with_pin(log_n,bytes,expected)
}

fn admit_with_pin(log_n:usize,bytes:&[u8],expected:Pin)->Result<AdmittedVerifierKey,String> {
    check_frame(log_n,bytes)?;
    if Blake2b512::digest(bytes).as_slice()!=expected.digest {
        return Err("verifier-key digest mismatch".into());
    }
    let verifier=decode_bounded(log_n,bytes)?;
    Ok(AdmittedVerifierKey {id:expected.id,log_n,verifier})
}

#[cfg(test)]
pub(crate) fn admit_generated_test_key(log_n:usize,bytes:&[u8],id:[u8;32])->Result<AdmittedVerifierKey,String> {
    let mut digest=[0;64];digest.copy_from_slice(Blake2b512::digest(bytes).as_slice());
    admit_with_pin(log_n,bytes,Pin {digest,id})
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Zero;
    #[test]
    fn dory_verifier_shape_covers_even_and_odd_polynomial_dimensions() {
        assert_eq!(dory_verifier_shape(18).unwrap(),(10,18));
        assert_eq!(dory_verifier_shape(22).unwrap(),(12,22));
        assert_eq!(dory_verifier_shape(41).unwrap(),(22,42));
    }
    #[test]
    fn generated_odd_key_rejects_each_vector_count_and_wrong_internal_capacity() {
        let log_n=9;let setup=pcs::generate_setup(log_n).unwrap();
        let bytes=pcs::encode(&ArkworksVerifierSetup(setup.verifier)).unwrap();
        let (length,max_log_n)=dory_verifier_shape(log_n).unwrap();
        let stride=8+384*length;
        for vector in 0..5 {
            let mut changed=bytes.clone();
            changed[vector*stride..vector*stride+8].copy_from_slice(&((length+1) as u64).to_le_bytes());
            assert!(decode_bounded(log_n,&changed).unwrap_err().contains("before allocation"),"vector {vector}");
        }
        let at=5*stride+576;
        for capacity in [max_log_n-1,max_log_n+2] {
            let mut changed=bytes.clone();
            changed[at..at+8].copy_from_slice(&(capacity as u64).to_le_bytes());
            assert!(decode_bounded(log_n,&changed).unwrap_err().contains("dimension"),"capacity {capacity}");
        }
    }
    #[test]
    #[ignore = "manual k=41 verifier-key export; writes only to a caller-selected new file"]
    fn diagnostic_export_k41_verifier_key_bytes() {
        let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_K41_VK_EXPORT")
            .expect("set NIPOPOW_K41_VK_EXPORT to a new local file path"));
        assert!(path.is_absolute(),"verifier-key export path must be absolute");
        assert!(path.parent().is_some_and(|parent|parent.is_dir()),"verifier-key export parent must exist");
        assert!(!path.exists(),"verifier-key export path already exists");
        let setup=pcs::generate_setup_for_scale_diagnostic(41).unwrap();
        let setup_id=setup.id.iter().map(|byte|format!("{byte:02x}")).collect::<String>();
        assert_eq!(setup_id,"ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6",
            "k41 deterministic setup changed since the measured baseline; do not promote this key");
        let verifier=&setup.verifier;
        assert_eq!(verifier.max_log_n,42);
        assert_eq!([verifier.delta_1l.len(),verifier.delta_1r.len(),verifier.delta_2l.len(),
            verifier.delta_2r.len(),verifier.chi.len()],[22;5]);
        let bytes=pcs::encode(&ArkworksVerifierSetup(verifier.clone())).unwrap();
        assert_eq!(bytes.len(),42_864);
        let mut output=std::fs::OpenOptions::new().write(true).create_new(true).open(&path)
            .expect("refusing to overwrite an existing verifier-key export");
        use std::io::Write;
        output.write_all(&bytes).unwrap();output.sync_all().unwrap();drop(output);
        let digest=Blake2b512::digest(&bytes).iter().map(|byte|format!("{byte:02x}")).collect::<String>();
        println!("k41_verifier_key_bytes={} serialized_max_log_n={} vector_length=22 setup_id={} blake2b512={}",
            bytes.len(),verifier.max_log_n,setup_id,digest);
    }
    fn fixture(log_n:usize)->&'static[u8] {
        match log_n {18=>include_bytes!("../fixtures/verifier-keys-v1/log18.vk"),
            22=>include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),
            41=>include_bytes!("../fixtures/verifier-keys-v1/log41.vk"),_=>unreachable!()}
    }
    #[test]
    fn admitted_fixtures_regenerate_exactly_with_old_setup_ids() {
        for log_n in [18,22] {
            let bytes=fixture(log_n);let key=admit(log_n,bytes).unwrap();
            let regenerated=pcs::generate_setup(log_n).unwrap();
            assert_eq!(pcs::encode(&ArkworksVerifierSetup(regenerated.verifier)).unwrap(),bytes);
            assert_eq!(key.id(),&regenerated.id);assert_eq!(key.log_n(),log_n);
            assert!(key.verifier().delta_1l[0].0.is_zero(),"legitimate target identities remain admitted");
        }
    }
    #[test]
    fn admitted_k41_fixture_has_authenticated_odd_dimension_and_capacity_42() {
        let bytes=fixture(41);assert_eq!(bytes.len(),42_864);
        let key=admit(41,bytes).unwrap();
        assert_eq!(key.log_n(),41);
        assert_eq!(key.id(),&hex("ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6"));
        let verifier=key.verifier();
        assert_eq!(verifier.max_log_n,42);
        assert_eq!([verifier.delta_1l.len(),verifier.delta_1r.len(),verifier.delta_2l.len(),
            verifier.delta_2r.len(),verifier.chi.len()],[22;5]);
        assert!(admit(40,bytes).unwrap_err_text().contains("unsupported"));
        assert!(admit(42,bytes).unwrap_err_text().contains("unsupported"));
    }
    #[test]
    fn public_admission_rejects_wrong_pin_dimension_and_framing() {
        let original=fixture(18);
        assert!(admit(17,original).unwrap_err_text().contains("unsupported"));
        assert!(admit(22,original).unwrap_err_text().contains("length"));
        let mut changed=original.to_vec();changed[8..392].copy_from_slice(&original[392..776]);
        assert!(decode_bounded(18,&changed).is_ok(),"isolate a validly encoded wrong key");
        assert!(admit(18,&changed).unwrap_err_text().contains("digest"));
        let mut trailing=original.to_vec();trailing.push(0);assert!(admit(18,&trailing).is_err());
        assert!(admit(18,&original[..original.len()-1]).is_err());
    }
    trait ErrorText {fn unwrap_err_text(self)->String;}
    impl<T> ErrorText for Result<T,String> {fn unwrap_err_text(self)->String {match self {Ok(_)=>panic!("expected rejection"),Err(e)=>e}}}
    #[test]
    fn private_decoder_rejects_each_count_dimension_and_length_before_allocation() {
        for k in [18,22,41] {
            let bytes=fixture(k);let (length,max_log_n)=dory_verifier_shape(k).unwrap();
            let stride=8+384*length;
            for j in 0..5 {for count in [0u64,1,u64::MAX] {
                let mut changed=bytes.to_vec();changed[j*stride..j*stride+8].copy_from_slice(&count.to_le_bytes());
                assert!(decode_bounded(k,&changed).unwrap_err_text().contains("before allocation"));
            }}
            let at=5*stride+576;
            for capacity in [max_log_n-1,max_log_n+2] {
                let mut changed=bytes.to_vec();
                changed[at..at+8].copy_from_slice(&(capacity as u64).to_le_bytes());
                assert!(decode_bounded(k,&changed).unwrap_err_text().contains("dimension"));
            }
            let mut trailing=bytes.to_vec();trailing.push(0);assert!(decode_bounded(k,&trailing).is_err());
            assert!(decode_bounded(k,&bytes[..bytes.len()-1]).is_err());
        }
    }
    #[test]
    fn private_decoder_validates_group_encodings_and_gt_membership() {
        let bytes=fixture(18);let fixed=5*(8+384*10);
        for (at,size) in [(8,384),(fixed,32),(fixed+32,64),(fixed+96,32),(fixed+128,64),(fixed+192,384)] {
            let mut changed=bytes.to_vec();changed[at..at+size].fill(0xff);
            assert!(decode_bounded(18,&changed).is_err(),"group offset {at}");
        }
        // Canonical extension-field element, but not an order-r target element.
        let invalid=dory_pcs::backends::arkworks::ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>(ark_bn254::Fq12::from(2u64)));
        let encoded=pcs::encode(&invalid).unwrap();assert_eq!(encoded.len(),384);
        let mut changed=bytes.to_vec();changed[8..392].copy_from_slice(&encoded);
        assert!(decode_bounded(18,&changed).is_err());
        let mut non_subgroup=None;
        for i in 0..128 {
            let x=ark_bn254::Fq2::new(ark_bn254::Fq::from(i as u64),ark_bn254::Fq::from(1u64));
            if let Some(p)=ark_bn254::G2Affine::get_point_from_x_unchecked(x,false) {
                if !p.is_in_correct_subgroup_assuming_on_curve(){non_subgroup=Some(p);break;}
            }
        }
        let p=non_subgroup.expect("bounded non-subgroup fixture search");assert!(p.is_on_curve());
        let encoded=pcs::encode(&dory_pcs::backends::arkworks::ArkG2(p.into())).unwrap();
        let mut changed=bytes.to_vec();changed[fixed+32..fixed+96].copy_from_slice(&encoded);
        assert!(decode_bounded(18,&changed).is_err());
    }
}

// This diagnostic exports the accepted PCS32 verifier key without adding a
// public admission pin. It is intentionally separate from `admit`.
#[cfg(test)]
mod pcs32_diagnostic_export {
    use super::*;
    use std::path::Path;

    const LOG_N:usize=32;
    const KEY_BYTES:usize=33_264;
    const SETUP_ID:&str="1ae7badc1e529c7a5cda709ad1b418af6ae2efb6b7b4d909816d091c3260a51b";

    fn validate_export_path(path:&Path)->Result<(),String>{
        if !path.is_absolute(){return Err("PCS32 key export path must be absolute".into());}
        let parent=path.parent().ok_or("PCS32 key export parent absent")?;
        if !parent.is_dir(){return Err("PCS32 key export parent must exist".into());}
        match std::fs::symlink_metadata(path){
            Ok(_)=>return Err("PCS32 key export path already exists".into()),
            Err(error) if error.kind()==std::io::ErrorKind::NotFound=>(),
            Err(error)=>return Err(format!("PCS32 key export path check failed: {error}")),
        }
        Ok(())
    }

    fn sha256_hex(bytes:&[u8])->Result<String,String>{
        if bytes.len()>KEY_BYTES{return Err("PCS32 key SHA-256 input cap".into());}
        let len=u32::try_from(bytes.len()).map_err(|_|"PCS32 key SHA-256 length")?;
        #[cfg(windows)]{
            use std::ffi::c_void;
            #[link(name="crypt32")]
            extern "system"{fn CryptHashCertificate2(alg:*const u16,flags:u32,reserved:*mut c_void,
                data:*const u8,len:u32,out:*mut u8,out_len:*mut u32)->i32;}
            let alg=[83u16,72,65,50,53,54,0];let mut out=[0u8;32];let mut out_len=32u32;
            let ok=unsafe{CryptHashCertificate2(alg.as_ptr(),0,std::ptr::null_mut(),bytes.as_ptr(),len,
                out.as_mut_ptr(),&mut out_len)};
            if ok==0||out_len!=32{return Err("PCS32 key SHA-256 failed".into());}
            Ok(out.iter().map(|byte|format!("{byte:02x}")).collect())
        }
        #[cfg(not(windows))]{let _=len;Err("PCS32 key export is Windows-only".into())}
    }

    #[test]
    fn pcs32_export_path_rejects_relative_missing_parent_and_existing_target(){
        assert!(validate_export_path(Path::new("relative-pcs32-vk.bin")).is_err());
        let missing=std::env::temp_dir().join(format!("nipopow-pcs32-missing-{}-{}",
            std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        assert!(!missing.exists());
        assert!(validate_export_path(&missing.join("key.bin")).is_err());
        assert!(validate_export_path(&Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml")).is_err());
    }

    #[test]
    fn pcs32_diagnostic_key_does_not_extend_public_admission(){
        assert!(pin(LOG_N).is_err());
        assert_eq!(MAX_PINNED_KEY_BYTES,42_864);
    }

    #[test]
    #[ignore="manual bounded PCS32 verifier-key export; caller selects an exclusive new file"]
    fn diagnostic_export_pcs32_verifier_key_bytes(){
        let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_PCS32_VK_EXPORT")
            .expect("set NIPOPOW_PCS32_VK_EXPORT to a new local file path"));
        validate_export_path(&path).expect("refusing an unsafe PCS32 verifier-key export path");

        let setup=pcs::generate_setup_for_scale_diagnostic(LOG_N).expect("PCS32 diagnostic setup");
        let setup_id=setup.id.iter().map(|byte|format!("{byte:02x}")).collect::<String>();
        assert_eq!(setup_id,SETUP_ID,"PCS32 deterministic setup changed; do not promote this key");
        let verifier=&setup.verifier;
        assert_eq!(verifier.max_log_n,32);
        assert_eq!([verifier.delta_1l.len(),verifier.delta_1r.len(),verifier.delta_2l.len(),
            verifier.delta_2r.len(),verifier.chi.len()],[17;5]);
        let bytes=pcs::encode(&ArkworksVerifierSetup(verifier.clone())).expect("PCS32 verifier-key encode");
        assert_eq!(bytes.len(),KEY_BYTES);

        // decode_bounded requests Validate::Yes, checks all vector/dimension
        // bounds, and requires canonical re-encoding before any file export.
        let decoded=decode_bounded(LOG_N,&bytes).expect("bounded validated PCS32 decode");
        assert_eq!(pcs::encode(&ArkworksVerifierSetup(decoded)).expect("PCS32 verifier-key re-encode"),bytes);
        let mut output=std::fs::OpenOptions::new().write(true).create_new(true).open(&path)
            .expect("exclusive PCS32 verifier-key create");
        use std::io::Write;
        output.write_all(&bytes).expect("PCS32 verifier-key write");
        output.sync_all().expect("PCS32 verifier-key flush");drop(output);

        let mut input=std::fs::File::open(&path).expect("PCS32 verifier-key readback");
        use std::io::Read;
        let mut readback=Vec::with_capacity(KEY_BYTES);
        input.take((KEY_BYTES+1) as u64).read_to_end(&mut readback).expect("PCS32 verifier-key bounded readback");
        assert_eq!(readback.len(),KEY_BYTES,"PCS32 verifier-key readback extent");
        assert_eq!(readback,bytes,"PCS32 verifier-key readback bytes");
        let sha256=sha256_hex(&readback).expect("PCS32 verifier-key SHA-256");
        let blake2b512=Blake2b512::digest(&readback).iter().map(|byte|format!("{byte:02x}")).collect::<String>();
        println!("pcs32_verifier_key_bytes={} setup_id={} sha256={} blake2b512={}",
            readback.len(),setup_id,sha256,blake2b512);
    }
}

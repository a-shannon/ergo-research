//! Optional one-role producer diagnostic on the retained original log32 X.
//! No RAW capture, setup generation, new key or PCS proof is performed here.
use super::*;
use std::{fs::{self,File},io::Read,path::PathBuf};
use std::os::windows::fs::OpenOptionsExt;

struct HeldBytes {_file:File,bytes:Vec<u8>}
fn path_env(name:&str)->Result<PathBuf,String> {
    let path=PathBuf::from(std::env::var_os(name).ok_or_else(||format!("missing {name}"))?);
    if !crate::preview_test_paths::absolute_outside_source(&path) {return Err("C589 external absolute input/output path".into());}
    Ok(path)
}
fn held(path:&Path,size:usize,expected:&str)->Result<HeldBytes,String> {
    let metadata=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !metadata.is_file() || metadata.file_type().is_symlink() || metadata.len()!=size as u64 || size>33264 {
        return Err("C589 bounded public file extent".into());
    }
    let mut file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=size as u64 {return Err("C589 held public extent".into());}
    let mut bytes=vec![0u8;size];file.read_exact(&mut bytes).map_err(|e|e.to_string())?;
    let mut extra=[0u8;1];
    if file.read(&mut extra).map_err(|e|e.to_string())?!=0
        || crate::native_prefix_auth_plan::role0_sha256(&bytes)?!=historical47_hex::<32>(expected)? {
        return Err("C589 public bytes hash/EOF".into());
    }
    Ok(HeldBytes {_file:file,bytes})
}
fn candidate(context:&ProofContext<'_>,source:&PackedFile,admitted:&Historical47Admission)
    ->Result<(Vec<u8>,InputClaim),String> {
    historical47_geometry(&context.geometry)?;
    historical47_refs(context.consumer,context.relation_refs())?;
    if context.height_binding!=HeightBinding::HistoricalDiagnostic || context.public_bytes!=admitted.frame
        || historical47_frame(&context.consumer.public)?!=admitted.frame || admitted.key.log_n()!=32 {
        return Err("C589 candidate public/context identity".into());
    }
    let mut transcript=context.transcript(0,&admitted.key,&admitted.commitment);
    let unverified=core_pool_boolean::prove_packed_native_role0_candidate(
        context.consumer.parent.core_pool(),source,&mut transcript,
        |t|{context.bind_role(0,t);Ok(())},|r,u,v|context.coefficients(0,r,u,v))?;
    let(proof,claim)=unverified.into_parts();let bytes=gkr::encode_proof(&proof)?;
    if bytes.len()!=7264 || claim.point.len()!=32 {return Err("C589 candidate role0 extent".into());}
    Ok((bytes,claim))
}

#[test]
#[ignore="retained log32 corpus; reviewed bounded one-role producer Job required"]
fn c589_retained_role0_candidate_export_and_independent_consumer()->Result<(),String> {
    let directory=path_env("NIPOPOW_COMMON51_PUBLIC_DIR")?;
    let frame=held(&directory.join("statement.bin"),571,
        "C44FDFD8F42EED0AAFF6DCD0543F6C877F4A63562A7C61131DA4344786695295")?;
    let commitment=held(&directory.join("commitment.bin"),384,
        "2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90")?;
    let retained=held(&directory.join("role-0.gkr"),7264,
        "23D0B271C42DCB2364A17899E1FAA60006E6C5775B6B5F64EFCD18CF3A0486C5")?;
    let key=held(&path_env("NIPOPOW_COMMON51_KEY_PATH")?,33264,
        "D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2")?;
    let metadata=held(&path_env("NIPOPOW_COMMON51_KEY_METADATA_PATH")?,40,
        "E44408DC018E99711273794DF3575BE7D180CF347448A021AA7EEC6BD0143401")?;
    let admitted=Historical47Admission::new(&frame.bytes,&key.bytes,&metadata.bytes,&commitment.bytes)?;
    let source=PackedFile::open_with_limit(path_env("NIPOPOW_C589_PACK_PATH")?,32,32)?;
    // This hashes the actual immutably locked source through the exact reader
    // later used by the candidate, against the retained BLAKE2b-256 identity.
    let bound=Historical50BoundSource::new(&source)?;bound.validate()?;
    let started=Instant::now();
    let(bytes,claim)={
        let consumer=historical47_consumer(&admitted)?;
        let(context,_)=ProofContext::historical_h12(&consumer,&admitted)?;
        candidate(&context,&source,&admitted)?
    }; // Drop the producer's graph before creating the independent consumer.
    let output=path_env("NIPOPOW_C589_ROLE0_OUT")?;
    let mut file=OpenOptions::new().write(true).create_new(true).open(&output).map_err(|e|e.to_string())?;
    file.write_all(&bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;drop(file);
    let sha=crate::native_prefix_auth_plan::role0_sha256(&bytes)?;
    let expected=sha.iter().map(|b|format!("{b:02X}")).collect::<String>();
    let exported=held(&output,7264,&expected)?;
    let derived={
        let consumer=historical47_consumer(&admitted)?;
        let(context,_)=ProofContext::historical_h12(&consumer,&admitted)?;
        let verified=context.verify_role(&RoleProof {role:0,bytes:exported.bytes.clone()},
            &admitted.key,&admitted.commitment).map_err(|e|format!("C589 independent role consumer: {e:?}"))?;
        verified.claim
    };
    if derived.point!=claim.point || derived.value!=claim.value {return Err("C589 independently derived claim mismatch".into());}
    bound.validate()?;
    let same=exported.bytes==retained.bytes;
    println!("C589_ROLE0_CANDIDATE_EXPORTED bytes=7264 sha256={expected} independent_gkr=true retained_byte_equal={same} common_opening_reusable={same} pcs_generated=false elapsed_us={} native_verified_token=false",started.elapsed().as_micros());
    if !same {return Err("C589 different role proof requires a new common PCS opening".into());}
    Ok(())
}

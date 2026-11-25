//! Detached production and public verification on the original N0 X, key and commitment.
use super::*;
use ark_serialize::CanonicalSerialize;

#[derive(Clone,Copy)]
pub(crate) struct Spec {
    role:H21CandidateRole,proof_var:&'static str,sha_var:&'static str,commitment_var:&'static str,
    output_var:&'static str,file:&'static str,lock:&'static str,admit_phase:&'static str,prove_phase:&'static str,
    produced:&'static str,accepted:&'static str,imported:&'static str,
}
pub(crate) const POINT:Spec=Spec{role:H21CandidateRole::Point,proof_var:"NIPOPOW_V2_POINT3_PROOF",
    sha_var:"NIPOPOW_V2_POINT3_SHA256",commitment_var:"NIPOPOW_V2_POINT3_COMMITMENT",
    output_var:"NIPOPOW_V2_POINT3_OUTPUT_DIR",file:"point-3.gkr",lock:"point-writer.lock",
    admit_phase:"detached-point-admit-witness",prove_phase:"detached-point-gkr",
    produced:"N0_POINT3_PRODUCED",accepted:"N0_POINT3_VERIFIED",imported:"N0_POINT3_IMPORTED"};
pub(crate) const METADATA:Spec=Spec{role:H21CandidateRole::Metadata,proof_var:"NIPOPOW_V2_META6_PROOF",
    sha_var:"NIPOPOW_V2_META6_SHA256",commitment_var:"NIPOPOW_V2_META6_COMMITMENT",
    output_var:"NIPOPOW_V2_META6_OUTPUT_DIR",file:"role-6-era.gkr",lock:"metadata-writer.lock",
    admit_phase:"detached-metadata-admit-witness",prove_phase:"detached-metadata-gkr",
    produced:"N0_META6_PRODUCED",accepted:"N0_META6_VERIFIED",imported:"N0_META6_IMPORTED"};
pub(crate) const TREE: Spec = Spec {
    role: H21CandidateRole::Tree, proof_var: "NIPOPOW_V2_TREE2_PROOF", sha_var: "NIPOPOW_V2_TREE2_SHA256",
    commitment_var: "NIPOPOW_V2_TREE2_COMMITMENT", output_var: "NIPOPOW_V2_TREE2_OUTPUT_DIR",
    file: "role-2.gkr", lock: "tree-writer.lock", admit_phase: "detached-tree-admit-witness",
    prove_phase: "detached-tree-gkr", produced: "N0_TREE2_PRODUCED", accepted: "N0_TREE2_VERIFIED", imported: "N0_TREE2_IMPORTED",
};
pub(crate) const HEIGHT_DAA: Spec = Spec {
    role: H21CandidateRole::HeightDaa, proof_var: "NIPOPOW_V2_DAA4_PROOF", sha_var: "NIPOPOW_V2_DAA4_SHA256",
    commitment_var: "NIPOPOW_V2_DAA4_COMMITMENT", output_var: "NIPOPOW_V2_DAA4_OUTPUT_DIR",
    file: "role-4.gkr", lock: "height-daa-writer.lock", admit_phase: "detached-height-daa-admit-witness",
    prove_phase: "detached-height-daa-gkr", produced: "N0_DAA4_PRODUCED", accepted: "N0_DAA4_VERIFIED", imported: "N0_DAA4_IMPORTED",
};

const KEY:&[u8]=include_bytes!("../fixtures/verifier-keys-v1/log41.vk");
const PUBLIC_ID:&str="cc066f5b3d742ddf9d4d20f228eeba7535d0a5ed39079ba6e119c88178860b90";
const KEY_SHA:&str="edf4b5c518f2701c9b11aaaadb454ae8ef31616ba9d1c0a4476bd755ffc29bd0";
const COMMITMENT_SHA:&str="e6fe4e4ec2337a2261d19b70aace5b3b225537a5fe4bd592117db989fcf99a59";
const WITNESS:[u8;64]=[
    0xde,0x20,0x57,0xb4,0x54,0x9f,0x24,0x01,0x60,0xe8,0x11,0xb7,0xcf,0x09,0xc2,0x2e,
    0x87,0x5b,0x03,0x91,0x6d,0x62,0x76,0xb0,0xde,0x59,0x98,0xda,0xbc,0xf5,0xf8,0xf4,
    0x64,0x4c,0x79,0x24,0xc0,0x24,0x5d,0x62,0x1b,0xb5,0x0f,0xb1,0x6a,0xc4,0x5e,0x97,
    0x3a,0x3a,0x69,0xb0,0xae,0x5e,0xd6,0x4e,0x52,0x51,0xc0,0x5a,0x5d,0x06,0x82,0xac,
];

fn sha(bytes:&[u8])->Result<String,String>{
    Ok(crate::native_prefix_auth_plan::role0_sha256(bytes)?.iter().map(|b|format!("{b:02x}")).collect())
}
fn external(name:&str)->Result<PathBuf,String>{
    let path=PathBuf::from(std::env::var_os(name).ok_or_else(||format!("missing {name}"))?);
    if !crate::preview_test_paths::absolute_outside_source(&path){return Err(format!("invalid {name}"));}
    Ok(path)
}
pub(super) fn requested(spec:Spec)->bool{
    std::env::var_os(spec.proof_var).is_some() || std::env::var_os(spec.sha_var).is_some()
}
fn proof_input(spec:Spec)->Result<Vec<u8>,String>{
    let path=external(spec.proof_var)?;
    let pin=std::env::var(spec.sha_var).map_err(|_|"missing detached proof SHA256")?;
    if pin.len()!=64 || !pin.bytes().all(|c|c.is_ascii_hexdigit()){return Err("invalid detached proof SHA256".into());}
    let bytes=read_held(&path,codec::GKR_BYTES[spec.role.index()])?;
    if !pin.eq_ignore_ascii_case(&sha(&bytes)?){return Err("detached proof digest mismatch".into());}
    Ok(bytes)
}
fn origin(context:&H21StructuralDiagnosticContext<'_>,key_bytes:&[u8],c:&[u8])->Result<(),String>{
    if crate::h21_snapshot::N!=1_819_648 || format!("{:x}",Blake2b::<U32>::digest(context.public_bytes))!=PUBLIC_ID
        || sha(key_bytes)?!=KEY_SHA || c.len()!=codec::COMMITMENT_BYTES || sha(c)?!=COMMITMENT_SHA
        || pcs::encode_commitment(&pcs::decode_commitment(c)?)?!=c {
        return Err("different historical N0 detached public input, key or commitment".into());
    }
    Ok(())
}
fn verified(spec:Spec,context:&H21StructuralDiagnosticContext<'_>,key:&verifier_key::AdmittedVerifierKey,
    c:&[u8],bytes:&[u8])->Result<Claim,String>{
    let role=spec.role.index();
    if bytes.len()!=codec::GKR_BYTES[role] {return Err("detached GKR extent".into());}
    let proof=gkr::decode_dimensions(&[codec::INPUT_BITS[role] as usize],bytes)?;
    if gkr::encode_proof(&proof)?!=bytes{return Err("noncanonical detached GKR".into());}
    let claim=verify_h21_role(context,key,c,role,&proof)?;
    if claim.point.len()!=41{return Err("wrong detached common claim".into());}
    Ok(claim)
}
fn claim_bytes(claim:&Claim)->Result<Vec<u8>,String>{
    let mut raw=Vec::with_capacity(42*32);
    for value in claim.point.iter().chain(std::iter::once(&claim.value)){
        value.serialize_compressed(&mut raw).map_err(|e|e.to_string())?;
    }
    if raw.len()!=42*32{return Err("detached common claim encoding length".into());}
    Ok(raw)
}
fn report(spec:Spec,label:&str,bytes:&[u8],claim:&Claim)->Result<(),String>{
    let raw=claim_bytes(claim)?;
    let role=spec.role.index();
    println!("{label} {}",serde_json::json!({"snapshot":"N0","role":role,"raw_input_bits":codec::INPUT_BITS[role],
        "common_input_bits":claim.point.len(),"proof_bytes":bytes.len(),"proof_sha256":sha(bytes)?,
        "claim_le_hex":raw.iter().map(|b|format!("{b:02x}")).collect::<String>(),"claim_sha256":sha(&raw)?,
        "public_identity_blake2b256":PUBLIC_ID,"key_sha256":KEY_SHA,"commitment_sha256":COMMITMENT_SHA}));
    Ok(())
}

/// Called at the requested ordinal only when it is missing from the contiguous stage.
/// Preverify before publishing; the ordinary stage reader verifies its own
/// immutable readback again and supplies the claim to the common opening.
pub(super) fn import(spec:Spec,context:&H21StructuralDiagnosticContext<'_>,key:&verifier_key::AdmittedVerifierKey,
    key_bytes:&[u8],c:&[u8],actual_witness:&[u8;64])->Result<(Vec<u8>,InputClaim),String>{
    origin(context,key_bytes,c)?;
    if actual_witness!=&WITNESS{return Err("detached import requires the original N0 witness".into());}
    let bytes=proof_input(spec)?;
    let claim=verified(spec,context,key,c,&bytes)?;
    report(spec,spec.imported,&bytes,&claim)?;
    Ok((bytes,InputClaim{point:claim.point,value:claim.value}))
}

/// The host constructs the inbox from locally held public inputs and one external proof.
pub(super) fn community_at_ordinal(
    spec: Spec, x: &[u8], context: &H21StructuralDiagnosticContext<'_>,
    key: &verifier_key::AdmittedVerifierKey, key_bytes: &[u8], c: &[u8],
    source: &packed::UntrustedH21CandidateFile, budget: sparse_stream_roster::H21Role1Budget,
) -> Result<Option<(Vec<u8>, InputClaim)>, String> {
    origin(context, key_bytes, c)?;
    if source.actual_blake2b512() != &WITNESS {
        return Err("different community role witness".into());
    }
    let packet = read_community_packet(spec, x, c)
        .and_then(|bytes| verified(spec, context, key, c, &bytes).map(|claim| (bytes, claim)));
    let (bytes, claim) = match packet {
        Ok(offer) => offer,
        Err(_) => {
            println!("N0_COMMUNITY_DECLINED role={} reason=packet", spec.role.index());
            return Ok(None);
        }
    };

    // PackedFile::evaluate(log41) uses 2^20 row weights, 2^21 column weights,
    // 2^21 output fields and a bounded 32 MiB read buffer.
    let available = budget.limit_bytes.checked_sub(budget.caller_context_bytes)
        .and_then(|v| v.checked_sub(budget.visitor_scratch_bytes))
        .and_then(|v| v.checked_sub(budget.unmeasured_bytes))
        .ok_or("community role evaluation budget underflow")?;
    if available < (512usize << 20) {
        return Err("insufficient community role evaluation budget".into());
    }
    if !matches_local_claim(source.untrusted_polynomial(), &claim)? {
        println!("N0_COMMUNITY_DECLINED role={} reason=witness", spec.role.index());
        return Ok(None);
    }
    report(spec, spec.imported, &bytes, &claim)?;
    Ok(Some((bytes, InputClaim { point: claim.point, value: claim.value })))
}

fn matches_local_claim(source: &packed::PackedFile, claim: &Claim) -> Result<bool, String> {
    Ok(source.evaluate(&claim.point)? == claim.value)
}

fn read_community_packet(spec: Spec, x: &[u8], c: &[u8]) -> Result<Vec<u8>, String> {
    let path = external(spec.proof_var)?;
    if path.file_name() != Some(std::ffi::OsStr::new(spec.file)) {
        return Err("different community role filename".into());
    }
    let dir = path.parent().ok_or("missing community inbox")?;
    packed::check_stage_directory(dir)?;
    let mut names = Vec::new();
    for item in fs::read_dir(dir).map_err(|e| e.to_string())?.take(4) {
        names.push(item.map_err(|e| e.to_string())?.file_name());
    }
    if names.len() != 3 || ![spec.file, "statement.bin", "commitment.bin"].iter()
        .all(|name| names.iter().any(|n| n == std::ffi::OsStr::new(name))) {
        return Err("unexpected community packet inventory".into());
    }
    if read_held(&dir.join("statement.bin"), x.len())? != x ||
       read_held(&dir.join("commitment.bin"), c.len())? != c {
        return Err("different community role public inputs".into());
    }
    proof_input(spec)
}

#[test]
#[cfg(windows)]
fn community_claim_is_checked_on_the_local_packed_witness() -> Result<(),String> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let tmp = std::env::temp_dir().join(format!("nipopow-community-{}-{nonce}.bits", std::process::id()));
    if !crate::preview_test_paths::absolute_outside_source(&tmp) { return Err("test temp path".into()); }
    let mut writer = crate::packed::PackedFileWriter::create_new(&tmp, 3)?;
    writer.write_bytes(&[0b0100_0000])?;
    let source = writer.finish()?;
    // Only vertex 6 is one, so the MLE equals (1-x0)*x1*x2 even off the Boolean cube.
    let a = Fr::from(3u64);
    let b = Fr::from(5u64);
    let c = Fr::from(11u64);
    let mut claim = Claim { point: vec![a, b, c], value: (Fr::one() - a) * b * c };
    assert!(matches_local_claim(&source, &claim)?);
    claim.value += Fr::one();
    assert!(!matches_local_claim(&source, &claim)?);
    claim.point.pop();
    assert!(matches_local_claim(&source, &claim).is_err());
    drop(source);
    fs::remove_file(tmp).map_err(|e| e.to_string())?;
    Ok(())
}

const OFFER_DIR:&str="NIPOPOW_V2_META6_OFFER_DIR";

fn offer_digest(raw:&[u8])->String{raw.iter().map(|b|format!("{b:02x}")).collect()}

/// One optional lookup after a verified 0..5 prefix. The host publishes a
/// complete directory via atomic no-replace rename. Only the public native
/// GKR verifier can supply a claim to stage six, even for an approved offer.
pub(super) fn metadata_at_ordinal(context:&H21StructuralDiagnosticContext<'_>,key:&verifier_key::AdmittedVerifierKey,
    key_bytes:&[u8],c:&[u8],witness:&[u8;64])->Result<Option<(Vec<u8>,InputClaim)>,String>{
    if requested(METADATA){
        if std::env::var_os(OFFER_DIR).is_some(){return Err("ambiguous detached metadata inputs".into());}
        return import(METADATA,context,key,key_bytes,c,witness).map(Some);
    }
    if std::env::var_os(OFFER_DIR).is_none(){return Ok(None);}
    let directory=external(OFFER_DIR)?;
    match fs::symlink_metadata(&directory){
        Err(e) if e.kind()==std::io::ErrorKind::NotFound=>return Ok(None),
        Err(e)=>return Err(format!("metadata offer directory: {e}")),
        Ok(_)=>(),
    }
    packed::check_stage_directory(&directory)?;
    let mut entries=Vec::new();
    for item in fs::read_dir(&directory).map_err(|e|e.to_string())?.take(3){
        entries.push(item.map_err(|e|e.to_string())?.file_name());
    }
    let decline=|reason:&str|{
        println!("N0_META6_OFFER_DECLINED {reason}");
        Ok(None)
    };
    if entries.len()!=2 || !["offer.bin",METADATA.file].iter().all(|name|
            entries.iter().any(|e|e==std::ffi::OsStr::new(name))){
        return decline("inventory");
    }
    let offer=directory.join("offer.bin");
    let proof=directory.join(METADATA.file);
    for (path,size) in [(&offer,104u64),(&proof,codec::GKR_BYTES[6] as u64)]{
        let info=fs::symlink_metadata(path).map_err(|e|format!("metadata offer entry: {e}"))?;
        if !info.file_type().is_file() || info.len()!=size{return decline("file type or extent");}
    }
    let header=read_held(&offer,104)?;
    if &header[..8]!=b"NPM6OF01"{return decline("format");}
    let acceptance_sha256=offer_digest(&header[8..40]);
    let bytes=read_held(&proof,codec::GKR_BYTES[6])?;
    let proof_sha256=sha(&bytes)?;
    if proof_sha256!=offer_digest(&header[40..72]){return decline("proof hash");}
    origin(context,key_bytes,c)?;
    if witness!=&WITNESS{return Err("metadata offer requires the original N0 witness".into());}
    let claim=match verified(METADATA,context,key,c,&bytes){Ok(claim)=>claim,Err(_)=>return decline("GKR")};
    let claim_sha256=sha(&claim_bytes(&claim)?)?;
    if claim_sha256!=offer_digest(&header[72..104]){return decline("claim hash");}
    report(METADATA,METADATA.imported,&bytes,&claim)?;
    println!("N0_META6_OFFER_USED {}",serde_json::json!({ "acceptance_sha256":acceptance_sha256,
        "proof_sha256":proof_sha256,"claim_sha256":claim_sha256 }));
    Ok(Some((bytes,InputClaim{point:claim.point,value:claim.value})))
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
pub(crate) fn verify_public(spec:Spec,owned:&H21StructuralDiagnostic)->Result<(),String>{
    let context=owned.context()?;
    let c=read_held(&external(spec.commitment_var)?,codec::COMMITMENT_BYTES)?;
    origin(&context,KEY,&c)?;
    let key=verifier_key::admit(41,KEY)?;
    let bytes=proof_input(spec)?;
    report(spec,spec.accepted,&bytes,&verified(spec,&context,&key,&c,&bytes)?)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
pub(crate) fn standalone_budget(spec:Spec)->Result<sparse_stream_roster::H21Role1Budget,String>{
    let field=|name|std::env::var(name).map_err(|_|format!("missing {name}"))?
        .parse::<usize>().map_err(|_|format!("invalid {name}"));
    let workers=field("RAYON_NUM_THREADS")?;
    if !(1..=2).contains(&workers) || (spec.role==H21CandidateRole::Metadata && workers!=2) || rayon::current_num_threads()!=workers
        || std::env::var("RUST_TEST_THREADS").as_deref()!=Ok("1") {
        return Err("wrong detached workers or libtest concurrency".into());
    }
    let budget=sparse_stream_roster::H21Role1Budget{limit_bytes:field("NIPOPOW_H21_ROLE_BUDGET_BYTES")?,
        caller_context_bytes:field("NIPOPOW_H21_CONTEXT_BYTES")?,visitor_scratch_bytes:field("NIPOPOW_H21_VISITOR_BYTES")?,
        unmeasured_bytes:field("NIPOPOW_H21_RESERVE_BYTES")?};
    if spec.role==H21CandidateRole::Metadata && budget.limit_bytes>15usize<<30 {
        return Err("detached metadata role budget exceeds 15 GiB".into());
    }
    // Retain the actual historical prover's context, visitor and unmeasured
    // allowances in addition to the worst-case 8.5 GiB POINT workspace.
    if budget.caller_context_bytes<(3usize<<30) || budget.visitor_scratch_bytes<(512usize<<20)
        || budget.unmeasured_bytes<(2usize<<30) {return Err("insufficient detached reservations".into());}
    if spec.role==H21CandidateRole::Point{h21_candidate_roles::h21_point_scratch(budget)?;}
    Ok(budget)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
pub(crate) fn produce(spec:Spec,owned:&H21StructuralDiagnostic,budget:sparse_stream_roster::H21Role1Budget)->Result<(),String>{
    let context=owned.context()?;
    if spec.role==H21CandidateRole::Point{h21_candidate_roles::h21_point_scratch(budget)?;}
    else if spec.role==H21CandidateRole::Metadata{sparse_stream_roster::require_detached_metadata_lanes(&context.candidate_role_shape(spec.role)?,budget)?;}
    let c=read_held(&external(spec.commitment_var)?,codec::COMMITMENT_BYTES)?;
    origin(&context,KEY,&c)?;
    let key=verifier_key::admit(41,KEY)?;
    let witness=external("NIPOPOW_H21_WITNESS")?;
    let out=external(spec.output_var)?;
    packed::check_stage_directory(&out)?;
    let out=fs::canonicalize(out).map_err(|e|e.to_string())?;
    let original=fs::canonicalize(witness.parent().ok_or("missing original N0 directory")?).map_err(|e|e.to_string())?;
    if out.starts_with(&original) || original.starts_with(&out)
        || out.components().any(|part|part.as_os_str().to_string_lossy().eq_ignore_ascii_case("role-checkpoints"))
        || fs::read_dir(&out).map_err(|e|e.to_string())?.next().is_some(){
        return Err("detached output must be an empty separate directory".into());
    }
    let _lock=packed::lock_stage_file(&out.join(spec.lock),true)?;
    // Admission hashes the full held file once. Each role then uses its
    // original prover on that same source.
    let source=phase(spec.admit_phase,||owned.open_untrusted_candidate(&witness,Some(WITNESS)))?;
    let (bytes,produced)=phase(spec.prove_phase,||context.prove_remaining_untrusted_candidate(
        spec.role,KEY,&c,&source,budget))?;
    let claim=verified(spec,&context,&key,&c,&bytes)?;
    if produced.point!=claim.point || produced.value!=claim.value{return Err("different produced and verified detached claim".into());}
    let temporary=out.join(format!("{}.partial",spec.file));
    let target=out.join(spec.file);
    drop(packed::create_blob(&temporary,&bytes)?);
    packed::publish_noreplace(&temporary,&target)?;
    let _sealed=packed::checked_blob(&target,&bytes)?;
    report(spec,spec.produced,&bytes,&claim)
}

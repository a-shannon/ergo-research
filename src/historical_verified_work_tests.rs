//! Real Historical51 packet -> opaque prefix -> three native membership paths.
//! Producer alone reads NP37. The fresh receiver reads public proof and paths.
use super::*;
use crate::{native_work_opening::{NativeWorkMembershipContext, NativeWorkOpening, MAX_OPENING_BYTES},
    packed_owner_assembly::NativePrefix, work_tree_wiring::Descriptor};
use std::{fs::{self, File, OpenOptions}, io::{Read, Write}, path::{Path, PathBuf}};

const HEIGHTS: [usize; 3] = [1024, 2048, 3072];
const PUBLIC_NAMES: [&str; 10] = ["statement.bin", "commitment.bin", "role-0.gkr", "role-1.gkr",
    "role-2.gkr", "role-3.gkr", "role-4.gkr", "role-5.gkr", "role-6.gkr", "common-opening.bin"];
const PREFIX_ENV: &str = "NIPOPOW_C584_PREFIX_PATH";

fn path_env(name: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(std::env::var_os(name).ok_or_else(|| format!("missing {name}"))?);
    if !path.is_absolute() { return Err(format!("{name} must be absolute")); }
    Ok(path)
}
fn read_bounded(path: &Path, cap: usize) -> Result<Vec<u8>, String> {
    let file = File::open(path).map_err(|error| format!("bounded input open: {error}"))?;
    let len = usize::try_from(file.metadata().map_err(|_| "input metadata")?.len())
        .map_err(|_| "input length conversion")?;
    if len == 0 || len > cap { return Err("bounded input extent".into()); }
    let mut bytes = Vec::with_capacity(len);
    file.take(cap as u64 + 1).read_to_end(&mut bytes).map_err(|_| "bounded input read")?;
    if bytes.len() != len { return Err("bounded input changed extent".into()); }
    Ok(bytes)
}
fn write_new(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut out = OpenOptions::new().write(true).create_new(true).open(path)
        .map_err(|error| format!("create-only opening: {error}"))?;
    out.write_all(bytes).map_err(|_| "opening write")?;
    out.sync_all().map_err(|_| "opening flush".into())
}

struct PublicPackage { files: [Vec<u8>; 10], key: Vec<u8>, metadata: Vec<u8> }
impl PublicPackage {
    fn read() -> Result<Self, String> {
        let dir = path_env("NIPOPOW_COMMON51_PUBLIC_DIR")?;
        let mut names = fs::read_dir(&dir).map_err(|_| "public package directory")?
            .map(|entry| entry.map_err(|_| "public package entry".to_string())?
                .file_name().into_string().map_err(|_| "public package name".to_string()))
            .collect::<Result<Vec<_>, _>>()?;
        names.sort();
        let mut expected = PUBLIC_NAMES.map(str::to_string).to_vec(); expected.sort();
        if names != expected { return Err("exact ten-file public package required".into()); }
        let mut files: [Vec<u8>; 10] = std::array::from_fn(|_| Vec::new());
        for (index, name) in PUBLIC_NAMES.iter().enumerate() {
            let cap = match index { 0 => 571, 1 => 384, 5 => 5696, 2..=8 => 7264,
                _ => HISTORICAL51_COMMON_BOUND };
            files[index] = read_bounded(&dir.join(name), cap)?;
        }
        let key = read_bounded(&path_env("NIPOPOW_COMMON51_KEY_PATH")?, 33264)?;
        let metadata = read_bounded(&path_env("NIPOPOW_COMMON51_KEY_METADATA_PATH")?, 40)?;
        Ok(Self { files, key, metadata })
    }
    fn bytes(&self) -> Historical51PublicBytes<'_> {
        Historical51PublicBytes { frame: &self.files[0], commitment: &self.files[1],
            roles: std::array::from_fn(|role| self.files[role + 2].as_slice()), common: &self.files[9] }
    }
    fn seal(&self) -> Result<VerifiedHistorical51Prefix, String> {
        let mut diagnostic = Historical51Diagnostics::default();
        let verified = verify_and_seal_historical_h12_prefix51(&self.bytes(), &self.key, &self.metadata,
            &Historical51TrustedKeyPolicy::fixed32_testonly(), &mut diagnostic)?;
        if diagnostic.role_completions != [1; 7] || diagnostic.pcs_completions != 1
            || diagnostic.successes != 1 { return Err("sealed prefix requires seven roles and PCS".into()); }
        Ok(verified)
    }
}

fn decode_np37(bytes: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    if bytes.len() > 2 * 1024 * 1024 || bytes.get(..4) != Some(b"NP37") {
        return Err("NP37 magic/extent".into());
    }
    let mut at = 4usize;
    fn word(bytes: &[u8], at: &mut usize) -> Result<usize, String> {
        let end = at.checked_add(4).ok_or("NP37 offset overflow")?;
        let value = bytes.get(*at..end).ok_or("NP37 truncated word")?;
        *at = end;
        Ok(u32::from_be_bytes(value.try_into().map_err(|_| "NP37 word")?) as usize)
    }
    if word(bytes, &mut at)? != 3073 { return Err("NP37 exact prefix count".into()); }
    let mut raws = Vec::with_capacity(3073);
    for _ in 0..3073 {
        let len = word(bytes, &mut at)?;
        if !(1..=514).contains(&len) { return Err("NP37 header extent".into()); }
        let end = at.checked_add(len).ok_or("NP37 RAW overflow")?;
        raws.push(bytes.get(at..end).ok_or("NP37 truncated RAW")?.to_vec()); at = end;
    }
    if at != bytes.len() { return Err("NP37 trailing bytes".into()); }
    Ok(raws)
}

fn make_opening(prefix: &NativePrefix, verified: &VerifiedHistorical51Prefix, height: usize)
    -> Result<([u8; 28], Vec<u8>), String> {
    let descriptor = Descriptor::new(verified.headers(), verified.root())?;
    let context = NativeWorkMembershipContext::new(verified.headers(), verified.root(), verified.total_be28())
        .map_err(|error| error.to_string())?;
    let position = height.checked_sub(2).ok_or("opening height before work leaves")?;
    let (lower, upper) = prefix.interval(height)?;
    let mut siblings = Vec::with_capacity(descriptor.leaves.trailing_zeros() as usize);
    for level in 1..=descriptor.leaves.trailing_zeros() as usize {
        let sibling_position = (position >> (level - 1)) ^ 1;
        siblings.push(if level == 1 { prefix.leaf_digest(sibling_position)? } else {
            let (base, count) = descriptor.level(level - 1)?;
            if sibling_position >= count { return Err("opening sibling outside level".into()); }
            prefix.node_digest(base + sibling_position)?
        });
    }
    let opening = NativeWorkOpening::new(position as u32, lower, upper, prefix.raw(height)?.to_vec(), siblings);
    let encoded = opening.encode(&context).map_err(|error| error.to_string())?;
    let member = verified.verify_work_opening(lower, &encoded).map_err(|error| error.to_string())?;
    if member.member().height() != height as u32 || member.history().binding_id() != verified.binding_id() {
        return Err("producer history-bound member mismatch".into());
    }
    Ok((lower, encoded))
}

fn coordinate(bytes: &[u8]) -> Result<[u8; 28], String> {
    // The test chooses the leaf's encoded lower endpoint as its public audit
    // coordinate. The sealed verifier subsequently checks the complete codec,
    // path, height, interval, native work and certified root.
    if bytes.len() > MAX_OPENING_BYTES { return Err("opening extent".into()); }
    bytes.get(12..40).ok_or("opening lower endpoint")?.try_into().map_err(|_| "opening coordinate".into())
}

fn reject_public_fault(package: &PublicPackage, frame: &[u8], commitment: &[u8], common: &[u8]) -> Result<(), String> {
    let original = package.bytes();
    let bytes = Historical51PublicBytes { frame, commitment, roles: original.roles, common };
    let mut diagnostic = Historical51Diagnostics::default();
    if verify_and_seal_historical_h12_prefix51(&bytes, &package.key, &package.metadata,
        &Historical51TrustedKeyPolicy::fixed32_testonly(), &mut diagnostic).is_ok()
        || diagnostic.successes != 0 { return Err("invalid proof minted a verified prefix".into()); }
    Ok(())
}

#[test]
fn c584_failed_envelope_cannot_mint_verified_prefix() {
    let bytes = Historical51PublicBytes { frame: &[], commitment: &[], roles: [&[]; 7], common: &[] };
    let mut diagnostic = Historical51Diagnostics::default();
    assert!(verify_and_seal_historical_h12_prefix51(&bytes, &[], &[],
        &Historical51TrustedKeyPolicy::fixed32_testonly(), &mut diagnostic).is_err());
    assert_eq!(diagnostic.successes, 0);
}

#[test]
fn c584_np37_codec_refuses_wrong_count_truncation_and_trailing_data() {
    assert!(decode_np37(b"NP37").is_err());
    let mut wrong = b"NP37".to_vec(); wrong.extend(3072u32.to_be_bytes());
    assert!(decode_np37(&wrong).unwrap_err().contains("count"));
    let mut truncated = b"NP37".to_vec(); truncated.extend(3073u32.to_be_bytes());
    truncated.extend(515u32.to_be_bytes());
    assert!(decode_np37(&truncated).unwrap_err().contains("extent"));
    let mut codec_only = b"NP37".to_vec(); codec_only.extend(3073u32.to_be_bytes());
    for _ in 0..3073 { codec_only.extend(1u32.to_be_bytes()); codec_only.push(1); }
    assert_eq!(decode_np37(&codec_only).unwrap().len(), 3073);
    codec_only.push(0);
    assert!(decode_np37(&codec_only).unwrap_err().contains("trailing"));
}

#[test]
#[ignore = "requires verified Historical51 public packet, key, NP37 prefix and fresh output directory"]
fn c584_verified_history_opening_producer() -> Result<(), String> {
    let package = PublicPackage::read()?;
    let verified = package.seal()?;
    let prefix_bytes = read_bounded(&path_env(PREFIX_ENV)?, 2 * 1024 * 1024)?;
    let raws = decode_np37(&prefix_bytes)?;
    let prefix = NativePrefix::from_raw_headers(&raws)?;
    let tip = ergo_header_core::blake2b256(prefix.raw(3073)?);
    if verified.headers() != 3073 || prefix.root() != verified.root()
        || prefix.total_be28() != verified.total_be28() || tip != verified.tip()
        || verified.genesis() != crate::header_order::MAINNET_GENESIS {
        return Err("NP37 native prefix differs from verified history".into());
    }
    let mut outputs = Vec::with_capacity(3);
    for height in HEIGHTS {
        let (_, encoded) = make_opening(&prefix, &verified, height)?;
        outputs.push((format!("work-{height}.bin"), encoded));
    }
    let output_dir = path_env("NIPOPOW_C584_OUTPUT_DIR")?;
    if output_dir.exists() { return Err("opening output directory must be fresh".into()); }
    fs::create_dir(&output_dir).map_err(|_| "opening output directory create")?;
    for (name, bytes) in &outputs { write_new(&output_dir.join(name), bytes)?; }
    println!("C584_HISTORY_BOUND_OPENINGS {}", serde_json::json!({"mode":"producer", "headers":verified.headers(),
        "heights":HEIGHTS, "opening_bytes":outputs.iter().map(|(_, bytes)| bytes.len()).collect::<Vec<_>>(),
        "binding_id":verified.binding_id(), "genesis":verified.genesis(), "raw_prefix_matches":true}));
    Ok(())
}

#[test]
#[ignore = "fresh receiver requires only Historical51 public packet, key and the three work opening files"]
fn c584_verified_history_opening_cold_consumer() -> Result<(), String> {
    if std::env::var_os(PREFIX_ENV).is_some() { return Err("cold receiver must not receive a RAW prefix path".into()); }
    let package = PublicPackage::read()?;
    let verified = package.seal()?;
    let input_dir = path_env("NIPOPOW_C584_OPENING_DIR")?;
    let mut names = fs::read_dir(&input_dir).map_err(|_| "opening input directory")?
        .map(|entry| entry.map_err(|_| "opening entry".to_string())?.file_name()
            .into_string().map_err(|_| "opening name".to_string())).collect::<Result<Vec<_>, _>>()?;
    names.sort();
    let mut expected = HEIGHTS.map(|height| format!("work-{height}.bin")).to_vec(); expected.sort();
    if names != expected { return Err("exact three-opening roster required".into()); }
    for height in HEIGHTS {
        let bytes = read_bounded(&input_dir.join(format!("work-{height}.bin")), MAX_OPENING_BYTES)?;
        let lower = coordinate(&bytes)?;
        let bound = verified.verify_work_opening(lower, &bytes).map_err(|error| error.to_string())?;
        if bound.member().height() != height as u32 || bound.member().root() != verified.root()
            || bound.member().headers() != verified.headers()
            || bound.member().total_be28() != verified.total_be28()
            || bound.member().profile() != verified.work_profile()
            || !std::ptr::eq(bound.history(), &verified) { return Err("cold history/member identity mismatch".into()); }
        let mut raw_fault = bytes.clone(); raw_fault[70] ^= 1;
        if verified.verify_work_opening(lower, &raw_fault).is_ok() { return Err("changed member RAW accepted".into()); }
        let mut sibling_fault = bytes.clone(); *sibling_fault.last_mut().ok_or("opening empty")? ^= 1;
        if verified.verify_work_opening(lower, &sibling_fault).is_ok() { return Err("changed sibling accepted".into()); }
        if verified.verify_work_opening(verified.total_be28(), &bytes).is_ok() {
            return Err("coordinate at certified total accepted".into());
        }
        let foreign = NativeWorkMembershipContext::new(verified.headers(), [0; 32], verified.total_be28())
            .map_err(|error| error.to_string())?;
        if foreign.verify_encoded(lower, &bytes).is_ok() { return Err("foreign caller root accepted opening".into()); }
    }
    for at in [43usize, 107, 139] {
        let mut frame = package.files[0].clone(); frame[at] ^= 1;
        reject_public_fault(&package, &frame, &package.files[1], &package.files[9])?;
    }
    let key = Historical51TrustedKeyPolicy::fixed32_testonly().admit_key(&package.bytes(), &package.key, &package.metadata)?;
    let zero = <dory_pcs::backends::arkworks::ArkGT as dory_pcs::primitives::arithmetic::Group>::identity();
    let original = pcs::decode_commitment(&package.files[1])?;
    let foreign_c = pcs::encode_commitment(&if original == zero { key.verifier().ht } else { zero })?;
    if foreign_c == package.files[1] { return Err("foreign commitment was not distinct".into()); }
    reject_public_fault(&package, &package.files[0], &foreign_c, &package.files[9])?;
    let mut failed_common = package.files[9].clone(); failed_common[0] ^= 1;
    reject_public_fault(&package, &package.files[0], &package.files[1], &failed_common)?;
    println!("C584_HISTORY_BOUND_OPENINGS {}", serde_json::json!({"mode":"cold-consumer", "headers":verified.headers(),
        "heights":HEIGHTS, "binding_id":verified.binding_id(), "verified_members":3,
        "opening_negatives":12, "failed_proof_no_seal":5, "raw_prefix_read":false,
        "scope":"historical51 diagnostic prefix plus authenticated work membership; no native PoW/freshness claim"}));
    Ok(())
}

#[test]
#[ignore = "fresh receiver requires Historical51 public proof, key and three authenticated v1 work openings"]
fn c585_history_bound_native_pow_cold_consumer() -> Result<(), String> {
    use crate::native_autolykos_pow::{self as native_pow, NativePowError};
    use ergo_header_core::PowSolution;
    use num_bigint::BigUint;

    if std::env::var_os(PREFIX_ENV).is_some() {
        return Err("PoW cold receiver must not receive a RAW prefix path".into());
    }
    let started = Instant::now();
    let package = PublicPackage::read()?;
    let verified = package.seal()?;
    let seal_ns = started.elapsed().as_nanos();
    let input_dir = path_env("NIPOPOW_C584_OPENING_DIR")?;
    let mut names = fs::read_dir(&input_dir).map_err(|_| "PoW opening directory")?
        .map(|entry| entry.map_err(|_| "PoW opening entry".to_string())?.file_name()
            .into_string().map_err(|_| "PoW opening name".to_string())).collect::<Result<Vec<_>, _>>()?;
    names.sort();
    let mut expected = HEIGHTS.map(|height| format!("work-{height}.bin")).to_vec(); expected.sort();
    if names != expected { return Err("PoW exact three-opening roster required".into()); }

    // Measure successful membership+native-PoW checks before any mutant work.
    let positive = Instant::now();
    let mut members = Vec::with_capacity(3);
    let mut positives = Vec::with_capacity(3);
    for height in HEIGHTS {
        let bytes = read_bounded(&input_dir.join(format!("work-{height}.bin")), MAX_OPENING_BYTES)?;
        let checked = Instant::now();
        let work = verified.verify_work_opening(coordinate(&bytes)?, &bytes)
            .map_err(|error| format!("authenticated PoW input: {error}"))?;
        if work.member().height() != height as u32 || work.member().header().version != 1 {
            return Err("unexpected Historical51 v1 opening".into());
        }
        let raw_id = ergo_header_core::blake2b256(work.member().raw());
        let raw = work.member().raw().to_vec();
        let pow = work.verify_native_pow().map_err(|error| format!("genuine opened native PoW: {error}"))?;
        if !std::ptr::eq(pow.history(), &verified) || pow.history().binding_id() != verified.binding_id()
            || pow.member().headers() != verified.headers() || pow.member().root() != verified.root()
            || pow.member().total_be28() != verified.total_be28()
            || pow.member().profile() != verified.work_profile()
            || pow.member().raw() != raw.as_slice()
            || pow.member().header().encode().map_err(|_| "checked PoW reencode")? != raw
            || ergo_header_core::blake2b256(pow.member().raw()) != raw_id {
            return Err("native PoW lost sealed history/member identity".into());
        }
        positives.push(serde_json::json!({"height":height, "membership_pow_ns":checked.elapsed().as_nanos(),
            "raw_id":raw_id}));
        members.push(pow);
    }
    let positive_ns = positive.elapsed().as_nanos();

    let negative = Instant::now();
    let mut nonce_negatives = 0;
    let mut distance_negatives = 0;
    let mut target_negatives = 0;
    for member in &members {
        let genuine = member.member().header();
        let PowSolution::V1 { distance, .. } = &genuine.pow else { return Err("expected v1 PoW solution".into()); };
        let d = BigUint::from_bytes_be(distance);
        let mut nonce = genuine.clone();
        if let PowSolution::V1 { nonce, .. } = &mut nonce.pow { nonce[7] ^= 1; }
        if native_pow::verify_header(&nonce) != Err(NativePowError::Equation) {
            return Err("authenticated header clone nonce fault was not an equation rejection".into());
        }
        nonce_negatives += 1;

        let mut changed_distance = genuine.clone();
        if let PowSolution::V1 { distance, .. } = &mut changed_distance.pow {
            *distance = (&d + BigUint::from(1u8)).to_bytes_be();
        }
        if native_pow::verify_header(&changed_distance) != Err(NativePowError::Equation) {
            return Err("authenticated header clone distance fault was not an equation rejection".into());
        }
        distance_negatives += 1;

        let mut target_equal = genuine.clone();
        let target = crate::daa_count::q() / crate::work_tree_work::native_decode(genuine.n_bits)?;
        if let PowSolution::V1 { distance, .. } = &mut target_equal.pow { *distance = target.to_bytes_be(); }
        if native_pow::verify_header(&target_equal) != Err(NativePowError::Target) {
            return Err("authenticated header clone strict target equality accepted".into());
        }
        target_negatives += 1;
    }
    println!("C585_HISTORY_BOUND_NATIVE_POW {}", serde_json::json!({
        "headers":verified.headers(), "heights":HEIGHTS, "binding_id":verified.binding_id(),
        "key_id":verified.key_id(), "genesis":verified.genesis(), "verified_members":members.len(),
        "seal_ns":seal_ns, "positive_membership_pow_ns":positive_ns, "positive_members":positives,
        "negative_ns":negative.elapsed().as_nanos(), "nonce_negatives":nonce_negatives,
        "distance_negatives":distance_negatives, "target_negatives":target_negatives,
        "raw_prefix_read":false,
        "scope":"fixed N3073 v1 history-bound openings plus native PoW; diagnostic key; no sampler, v2-history, freshness or complete V2 claim"}));
    Ok(())
}

#[test]
#[ignore="retained NP37/public proof and existing work1024 opening; fresh checkpoint packet output"]
fn c590_checkpoint_anchor_packet_producer()->Result<(),String> {
    use crate::historical_prefix_proof::checkpoint_anchor590::{VerifiedBase,diagnostic_profile};
    let package=PublicPackage::read()?;
    let base=VerifiedBase::verify(package.bytes(),&package.key,&package.metadata)?;
    let prefix_bytes=read_bounded(&path_env(PREFIX_ENV)?,2*1024*1024)?;
    if crate::native_prefix_auth_plan::role0_sha256(&prefix_bytes)?!=historical47_hex::<32>(
        "A577D3CDE3CB063B4C4945F95C67B07FCE500486ACBD36F77AA3D3F586CB022A")? {
        return Err("C590 retained NP37 bytes identity".into());
    }
    let prefix=NativePrefix::from_raw_headers(&decode_np37(&prefix_bytes)?)?;
    if prefix.header_count()!=base.history().headers()||prefix.root()!=base.history().root()
        ||prefix.total_be28()!=base.history().total_be28()
        ||ergo_header_core::blake2b256(prefix.raw(3073)?)!=base.history().tip() {
        return Err("C590 NP37 prefix differs from verified base".into());
    }
    let h=1024usize;let f=1087usize;
    let old_dir=path_env("NIPOPOW_C584_OPENING_DIR")?;
    let anchor_h=read_bounded(&old_dir.join("work-1024.bin"),MAX_OPENING_BYTES)?;
    let(_,anchor_f)=make_opening(&prefix,base.history(),f)?;
    let total=num_bigint::BigUint::from_bytes_be(&base.history().total_be28());
    let floor=num_bigint::BigUint::from_bytes_be(&prefix.interval(f)?.1);
    if floor>=total {return Err("C590 producer nonpositive audit work".into());}
    let magnitude=(total-floor).to_bytes_be();if magnitude.len()>28 {return Err("C590 work width".into());}
    let mut audit=[0u8;28];audit[28-magnitude.len()..].copy_from_slice(&magnitude);
    let verified=base.checkpoint(&diagnostic_profile(),h as u64,prefix.raw(h)?,audit,&anchor_h,&anchor_f)?;
    let packet=verified.encode()?;
    let output=path_env("NIPOPOW_C590_PACKET_OUT")?;
    if !crate::preview_test_paths::absolute_outside_source(&output) {return Err("C590 packet outside source".into());}
    write_new(&output,&packet)?;
    let sha=crate::native_prefix_auth_plan::role0_sha256(&packet)?;
    println!("C590_CHECKPOINT_PACKET_PRODUCER {}",serde_json::json!({"h":verified.h(),"f":verified.f(),
        "bytes":packet.len(),"sha256":sha,"raw_bytes":verified.header_raw().len(),
        "floor_work":verified.floor_work(),"audit_work":verified.audit_work(),
        "new_gkr":false,"new_pcs":false,"full_s":false,"work_maturity":false}));Ok(())
}

#[test]
#[ignore="fresh cold receiver reads only the unique checkpoint packet"]
fn c590_checkpoint_anchor_packet_cold_consumer()->Result<(),String> {
    use crate::historical_prefix_proof::checkpoint_anchor590::{verify_packet,native_negative_controls,
        validate_cold_environment_names,MAX_PACKET_BYTES};
    validate_cold_environment_names(std::env::vars_os().map(|(name,_)|name))?;
    let path=path_env("NIPOPOW_C590_PACKET_PATH")?;
    let packet=read_bounded(&path,MAX_PACKET_BYTES)?;
    let verified=verify_packet(&packet)?;
    if verified.h()!=1024||verified.f()!=1087||verified.encode()?!=packet {return Err("C590 cold packet/result mismatch".into());}
    let negatives=native_negative_controls(&verified)?;
    let sha=crate::native_prefix_auth_plan::role0_sha256(&verified.encode()?)?;
    println!("C590_CHECKPOINT_PACKET_COLD_PASS {}",serde_json::json!({"h":verified.h(),"f":verified.f(),
        "bytes":packet.len(),"sha256":sha,"raw_bytes":verified.header_raw().len(),
        "floor_work":verified.floor_work(),"audit_work":verified.audit_work(),"negatives":negatives,
        "binding_id":verified.history().binding_id(),"raw_prefix_read":false,"packet_only":true,
        "new_gkr":false,"new_pcs":false,"full_s":false,"work_maturity":false}));Ok(())
}

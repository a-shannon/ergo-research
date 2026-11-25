//! Bounded exact-RAW Legacy m=3/m=4 packet: one composite GKR and one PCS.
//! The caller owns the selected code profile, exact RAW roster, and admitted
//! diagnostic key. This relation proves neither history inclusion nor PoW.
use crate::{
    daa_short_legacy_join::{Plan, Profile, INPUT_LOG, LOCAL_LOG, ROW_LOCAL_LOG, ROW_LOG, SLOT_LOG, WIDTH},
    gkr::{self, InputClaim},
    packed::{self, PackedCommitted, PackedFile},
    pcs::{self, Setup},
    sparse_stream_roster,
    transcript::Transcript,
    verifier_key::AdmittedVerifierKey,
};
use ark_bn254::Fr;
use serde::{Deserialize, Serialize};

const FAMILY: &str = "legacy-short-m3-m4-exact-raw-one-gkr-one-pcs-v1";
const DOMAIN: &[u8] = b"nipopow-short-legacy-m3-m4-packet-v1";
const MAGIC: &[u8; 8] = b"SLGAAP01";
const VERSION: u8 = 1;
const EXPECTED_CAP: usize = 16_384;
const RAW_CAP: usize = 514;
const ARITH_INPUT_LEN: usize = 1 << 16;
const ARITH_ROWS: usize = 1 << 17;
const EXPECTED_ALIASES: [usize; 2] = [22_274, 26_588];
const EXPECTED_TOTAL_TERMS: [usize; 2] = [1_848_609, 2_199_506];
const EXPECTED_RAW_PIN_TERMS: [usize; 2] = [20_610, 24_732];
// The m2 packet and this family share the exact log20/log22 GKR and log20 PCS
// geometry. Codec lengths remain fixed; section tags and lengths are checked
// before any proof allocation.
const SECTION_BYTES: [usize; 3] = [4_576, 26_829, 32];
pub(crate) const PACKET_BYTES: usize = 8 + 1 + 3 * 5 + 4_576 + 26_829 + 32;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExpectedStatement {
    version: u8,
    family: String,
    profile: String,
    input_log: u8,
    row_log: u8,
    ratio_count: u8,
    serializer_count: u8,
    owner_count: u8,
    serializer_owners: Vec<u8>,
    arithmetic_owner: u8,
    adjacency_owner: u8,
    reserved_owners: Vec<u8>,
    sample_heights: Vec<u32>,
    arithmetic_input_len: u32,
    arithmetic_rows: u32,
    arithmetic_terms: u32,
    arithmetic_live_bits: u32,
    alias_count: u32,
    raw_pin_count: u32,
    total_terms: u64,
    descriptor_hex: String,
    setup_id: [u8; 32],
    commitment_hex: String,
    raw_headers_hex: Vec<String>,
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(text: &str) -> Result<Vec<u8>, String> {
    if text.len() % 2 != 0
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("noncanonical lowercase hex".into());
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

fn profile_index(profile: Profile) -> usize {
    profile.count() - 3
}

fn expected_owner_layout(profile: Profile) -> (Vec<u8>, u8, u8, Vec<u8>) {
    let serializers = (0..profile.serializer_count())
        .map(|owner| owner as u8)
        .collect();
    let arithmetic = profile.arithmetic_owner() as u8;
    let adjacency = profile.adjacency_owner() as u8;
    let reserved = if profile == Profile::M3 {
        vec![7]
    } else {
        Vec::new()
    };
    (serializers, arithmetic, adjacency, reserved)
}

impl ExpectedStatement {
    fn validate(&self) -> Result<Profile, String> {
        let profile = Profile::parse(&self.profile)?;
        let i = profile_index(profile);
        let (serializer_owners, arithmetic_owner, adjacency_owner, reserved_owners) =
            expected_owner_layout(profile);
        if self.version != VERSION
            || self.family != FAMILY
            || self.input_log as usize != INPUT_LOG
            || self.row_log as usize != ROW_LOG
            || self.ratio_count as usize != profile.count()
            || self.serializer_count as usize != profile.serializer_count()
            || self.owner_count as usize != profile.adjacency_owner() + 1
            || self.serializer_owners != serializer_owners
            || self.arithmetic_owner != arithmetic_owner
            || self.adjacency_owner != adjacency_owner
            || self.reserved_owners != reserved_owners
            || self.sample_heights != profile.heights()
            || self.arithmetic_input_len as usize != ARITH_INPUT_LEN
            || self.arithmetic_rows as usize != ARITH_ROWS
            || self.arithmetic_terms as usize != profile.expected_arith_terms()
            || self.arithmetic_live_bits as usize != profile.expected_live_bits()
            || self.alias_count as usize != EXPECTED_ALIASES[i]
            || self.raw_pin_count as usize != EXPECTED_RAW_PIN_TERMS[i]
            || self.total_terms as usize != EXPECTED_TOTAL_TERMS[i]
            || self.raw_headers_hex.len() != profile.serializer_count()
        {
            return Err("short Legacy expected profile/count/layout/inventory mismatch".into());
        }
        pcs::decode_commitment(&unhex(&self.commitment_hex)?)?;
        let descriptor = unhex(&self.descriptor_hex)?;
        if descriptor.len() != 32 {
            return Err("short Legacy descriptor length mismatch".into());
        }
        for raw in &self.raw_headers_hex {
            if raw.is_empty() || raw.len() > 2 * RAW_CAP {
                return Err("short Legacy expected RAW cap".into());
            }
            unhex(raw)?;
        }
        Ok(profile)
    }

    fn validate_plan(&self, plan: &Plan) -> Result<(), String> {
        let profile = self.validate()?;
        if profile != plan.profile()
            || self.raw_headers_hex
                != plan.raws().iter().map(|raw| hex(raw)).collect::<Vec<_>>()
            || self.alias_count as usize != plan.alias_count()
            || self.raw_pin_count as usize != plan.raw_pin_count()
            || self.total_terms as usize != plan.term_count()
        {
            return Err("short Legacy expected statement does not match verified plan".into());
        }
        if self.descriptor_hex != hex(&plan.descriptor()) {
            return Err("short Legacy descriptor mismatch".into());
        }
        Ok(())
    }

    pub(crate) fn new(
        plan: &Plan,
        setup: &Setup,
        committed: &PackedCommitted,
    ) -> Result<Self, String> {
        let profile = plan.profile();
        let i = profile_index(profile);
        let (serializer_owners, arithmetic_owner, adjacency_owner, reserved_owners) =
            expected_owner_layout(profile);
        let value = Self {
            version: VERSION,
            family: FAMILY.into(),
            profile: profile.name().into(),
            input_log: INPUT_LOG as u8,
            row_log: ROW_LOG as u8,
            ratio_count: profile.count() as u8,
            serializer_count: profile.serializer_count() as u8,
            owner_count: (profile.adjacency_owner() + 1) as u8,
            serializer_owners,
            arithmetic_owner,
            adjacency_owner,
            reserved_owners,
            sample_heights: profile.heights(),
            arithmetic_input_len: ARITH_INPUT_LEN as u32,
            arithmetic_rows: ARITH_ROWS as u32,
            arithmetic_terms: profile.expected_arith_terms() as u32,
            arithmetic_live_bits: profile.expected_live_bits() as u32,
            alias_count: EXPECTED_ALIASES[i] as u32,
            raw_pin_count: EXPECTED_RAW_PIN_TERMS[i] as u32,
            total_terms: EXPECTED_TOTAL_TERMS[i] as u64,
            descriptor_hex: hex(&plan.descriptor()),
            setup_id: setup.id,
            commitment_hex: hex(&pcs::encode_commitment(&committed.commitment)?),
            raw_headers_hex: plan.raws().iter().map(|raw| hex(raw)).collect(),
        };
        value.validate()?;
        value.validate_plan(plan)?;
        Ok(value)
    }

    fn raws(&self) -> Result<Vec<Vec<u8>>, String> {
        self.raw_headers_hex.iter().map(|raw| unhex(raw)).collect()
    }
}

pub(crate) fn encode_expected(expected: &ExpectedStatement) -> Result<Vec<u8>, String> {
    expected.validate()?;
    let bytes = serde_json::to_vec_pretty(expected).map_err(|e| e.to_string())?;
    if bytes.len() > EXPECTED_CAP {
        return Err("short Legacy expected cap".into());
    }
    Ok(bytes)
}

fn decode_expected(bytes: &[u8]) -> Result<ExpectedStatement, String> {
    if bytes.is_empty() || bytes.len() > EXPECTED_CAP {
        return Err("short Legacy expected length".into());
    }
    let expected: ExpectedStatement =
        serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    expected.validate()?;
    if encode_expected(&expected)? != bytes {
        return Err("noncanonical short Legacy expected statement".into());
    }
    Ok(expected)
}

#[derive(Clone)]
pub(crate) struct Packet {
    gkr: Vec<u8>,
    pcs: Vec<u8>,
    post_pcs: Vec<u8>,
}

pub(crate) fn encode_packet(packet: &Packet) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::with_capacity(PACKET_BYTES);
    bytes.extend_from_slice(MAGIC);
    bytes.push(VERSION);
    for (index, section) in [&packet.gkr, &packet.pcs, &packet.post_pcs]
        .into_iter()
        .enumerate()
    {
        if section.len() != SECTION_BYTES[index] {
            return Err(format!("short Legacy section {index} length"));
        }
        bytes.push(index as u8);
        bytes.extend_from_slice(&(section.len() as u32).to_le_bytes());
        bytes.extend_from_slice(section);
    }
    if bytes.len() != PACKET_BYTES {
        return Err("short Legacy packet size drift".into());
    }
    Ok(bytes)
}

fn decode_packet(bytes: &[u8]) -> Result<Packet, String> {
    if bytes.len() != PACKET_BYTES {
        return Err("short Legacy packet length/EOF".into());
    }
    if &bytes[..8] != MAGIC || bytes[8] != VERSION {
        return Err("short Legacy packet profile".into());
    }
    let mut at = 9usize;
    let mut ranges = [(0usize, 0usize); 3];
    for (index, expected_size) in SECTION_BYTES.into_iter().enumerate() {
        if bytes[at] as usize != index {
            return Err("short Legacy component order".into());
        }
        let size = u32::from_le_bytes(bytes[at + 1..at + 5].try_into().unwrap()) as usize;
        if size != expected_size {
            return Err("short Legacy component size before allocation".into());
        }
        at += 5;
        ranges[index] = (at, at + size);
        at += size;
    }
    if at != bytes.len() {
        return Err("short Legacy trailing bytes".into());
    }
    let section = |index: usize| bytes[ranges[index].0..ranges[index].1].to_vec();
    Ok(Packet {
        gkr: section(0),
        pcs: section(1),
        post_pcs: section(2),
    })
}

fn bind(plan: &Plan, expected: &ExpectedStatement, transcript: &mut Transcript) {
    transcript.append_bytes(b"packet-family", FAMILY.as_bytes());
    transcript.append_bytes(b"packet-domain", DOMAIN);
    transcript.append_bytes(b"packet-magic", MAGIC);
    transcript.append_u64(b"packet-version", VERSION as u64);
    transcript.append_u64(b"mandatory-gkr", 1);
    transcript.append_u64(b"mandatory-pcs", 1);
    transcript.append_u64(b"arithmetic-live-bits", expected.arithmetic_live_bits as u64);
    transcript.append_u64(b"raw-pin-count", expected.raw_pin_count as u64);
    transcript.append_u64(b"total-terms", expected.total_terms);
    transcript.append_bytes(b"verified-plan-descriptor", &plan.descriptor());
    plan.bind(
        transcript,
        &expected.setup_id,
        &unhex(&expected.commitment_hex).expect("validated expected commitment"),
    );
}

fn verify_gkr(
    plan: &Plan,
    expected: &ExpectedStatement,
    packet: &Packet,
) -> Result<(InputClaim, Transcript), String> {
    let proof = gkr::decode_dimensions(&[INPUT_LOG], &packet.gkr)?;
    if gkr::encode_proof(&proof)? != packet.gkr {
        return Err("noncanonical short Legacy GKR codec".into());
    }
    let mut transcript = Transcript::new(DOMAIN);
    let claim = gkr::verify_with_wiring(
        &[INPUT_LOG],
        1 << ROW_LOG,
        &proof,
        &mut transcript,
        |transcript| bind(plan, expected, transcript),
        |_, r, u, v| {
            plan.coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        },
    )
    .map_err(|e| format!("short Legacy GKR: {e}"))?;
    Ok((claim, transcript))
}

/// The caller selects the verifier-owned profile before reading untrusted bytes.
/// No packet-supplied profile, roster, claim point, or opening is authoritative.
pub(crate) fn verify_with_key(
    verifier_profile: Profile,
    expected_bytes: &[u8],
    packet_bytes: &[u8],
    key: &AdmittedVerifierKey,
) -> Result<serde_json::Value, String> {
    let started = std::time::Instant::now();
    let expected = decode_expected(expected_bytes)?;
    if expected.profile != verifier_profile.name() {
        return Err("short Legacy verifier-owned profile mismatch".into());
    }
    let packet = decode_packet(packet_bytes)?;
    if key.log_n() != INPUT_LOG || key.id() != &expected.setup_id {
        return Err("short Legacy admitted key mismatch".into());
    }
    let raws = expected.raws()?;
    let plan = Plan::build(verifier_profile, &raws)?;
    expected.validate_plan(&plan)?;
    let (claim, mut transcript) = verify_gkr(&plan, &expected, &packet)?;
    let commitment = pcs::decode_commitment(&unhex(&expected.commitment_hex)?)?;
    let proof = pcs::decode_proof(&packet.pcs, INPUT_LOG)?;
    if pcs::encode_proof(&proof)? != packet.pcs {
        return Err("noncanonical short Legacy PCS codec".into());
    }
    pcs::verify_admitted(
        commitment,
        claim.value,
        &claim.point,
        &proof,
        key,
        &mut transcript,
    )
    .map_err(|e| format!("short Legacy PCS: {e}"))?;
    if pcs::encode(&transcript.challenge_scalar(b"short-legacy-post-pcs"))? != packet.post_pcs {
        return Err("short Legacy post-PCS artifact mismatch".into());
    }
    Ok(serde_json::json!({
        "family": FAMILY,
        "profile": verifier_profile.name(),
        "gkr_proofs": 1,
        "pcs_openings": 1,
        "proof_bytes": packet_bytes.len(),
        "verify_seconds": started.elapsed().as_secs_f64(),
        "claim_ceiling": "fixed exact RAW m3/m4 roster, local Legacy arithmetic and direct final-sample edge; no authenticated history or PoW; diagnostic BN254"
    }))
}

fn read_owner(source: &PackedFile, slot: usize) -> Result<Vec<Fr>, String> {
    if source.input_len() != 1 << INPUT_LOG || slot >= 1 << SLOT_LOG {
        return Err("short Legacy packed owner bounds invalid".into());
    }
    // PackedFile caps each read at 2^16 coordinates. Concatenate the two
    // adjacent copies to reconstruct one 2^17 owner in LSB-first order.
    let mut values = source.read_copy(WIDTH / 2, 2 * slot)?;
    values.extend(source.read_copy(WIDTH / 2, 2 * slot + 1)?);
    if values.len() != WIDTH {
        return Err("short Legacy packed owner width changed".into());
    }
    Ok(values)
}

pub(crate) fn prove(
    verifier_profile: Profile,
    expected: &ExpectedStatement,
    source: &PackedFile,
    setup: &Setup,
    committed: &PackedCommitted,
) -> Result<(Packet, serde_json::Value), String> {
    let profile = expected.validate()?;
    if profile != verifier_profile
        || setup.log_n != INPUT_LOG
        || source.input_len() != 1 << INPUT_LOG
        || setup.id != expected.setup_id
        || committed.nu != INPUT_LOG / 2
        || committed.sigma != INPUT_LOG.div_ceil(2)
        || pcs::encode_commitment(&committed.commitment)? != unhex(&expected.commitment_hex)?
    {
        return Err("short Legacy producer setup/statement mismatch".into());
    }
    let raws = expected.raws()?;
    let plan = Plan::build(verifier_profile, &raws)?;
    expected.validate_plan(&plan)?;
    let mut transcript = Transcript::new(DOMAIN);
    let mark = std::time::Instant::now();
    let (proof, claim, incremental_u, incremental_v) = sparse_stream_roster::prove_edge_terms(
        LOCAL_LOG,
        SLOT_LOG,
        ROW_LOCAL_LOG,
        0,
        &[ROW_LOCAL_LOG],
        |left, slot, sink| plan.visit_endpoint(left, slot, sink),
        |slot| read_owner(source, slot),
        &mut transcript,
        |transcript| bind(&plan, expected, transcript),
        |r, u, v| plan.coefficients(r, u, v),
    )?;
    let gkr_seconds = mark.elapsed().as_secs_f64();
    if source.evaluate(&claim.point)? != claim.value {
        return Err("short Legacy common witness claim mismatch".into());
    }
    let mark = std::time::Instant::now();
    let opening = packed::open(committed, source, &claim.point, setup, &mut transcript)?;
    let pcs_seconds = mark.elapsed().as_secs_f64();
    let packet = Packet {
        gkr: gkr::encode_proof(&proof)?,
        pcs: pcs::encode_proof(&opening)?,
        post_pcs: pcs::encode(&transcript.challenge_scalar(b"short-legacy-post-pcs"))?,
    };
    encode_packet(&packet)?;
    Ok((
        packet,
        serde_json::json!({
            "profile": verifier_profile.name(),
            "gkr_seconds": gkr_seconds,
            "pcs_seconds": pcs_seconds,
            "input_log": INPUT_LOG,
            "row_log": ROW_LOG,
            "serializer_count": verifier_profile.serializer_count(),
            "arithmetic_owner": verifier_profile.arithmetic_owner(),
            "adjacency_owner": verifier_profile.adjacency_owner(),
            "reserved_owners": if verifier_profile == Profile::M3 { vec![7] } else { vec![] },
            "arithmetic_input_len": ARITH_INPUT_LEN,
            "arithmetic_rows": ARITH_ROWS,
            "arithmetic_terms": verifier_profile.expected_arith_terms(),
            "arithmetic_live_bits": verifier_profile.expected_live_bits(),
            "aliases": plan.alias_count(),
            "raw_pin_terms": plan.raw_pin_count(),
            "total_terms": plan.term_count(),
            "incremental_u": incremental_u,
            "incremental_v": incremental_v
        }),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{One, Zero};
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    use std::{
        io::Write,
        path::{Path, PathBuf},
    };

    fn profile_label(profile: Profile) -> &'static str {
        match profile {
            Profile::M3 => "M3",
            Profile::M4 => "M4",
        }
    }

    fn output_env(profile: Profile) -> &'static str {
        match profile {
            Profile::M3 => "NIPOPOW_SHORT34_M3_PACKET_DIR",
            Profile::M4 => "NIPOPOW_SHORT34_M4_PACKET_DIR",
        }
    }

    fn input_env(profile: Profile) -> &'static str {
        match profile {
            Profile::M3 => "NIPOPOW_SHORT34_M3_PACKET_INPUT_DIR",
            Profile::M4 => "NIPOPOW_SHORT34_M4_PACKET_INPUT_DIR",
        }
    }

    fn fresh_temp_dir(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "nipopow-short34-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn output_directory(profile: Profile) -> PathBuf {
        let path = std::env::var_os(output_env(profile))
            .map(PathBuf::from)
            .unwrap_or_else(|| fresh_temp_dir(profile_label(profile)));
        std::fs::create_dir_all(&path).unwrap();
        path
    }

    fn input_directory(profile: Profile) -> PathBuf {
        PathBuf::from(std::env::var_os(input_env(profile)).expect("fresh consumer inputs required"))
    }

    fn create(path: &Path, bytes: &[u8]) {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .unwrap();
        file.write_all(bytes).unwrap();
        file.sync_all().unwrap();
    }

    fn key(setup: &Setup) -> AdmittedVerifierKey {
        let bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
        crate::verifier_key::admit_generated_test_key(INPUT_LOG, &bytes, setup.id).unwrap()
    }

    fn expected_bytes(expected: &ExpectedStatement) -> Vec<u8> {
        serde_json::to_vec_pretty(expected).unwrap()
    }

    fn coherent_expected_for_profile(
        basis: &ExpectedStatement,
        profile: Profile,
    ) -> ExpectedStatement {
        let raws = crate::daa_short_legacy_join::fixture_raws(profile);
        let plan = Plan::build(profile, &raws).unwrap();
        let (serializer_owners, arithmetic_owner, adjacency_owner, reserved_owners) =
            expected_owner_layout(profile);
        let index = profile_index(profile);
        let mut expected = basis.clone();
        expected.profile = profile.name().into();
        expected.ratio_count = profile.count() as u8;
        expected.serializer_count = profile.serializer_count() as u8;
        expected.owner_count = (profile.adjacency_owner() + 1) as u8;
        expected.serializer_owners = serializer_owners;
        expected.arithmetic_owner = arithmetic_owner;
        expected.adjacency_owner = adjacency_owner;
        expected.reserved_owners = reserved_owners;
        expected.sample_heights = profile.heights();
        expected.arithmetic_terms = profile.expected_arith_terms() as u32;
        expected.arithmetic_live_bits = profile.expected_live_bits() as u32;
        expected.alias_count = EXPECTED_ALIASES[index] as u32;
        expected.raw_pin_count = EXPECTED_RAW_PIN_TERMS[index] as u32;
        expected.total_terms = EXPECTED_TOTAL_TERMS[index] as u64;
        expected.descriptor_hex = hex(&plan.descriptor());
        expected.raw_headers_hex = raws.iter().map(|raw| hex(raw)).collect();
        expected.validate().unwrap();
        expected.validate_plan(&plan).unwrap();
        expected
    }

    fn reject(
        profile: Profile,
        expected: &[u8],
        packet: &[u8],
        key: &AdmittedVerifierKey,
        message: &str,
        label: &str,
    ) {
        let error = verify_with_key(profile, expected, packet, key).unwrap_err();
        assert!(error.contains(message), "{label}: {error}");
    }

    fn expected_statement_faults(
        profile: Profile,
        expected: &ExpectedStatement,
        packet: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = 0;
        let mut changed = expected.clone();
        changed.profile = match profile {
            Profile::M3 => Profile::M4.name(),
            Profile::M4 => Profile::M3.name(),
        }
        .into();
        reject(
            profile,
            &expected_bytes(&changed),
            packet,
            key,
            "profile/count/layout/inventory",
            "profile",
        );
        count += 1;

        let other_profile = match profile {
            Profile::M3 => Profile::M4,
            Profile::M4 => Profile::M3,
        };
        let coherent_other = coherent_expected_for_profile(expected, other_profile);
        reject(
            profile,
            &expected_bytes(&coherent_other),
            packet,
            key,
            "verifier-owned profile mismatch",
            "coherent expected profile differs from caller-owned profile",
        );
        count += 1;

        let mut changed = expected.clone();
        changed.version += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "profile/count/layout/inventory", "version");
        count += 1;
        let mut changed = expected.clone();
        changed.family.push_str("-altered");
        reject(profile, &expected_bytes(&changed), packet, key, "profile/count/layout/inventory", "family");
        count += 1;

        let mut changed = expected.clone();
        changed.ratio_count += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "profile/count", "count");
        count += 1;
        let mut changed = expected.clone();
        changed.serializer_count += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "serializer count");
        count += 1;
        let mut changed = expected.clone();
        changed.owner_count += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "owner count");
        count += 1;
        let mut changed = expected.clone();
        changed.input_log += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "input dimension");
        count += 1;
        let mut changed = expected.clone();
        changed.row_log += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "row dimension");
        count += 1;
        let mut changed = expected.clone();
        changed.arithmetic_input_len += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "inventory", "arithmetic input length");
        count += 1;
        let mut changed = expected.clone();
        changed.arithmetic_rows += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "inventory", "arithmetic row count");
        count += 1;
        let mut changed = expected.clone();
        changed.arithmetic_terms += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "inventory", "arithmetic terms");
        count += 1;
        let mut changed = expected.clone();
        changed.arithmetic_live_bits += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "inventory", "live bits");
        count += 1;
        let mut changed = expected.clone();
        changed.alias_count += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "inventory", "alias count");
        count += 1;
        let mut changed = expected.clone();
        changed.raw_pin_count += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "inventory", "RAW pins");
        count += 1;
        let mut changed = expected.clone();
        changed.total_terms += 1;
        reject(profile, &expected_bytes(&changed), packet, key, "inventory", "total terms");
        count += 1;
        let mut changed = expected.clone();
        changed.sample_heights.swap(0, 1);
        reject(profile, &expected_bytes(&changed), packet, key, "count/layout", "ordered heights");
        count += 1;
        let mut changed = expected.clone();
        changed.serializer_owners[0] ^= 1;
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "serializer owner");
        count += 1;
        let mut changed = expected.clone();
        changed.reserved_owners.push(6);
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "reserved owner");
        count += 1;
        let mut changed = expected.clone();
        changed.arithmetic_owner ^= 1;
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "arithmetic owner");
        count += 1;
        let mut changed = expected.clone();
        changed.adjacency_owner ^= 1;
        reject(profile, &expected_bytes(&changed), packet, key, "layout", "adjacency owner");
        count += 1;
        let mut changed = expected.clone();
        changed.raw_headers_hex.pop();
        reject(profile, &expected_bytes(&changed), packet, key, "profile/count/layout/inventory", "RAW vector count");
        count += 1;
        let mut changed = expected.clone();
        changed.setup_id[0] ^= 1;
        reject(profile, &expected_bytes(&changed), packet, key, "admitted key mismatch", "key id");
        count += 1;
        let mut changed = expected.clone();
        let descriptor = unhex(&changed.descriptor_hex).unwrap();
        let mut descriptor = descriptor;
        descriptor[0] ^= 1;
        changed.descriptor_hex = hex(&descriptor);
        reject(
            profile,
            &expected_bytes(&changed),
            packet,
            key,
            "descriptor mismatch",
            "descriptor single-bit mutation",
        );
        count += 1;
        let mut changed = expected.clone();
        changed.commitment_hex = "00".into();
        reject(profile, &expected_bytes(&changed), packet, key, "commitment length mismatch", "commitment encoding length");
        count += 1;
        let mut changed = expected.clone();
        changed.raw_headers_hex.swap(0, 1);
        reject(
            profile,
            &encode_expected(&changed).unwrap(),
            packet,
            key,
            "roster differs from verifier-owned RAW fixtures",
            "RAW order",
        );
        count += 1;
        count
    }

    fn raw_field_faults(
        profile: Profile,
        expected: &ExpectedStatement,
        packet: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = 0;
        for slot in 0..expected.raw_headers_hex.len() {
            for field in ["height", "timestamp", "nbits"] {
                let raw = unhex(&expected.raw_headers_hex[slot]).unwrap();
                let mut header = ergo_header_core::Header::decode(&raw, None).unwrap();
                match field {
                    "height" => header.height += 1,
                    "timestamp" => header.timestamp += 1,
                    "nbits" => header.n_bits ^= 1,
                    _ => unreachable!(),
                }
                let changed_raw = header.encode().unwrap();
                assert_ne!(raw, changed_raw);
                let mut changed = expected.clone();
                changed.raw_headers_hex[slot] = hex(&changed_raw);
                reject(
                    profile,
                    &encode_expected(&changed).unwrap(),
                    packet,
                    key,
                    "roster differs from verifier-owned RAW fixtures",
                    &format!("RAW slot{slot} {field}"),
                );
                count += 1;
            }
        }
        for slot in [profile.count(), profile.count() + 1] {
            let raw = unhex(&expected.raw_headers_hex[slot]).unwrap();
            let mut header = ergo_header_core::Header::decode(&raw, None).unwrap();
            header.parent_id[0] ^= 1;
            let mut changed = expected.clone();
            changed.raw_headers_hex[slot] = hex(&header.encode().unwrap());
            reject(
                profile,
                &encode_expected(&changed).unwrap(),
                packet,
                key,
                "roster differs from verifier-owned RAW fixtures",
                &format!("RAW parent ID slot{slot}"),
            );
            count += 1;
        }
        count
    }

    fn decoder_faults(
        profile: Profile,
        expected: &ExpectedStatement,
        packet: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let canonical = encode_expected(expected).unwrap();
        let text = String::from_utf8(canonical.clone()).unwrap();
        let oversized_expected = vec![b' '; EXPECTED_CAP + 1];
        reject(
            profile,
            &oversized_expected,
            packet,
            key,
            "short Legacy expected length",
            "pre-JSON expected cap",
        );
        let mut oversized_raw = expected.clone();
        oversized_raw.raw_headers_hex[0] = "00".repeat(RAW_CAP + 1);
        let oversized_raw_bytes = expected_bytes(&oversized_raw);
        assert!(oversized_raw_bytes.len() < EXPECTED_CAP);
        reject(
            profile,
            &oversized_raw_bytes,
            packet,
            key,
            "short Legacy expected RAW cap",
            "individual RAW cap below expected JSON cap",
        );

        let unknown = text.replacen("{", "{\n  \"unexpected\": 1,", 1);
        reject(
            profile,
            unknown.as_bytes(),
            packet,
            key,
            "unknown field",
            "unknown expected field",
        );

        let duplicate = text.replacen(
            "{",
            "{\n  \"version\": 1,",
            1,
        );
        reject(
            profile,
            duplicate.as_bytes(),
            packet,
            key,
            "duplicate field",
            "duplicate expected field",
        );

        let mut upper = expected.clone();
        let raw = &mut upper.raw_headers_hex[0];
        let index = raw
            .bytes()
            .position(|byte| (b'a'..=b'f').contains(&byte))
            .expect("pinned RAW contains lowercase hex letters");
        let upper_hex_char = (raw.as_bytes()[index] as char).to_ascii_uppercase().to_string();
        raw.replace_range(index..=index, &upper_hex_char);
        let upper_bytes = expected_bytes(&upper);
        reject(
            profile,
            &upper_bytes,
            packet,
            key,
            "noncanonical lowercase hex",
            "uppercase expected hex",
        );

        let mut spaced = canonical.clone();
        spaced.push(b' ');
        reject(
            profile,
            &spaced,
            packet,
            key,
            "noncanonical short Legacy expected statement",
            "JSON canonical form",
        );

        let mut count = 6;
        let mut bad = packet.to_vec();
        bad[0] ^= 1;
        reject(profile, &canonical, &bad, key, "packet profile", "packet magic");
        bad = packet.to_vec();
        bad[8] ^= 1;
        reject(profile, &canonical, &bad, key, "packet profile", "packet version");
        count += 2;
        for index in 0..3 {
            let mut bad = packet.to_vec();
            let tag_at = 9 + SECTION_BYTES[..index].iter().map(|n| 5 + n).sum::<usize>();
            bad[tag_at] = ((index + 1) % 3) as u8;
            reject(profile, &canonical, &bad, key, "component order", &format!("section tag {index}"));
            count += 1;
        }
        for index in 0..3 {
            let mut bad = packet.to_vec();
            let tag_at = 9 + SECTION_BYTES[..index].iter().map(|n| 5 + n).sum::<usize>();
            bad[tag_at + 1..tag_at + 5].copy_from_slice(&0u32.to_le_bytes());
            reject(
                profile,
                &canonical,
                &bad,
                key,
                "component size before allocation",
                &format!("section length {index}"),
            );
            count += 1;
        }
        for size in [0, 14, PACKET_BYTES - 1] {
            reject(
                profile,
                &canonical,
                &packet[..size],
                key,
                "packet length/EOF",
                "truncation",
            );
            count += 1;
        }
        let mut trailing = packet.to_vec();
        trailing.push(0);
        reject(profile, &canonical, &trailing, key, "packet length/EOF", "trailing bytes");
        count += 1;
        let mut section_at = 9usize;
        for (index, size) in SECTION_BYTES.into_iter().enumerate() {
            let mut omitted = packet.to_vec();
            omitted.drain(section_at..section_at + 5 + size);
            reject(
                profile,
                &canonical,
                &omitted,
                key,
                "packet length/EOF",
                &format!("omitted component {index}"),
            );
            count += 1;
            section_at += 5 + size;
        }
        assert_eq!(section_at, PACKET_BYTES);
        count
    }

    fn producer_cryptographic_faults(
        profile: Profile,
        expected: &ExpectedStatement,
        expected_json: &[u8],
        packet: &Packet,
        packet_bytes: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = 0;
        let mut changed = expected.clone();
        let mut commitment = pcs::decode_commitment(&unhex(&expected.commitment_hex).unwrap()).unwrap();
        let delta = commitment.0;
        commitment.0 += delta;
        changed.commitment_hex = hex(&pcs::encode_commitment(&commitment).unwrap());
        assert_ne!(changed.commitment_hex, expected.commitment_hex);
        reject(
            profile,
            &encode_expected(&changed).unwrap(),
            packet_bytes,
            key,
            "short Legacy GKR",
            "commitment-bound transcript",
        );
        count += 1;

        let mut changed = packet.clone();
        let mut proof = gkr::decode_dimensions(&[INPUT_LOG], &changed.gkr).unwrap();
        proof.layers[0].rounds[0][0] += Fr::one();
        changed.gkr = gkr::encode_proof(&proof).unwrap();
        reject(
            profile,
            expected_json,
            &encode_packet(&changed).unwrap(),
            key,
            "short Legacy GKR",
            "GKR message mutation",
        );
        count += 1;

        // t*(t-1) preserves the line endpoints; the PCS opening must reject
        // the different GKR terminal claim.
        let mut changed = packet.clone();
        let mut proof = gkr::decode_dimensions(&[INPUT_LOG], &changed.gkr).unwrap();
        proof.layers[0].line_coefficients[1] -= Fr::one();
        proof.layers[0].line_coefficients[2] += Fr::one();
        changed.gkr = gkr::encode_proof(&proof).unwrap();
        reject(
            profile,
            expected_json,
            &encode_packet(&changed).unwrap(),
            key,
            "short Legacy PCS",
            "PCS-only terminal claim mutation",
        );
        count += 1;

        let mut changed = packet.clone();
        let mut proof = pcs::decode_proof(&changed.pcs, INPUT_LOG).unwrap();
        let delta = proof.first_messages[0].d1_left.0;
        proof.first_messages[0].d1_left.0 += delta;
        changed.pcs = pcs::encode_proof(&proof).unwrap();
        reject(
            profile,
            expected_json,
            &encode_packet(&changed).unwrap(),
            key,
            "short Legacy PCS",
            "PCS proof mutation",
        );
        count += 1;

        let mut changed = packet.clone();
        changed.post_pcs[0] ^= 1;
        reject(
            profile,
            expected_json,
            &encode_packet(&changed).unwrap(),
            key,
            "post-PCS artifact mismatch",
            "post-PCS mutation",
        );
        count += 1;
        count
    }

    fn assert_owner_boundary(profile: Profile, plan: &Plan) {
        let mut emitted = 0usize;
        plan.visit_endpoint(true, 7, &mut |_| {
            emitted += 1;
            Ok(())
        })
        .unwrap();
        if profile == Profile::M3 {
            assert_eq!(emitted, 0, "m3 owner7 is reserved");
        } else {
            assert!(emitted > 0, "m4 owner7 carries adjacency terms");
        }
    }

    fn run_owner_reader_test() {
        let dir = fresh_temp_dir("owner-reader");
        std::fs::create_dir_all(&dir).unwrap();
        let bytes = (0..(1 << INPUT_LOG) / 8)
            .map(|i| ((i * 37 + (i >> 8) * 13 + (i >> 13) * 59) % 256) as u8)
            .collect::<Vec<_>>();
        let mut writer =
            packed::PackedFileWriter::create_new(&dir.join("owner-reader.bits"), INPUT_LOG)
                .unwrap();
        writer.write_bytes(&bytes).unwrap();
        let source = writer.finish().unwrap();
        assert!(source.read_copy(WIDTH, 0).is_err(), "the underlying read cap remains 2^16");
        for slot in 0..1 << SLOT_LOG {
            let values = read_owner(&source, slot).unwrap();
            assert_eq!(values.len(), WIDTH);
            for (local, actual) in values.iter().enumerate() {
                let bit = slot * WIDTH + local;
                assert_eq!(
                    *actual,
                    Fr::from(((bytes[bit / 8] >> (bit % 8)) & 1) as u64),
                    "owner {slot} coordinate {local}"
                );
            }
        }
        assert!(read_owner(&source, 1 << SLOT_LOG)
            .unwrap_err()
            .contains("bounds"));
        let mut wrong_writer = packed::PackedFileWriter::create_new(
            &dir.join("wrong-owner-shape.bits"),
            INPUT_LOG - 1,
        )
        .unwrap();
        wrong_writer.write_bytes(&bytes[..bytes.len() / 2]).unwrap();
        let wrong_source = wrong_writer.finish().unwrap();
        assert!(read_owner(&wrong_source, 0)
            .unwrap_err()
            .contains("bounds"));
    }

    fn run_producer(profile: Profile) {
        let whole = std::time::Instant::now();
        let dir = output_directory(profile);
        let raws = crate::daa_short_legacy_join::fixture_raws(profile);
        let plan = Plan::build(profile, &raws).unwrap();
        assert_eq!(plan.alias_count(), EXPECTED_ALIASES[profile_index(profile)]);
        assert_eq!(plan.term_count(), EXPECTED_TOTAL_TERMS[profile_index(profile)]);
        assert_eq!(plan.raw_pin_count(), EXPECTED_RAW_PIN_TERMS[profile_index(profile)]);
        assert_owner_boundary(profile, &plan);
        let witness = plan.materialize_witness().unwrap();
        plan.check_residuals(&witness).unwrap();
        let witness_bytes = witness
            .chunks_exact(8)
            .map(|bits| {
                bits.iter().enumerate().fold(0u8, |byte, (index, bit)| {
                    assert!(bit.is_zero() || bit.is_one());
                    byte | ((bit.is_one() as u8) << index)
                })
            })
            .collect::<Vec<_>>();
        let mut writer =
            packed::PackedFileWriter::create_new(&dir.join("witness.bits"), INPUT_LOG).unwrap();
        writer.write_bytes(&witness_bytes).unwrap();
        let source = writer.finish().unwrap();
        drop(witness);

        let mark = std::time::Instant::now();
        let setup = pcs::generate_setup(INPUT_LOG).unwrap();
        let setup_seconds = mark.elapsed().as_secs_f64();
        let admitted = key(&setup);
        let mark = std::time::Instant::now();
        let committed = packed::commit(&source, &setup).unwrap();
        let commit_seconds = mark.elapsed().as_secs_f64();
        let expected = ExpectedStatement::new(&plan, &setup, &committed).unwrap();
        let expected_json = encode_expected(&expected).unwrap();
        let (packet, metrics) = prove(profile, &expected, &source, &setup, &committed).unwrap();
        let packet_bytes = encode_packet(&packet).unwrap();
        let report = verify_with_key(profile, &expected_json, &packet_bytes, &admitted).unwrap();

        let cryptographic_negatives = producer_cryptographic_faults(
            profile,
            &expected,
            &expected_json,
            &packet,
            &packet_bytes,
            &admitted,
        );
        let decoder_negative_count =
            decoder_faults(profile, &expected, &packet_bytes, &admitted);
        let receipt = serde_json::json!({
            "family": FAMILY,
            "profile": profile.name(),
            "producer": metrics,
            "consumer": report,
            "packet_bytes": packet_bytes.len(),
            "isolated_cryptographic_negatives": cryptographic_negatives,
            "isolated_decoder_negatives": decoder_negative_count,
            "setup_seconds": setup_seconds,
            "commit_seconds": commit_seconds,
            "whole_seconds": whole.elapsed().as_secs_f64(),
            "key_admission": "independently generated diagnostic test key; not a released production pin"
        });
        create(&dir.join("expected.json"), &expected_json);
        create(&dir.join("packet.bin"), &packet_bytes);
        create(&dir.join("post-pcs.bin"), &packet.post_pcs);
        create(
            &dir.join("producer.json"),
            &serde_json::to_vec_pretty(&receipt).unwrap(),
        );
        println!("{receipt}");
    }

    fn run_fresh_consumer(profile: Profile) {
        let dir = input_directory(profile);
        let expected_bytes = std::fs::read(dir.join("expected.json")).unwrap();
        let packet_bytes = std::fs::read(dir.join("packet.bin")).unwrap();
        let setup = pcs::generate_setup(INPUT_LOG).unwrap();
        let admitted = key(&setup);
        let report = verify_with_key(profile, &expected_bytes, &packet_bytes, &admitted).unwrap();
        let expected = decode_expected(&expected_bytes).unwrap();
        let expected_negatives =
            expected_statement_faults(profile, &expected, &packet_bytes, &admitted);
        let raw_negatives = raw_field_faults(profile, &expected, &packet_bytes, &admitted);
        let decoder_negative_count =
            decoder_faults(profile, &expected, &packet_bytes, &admitted);
        println!(
            "{}",
            serde_json::json!({
                "consumer": report,
                "isolated_expected_statement_negatives": expected_negatives,
                "isolated_expected_raw_negatives": raw_negatives,
                "isolated_decoder_negatives": decoder_negative_count,
                "scope": "fresh process verifies serialized producer output; exact RAW mutations fail verifier-owned roster pin"
            })
        );
    }

    #[test]
    fn short_legacy_packet_owner_reader_preserves_coordinates_and_bounds() {
        run_owner_reader_test();
    }

    #[test]
    fn short_legacy_packet_m3_one_gkr_one_pcs_producer_and_faults() {
        run_producer(Profile::M3);
    }

    #[test]
    fn short_legacy_packet_m4_one_gkr_one_pcs_producer_and_faults() {
        run_producer(Profile::M4);
    }

    #[test]
    #[ignore = "separate fresh m3 consumer requires NIPOPOW_SHORT34_M3_PACKET_INPUT_DIR"]
    fn short_legacy_packet_m3_fresh_serialized_consumer() {
        run_fresh_consumer(Profile::M3);
    }

    #[test]
    #[ignore = "separate fresh m4 consumer requires NIPOPOW_SHORT34_M4_PACKET_INPUT_DIR"]
    fn short_legacy_packet_m4_fresh_serialized_consumer() {
        run_fresh_consumer(Profile::M4);
    }
}

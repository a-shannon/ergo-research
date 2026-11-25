//! Fixed producer/consumer packet for the bounded DAA/serializer join.
//!
//! The caller supplies expected raw headers, setup identity, and common packed
//! commitment independently. The verifier derives every GKR terminal claim,
//! embedding, and the seven-entry opening roster from fixed code-owned roles.
//! This diagnostic profile proves no historical inclusion, PoW, or consensus.
use ark_bn254::Fr;
use blake2::{digest::consts::U32, Blake2b, Digest};
use dory_pcs::backends::arkworks::ArkGT;
use serde::{Deserialize, Serialize};
use std::{path::Path, time::Instant};

use crate::{
    daa_serializer_join::{JoinPlan, Role},
    gkr::InputClaim,
    opening_batch::{self, Claim, Statement as OpeningStatement},
    packed::{self, PackedCommitted, PackedFile},
    pcs::{self, Setup},
    sparse,
    transcript::Transcript,
    verifier_key,
};

pub const PROFILE: &str = "mainnet-mapped-daa-fullserializer-join-v2";
const DOMAIN: &[u8] = b"nipopow-mainnet-mapped-daa-fullserializer-join-v2";
const MAGIC: &[u8; 8] = b"DAAJPK02";
const VERSION: u8 = 2;
const GLOBAL_LOG: usize = 22;
const EXPECTED_CAP: usize = 16_384;
const SECTION_BYTES: [usize; 5] = [4_576, 4_128, 4_576, 5_024, 31_581];
pub const PACKET_BYTES: usize = 49_919;
const ROLE_NAMES: [&str; 4] = ["serializer-a", "serializer-b", "daa", "aliases"];
const ROLE_ORDER: [Role; 4] = [
    Role::SerializerA,
    Role::SerializerB,
    Role::Daa,
    Role::Aliases,
];

/// Caller-owned expected inputs. Canonical lowercase hex keeps JSON bounded
/// and makes the ten raw headers explicit instead of deriving them from proof.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExpectedStatement {
    pub version: u8,
    pub profile: String,
    pub domain: String,
    pub log_n: u8,
    pub roles: [String; 4],
    pub setup_id: [u8; 32],
    pub commitment_hex: String,
    pub raw_lengths: [u16; 10],
    pub raw_headers_hex: [String; 10],
}

impl ExpectedStatement {
    pub fn new(
        raw_headers: &[Vec<u8>],
        setup_id: [u8; 32],
        commitment: &ArkGT,
    ) -> Result<Self, String> {
        if raw_headers.len() != 10 {
            return Err("expected exactly ten raw headers".into());
        }
        let raw_headers_hex: [String; 10] = raw_headers
            .iter()
            .map(|raw| hex_encode(raw))
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|_| "raw header roster length")?;
        let value = Self {
            version: VERSION,
            profile: PROFILE.into(),
            domain: String::from_utf8(DOMAIN.to_vec()).map_err(|e| e.to_string())?,
            log_n: GLOBAL_LOG as u8,
            roles: ROLE_NAMES.map(str::to_owned),
            setup_id,
            commitment_hex: hex_encode(&pcs::encode_commitment(commitment)?),
            raw_lengths: raw_headers
                .iter()
                .map(|raw| u16::try_from(raw.len()).map_err(|_| "raw header length overflow"))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .map_err(|_| "raw header roster length")?,
            raw_headers_hex,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.version != VERSION
            || self.profile != PROFILE
            || self.domain.as_bytes() != DOMAIN
            || self.log_n as usize != GLOBAL_LOG
            || self.roles != ROLE_NAMES.map(str::to_owned)
        {
            return Err("DAA packet profile, domain, dimensions, or roster rejected".into());
        }
        let commitment = hex_decode_canonical(&self.commitment_hex)?;
        pcs::decode_commitment(&commitment)?;
        for (raw_hex, expected_len) in self.raw_headers_hex.iter().zip(self.raw_lengths) {
            let raw = hex_decode_canonical(raw_hex)?;
            if raw.is_empty() || raw.len() > 514 || raw.len() != expected_len as usize {
                return Err("expected raw header cap rejected".into());
            }
        }
        Ok(())
    }

    fn raw_headers(&self) -> Result<[Vec<u8>; 10], String> {
        self.raw_headers_hex
            .iter()
            .map(|raw| hex_decode_canonical(raw))
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|_| "expected raw roster length".into())
    }

    fn commitment(&self) -> Result<ArkGT, String> {
        pcs::decode_commitment(&hex_decode_canonical(&self.commitment_hex)?)
    }
}

pub fn encode_expected(expected: &ExpectedStatement) -> Result<Vec<u8>, String> {
    expected.validate()?;
    let bytes = serde_json::to_vec_pretty(expected).map_err(|e| e.to_string())?;
    if bytes.len() > EXPECTED_CAP {
        return Err("DAA expected statement exceeds cap".into());
    }
    Ok(bytes)
}

pub fn decode_expected(bytes: &[u8]) -> Result<ExpectedStatement, String> {
    if bytes.is_empty() || bytes.len() > EXPECTED_CAP {
        return Err("DAA expected statement length rejected".into());
    }
    let expected: ExpectedStatement = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    expected.validate()?;
    if encode_expected(&expected)? != bytes {
        return Err("noncanonical DAA expected statement".into());
    }
    Ok(expected)
}

/// Four mandatory GKR streams followed by exactly one seven-claim PCS batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofPacket {
    pub gkr: [Vec<u8>; 4],
    pub opening_batch: Vec<u8>,
}

fn sections(packet: &ProofPacket) -> impl Iterator<Item = &Vec<u8>> {
    packet
        .gkr
        .iter()
        .chain(std::iter::once(&packet.opening_batch))
}

pub fn encode_packet(packet: &ProofPacket) -> Result<Vec<u8>, String> {
    for (index, section) in sections(packet).enumerate() {
        if section.len() != SECTION_BYTES[index] {
            return Err(format!("DAA section {index} length rejected"));
        }
    }
    let mut bytes = Vec::with_capacity(PACKET_BYTES);
    bytes.extend_from_slice(MAGIC);
    bytes.push(VERSION);
    for (index, section) in sections(packet).enumerate() {
        bytes.push(index as u8);
        bytes.extend_from_slice(&(section.len() as u32).to_le_bytes());
        bytes.extend_from_slice(section);
    }
    if bytes.len() != PACKET_BYTES {
        return Err("DAA frozen packet size drift".into());
    }
    Ok(bytes)
}

pub fn decode_packet(bytes: &[u8]) -> Result<ProofPacket, String> {
    if bytes.len() != PACKET_BYTES {
        return Err("DAA packet length/EOF rejected".into());
    }
    if &bytes[..8] != MAGIC || bytes[8] != VERSION {
        return Err("DAA packet header rejected".into());
    }
    let mut ranges = [(0usize, 0usize); 5];
    let mut at = 9usize;
    for (index, range) in ranges.iter_mut().enumerate() {
        let head_end = at.checked_add(5).ok_or("DAA section header overflow")?;
        let head = bytes
            .get(at..head_end)
            .ok_or("truncated DAA section header")?;
        if head[0] as usize != index {
            return Err("DAA section role/order rejected".into());
        }
        let size = u32::from_le_bytes(head[1..5].try_into().unwrap()) as usize;
        if size != SECTION_BYTES[index] {
            return Err("DAA section length rejected before allocation".into());
        }
        at = head_end;
        let end = at.checked_add(size).ok_or("DAA section range overflow")?;
        bytes.get(at..end).ok_or("truncated DAA section")?;
        *range = (at, end);
        at = end;
    }
    if at != bytes.len() {
        return Err("DAA packet trailing bytes".into());
    }
    let copy = |index: usize| bytes[ranges[index].0..ranges[index].1].to_vec();
    Ok(ProofPacket {
        gkr: std::array::from_fn(copy),
        opening_batch: copy(4),
    })
}

/// Producer entry point. The packed witness and commitment must already exist;
/// all role circuits, slices, selectors, and the seven-claim roster are fixed.
pub fn prove(
    plan: &JoinPlan,
    expected: &ExpectedStatement,
    witness: &[Fr],
    source: &PackedFile,
    setup: &Setup,
    committed: &PackedCommitted,
) -> Result<ProofPacket, String> {
    prove_with_metrics(plan, expected, witness, source, setup, committed).map(|(packet, _)| packet)
}

#[derive(Clone, Debug, Default)]
struct ProducerMetrics {
    gkr_prove_seconds: [f64; 4],
    gkr_roundtrip_seconds: [f64; 4],
    positive_opening_seconds: f64,
    positive_packet_seconds: f64,
    proof_bytes: usize,
    gkr_roles: usize,
    opening_claims: usize,
    opening_batches: usize,
}

fn prove_with_metrics(
    plan: &JoinPlan,
    expected: &ExpectedStatement,
    witness: &[Fr],
    source: &PackedFile,
    setup: &Setup,
    committed: &PackedCommitted,
) -> Result<(ProofPacket, ProducerMetrics), String> {
    let total_started = Instant::now();
    expected.validate()?;
    validate_expected_plan(expected, plan)?;
    admit_setup_and_commitment(expected, setup, committed)?;
    JoinPlan::validate_boolean_witness(witness)?;
    if source.input_len() != 1usize << GLOBAL_LOG {
        return Err("packed source dimension rejected".into());
    }
    compare_packed_source(source, witness)?;
    let views = plan.role_views(witness)?;
    let mut claims = Vec::with_capacity(4);
    let mut streams = Vec::with_capacity(4);
    let mut metrics = ProducerMetrics::default();
    for (index, view) in views.iter().enumerate() {
        if view.role() != ROLE_ORDER[index] {
            return Err("producer role order drift".into());
        }
        let mut producer = role_transcript(
            expected,
            index,
            view.circuit(),
            view.log_copies(),
            view.selector(),
        )?;
        let prove_started = Instant::now();
        let (proof, checked) = sparse::prove(
            view.circuit(),
            view.input(),
            view.log_copies(),
            &mut producer,
        )
        .map_err(|e| format!("DAA role {} prove: {e}", ROLE_NAMES[index]))?;
        metrics.gkr_prove_seconds[index] = prove_started.elapsed().as_secs_f64();
        let roundtrip_started = Instant::now();
        check_local_and_global_claim(source, view.role(), view.input(), &checked)?;
        let encoded = crate::gkr::encode_proof(&proof)?;
        if encoded.len() != SECTION_BYTES[index] {
            return Err(format!("DAA role {index} proof length drift"));
        }
        let decoded = sparse::decode_proof(view.circuit(), view.log_copies(), &encoded)?;
        let mut consumer = role_transcript(
            expected,
            index,
            view.circuit(),
            view.log_copies(),
            view.selector(),
        )?;
        let verified =
            sparse::verify(view.circuit(), view.log_copies(), &decoded, &mut consumer)
                .map_err(|e| format!("DAA role {} local roundtrip: {e}", ROLE_NAMES[index]))?;
        check_transcript_continuation(&producer, &consumer)?;
        if checked != verified {
            return Err("GKR producer/consumer terminal differs".into());
        }
        metrics.gkr_roundtrip_seconds[index] = roundtrip_started.elapsed().as_secs_f64();
        claims.push(derived_claim(view.role(), &verified)?);
        streams.push(encoded);
    }
    let claims: [Claim; 4] = claims
        .try_into()
        .map_err(|_| "DAA role claim roster length")?;
    let statement = opening_statement(expected, &claims)?;
    let opening_started = Instant::now();
    let (opening, _, producer) = opening_batch::prove(source, committed, setup, &statement)?;
    let opening_bytes = opening_batch::encode_proof(&opening, GLOBAL_LOG)?;
    if opening_bytes.len() != SECTION_BYTES[4] {
        return Err("DAA opening proof length drift".into());
    }
    let decoded = opening_batch::decode_proof(&opening_bytes, GLOBAL_LOG)?;
    let consumer = opening_batch::verify(&statement, setup, &decoded)?;
    check_transcript_continuation(&producer, &consumer)?;
    metrics.positive_opening_seconds = opening_started.elapsed().as_secs_f64();
    let gkr: [Vec<u8>; 4] = streams
        .try_into()
        .map_err(|_| "DAA GKR section roster length")?;
    let packet = ProofPacket {
        gkr,
        opening_batch: opening_bytes,
    };
    let _framed = encode_packet(&packet)?;
    metrics.positive_packet_seconds = total_started.elapsed().as_secs_f64();
    metrics.proof_bytes = PACKET_BYTES;
    metrics.gkr_roles = 4;
    metrics.opening_claims = 7;
    metrics.opening_batches = 1;
    Ok((packet, metrics))
}

#[derive(Clone, Debug)]
pub struct VerifyReport {
    pub profile: &'static str,
    pub proof_bytes: usize,
    pub mandatory_gkr_roles: usize,
    pub derived_opening_claims: usize,
    pub opening_batches: usize,
    pub key_admission_seconds: f64,
    pub circuit_seconds: f64,
    pub verification_seconds: f64,
}

/// Fresh verifier with a code-pinned k22 verifier key. Expected headers and
/// common commitment are independently supplied serialized inputs.
pub fn verify(expected_bytes: &[u8], packet_bytes: &[u8]) -> Result<VerifyReport, String> {
    let started = Instant::now();
    let expected = decode_expected(expected_bytes)?;
    let packet = decode_packet(packet_bytes)?;
    let key_started = Instant::now();
    let key = verifier_key::admit(
        GLOBAL_LOG,
        include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),
    )?;
    admit_expected_key(&expected, &key)?;
    let key_seconds = key_started.elapsed().as_secs_f64();
    let circuit_started = Instant::now();
    let plan = plan_from_expected(&expected)?;
    let specs = plan.role_specs()?;
    let commitment = expected.commitment()?;
    let raw_id = raw_identity(&expected)?;
    let circuit_seconds = circuit_started.elapsed().as_secs_f64();
    let claims = verify_gkr_claims(&expected, &specs, &packet)?;
    let statement =
        fixed_opening_statement(GLOBAL_LOG, expected.setup_id, commitment, raw_id, &claims);
    let decoded_opening = opening_batch::decode_proof(&packet.opening_batch, GLOBAL_LOG)?;
    // This is the single admitted PCS verification for the seven code-derived claims.
    opening_batch::verify_admitted(&statement, &key, &decoded_opening)
        .map_err(|e| format!("DAA seven-claim opening batch rejected: {e}"))?;
    Ok(VerifyReport {
        profile: PROFILE,
        proof_bytes: packet_bytes.len(),
        mandatory_gkr_roles: 4,
        derived_opening_claims: 7,
        opening_batches: 1,
        key_admission_seconds: key_seconds,
        circuit_seconds,
        verification_seconds: started.elapsed().as_secs_f64(),
    })
}

fn admit_setup_and_commitment(
    expected: &ExpectedStatement,
    setup: &Setup,
    committed: &PackedCommitted,
) -> Result<(), String> {
    if setup.log_n != GLOBAL_LOG
        || setup.id != expected.setup_id
        || committed.nu != GLOBAL_LOG / 2
        || committed.sigma != GLOBAL_LOG.div_ceil(2)
        || pcs::encode_commitment(&committed.commitment)?
            != hex_decode_canonical(&expected.commitment_hex)?
    {
        return Err("DAA producer setup/common commitment rejected".into());
    }
    Ok(())
}

fn admit_expected_key(
    expected: &ExpectedStatement,
    key: &verifier_key::AdmittedVerifierKey,
) -> Result<(), String> {
    if key.log_n() != GLOBAL_LOG || key.id() != &expected.setup_id {
        return Err("DAA expected setup does not match admitted key".into());
    }
    Ok(())
}

fn validate_expected_plan(expected: &ExpectedStatement, plan: &JoinPlan) -> Result<(), String> {
    let raw = expected.raw_headers()?;
    if plan
        .raw_headers()
        .iter()
        .map(Vec::as_slice)
        .ne(raw.iter().map(Vec::as_slice))
    {
        return Err("DAA expected raw headers differ from producer plan".into());
    }
    Ok(())
}

fn plan_from_expected(expected: &ExpectedStatement) -> Result<JoinPlan, String> {
    let raw = expected.raw_headers()?;
    let samples: [&[u8]; 9] = raw[..9]
        .iter()
        .map(Vec::as_slice)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| "expected sample roster length")?;
    JoinPlan::build(samples, &raw[9])
}

fn role_transcript(
    expected: &ExpectedStatement,
    index: usize,
    circuit: &sparse::Circuit,
    copies: usize,
    selector: &[bool],
) -> Result<Transcript, String> {
    if index >= ROLE_NAMES.len() || copies > 3 {
        return Err("DAA role prebinding bounds rejected".into());
    }
    let raw_id = raw_identity(expected)?;
    let mut transcript = Transcript::new(DOMAIN);
    transcript.append_bytes(b"daa-packet-profile", PROFILE.as_bytes());
    transcript.append_bytes(b"daa-packet-domain", DOMAIN);
    transcript.append_bytes(
        b"daa-packet-layout",
        b"bn254-fr-canonical32-lsb-low-column-high-row-k22-mapped-daa-v2",
    );
    transcript.append_u64(b"daa-packet-version", VERSION as u64);
    transcript.append_bytes(b"daa-packet-raw-identity", &raw_id);
    transcript.append_u64(b"daa-packet-role-index", index as u64);
    transcript.append_bytes(b"daa-packet-role-name", ROLE_NAMES[index].as_bytes());
    transcript.append_u64(b"daa-packet-global-log", GLOBAL_LOG as u64);
    transcript.append_u64(
        b"daa-packet-local-log",
        circuit.input_len.trailing_zeros() as u64 + copies as u64,
    );
    transcript.append_u64(b"daa-packet-row-count", circuit.row_count as u64);
    transcript.append_u64(b"daa-packet-term-count", circuit.terms.len() as u64);
    transcript.append_u64(b"daa-packet-copies", copies as u64);
    transcript.append_u64(b"daa-packet-selector-length", selector.len() as u64);
    for bit in selector {
        transcript.append_u64(b"daa-packet-selector-bit", *bit as u64);
    }
    transcript.append_bytes(b"daa-packet-setup-id", &expected.setup_id);
    transcript.append_bytes(
        b"daa-packet-common-commitment",
        &hex_decode_canonical(&expected.commitment_hex)?,
    );
    Ok(transcript)
}

fn raw_identity(expected: &ExpectedStatement) -> Result<[u8; 32], String> {
    let raw = expected.raw_headers()?;
    let mut h = Blake2b::<U32>::new();
    h.update(b"nipopow-mapped-daa-packet-expected-raw-v2");
    h.update((PROFILE.len() as u64).to_le_bytes());
    h.update(PROFILE.as_bytes());
    for (index, bytes) in raw.iter().enumerate() {
        h.update((index as u64).to_le_bytes());
        h.update((bytes.len() as u64).to_le_bytes());
        h.update(bytes);
    }
    Ok(h.finalize().into())
}

fn derived_claim(role: Role, claim: &InputClaim) -> Result<Claim, String> {
    let point = JoinPlan::embed_point(role, &claim.point)?;
    JoinPlan::validate_embedded_point(role, &point)?;
    Ok(Claim {
        point,
        value: claim.value,
    })
}

fn opening_statement(
    expected: &ExpectedStatement,
    claims: &[Claim; 4],
) -> Result<OpeningStatement, String> {
    Ok(fixed_opening_statement(
        GLOBAL_LOG,
        expected.setup_id,
        expected.commitment()?,
        raw_identity(expected)?,
        claims,
    ))
}

fn verify_gkr_claims(
    expected: &ExpectedStatement,
    specs: &[crate::daa_serializer_join::RoleSpec<'_>; 4],
    packet: &ProofPacket,
) -> Result<[Claim; 4], String> {
    let mut claims = Vec::with_capacity(4);
    for (index, spec) in specs.iter().enumerate() {
        if spec.role() != ROLE_ORDER[index] {
            return Err("consumer role order drift".into());
        }
        let decoded = sparse::decode_proof(spec.circuit(), spec.log_copies(), &packet.gkr[index])
            .map_err(|e| format!("DAA role {} decode: {e}", ROLE_NAMES[index]))?;
        let mut transcript = role_transcript(
            expected,
            index,
            spec.circuit(),
            spec.log_copies(),
            spec.selector(),
        )?;
        let claim = sparse::verify(spec.circuit(), spec.log_copies(), &decoded, &mut transcript)
            .map_err(|e| format!("DAA role {} verify: {e}", ROLE_NAMES[index]))?;
        claims.push(derived_claim(spec.role(), &claim)?);
    }
    claims
        .try_into()
        .map_err(|_| "DAA derived claim roster length".into())
}

fn fixed_opening_statement(
    log_n: usize,
    setup_id: [u8; 32],
    commitment: ArkGT,
    raw_id: [u8; 32],
    claims: &[Claim; 4],
) -> OpeningStatement {
    OpeningStatement {
        log_n,
        setup_id,
        commitment,
        corpus_id: Some(raw_id),
        claims: [
            claims[0].clone(),
            claims[1].clone(),
            claims[2].clone(),
            claims[3].clone(),
            claims[0].clone(),
            claims[1].clone(),
            claims[2].clone(),
        ],
    }
}

fn check_local_and_global_claim(
    source: &PackedFile,
    role: Role,
    input: &[Fr],
    claim: &InputClaim,
) -> Result<(), String> {
    let local = crate::gkr::mle(input, &claim.point).map_err(|e| e.to_string())?;
    if local != claim.value {
        return Err("GKR terminal differs from local input MLE".into());
    }
    let embedded = JoinPlan::embed_point(role, &claim.point)?;
    if source.evaluate(&embedded)? != claim.value {
        return Err("GKR terminal differs from common packed MLE".into());
    }
    Ok(())
}

fn compare_packed_source(source: &PackedFile, witness: &[Fr]) -> Result<(), String> {
    for copy in 0..64 {
        let packed = source.read_copy(1 << 16, copy)?;
        let start = copy * (1 << 16);
        if packed.as_slice() != &witness[start..start + (1 << 16)] {
            return Err(format!(
                "packed source differs from Boolean witness at copy {copy}"
            ));
        }
    }
    Ok(())
}

fn check_transcript_continuation(
    producer: &Transcript,
    consumer: &Transcript,
) -> Result<(), String> {
    if (
        producer.challenges(),
        producer.raw_queries(),
        producer.bytes_absorbed(),
    ) != (
        consumer.challenges(),
        consumer.raw_queries(),
        consumer.bytes_absorbed(),
    ) {
        return Err("producer/consumer transcript ledger differs".into());
    }
    let mut p = producer.clone();
    let mut c = consumer.clone();
    if p.try_challenge_scalar(b"daa-packet-continuation")?
        != c.try_challenge_scalar(b"daa-packet-continuation")?
    {
        return Err("producer/consumer transcript continuation differs".into());
    }
    Ok(())
}

fn hex_encode(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn hex_decode_canonical(text: &str) -> Result<Vec<u8>, String> {
    if text.len() % 2 != 0
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("hex must be even-length lowercase canonical text".into());
    }
    text.as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let digit = |b: u8| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
            Ok(digit(pair[0]) * 16 + digit(pair[1]))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{One, Zero};
    use serde::Deserialize;
    use std::{collections::HashMap, env, fs, fs::OpenOptions, io::Write};

    const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");
    const EXPECTED_FILE: &str = "daa-serializer-expected.json";
    const PROOF_FILE: &str = "daa-serializer-proof.bin";
    const PACKED_FILE: &str = "daa-serializer-packed.bits";

    #[derive(Deserialize)]
    struct Fixture {
        cases: Vec<Case>,
        headers: Vec<HeaderEntry>,
    }
    #[derive(Deserialize)]
    struct Case {
        child: u32,
        parent: u32,
        samples: Vec<u32>,
    }
    #[derive(Deserialize)]
    struct HeaderEntry {
        height: u32,
        raw_hex: String,
    }

    fn fixture_plan() -> (JoinPlan, Vec<u8>) {
        let fixture: Fixture = serde_json::from_str(FIXTURE).unwrap();
        let mut headers = HashMap::new();
        for entry in fixture.headers {
            headers.insert(entry.height, hex_decode_canonical(&entry.raw_hex).unwrap());
        }
        let case = fixture
            .cases
            .into_iter()
            .find(|case| case.child == 844_801)
            .unwrap();
        assert_eq!(case.parent + 1, case.child);
        let samples: [&[u8]; 9] = case
            .samples
            .iter()
            .map(|height| headers[height].as_slice())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let child = headers[&case.child].clone();
        (JoinPlan::build(samples, &child).unwrap(), child)
    }

    fn artifact_dir() -> Option<std::path::PathBuf> {
        env::var_os("NIPOPOW_DAA_PACKET_DIR").map(std::path::PathBuf::from)
    }

    fn create_new(path: &Path, bytes: &[u8]) {
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .unwrap();
        file.write_all(bytes).unwrap();
        file.sync_all().unwrap();
    }

    #[test]
    fn fixed_expected_and_packet_framing_reject_shape_mutants() {
        assert_eq!(
            PACKET_BYTES,
            9 + 5 * 5 + SECTION_BYTES.iter().sum::<usize>()
        );
        let packet = ProofPacket {
            gkr: std::array::from_fn(|index| vec![0; SECTION_BYTES[index]]),
            opening_batch: vec![0; SECTION_BYTES[4]],
        };
        let encoded = encode_packet(&packet).unwrap();
        assert_eq!(encoded.len(), PACKET_BYTES);
        assert_eq!(PACKET_BYTES, 49_919);
        assert_eq!(SECTION_BYTES, [4_576, 4_128, 4_576, 5_024, 31_581]);
        assert_eq!(decode_packet(&encoded).unwrap(), packet);
        let mut bad = encoded.clone();
        bad[0] ^= 1;
        assert!(decode_packet(&bad).is_err());
        let mut bad = encoded.clone();
        bad[8] += 1;
        assert!(decode_packet(&bad).is_err());
        let mut v1 = encoded.clone();
        v1[8] = 1;
        assert!(decode_packet(&v1).is_err());
        let mut bad = encoded.clone();
        bad[9] = 1;
        assert!(decode_packet(&bad).is_err());
        let mut bad = encoded.clone();
        bad[10..14].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(decode_packet(&bad).is_err());
        assert!(decode_packet(&encoded[..encoded.len() - 1]).is_err());
        let mut bad = encoded;
        bad.push(0);
        assert!(decode_packet(&bad).is_err());
    }

    #[test]
    fn expected_statement_is_canonical_and_bounded() {
        let (plan, _) = fixture_plan();
        let expected =
            ExpectedStatement::new(plan.raw_headers(), [3; 32], &ArkGT::default()).unwrap();
        let encoded = encode_expected(&expected).unwrap();
        assert_eq!(decode_expected(&encoded).unwrap(), expected);
        let mut unknown: serde_json::Value = serde_json::from_slice(&encoded).unwrap();
        unknown["unreviewed"] = serde_json::json!(true);
        assert!(decode_expected(&serde_json::to_vec(&unknown).unwrap()).is_err());
        let mut wrong = expected;
        wrong.roles[0] = "aliases".into();
        assert!(wrong.validate().is_err());
        let mut v1 = decode_expected(&encoded).unwrap();
        v1.version = 1;
        assert!(v1.validate().is_err());
        let mut wrong_length = decode_expected(&encoded).unwrap();
        wrong_length.raw_lengths[0] += 1;
        assert!(wrong_length.validate().is_err());
    }

    /// Run in a producer process after setting NIPOPOW_DAA_PACKET_DIR. It
    /// writes only create-new diagnostic artifacts; no path is baked into code.
    #[test]
    fn diagnostic_producer_when_artifact_directory_is_set() {
        let Some(dir) = artifact_dir() else { return };
        let (plan, _) = fixture_plan();
        let witness = plan.materialize_witness().unwrap();
        JoinPlan::validate_boolean_witness(&witness).unwrap();
        let setup_started = Instant::now();
        let setup = pcs::generate_setup(GLOBAL_LOG).unwrap();
        let setup_seconds = setup_started.elapsed().as_secs_f64();
        let pack_started = Instant::now();
        let packed_path = dir.join(PACKED_FILE);
        let source = JoinPlan::write_boolean_packed(&packed_path, &witness).unwrap();
        let pack_seconds = pack_started.elapsed().as_secs_f64();
        let commit_started = Instant::now();
        let committed = packed::commit(&source, &setup).unwrap();
        let commit_seconds = commit_started.elapsed().as_secs_f64();
        let expected =
            ExpectedStatement::new(plan.raw_headers(), setup.id, &committed.commitment).unwrap();
        let expected_bytes = encode_expected(&expected).unwrap();
        let (packet, producer_metrics) =
            prove_with_metrics(&plan, &expected, &witness, &source, &setup, &committed).unwrap();
        let packet_bytes = encode_packet(&packet).unwrap();
        println!(
            "DAA_PACKET_PRODUCER setup_seconds={setup_seconds:.3} pack_seconds={pack_seconds:.3} commit_seconds={commit_seconds:.3} metrics={producer_metrics:?}",
        );
        let specs = plan.role_specs().unwrap();
        let four_claims = verify_gkr_claims(&expected, &specs, &packet).unwrap();
        let wrong_opening_statement = OpeningStatement {
            log_n: GLOBAL_LOG,
            setup_id: setup.id,
            commitment: committed.commitment.clone(),
            corpus_id: Some(raw_identity(&expected).unwrap()),
            claims: [
                four_claims[0].clone(),
                four_claims[1].clone(),
                four_claims[2].clone(),
                four_claims[0].clone(),
                four_claims[0].clone(),
                four_claims[1].clone(),
                four_claims[2].clone(),
            ],
        };
        let negative_started = Instant::now();
        let (wrong_opening, _, _) =
            opening_batch::prove(&source, &committed, &setup, &wrong_opening_statement).unwrap();
        let wrong_opening_decoded = opening_batch::decode_proof(
            &opening_batch::encode_proof(&wrong_opening, GLOBAL_LOG).unwrap(),
            GLOBAL_LOG,
        )
        .unwrap();
        opening_batch::verify(&wrong_opening_statement, &setup, &wrong_opening_decoded).unwrap();
        let mut wrong_roster_packet = packet.clone();
        wrong_roster_packet.opening_batch =
            opening_batch::encode_proof(&wrong_opening, GLOBAL_LOG).unwrap();
        let wrong_roster_bytes = encode_packet(&wrong_roster_packet).unwrap();
        let wrong_roster_error = verify(&expected_bytes, &wrong_roster_bytes).unwrap_err();
        assert!(
            wrong_roster_error.contains("opening batch rejected"),
            "wrong roster did not reach final PCS gate: {wrong_roster_error}"
        );
        println!(
            "DAA_PACKET_NEGATIVE duplicate_alias_opening_seconds={:.3} accepted=false",
            negative_started.elapsed().as_secs_f64()
        );

        let mut wrong_setup = expected.clone();
        wrong_setup.setup_id[0] ^= 1;
        let wrong_setup_bytes = serde_json::to_vec_pretty(&wrong_setup).unwrap();
        let error = verify(&wrong_setup_bytes, &packet_bytes).unwrap_err();
        assert!(
            error.contains("does not match admitted key"),
            "wrong setup missed key guard: {error}"
        );

        let mut wrong_domain = expected.clone();
        wrong_domain.domain.push_str("-foreign");
        let wrong_domain_bytes = serde_json::to_vec_pretty(&wrong_domain).unwrap();
        let error = verify(&wrong_domain_bytes, &packet_bytes).unwrap_err();
        assert!(
            error.contains("profile, domain"),
            "foreign domain missed profile guard: {error}"
        );

        let mut wrong_commitment = expected.clone();
        wrong_commitment.commitment_hex =
            hex_encode(&pcs::encode_commitment(&ArkGT::default()).unwrap());
        assert_ne!(wrong_commitment.commitment_hex, expected.commitment_hex);
        let wrong_commitment_bytes = encode_expected(&wrong_commitment).unwrap();
        let error = verify(&wrong_commitment_bytes, &packet_bytes).unwrap_err();
        assert!(
            error.contains("serializer-a verify"),
            "wrong common commitment missed GKR binding: {error}"
        );

        let mut noncanonical_scalar = packet.clone();
        noncanonical_scalar.gkr[0][..32].fill(0xff);
        let error = verify(
            &expected_bytes,
            &encode_packet(&noncanonical_scalar).unwrap(),
        )
        .unwrap_err();
        assert!(
            error.contains("serializer-a decode"),
            "noncanonical GKR scalar missed decoder: {error}"
        );

        let specs = plan.role_specs().unwrap();
        let mut changed_gkr = packet.clone();
        let mut role_proof = sparse::decode_proof(
            specs[0].circuit(),
            specs[0].log_copies(),
            &changed_gkr.gkr[0],
        )
        .unwrap();
        role_proof.layers[0].rounds[0][0] += Fr::one();
        changed_gkr.gkr[0] = crate::gkr::encode_proof(&role_proof).unwrap();
        let error = verify(&expected_bytes, &encode_packet(&changed_gkr).unwrap()).unwrap_err();
        assert!(
            error.contains("serializer-a verify"),
            "canonical GKR mutant missed verifier: {error}"
        );

        let mut changed_opening = packet.clone();
        let mut opening =
            opening_batch::decode_proof(&changed_opening.opening_batch, GLOBAL_LOG).unwrap();
        opening.terminal += Fr::one();
        changed_opening.opening_batch = opening_batch::encode_proof(&opening, GLOBAL_LOG).unwrap();
        let error = verify(&expected_bytes, &encode_packet(&changed_opening).unwrap()).unwrap_err();
        assert!(
            error.contains("opening batch rejected"),
            "canonical opening terminal mutant missed opening verifier: {error}"
        );

        let mut changed_source = expected.clone();
        let mut changed_raw = changed_source.raw_headers().unwrap()[0].clone();
        let mut changed_header = ergo_header_core::Header::decode(&changed_raw, None).unwrap();
        changed_header.parent_id[0] ^= 1;
        changed_raw = changed_header.encode().unwrap();
        changed_source.raw_headers_hex[0] = hex_encode(&changed_raw);
        changed_source.raw_lengths[0] = changed_raw.len() as u16;
        let changed_source_bytes = encode_expected(&changed_source).unwrap();
        let error = verify(&changed_source_bytes, &packet_bytes).unwrap_err();
        assert!(
            error.contains("verify"),
            "changed expected raw source rejected before GKR consumer: {error}"
        );
        create_new(&dir.join(EXPECTED_FILE), &expected_bytes);
        create_new(&dir.join(PROOF_FILE), &packet_bytes);
    }

    /// Run in a separate fresh verifier process after the producer test.
    #[test]
    fn diagnostic_fresh_consumer_when_artifact_directory_is_set() {
        let Some(dir) = artifact_dir() else { return };
        let expected = fs::read(dir.join(EXPECTED_FILE)).unwrap();
        let packet = fs::read(dir.join(PROOF_FILE)).unwrap();
        let report = verify(&expected, &packet).unwrap();
        assert_eq!(report.proof_bytes, PACKET_BYTES);
        assert_eq!(report.mandatory_gkr_roles, 4);
        assert_eq!(report.derived_opening_claims, 7);
        assert_eq!(report.opening_batches, 1);
        println!("DAA_PACKET_CONSUMER {report:?}");
    }

    #[test]
    fn boolean_packing_rejects_active_and_upper_half_non_boolean_coordinates() {
        let mut witness = vec![Fr::zero(); 1 << GLOBAL_LOG];
        witness[17] = Fr::from(2u64);
        assert!(JoinPlan::validate_boolean_witness(&witness).is_err());
        witness[17] = Fr::zero();
        witness[(1 << GLOBAL_LOG) - 1] = Fr::from(7u64);
        assert!(JoinPlan::validate_boolean_witness(&witness).is_err());
        witness[(1 << GLOBAL_LOG) - 1] = Fr::one();
        assert!(JoinPlan::validate_boolean_witness(&witness).is_ok());
    }

    #[test]
    fn fixed_roster_rejects_omission_substitution_and_reordering() {
        assert!(JoinPlan::validate_mandatory_roster(&ROLE_ORDER).is_ok());
        assert!(JoinPlan::validate_mandatory_roster(&ROLE_ORDER[..3]).is_err());
        assert!(JoinPlan::validate_mandatory_roster(&[
            Role::SerializerA,
            Role::SerializerB,
            Role::Daa,
            Role::Daa
        ])
        .is_err());
        assert!(JoinPlan::validate_mandatory_roster(&[
            Role::SerializerB,
            Role::SerializerA,
            Role::Daa,
            Role::Aliases
        ])
        .is_err());
    }
}

//! Serialized verifier packet for four private headers and one DAA carry edge.
//!
//! This packet carries public endpoints and a single common GKR/PCS proof. It
//! contains no interior RAWs or interior digest pins. Its scope is a diagnostic
//! local join, not full-history verification, PoW/order validation, or a
//! production security claim. GKR/PCS here does not provide a confidentiality
//! or zero-knowledge guarantee.

use crate::{
    four_header_link_join::{
        Plan, BASE_ROW_LOG, FAMILY_LOG, INPUT_LOG, LOCAL_LOG, MEMBER_ROW_BITS, SLOT_LOG,
        TOTAL_TERMS, FIXED_HEIGHTS, CARRY_EDGE, EXTRA_TERMS, RELEASED_TERMS,
    },
    gkr::{self, InputClaim},
    packed::{self, PackedCommitted, PackedFile},
    pcs::{self, Setup},
    sparse_stream_roster,
    transcript::Transcript,
    verifier_key::AdmittedVerifierKey,
};
use ark_bn254::{Fr, G1Projective, G2Projective};
use ark_ec::pairing::PairingOutput;
use ark_ff::Zero;
use ark_serialize::CanonicalSerialize;
use serde::{Deserialize, Serialize};
use std::{path::Path, time::Instant};

const FAMILY: &str = "four-private-consecutive-headers-decoded-carry-one-gkr-one-pcs-v2";
const PROFILE: &str = "four-header-link-decoded-carry-log22-row24-v2";
const DOMAIN: &[u8] = b"nipopow-four-header-link-decoded-carry-packet-v2";
const MAGIC: &[u8; 8] = b"FVHLAP02";
const VERSION: u8 = 2;
const EXPECTED_CAP: usize = 16_384;
const MAX_PACKET_CAP: usize = 65_536;
const POST_PCS_BYTES: usize = 32;
const ADJACENCY_TERMS: usize = 1_280;
const BOUNDARY_TERMS: usize = 1_893_452 - RELEASED_TERMS;
const CORE_TERMS: usize = 5_519_360;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExpectedStatement {
    version: u8,
    family: String,
    profile: String,
    start_hex: String,
    tip_hex: String,
    input_log: u8,
    row_log: u8,
    slot_log: u8,
    base_row_log: u8,
    family_log: u8,
    member_row_bits: [u8; 4],
    adjacency_terms: u32,
    boundary_terms: u32,
    core_terms: u32,
    carry_height_terms: u32,
    fixed_heights: [u32; 4],
    carry_edge: [u8; 2],
    total_terms: u64,
    descriptor_hex: String,
    setup_id_hex: String,
    commitment_hex: String,
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(text: &str) -> Result<Vec<u8>, String> {
    if text.len() % 2 != 0
        || !text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("noncanonical lowercase hex".into());
    }
    (0..text.len())
        .step_by(2)
        .map(|index| {
            u8::from_str_radix(&text[index..index + 2], 16).map_err(|error| error.to_string())
        })
        .collect()
}

fn codec_section_lengths() -> Result<[usize; 3], String> {
    let scalar_bytes = Fr::zero().compressed_size();
    let gkr_scalars = INPUT_LOG
        .checked_mul(7)
        .and_then(|count| count.checked_add(3))
        .ok_or("GKR section size overflow")?;
    let gkr_bytes = gkr_scalars
        .checked_mul(scalar_bytes)
        .ok_or("GKR section size overflow")?;

    let gt_bytes = PairingOutput::<ark_bn254::Bn254>::zero().compressed_size();
    let g1_bytes = G1Projective::zero().compressed_size();
    let g2_bytes = G2Projective::zero().compressed_size();
    let sigma = INPUT_LOG.div_ceil(2);
    let pcs_bytes = 2usize
        .checked_mul(gt_bytes)
        .and_then(|bytes| bytes.checked_add(g1_bytes))
        .and_then(|bytes| bytes.checked_add(4))
        .and_then(|bytes| {
            sigma
                .checked_mul(6 * gt_bytes + 3 * g1_bytes + 3 * g2_bytes)
                .and_then(|rounds| bytes.checked_add(rounds))
        })
        .and_then(|bytes| bytes.checked_add(1 + g1_bytes + g2_bytes + 8))
        .ok_or("PCS section size overflow")?;
    Ok([gkr_bytes, pcs_bytes, POST_PCS_BYTES])
}

fn packet_len() -> Result<usize, String> {
    codec_section_lengths()?
        .into_iter()
        .try_fold(9usize, |total, section| {
            total
                .checked_add(5 + section)
                .ok_or_else(|| "packet size overflow".into())
        })
}

impl ExpectedStatement {
    pub(crate) fn new(
        plan: &Plan,
        setup: &Setup,
        committed: &PackedCommitted,
    ) -> Result<Self, String> {
        let statement = Self {
            version: VERSION,
            family: FAMILY.into(),
            profile: PROFILE.into(),
            start_hex: hex(&plan.start()),
            tip_hex: hex(&plan.tip()),
            input_log: INPUT_LOG as u8,
            row_log: (BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG) as u8,
            slot_log: SLOT_LOG as u8,
            base_row_log: BASE_ROW_LOG as u8,
            family_log: FAMILY_LOG as u8,
            member_row_bits: MEMBER_ROW_BITS.map(|bits| bits as u8),
            adjacency_terms: ADJACENCY_TERMS as u32,
            boundary_terms: BOUNDARY_TERMS as u32,
            core_terms: CORE_TERMS as u32,
            carry_height_terms: EXTRA_TERMS as u32,
            fixed_heights: FIXED_HEIGHTS,
            carry_edge: CARRY_EDGE.map(|slot| slot as u8),
            total_terms: TOTAL_TERMS as u64,
            descriptor_hex: hex(&plan.descriptor()),
            setup_id_hex: hex(&setup.id),
            commitment_hex: hex(&pcs::encode_commitment(&committed.commitment)?),
        };
        statement.validate_shape()?;
        statement.validate_plan(plan)?;
        Ok(statement)
    }

    fn validate_shape(&self) -> Result<(), String> {
        if self.version != VERSION
            || self.family != FAMILY
            || self.profile != PROFILE
            || self.input_log as usize != INPUT_LOG
            || self.row_log as usize != BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG
            || self.slot_log as usize != SLOT_LOG
            || self.base_row_log as usize != BASE_ROW_LOG
            || self.family_log as usize != FAMILY_LOG
            || self.member_row_bits.map(usize::from) != MEMBER_ROW_BITS
            || self.adjacency_terms as usize != ADJACENCY_TERMS
            || self.boundary_terms as usize != BOUNDARY_TERMS
            || self.core_terms as usize != CORE_TERMS
            || self.carry_height_terms as usize != EXTRA_TERMS
            || self.fixed_heights != FIXED_HEIGHTS
            || self.carry_edge.map(usize::from) != CARRY_EDGE
            || self.total_terms as usize != TOTAL_TERMS
        {
            return Err("four-header expected profile/dimension/count mismatch".into());
        }
        if unhex(&self.start_hex)?.len() != 32 || unhex(&self.tip_hex)?.len() != 32 {
            return Err("four-header endpoint length mismatch".into());
        }
        if unhex(&self.descriptor_hex)?.len() != 32 || unhex(&self.setup_id_hex)?.len() != 32 {
            return Err("four-header descriptor/setup ID length mismatch".into());
        }
        let commitment = unhex(&self.commitment_hex)?;
        if commitment.len() != PairingOutput::<ark_bn254::Bn254>::zero().compressed_size() {
            return Err("four-header commitment length mismatch".into());
        }
        Ok(())
    }

    fn validate_commitment(&self) -> Result<(), String> {
        pcs::decode_commitment(&unhex(&self.commitment_hex)?)
            .map_err(|error| format!("four-header commitment codec: {error}"))?;
        Ok(())
    }

    fn validate_plan(&self, plan: &Plan) -> Result<(), String> {
        self.validate_shape()?;
        if unhex(&self.start_hex)?.as_slice() != plan.start().as_slice()
            || unhex(&self.tip_hex)?.as_slice() != plan.tip().as_slice()
            || unhex(&self.descriptor_hex)?.as_slice() != plan.descriptor().as_slice()
            || plan.term_count() != TOTAL_TERMS
        {
            return Err("four-header expected statement does not match canonical plan".into());
        }
        Ok(())
    }
}

pub(crate) fn encode_expected(expected: &ExpectedStatement) -> Result<Vec<u8>, String> {
    expected.validate_shape()?;
    expected.validate_commitment()?;
    let bytes = serde_json::to_vec_pretty(expected).map_err(|error| error.to_string())?;
    if bytes.is_empty() || bytes.len() > EXPECTED_CAP {
        return Err("four-header expected cap exceeded".into());
    }
    Ok(bytes)
}

fn decode_expected(bytes: &[u8]) -> Result<ExpectedStatement, String> {
    if bytes.is_empty() || bytes.len() > EXPECTED_CAP {
        return Err("four-header expected length/cap rejected".into());
    }
    let expected: ExpectedStatement =
        serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
    expected.validate_shape()?;
    let canonical = serde_json::to_vec_pretty(&expected).map_err(|error| error.to_string())?;
    if canonical != bytes {
        return Err("noncanonical four-header expected JSON".into());
    }
    Ok(expected)
}

#[derive(Clone)]
struct Packet {
    gkr: Vec<u8>,
    pcs: Vec<u8>,
    post_pcs: Vec<u8>,
}

fn encode_packet(packet: &Packet) -> Result<Vec<u8>, String> {
    let sizes = codec_section_lengths()?;
    let mut bytes = Vec::with_capacity(packet_len()?);
    bytes.extend_from_slice(MAGIC);
    bytes.push(VERSION);
    for (index, (section, expected_size)) in [&packet.gkr, &packet.pcs, &packet.post_pcs]
        .into_iter()
        .zip(sizes)
        .enumerate()
    {
        if section.len() != expected_size {
            return Err(format!(
                "four-header packet section {index} length mismatch"
            ));
        }
        bytes.push(index as u8);
        bytes.extend_from_slice(&(expected_size as u32).to_le_bytes());
        bytes.extend_from_slice(section);
    }
    if bytes.len() > MAX_PACKET_CAP || bytes.len() != packet_len()? {
        return Err("four-header packet size/cap mismatch".into());
    }
    Ok(bytes)
}

fn decode_packet(bytes: &[u8]) -> Result<Packet, String> {
    let sizes = codec_section_lengths()?;
    if bytes.len() > MAX_PACKET_CAP || bytes.len() != packet_len()? {
        return Err("four-header packet length/cap/EOF rejected".into());
    }
    if &bytes[..8] != MAGIC || bytes[8] != VERSION {
        return Err("four-header packet magic/version mismatch".into());
    }
    let mut at = 9usize;
    let mut ranges = [(0usize, 0usize); 3];
    for (index, expected_size) in sizes.into_iter().enumerate() {
        if bytes[at] as usize != index {
            return Err("four-header packet section tag/order mismatch".into());
        }
        let size = u32::from_le_bytes(bytes[at + 1..at + 5].try_into().unwrap()) as usize;
        if size != expected_size {
            return Err("four-header packet section length mismatch".into());
        }
        at += 5;
        ranges[index] = (at, at + size);
        at += size;
    }
    if at != bytes.len() {
        return Err("four-header packet trailing bytes".into());
    }
    let section = |index: usize| bytes[ranges[index].0..ranges[index].1].to_vec();
    Ok(Packet {
        gkr: section(0),
        pcs: section(1),
        post_pcs: section(2),
    })
}

fn bind(plan: &Plan, setup_id: &[u8; 32], commitment: &[u8], transcript: &mut Transcript) {
    transcript.append_bytes(b"packet-family", FAMILY.as_bytes());
    transcript.append_bytes(b"packet-domain", DOMAIN);
    transcript.append_bytes(b"packet-magic", MAGIC);
    transcript.append_u64(b"packet-version", VERSION as u64);
    transcript.append_u64(b"mandatory-gkr", 1);
    transcript.append_u64(b"mandatory-pcs", 1);
    plan.bind(transcript);
    transcript.append_bytes(b"admitted-log22-setup-id", setup_id);
    transcript.append_bytes(b"common-packed-commitment", commitment);
}

fn verify_gkr(
    plan: &Plan,
    expected: &ExpectedStatement,
    packet: &Packet,
) -> Result<(InputClaim, Transcript), String> {
    verify_gkr_with_domain(plan, expected, packet, DOMAIN)
}

fn verify_gkr_with_domain(
    plan: &Plan,
    expected: &ExpectedStatement,
    packet: &Packet,
    domain: &[u8],
) -> Result<(InputClaim, Transcript), String> {
    let proof = gkr::decode_dimensions(&[INPUT_LOG], &packet.gkr)
        .map_err(|error| format!("four-header GKR codec: {error}"))?;
    if gkr::encode_proof(&proof)? != packet.gkr {
        return Err("noncanonical four-header GKR codec".into());
    }
    let setup_id: [u8; 32] = unhex(&expected.setup_id_hex)?
        .try_into()
        .map_err(|_| "setup ID length")?;
    let commitment = unhex(&expected.commitment_hex)?;
    let mut transcript = Transcript::new(domain);
    let claim = gkr::verify_with_wiring(
        &[INPUT_LOG],
        1usize << (BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG),
        &proof,
        &mut transcript,
        |transcript| bind(plan, &setup_id, &commitment, transcript),
        |_, r, u, v| {
            plan.coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        },
    )
    .map_err(|error| format!("four-header GKR: {error}"))?;
    Ok((claim, transcript))
}

/// Verify serialized public metadata and proof bytes against endpoints supplied
/// by the caller's verifier contract. These endpoints are compared before the
/// canonical plan is reconstructed from them.
pub(crate) fn verify_with_key(
    verifier_start: [u8; 32],
    verifier_tip: [u8; 32],
    expected_bytes: &[u8],
    packet_bytes: &[u8],
    key: &AdmittedVerifierKey,
) -> Result<serde_json::Value, String> {
    let started = Instant::now();
    let expected = decode_expected(expected_bytes)?;
    if unhex(&expected.start_hex)?.as_slice() != verifier_start.as_slice()
        || unhex(&expected.tip_hex)?.as_slice() != verifier_tip.as_slice()
    {
        return Err("four-header caller endpoints differ from expected statement".into());
    }
    expected.validate_commitment()?;
    if key.log_n() != INPUT_LOG || unhex(&expected.setup_id_hex)?.as_slice() != key.id().as_slice()
    {
        return Err("four-header admitted diagnostic key mismatch".into());
    }
    let packet = decode_packet(packet_bytes)?;
    let plan = Plan::build(verifier_start, verifier_tip)?;
    expected.validate_plan(&plan)?;
    let (claim, mut transcript) = verify_gkr(&plan, &expected, &packet)?;
    let commitment = pcs::decode_commitment(&unhex(&expected.commitment_hex)?)?;
    let proof = pcs::decode_proof(&packet.pcs, INPUT_LOG)
        .map_err(|error| format!("four-header PCS codec: {error}"))?;
    if pcs::encode_proof(&proof)? != packet.pcs {
        return Err("noncanonical four-header PCS codec".into());
    }
    pcs::verify_admitted(
        commitment,
        claim.value,
        &claim.point,
        &proof,
        key,
        &mut transcript,
    )
    .map_err(|error| format!("four-header PCS: {error}"))?;
    let post = pcs::encode(&transcript.challenge_scalar(b"four-header-post-pcs"))?;
    if post != packet.post_pcs {
        return Err("four-header post-PCS transcript artifact mismatch".into());
    }
    Ok(serde_json::json!({
        "family": FAMILY,
        "profile": PROFILE,
        "input_log": INPUT_LOG,
        "row_log": BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG,
        "term_count": TOTAL_TERMS,
        "fixed_heights": FIXED_HEIGHTS,
        "decoded_carry_edge": CARRY_EDGE,
        "gkr_proofs": 1,
        "pcs_openings": 1,
        "packet_bytes": packet_bytes.len(),
        "verify_seconds": started.elapsed().as_secs_f64(),
        "claim_ceiling": "four canonical header hashes/links, fixed heights 3072..3075 and decoded-difficulty Carry 3073->3074 under one X/C; excludes other DAA, work, PoW, timestamp ordering, full history and production security; diagnostic BN254"
    }))
}

fn read_owner(source: &PackedFile, slot: usize) -> Result<Vec<Fr>, String> {
    if source.input_len() != 1usize << INPUT_LOG || slot >= 1usize << SLOT_LOG {
        return Err("four-header packed owner bounds invalid".into());
    }
    let mut values = Vec::with_capacity(1usize << LOCAL_LOG);
    for chunk in 0..(1usize << (LOCAL_LOG - 16)) {
        values.extend(source.read_copy(1usize << 16, slot * (1usize << (LOCAL_LOG - 16)) + chunk)?);
    }
    if values.len() != 1usize << LOCAL_LOG {
        return Err("four-header packed owner width changed".into());
    }
    Ok(values)
}

pub(crate) fn prove(
    plan: &Plan,
    expected: &ExpectedStatement,
    source: &PackedFile,
    setup: &Setup,
    committed: &PackedCommitted,
) -> Result<(Vec<u8>, serde_json::Value), String> {
    expected.validate_plan(plan)?;
    if setup.log_n != INPUT_LOG
        || source.input_len() != 1usize << INPUT_LOG
        || unhex(&expected.setup_id_hex)?.as_slice() != setup.id.as_slice()
        || committed.nu != INPUT_LOG / 2
        || committed.sigma != INPUT_LOG.div_ceil(2)
        || pcs::encode_commitment(&committed.commitment)? != unhex(&expected.commitment_hex)?
    {
        return Err("four-header producer setup/statement mismatch".into());
    }
    let setup_id = setup.id;
    let commitment = unhex(&expected.commitment_hex)?;
    let mut transcript = Transcript::new(DOMAIN);
    let mark = Instant::now();
    // The streamed engine takes a local copy width; slot bits supply the rest.
    if LOCAL_LOG + SLOT_LOG != INPUT_LOG {
        return Err("four-header local/global prover dimension mismatch".into());
    }
    let (proof, claim, incremental_u, incremental_v) = sparse_stream_roster::prove_edge_terms(
        LOCAL_LOG,
        SLOT_LOG,
        BASE_ROW_LOG,
        FAMILY_LOG,
        &MEMBER_ROW_BITS,
        |left, slot, sink| plan.visit_endpoint(left, slot, sink),
        |slot| read_owner(source, slot),
        &mut transcript,
        |transcript| bind(plan, &setup_id, &commitment, transcript),
        |r, u, v| plan.coefficients(r, u, v),
    )?;
    let gkr_seconds = mark.elapsed().as_secs_f64();
    if source.evaluate(&claim.point)? != claim.value {
        return Err("four-header common witness claim mismatch".into());
    }
    let mark = Instant::now();
    let opening = packed::open(committed, source, &claim.point, setup, &mut transcript)?;
    let pcs_seconds = mark.elapsed().as_secs_f64();
    let packet = Packet {
        gkr: gkr::encode_proof(&proof)?,
        pcs: pcs::encode_proof(&opening)?,
        post_pcs: pcs::encode(&transcript.challenge_scalar(b"four-header-post-pcs"))?,
    };
    let packet_bytes = encode_packet(&packet)?;
    let packet_len = packet_bytes.len();
    Ok((
        packet_bytes,
        serde_json::json!({
            "family": FAMILY,
            "profile": PROFILE,
            "input_log": INPUT_LOG,
            "row_log": BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG,
            "term_count": plan.term_count(),
            "gkr_seconds": gkr_seconds,
            "pcs_seconds": pcs_seconds,
            "gkr_proofs": 1,
            "pcs_openings": 1,
            "packet_bytes": packet_len,
            "incremental_u": incremental_u,
            "incremental_v": incremental_v,
            "claim_ceiling": "four canonical header hashes/links, fixed heights 3072..3075 and decoded-difficulty Carry 3073->3074 under one X/C; excludes other DAA, work, PoW, timestamp ordering, full history and production security; diagnostic BN254"
        }),
    ))
}

pub(crate) fn write_create_new(path: &Path, bytes: &[u8]) -> Result<(), String> {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("four-header artifact create: {error}"))?;
    file.write_all(bytes)
        .map_err(|error| format!("four-header artifact write: {error}"))?;
    file.sync_all()
        .map_err(|error| format!("four-header artifact sync: {error}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn packet_codec_lengths_derive_from_log22_codecs() {
        let lengths = codec_section_lengths().unwrap();
        assert_eq!(
            lengths[0],
            (7 * INPUT_LOG + 3) * Fr::zero().compressed_size()
        );
        assert_eq!(lengths[2], POST_PCS_BYTES);
        assert_eq!(
            packet_len().unwrap(),
            9 + lengths.iter().map(|size| 5 + size).sum::<usize>()
        );
        assert!(packet_len().unwrap() <= MAX_PACKET_CAP);
    }

    #[test]
    fn strict_packet_framing_rejects_magic_order_size_eof_and_tail() {
        let good = Packet {
            gkr: vec![0; codec_section_lengths().unwrap()[0]],
            pcs: vec![0; codec_section_lengths().unwrap()[1]],
            post_pcs: vec![0; POST_PCS_BYTES],
        };
        let bytes = encode_packet(&good).unwrap();
        assert_eq!(decode_packet(&bytes).unwrap().gkr.len(), good.gkr.len());
        for index in [0usize, 8, 9, 10] {
            let mut changed = bytes.clone();
            changed[index] ^= 1;
            assert!(
                decode_packet(&changed).is_err(),
                "single packet byte {index} must reject"
            );
        }
        let mut payload_changed = bytes.clone();
        *payload_changed.last_mut().unwrap() ^= 1;
        assert!(
            decode_packet(&payload_changed).is_ok(),
            "section framing leaves proof semantics to codecs"
        );
        assert!(decode_packet(&bytes[..bytes.len() - 1]).is_err());
        let mut trailing = bytes;
        trailing.push(0);
        assert!(decode_packet(&trailing).is_err());
    }

    #[test]
    fn expected_json_is_canonical_and_denies_duplicate_unknown_fields() {
        let mut statement = ExpectedStatement {
            version: VERSION,
            family: FAMILY.into(),
            profile: PROFILE.into(),
            start_hex: "00".repeat(32),
            tip_hex: "11".repeat(32),
            input_log: INPUT_LOG as u8,
            row_log: (BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG) as u8,
            slot_log: SLOT_LOG as u8,
            base_row_log: BASE_ROW_LOG as u8,
            family_log: FAMILY_LOG as u8,
            member_row_bits: MEMBER_ROW_BITS.map(|value| value as u8),
            adjacency_terms: ADJACENCY_TERMS as u32,
            boundary_terms: BOUNDARY_TERMS as u32,
            core_terms: CORE_TERMS as u32,
            carry_height_terms: EXTRA_TERMS as u32,
            fixed_heights: FIXED_HEIGHTS,
            carry_edge: CARRY_EDGE.map(|slot| slot as u8),
            total_terms: TOTAL_TERMS as u64,
            descriptor_hex: "22".repeat(32),
            setup_id_hex: "33".repeat(32),
            commitment_hex: hex(&pcs::encode(
                &ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero(),
            )
            .unwrap()),
        };
        let encoded = encode_expected(&statement).unwrap();
        assert_eq!(decode_expected(&encoded).unwrap(), statement);
        let mut whitespace = encoded.clone();
        whitespace.push(b' ');
        assert!(decode_expected(&whitespace).is_err());
        let mut duplicate = encoded.clone();
        let duplicate_field = b"\n  \"version\": 1,";
        duplicate.splice(1..1, duplicate_field.iter().copied());
        assert!(decode_expected(&duplicate).is_err());
        let mut unknown = encoded.clone();
        let close = unknown.iter().rposition(|byte| *byte == b'}').unwrap();
        unknown.splice(close..close, b",\n  \"raw_headers\": []\n".iter().copied());
        assert!(decode_expected(&unknown).is_err());
        assert!(decode_expected(&vec![b' '; EXPECTED_CAP + 1]).is_err());
        statement.start_hex = "AA".repeat(32);
        assert!(statement.validate_shape().is_err());
    }

    #[test]
    fn expected_fixed_profile_and_each_mandatory_dimension_or_count_are_single_fault() {
        let base = ExpectedStatement {
            version: VERSION,
            family: FAMILY.into(),
            profile: PROFILE.into(),
            start_hex: "00".repeat(32),
            tip_hex: "11".repeat(32),
            input_log: INPUT_LOG as u8,
            row_log: (BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG) as u8,
            slot_log: SLOT_LOG as u8,
            base_row_log: BASE_ROW_LOG as u8,
            family_log: FAMILY_LOG as u8,
            member_row_bits: MEMBER_ROW_BITS.map(|value| value as u8),
            adjacency_terms: ADJACENCY_TERMS as u32,
            boundary_terms: BOUNDARY_TERMS as u32,
            core_terms: CORE_TERMS as u32,
            carry_height_terms: EXTRA_TERMS as u32,
            fixed_heights: FIXED_HEIGHTS,
            carry_edge: CARRY_EDGE.map(|slot| slot as u8),
            total_terms: TOTAL_TERMS as u64,
            descriptor_hex: "22".repeat(32),
            setup_id_hex: "33".repeat(32),
            commitment_hex: hex(&pcs::encode(&PairingOutput::<ark_bn254::Bn254>::zero()).unwrap()),
        };
        assert!(base.validate_shape().is_ok());
        let mut cases: Vec<(&str, ExpectedStatement)> = Vec::new();
        macro_rules! fault {
            ($name:literal, $field:ident, $value:expr) => {{
                let mut v = base.clone();
                v.$field = $value;
                cases.push(($name, v));
            }};
        }
        fault!("version", version, VERSION + 1);
        fault!("family", family, "other".into());
        fault!("profile", profile, "other".into());
        fault!("input_log", input_log, INPUT_LOG as u8 - 1);
        fault!(
            "row_log",
            row_log,
            (BASE_ROW_LOG + SLOT_LOG + FAMILY_LOG) as u8 - 1
        );
        fault!("slot_log", slot_log, SLOT_LOG as u8 - 1);
        fault!("base_row_log", base_row_log, BASE_ROW_LOG as u8 - 1);
        fault!("family_log", family_log, FAMILY_LOG as u8 - 1);
        fault!("member_row_bits", member_row_bits, [9, 19, 19, 20]);
        fault!(
            "adjacency_terms",
            adjacency_terms,
            ADJACENCY_TERMS as u32 - 1
        );
        fault!("boundary_terms", boundary_terms, BOUNDARY_TERMS as u32 - 1);
        fault!("core_terms", core_terms, CORE_TERMS as u32 - 1);
        fault!("carry_terms", carry_height_terms, EXTRA_TERMS as u32 - 1);
        fault!("carry_edge", carry_edge, [2, 3]);
        fault!("fixed_height", fixed_heights, [3072, 3073, 3075, 3076]);
        fault!("old_profile", profile, "four-header-link-log22-row24-v1".into());
        fault!("total_terms", total_terms, TOTAL_TERMS as u64 - 1);
        fault!("descriptor_length", descriptor_hex, "22".repeat(31));
        fault!("setup_id_length", setup_id_hex, "33".repeat(31));
        fault!("commitment_length", commitment_hex, "44".repeat(32));
        for (name, changed) in cases {
            assert!(
                changed.validate_shape().is_err(),
                "single fault {name} must reject"
            );
        }
    }
}

#[cfg(test)]
mod integration_tests {
    use super::*;
    use crate::four_header_link_join::{fixture_raws, FIXTURE_START, FIXTURE_TIP, ROW_LOG};
    use ark_ff::One;
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    use std::{
        path::{Path, PathBuf},
        time::Instant,
    };

    const INPUT_ENV: &str = "NIPOPOW_FOUR_LINK_PACKET_INPUT_DIR";
    const OUTPUT_ENV: &str = "NIPOPOW_FOUR_LINK_PACKET_DIR";

    fn temp_dir(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "nipopow-four-link-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn output_dir() -> PathBuf {
        let path = std::env::var_os(OUTPUT_ENV)
            .map(PathBuf::from)
            .unwrap_or_else(|| temp_dir("producer"));
        std::fs::create_dir_all(&path).unwrap();
        path
    }

    const PINNED_KEY: &[u8] = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");

    fn pinned_key() -> AdmittedVerifierKey {
        crate::verifier_key::admit(INPUT_LOG, PINNED_KEY).unwrap()
    }

    fn key(setup: &Setup) -> AdmittedVerifierKey {
        let bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
        assert_eq!(bytes.as_slice(), PINNED_KEY, "generated setup key drifted");
        let admitted = pinned_key();
        assert_eq!(&setup.id, admitted.id(), "generated setup identity drifted");
        admitted
    }

    fn write_new(path: &Path, bytes: &[u8]) {
        write_create_new(path, bytes).unwrap();
    }

    fn verify_error(
        start: [u8; 32],
        tip: [u8; 32],
        expected: &[u8],
        packet: &[u8],
        key: &AdmittedVerifierKey,
        marker: &str,
        label: &str,
    ) -> String {
        let error = verify_with_key(start, tip, expected, packet, key).unwrap_err();
        assert!(
            error.starts_with(marker),
            "{label}: expected error prefix {marker:?}, received {error:?}"
        );
        error
    }

    fn encoded(expected: &ExpectedStatement) -> Vec<u8> {
        encode_expected(expected).unwrap()
    }

    fn flip_hex(text: &str) -> String {
        let mut bytes = unhex(text).unwrap();
        bytes[0] ^= 1;
        hex(&bytes)
    }

    fn first_challenge(plan: &Plan, expected: &ExpectedStatement, domain: &[u8]) -> Vec<Fr> {
        let setup_id: [u8; 32] = unhex(&expected.setup_id_hex).unwrap().try_into().unwrap();
        let commitment = unhex(&expected.commitment_hex).unwrap();
        let mut transcript = Transcript::new(domain);
        bind(plan, &setup_id, &commitment, &mut transcript);
        gkr::output_point(1usize << ROW_LOG, &mut transcript)
    }

    fn expected_faults(
        expected: &ExpectedStatement,
        packet: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = 0;
        macro_rules! fault {
            ($name:literal, $field:ident, $value:expr) => {{
                let mut changed = expected.clone();
                changed.$field = $value;
                verify_error(
                    FIXTURE_START,
                    FIXTURE_TIP,
                    &serde_json::to_vec_pretty(&changed).unwrap(),
                    packet,
                    key,
                    "four-header expected profile/dimension/count mismatch",
                    $name,
                );
                count += 1;
            }};
        }
        fault!("version", version, VERSION + 1);
        fault!("family", family, "altered-family".into());
        fault!("profile", profile, "altered-profile".into());
        fault!("input log", input_log, INPUT_LOG as u8 - 1);
        fault!("row log", row_log, ROW_LOG as u8 - 1);
        fault!("slot log", slot_log, SLOT_LOG as u8 - 1);
        fault!("base row log", base_row_log, BASE_ROW_LOG as u8 - 1);
        fault!("family log", family_log, FAMILY_LOG as u8 - 1);
        fault!("member row width 0", member_row_bits, [8, 19, 20, 20]);
        fault!("member row width 1", member_row_bits, [9, 18, 20, 20]);
        fault!("member row width 2", member_row_bits, [9, 19, 19, 20]);
        fault!("member row width 3", member_row_bits, [9, 19, 20, 19]);
        fault!(
            "adjacency count",
            adjacency_terms,
            ADJACENCY_TERMS as u32 - 1
        );
        fault!("boundary count", boundary_terms, BOUNDARY_TERMS as u32 - 1);
        fault!("core count", core_terms, CORE_TERMS as u32 - 1);
        fault!("carry count", carry_height_terms, EXTRA_TERMS as u32 - 1);
        fault!("carry edge", carry_edge, [2, 3]);
        fault!("fixed heights", fixed_heights, [3072, 3073, 3075, 3076]);
        fault!("v1 profile", profile, "four-header-link-log22-row24-v1".into());
        fault!("total count", total_terms, TOTAL_TERMS as u64 - 1);

        let mut changed = expected.clone();
        changed.start_hex = flip_hex(&changed.start_hex);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &encoded(&changed),
            packet,
            key,
            "four-header caller endpoints differ from expected statement",
            "expected start",
        );
        count += 1;
        let mut changed = expected.clone();
        changed.tip_hex = flip_hex(&changed.tip_hex);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &encoded(&changed),
            packet,
            key,
            "four-header caller endpoints differ from expected statement",
            "expected tip",
        );
        count += 1;

        let mut changed = expected.clone();
        changed.descriptor_hex = flip_hex(&changed.descriptor_hex);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &encoded(&changed),
            packet,
            key,
            "four-header expected statement does not match canonical plan",
            "descriptor",
        );
        count += 1;
        let mut changed = expected.clone();
        changed.setup_id_hex = flip_hex(&changed.setup_id_hex);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &encoded(&changed),
            packet,
            key,
            "four-header admitted diagnostic key mismatch",
            "setup ID",
        );
        count += 1;
        let mut changed = expected.clone();
        let mut commitment =
            pcs::decode_commitment(&unhex(&changed.commitment_hex).unwrap()).unwrap();
        let delta = commitment.0;
        commitment.0 += delta;
        changed.commitment_hex = hex(&pcs::encode_commitment(&commitment).unwrap());
        assert_ne!(changed.commitment_hex, expected.commitment_hex);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &encoded(&changed),
            packet,
            key,
            "four-header GKR:",
            "common commitment transcript binding",
        );
        count += 1;
        count
    }

    fn endpoint_faults(
        expected: &ExpectedStatement,
        packet: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = 0;
        let mut caller_start = FIXTURE_START;
        caller_start[0] ^= 1;
        verify_error(
            caller_start,
            FIXTURE_TIP,
            &encoded(expected),
            packet,
            key,
            "four-header caller endpoints differ from expected statement",
            "caller start mismatch",
        );
        count += 1;
        let mut caller_tip = FIXTURE_TIP;
        caller_tip[0] ^= 1;
        verify_error(
            FIXTURE_START,
            caller_tip,
            &encoded(expected),
            packet,
            key,
            "four-header caller endpoints differ from expected statement",
            "caller tip mismatch",
        );
        count += 1;

        let old_plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        let original_challenge = first_challenge(&old_plan, expected, DOMAIN);
        let mut changed_start = FIXTURE_START;
        changed_start[0] ^= 1;
        let start_plan = Plan::build(changed_start, FIXTURE_TIP).unwrap();
        let mut start_expected = expected.clone();
        start_expected.start_hex = hex(&changed_start);
        start_expected.descriptor_hex = hex(&start_plan.descriptor());
        let start_bytes = encoded(&start_expected);
        let admitted_start = decode_expected(&start_bytes).unwrap();
        admitted_start.validate_plan(&start_plan).unwrap();
        assert_ne!(
            original_challenge,
            first_challenge(&start_plan, &admitted_start, DOMAIN)
        );
        verify_error(
            changed_start,
            FIXTURE_TIP,
            &start_bytes,
            packet,
            key,
            "four-header GKR:",
            "coherent changed start reaches GKR",
        );
        count += 1;

        let mut changed_tip = FIXTURE_TIP;
        changed_tip[0] ^= 1;
        let tip_plan = Plan::build(FIXTURE_START, changed_tip).unwrap();
        let mut tip_expected = expected.clone();
        tip_expected.tip_hex = hex(&changed_tip);
        tip_expected.descriptor_hex = hex(&tip_plan.descriptor());
        let tip_bytes = encoded(&tip_expected);
        let admitted_tip = decode_expected(&tip_bytes).unwrap();
        admitted_tip.validate_plan(&tip_plan).unwrap();
        assert_ne!(
            original_challenge,
            first_challenge(&tip_plan, &admitted_tip, DOMAIN)
        );
        verify_error(
            FIXTURE_START,
            changed_tip,
            &tip_bytes,
            packet,
            key,
            "four-header GKR:",
            "coherent changed tip reaches GKR",
        );
        count += 1;
        count
    }

    fn decoder_faults(expected_bytes: &[u8], packet: &[u8], key: &AdmittedVerifierKey) -> usize {
        let mut count = 0;
        let mut malformed_commitment = decode_expected(expected_bytes).unwrap();
        malformed_commitment.commitment_hex = hex(&vec![
            0xff;
            PairingOutput::<ark_bn254::Bn254>::zero()
                .compressed_size()
        ]);
        malformed_commitment.validate_shape().unwrap();
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &serde_json::to_vec_pretty(&malformed_commitment).unwrap(),
            packet,
            key,
            "four-header commitment codec:",
            "same-length malformed metadata commitment",
        );
        count += 1;
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &vec![b' '; EXPECTED_CAP + 1],
            packet,
            key,
            "four-header expected length/cap",
            "expected cap",
        );
        count += 1;
        let json_text = String::from_utf8(expected_bytes.to_vec()).unwrap();
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            json_text
                .replacen("{", "{\n  \"unknown\": 1,", 1)
                .as_bytes(),
            packet,
            key,
            "unknown field",
            "unknown expected field",
        );
        count += 1;
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            json_text
                .replacen("{", "{\n  \"version\": 1,", 1)
                .as_bytes(),
            packet,
            key,
            "duplicate field",
            "duplicate expected field",
        );
        count += 1;
        let descriptor = serde_json::from_slice::<serde_json::Value>(expected_bytes).unwrap()
            ["descriptor_hex"]
            .as_str()
            .unwrap()
            .to_string();
        let descriptor_field = format!("\"descriptor_hex\": \"{descriptor}\"");
        let uppercase_field = format!("\"descriptor_hex\": \"{}\"", "AA".repeat(32));
        let uppercase = json_text.replace(&descriptor_field, &uppercase_field);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            uppercase.as_bytes(),
            packet,
            key,
            "noncanonical lowercase hex",
            "uppercase hex",
        );
        count += 1;
        let mut whitespace = expected_bytes.to_vec();
        whitespace.push(b' ');
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            &whitespace,
            packet,
            key,
            "noncanonical four-header expected JSON",
            "noncanonical expected JSON",
        );
        count += 1;

        for field in [
            "version",
            "family",
            "profile",
            "start_hex",
            "tip_hex",
            "input_log",
            "row_log",
            "slot_log",
            "base_row_log",
            "family_log",
            "member_row_bits",
            "adjacency_terms",
            "boundary_terms",
            "core_terms",
            "carry_height_terms",
            "fixed_heights",
            "carry_edge",
            "total_terms",
            "descriptor_hex",
            "setup_id_hex",
            "commitment_hex",
        ] {
            let mut object = serde_json::from_slice::<serde_json::Value>(expected_bytes).unwrap();
            object.as_object_mut().unwrap().remove(field).unwrap();
            let error = verify_with_key(
                FIXTURE_START,
                FIXTURE_TIP,
                &serde_json::to_vec(&object).unwrap(),
                packet,
                key,
            )
            .unwrap_err();
            assert!(
                error.starts_with("missing field"),
                "missing {field}: {error}"
            );
            count += 1;
        }

        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &vec![0; MAX_PACKET_CAP + 1],
            key,
            "four-header packet length/cap/EOF",
            "packet cap",
        );
        count += 1;
        let mut changed = packet.to_vec();
        changed[0] ^= 1;
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &changed,
            key,
            "four-header packet magic/version mismatch",
            "magic",
        );
        count += 1;
        changed = packet.to_vec();
        changed[8] ^= 1;
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &changed,
            key,
            "four-header packet magic/version mismatch",
            "version",
        );
        count += 1;

        let offset = |index: usize| {
            9 + codec_section_lengths().unwrap()[..index]
                .iter()
                .map(|n| 5 + n)
                .sum::<usize>()
        };
        for index in 0..3 {
            changed = packet.to_vec();
            changed[offset(index)] = ((index + 1) % 3) as u8;
            verify_error(
                FIXTURE_START,
                FIXTURE_TIP,
                expected_bytes,
                &changed,
                key,
                "four-header packet section tag/order mismatch",
                &format!("tag {index}"),
            );
            count += 1;
        }
        for index in 0..3 {
            changed = packet.to_vec();
            let at = offset(index) + 1;
            changed[at..at + 4].copy_from_slice(&0u32.to_le_bytes());
            verify_error(
                FIXTURE_START,
                FIXTURE_TIP,
                expected_bytes,
                &changed,
                key,
                "four-header packet section length mismatch",
                &format!("length {index}"),
            );
            count += 1;
        }
        for size in [0usize, 8, 9, packet.len() - 1] {
            verify_error(
                FIXTURE_START,
                FIXTURE_TIP,
                expected_bytes,
                &packet[..size],
                key,
                "four-header packet length/cap/EOF",
                &format!("truncation {size}"),
            );
            count += 1;
        }
        changed = packet.to_vec();
        changed.push(0);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &changed,
            key,
            "four-header packet length/cap/EOF",
            "trailing bytes",
        );
        count += 1;
        let mut section_start = 9usize;
        for (index, size) in codec_section_lengths().unwrap().into_iter().enumerate() {
            changed = packet.to_vec();
            changed.drain(section_start..section_start + 5 + size);
            verify_error(
                FIXTURE_START,
                FIXTURE_TIP,
                expected_bytes,
                &changed,
                key,
                "four-header packet length/cap/EOF",
                &format!("omitted section {index}"),
            );
            section_start += 5 + size;
            count += 1;
        }
        assert_eq!(section_start, packet.len());

        changed = packet.to_vec();
        let gkr_start = offset(0) + 5;
        changed[gkr_start..gkr_start + 32].fill(0xff);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &changed,
            key,
            "four-header GKR codec:",
            "noncanonical GKR scalar",
        );
        count += 1;
        changed = packet.to_vec();
        let pcs_start = offset(1) + 5;
        changed[pcs_start..pcs_start + 32].fill(0xff);
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &changed,
            key,
            "four-header PCS codec:",
            "noncanonical PCS point",
        );
        count += 1;
        count
    }

    fn consumer_crypto_faults(
        expected: &ExpectedStatement,
        expected_bytes: &[u8],
        packet: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = 0;
        let original = decode_packet(packet).unwrap();
        let mut changed = original.clone();
        let mut gkr_proof = gkr::decode_dimensions(&[INPUT_LOG], &changed.gkr).unwrap();
        gkr_proof.layers[0].rounds[0][0] += Fr::one();
        changed.gkr = gkr::encode_proof(&gkr_proof).unwrap();
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &encode_packet(&changed).unwrap(),
            key,
            "four-header GKR:",
            "fresh consumer GKR message",
        );
        count += 1;

        changed = original.clone();
        let mut pcs_proof = pcs::decode_proof(&changed.pcs, INPUT_LOG).unwrap();
        let delta = pcs_proof.first_messages[0].d1_left.0;
        assert!(!delta.is_zero(), "fixture PCS message must be nonidentity");
        pcs_proof.first_messages[0].d1_left.0 += delta;
        changed.pcs = pcs::encode_proof(&pcs_proof).unwrap();
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &encode_packet(&changed).unwrap(),
            key,
            "four-header PCS:",
            "fresh consumer PCS message",
        );
        count += 1;

        changed = original;
        changed.post_pcs[0] ^= 1;
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &encode_packet(&changed).unwrap(),
            key,
            "four-header post-PCS transcript artifact mismatch",
            "fresh consumer post-PCS",
        );
        count += 1;

        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        let domain_error = match verify_gkr_with_domain(
            &plan,
            expected,
            &decode_packet(packet).unwrap(),
            b"changed-four-header-domain",
        ) {
            Err(error) => error,
            Ok(_) => panic!("fresh consumer accepted a packet under a changed domain"),
        };
        assert!(
            domain_error.to_string().starts_with("four-header GKR:"),
            "fresh consumer domain fault: {domain_error}"
        );
        count += 1;
        count
    }

    fn producer_crypto_faults(
        plan: &Plan,
        expected: &ExpectedStatement,
        expected_bytes: &[u8],
        packet_bytes: &[u8],
        source: &PackedFile,
        setup: &Setup,
        committed: &PackedCommitted,
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = consumer_crypto_faults(expected, expected_bytes, packet_bytes, key);
        let mut packet = decode_packet(packet_bytes).unwrap();
        let mut proof = gkr::decode_dimensions(&[INPUT_LOG], &packet.gkr).unwrap();
        proof.layers[0].line_coefficients[1] -= Fr::one();
        proof.layers[0].line_coefficients[2] += Fr::one();
        packet.gkr = gkr::encode_proof(&proof).unwrap();
        let (claim, mut transcript) = verify_gkr(plan, expected, &packet).unwrap();
        let actual_value = source.evaluate(&claim.point).unwrap();
        assert_ne!(
            actual_value, claim.value,
            "wrong terminal claim must differ from committed witness evaluation"
        );
        let opening =
            packed::open(committed, source, &claim.point, setup, &mut transcript).unwrap();
        packet.pcs = pcs::encode_proof(&opening).unwrap();
        packet.post_pcs =
            pcs::encode(&transcript.challenge_scalar(b"four-header-post-pcs")).unwrap();
        verify_error(
            FIXTURE_START,
            FIXTURE_TIP,
            expected_bytes,
            &encode_packet(&packet).unwrap(),
            key,
            "four-header PCS:",
            "valid opening at wrong terminal point",
        );
        count += 1;
        count
    }

    fn run_owner_loader() {
        let dir = temp_dir("loader");
        std::fs::create_dir_all(&dir).unwrap();
        let bytes = (0..(1usize << INPUT_LOG) / 8)
            .map(|i| ((i * 37 + (i >> 8) * 13 + (i >> 13) * 59) % 256) as u8)
            .collect::<Vec<_>>();
        let path = dir.join("owner.bits");
        let mut writer = packed::PackedFileWriter::create_new(&path, INPUT_LOG).unwrap();
        writer.write_bytes(&bytes).unwrap();
        let source = writer.finish().unwrap();
        assert!(
            source.read_copy(1usize << LOCAL_LOG, 0).is_err(),
            "base reader cap must stay at 2^16"
        );
        for slot in 0..(1usize << SLOT_LOG) {
            let values = read_owner(&source, slot).unwrap();
            assert_eq!(values.len(), 1usize << LOCAL_LOG);
            for (local, value) in values.iter().enumerate() {
                let bit = slot * (1usize << LOCAL_LOG) + local;
                assert_eq!(
                    *value,
                    Fr::from(((bytes[bit / 8] >> (bit % 8)) & 1) as u64),
                    "slot {slot}, coordinate {local}"
                );
            }
        }
        assert!(read_owner(&source, 4).unwrap_err().contains("bounds"));
        drop(source);
        std::fs::remove_file(path).unwrap();
        let wrong_path = dir.join("wrong-log.bits");
        let mut wrong = packed::PackedFileWriter::create_new(&wrong_path, INPUT_LOG - 1).unwrap();
        wrong.write_bytes(&bytes[..bytes.len() / 2]).unwrap();
        let wrong = wrong.finish().unwrap();
        assert!(read_owner(&wrong, 0).unwrap_err().contains("bounds"));
        drop(wrong);
        std::fs::remove_file(wrong_path).unwrap();
    }

    fn run_producer() {
        let whole = Instant::now();
        let dir = output_dir();
        let raws = fixture_raws().unwrap();
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        assert_eq!(plan.term_count(), TOTAL_TERMS);
        let source = plan
            .write_witness(&raws, &dir.join("witness.bits"))
            .unwrap();
        let started = Instant::now();
        let setup = pcs::generate_setup(INPUT_LOG).unwrap();
        let setup_seconds = started.elapsed().as_secs_f64();
        let started = Instant::now();
        let admitted = key(&setup);
        let key_admission_seconds = started.elapsed().as_secs_f64();
        let started = Instant::now();
        let committed = packed::commit(&source, &setup).unwrap();
        let commitment_seconds = started.elapsed().as_secs_f64();
        let expected = ExpectedStatement::new(&plan, &setup, &committed).unwrap();
        let expected_bytes = encode_expected(&expected).unwrap();
        assert!(!String::from_utf8_lossy(&expected_bytes).contains("raw_headers"));
        assert!(!String::from_utf8_lossy(&expected_bytes).contains("witness"));
        let (packet_bytes, producer_metrics) =
            prove(&plan, &expected, &source, &setup, &committed).unwrap();
        let verify_started = Instant::now();
        let positive = verify_with_key(
            FIXTURE_START,
            FIXTURE_TIP,
            &expected_bytes,
            &packet_bytes,
            &admitted,
        )
        .unwrap();
        let positive_verify_seconds = verify_started.elapsed().as_secs_f64();
        write_new(&dir.join("expected.json"), &expected_bytes);
        write_new(&dir.join("packet.bin"), &packet_bytes);
        let packet = decode_packet(&packet_bytes).unwrap();
        write_new(&dir.join("post-pcs.bin"), &packet.post_pcs);
        let expected_count = expected_faults(&expected, &packet_bytes, &admitted);
        let endpoint_count = endpoint_faults(&expected, &packet_bytes, &admitted);
        let decoder_count = decoder_faults(&expected_bytes, &packet_bytes, &admitted);
        let crypto_count = producer_crypto_faults(
            &plan,
            &expected,
            &expected_bytes,
            &packet_bytes,
            &source,
            &setup,
            &committed,
            &admitted,
        );
        let report = serde_json::json!({
            "family": FAMILY, "profile": PROFILE, "input_log": INPUT_LOG, "row_log": ROW_LOG,
            "expected_bytes": expected_bytes.len(), "packet_bytes": packet_bytes.len(),
            "section_bytes": codec_section_lengths().unwrap(), "term_count": plan.term_count(),
            "gkr_proofs": 1, "pcs_openings": 1, "positive_consumer": positive,
            "producer_metrics": producer_metrics, "setup_seconds": setup_seconds,
            "key_admission_seconds": key_admission_seconds, "commitment_seconds": commitment_seconds,
            "positive_verify_seconds": positive_verify_seconds, "whole_seconds": whole.elapsed().as_secs_f64(),
            "expected_field_negatives": expected_count, "endpoint_negatives": endpoint_count,
            "decoder_negatives": decoder_count, "crypto_negatives": crypto_count,
            "claim_ceiling": "four canonical header hashes/links, fixed heights 3072..3075 and decoded-difficulty Carry 3073->3074 under one X/C; excludes other DAA, work, PoW, timestamp ordering, full history and production security; diagnostic BN254"
        });
        write_new(
            &dir.join("producer.json"),
            &serde_json::to_vec_pretty(&report).unwrap(),
        );
        println!("{report}");
    }

    fn run_fresh_consumer() {
        let whole = Instant::now();
        let dir = PathBuf::from(
            std::env::var_os(INPUT_ENV).expect("fresh consumer input directory required"),
        );
        let expected_bytes = std::fs::read(dir.join("expected.json")).unwrap();
        let packet_bytes = std::fs::read(dir.join("packet.bin")).unwrap();
        let expected = decode_expected(&expected_bytes).unwrap();
        let started = Instant::now();
        let admitted = pinned_key();
        let key_admission_seconds = started.elapsed().as_secs_f64();
        let started = Instant::now();
        let report = verify_with_key(
            FIXTURE_START,
            FIXTURE_TIP,
            &expected_bytes,
            &packet_bytes,
            &admitted,
        )
        .unwrap();
        let verify_seconds = started.elapsed().as_secs_f64();
        let expected_count = expected_faults(&expected, &packet_bytes, &admitted);
        let endpoint_count = endpoint_faults(&expected, &packet_bytes, &admitted);
        let decoder_count = decoder_faults(&expected_bytes, &packet_bytes, &admitted);
        let crypto_count =
            consumer_crypto_faults(&expected, &expected_bytes, &packet_bytes, &admitted);
        println!(
            "{}",
            serde_json::json!({
                "consumer": report, "key_source": "release-pinned log22 fixture", "key_admission_seconds": key_admission_seconds,
                "verify_seconds": verify_seconds, "whole_process_seconds": whole.elapsed().as_secs_f64(),
                "expected_field_negatives": expected_count, "endpoint_negatives": endpoint_count,
                "decoder_negatives": decoder_count, "crypto_negatives": crypto_count,
                "claim_ceiling": "fresh consumer reads expected.json and packet.bin only; caller supplies endpoints; no fixture RAW admission; diagnostic BN254"
            })
        );
    }

    #[test]
    fn four_header_packet_loader_all_four_owners_and_bounds() {
        run_owner_loader();
    }

    #[test]
    fn four_header_packet_producer_one_gkr_one_pcs_exports_and_faults() {
        run_producer();
    }

    #[test]
    #[ignore = "fresh process requires NIPOPOW_FOUR_LINK_PACKET_INPUT_DIR with expected.json and packet.bin"]
    fn four_header_packet_fresh_serialized_consumer() {
        run_fresh_consumer();
    }
}

//! Standalone, fixed-profile H4 consumer. Statements belong to the caller;
//! terminal claims and their opening roster are derived by this verifier.
use ark_bn254::Fr;
use ark_ff::Zero;
use blake2::{digest::consts::U32, Blake2b, Digest};
use dory_pcs::backends::arkworks::ArkGT;
use serde::{Deserialize, Serialize};
use std::time::Instant;

use crate::{
    h4_analytic, header_compact_links, header_order,
    opening_batch::{self, Claim, Statement},
    pcs, segment_points, segment_relation, sparse,
    transcript::Transcript,
    verifier_key, work_tree_fixed_hash as fixed, work_tree_layout as layout,
};

pub const GLOBAL_LOG: usize = 22;
pub const CORE_COUNT: usize = 7;
pub const SEMANTIC_COUNT: usize = 7;
pub const STATEMENT_CAP: usize = 8192;
pub const PROFILE: &str = "mainnet-h4-header-tree-analytic-v3";
pub const SCOPE: &str = "bounded H4 header structure/work tree and early DAA inheritance; no retarget/PoW/history guarantee";
const MAGIC: &[u8; 8] = b"H4PKT003";
const VERSION: u8 = 3;
const CORE_STARTS: [usize; 3] = [720896, 851968, fixed::NODE_CORE];
const CORE_LOGS: [usize; CORE_COUNT] = [19, 19, 19, 19, 18, 18, 18];
const SEMANTIC_LOGS: [usize; SEMANTIC_COUNT] = [22, 22, 19, 15, 12, 11, 11];
pub const SEMANTIC_ROLES: [&[u8]; SEMANTIC_COUNT] = [
    b"retained-header-boundary",
    b"work-tree-early-daa",
    b"header-serializer",
    b"header-point-membership",
    b"header-order",
    b"header-hash-adjacency",
    b"header-metadata-adjacency",
];
const OPENING_BYTES: usize = 31_581;
const COMMITMENT_BYTES: usize = 384;
/// Fourteen fixed-shape GKR streams and two seven-claim log22 opening batches, plus framing.
pub const PROOF_CAP: usize = 118_803;

const fn setup_id() -> [u8; 32] {
    let text = b"94f67a7bd4490c3c563a7e421b4dbfdbe88cc09d090bb85d9ac8226337b73955";
    let mut out = [0; 32];
    let mut i = 0;
    while i < 32 {
        let a = text[2 * i];
        let b = text[2 * i + 1];
        let high = if a <= b'9' { a - b'0' } else { a - b'a' + 10 };
        let low = if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
        out[i] = high * 16 + low;
        i += 1;
    }
    out
}
pub const SETUP_ID: [u8; 32] = setup_id();

/// The caller independently selects or authenticates these expected values.
/// Dimensions, Mainnet genesis, wire banks, roles and profiles are code-owned.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExpectedStatement {
    pub root: [u8; 32],
    pub total_be28: [u8; 28],
    pub tip: [u8; 32],
    pub tip_time: i64,
    pub setup_id: [u8; 32],
    pub commitment: Vec<u8>,
}

impl ExpectedStatement {
    pub fn new(
        root: [u8; 32],
        total_be28: [u8; 28],
        tip: [u8; 32],
        tip_time: i64,
        commitment: &ArkGT,
    ) -> Result<Self, String> {
        let statement = Self {
            root,
            total_be28,
            tip,
            tip_time,
            setup_id: SETUP_ID,
            commitment: pcs::encode_commitment(commitment)?,
        };
        statement.validate()?;
        Ok(statement)
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.setup_id != SETUP_ID {
            return Err("H4 statement setup identity mismatch".into());
        }
        if self.commitment.len() != COMMITMENT_BYTES {
            return Err("H4 statement commitment length mismatch".into());
        }
        pcs::decode_commitment(&self.commitment)?;
        Ok(())
    }
}

pub fn encode_statement(expected: &ExpectedStatement) -> Result<Vec<u8>, String> {
    expected.validate()?;
    let bytes = serde_json::to_vec_pretty(expected).map_err(|e| e.to_string())?;
    if bytes.len() > STATEMENT_CAP {
        return Err("H4 statement exceeds fixed cap".into());
    }
    Ok(bytes)
}

pub fn decode_statement(bytes: &[u8]) -> Result<ExpectedStatement, String> {
    if bytes.len() > STATEMENT_CAP {
        return Err("H4 statement exceeds fixed cap".into());
    }
    let expected: ExpectedStatement = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    expected.validate()?;
    if encode_statement(&expected)? != bytes {
        return Err("noncanonical H4 statement".into());
    }
    Ok(expected)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub core_gkr: [Vec<u8>; CORE_COUNT],
    pub semantic_gkr: [Vec<u8>; SEMANTIC_COUNT],
    /// Fixed order: seven core claims followed by seven semantic claims.
    pub opening_batches: [Vec<u8>; 2],
}

fn section_size(index: usize) -> Result<usize, String> {
    if index < CORE_COUNT {
        return Ok(32 * (7 * CORE_LOGS[index] + 3));
    }
    if index < CORE_COUNT + SEMANTIC_COUNT {
        return Ok(32 * (7 * SEMANTIC_LOGS[index - CORE_COUNT] + 3));
    }
    if index < CORE_COUNT + SEMANTIC_COUNT + 2 {
        return Ok(OPENING_BYTES);
    }
    Err("H4 section role outside fixed roster".into())
}

fn sections(proof: &Proof) -> impl Iterator<Item = &Vec<u8>> {
    proof
        .core_gkr
        .iter()
        .chain(proof.semantic_gkr.iter())
        .chain(proof.opening_batches.iter())
}

fn validate_proof_shape(proof: &Proof) -> Result<(), String> {
    for (index, part) in sections(proof).enumerate() {
        if part.len() != section_size(index)? {
            return Err(format!("H4 section {index} length mismatch"));
        }
    }
    Ok(())
}

/// Fixed positional role tags, lengths and exact EOF; no received claim list.
pub fn encode_proof(proof: &Proof) -> Result<Vec<u8>, String> {
    validate_proof_shape(proof)?;
    let mut out = Vec::with_capacity(PROOF_CAP);
    out.extend_from_slice(MAGIC);
    out.push(VERSION);
    for (index, part) in sections(proof).enumerate() {
        out.push(index as u8);
        out.extend_from_slice(&(part.len() as u32).to_le_bytes());
        out.extend_from_slice(part);
    }
    if out.len() != PROOF_CAP {
        return Err("H4 frozen packet size drift".into());
    }
    Ok(out)
}

pub fn decode_proof(bytes: &[u8]) -> Result<Proof, String> {
    if bytes.len() != PROOF_CAP {
        return Err("H4 packet length/EOF rejected".into());
    }
    if &bytes[..8] != MAGIC || bytes[8] != VERSION {
        return Err("H4 packet header rejected".into());
    }
    // Validate every component and all offsets before copying any section.
    let mut ranges = [(0usize, 0usize); CORE_COUNT + SEMANTIC_COUNT + 2];
    let mut at = 9usize;
    for (index, range) in ranges.iter_mut().enumerate() {
        let end = at
            .checked_add(5)
            .ok_or("H4 section header offset overflow")?;
        let header = bytes.get(at..end).ok_or("truncated H4 section header")?;
        if header[0] as usize != index {
            return Err("H4 section role/order rejected".into());
        }
        let size = u32::from_le_bytes(header[1..5].try_into().unwrap()) as usize;
        if size != section_size(index)? {
            return Err("H4 section length rejected before allocation".into());
        }
        at = end;
        let end = at.checked_add(size).ok_or("H4 section offset overflow")?;
        bytes.get(at..end).ok_or("truncated H4 section")?;
        *range = (at, end);
        at = end;
    }
    if at != bytes.len() {
        return Err("H4 packet has trailing bytes".into());
    }
    let copy = |index: usize| {
        let (start, end) = ranges[index];
        bytes[start..end].to_vec()
    };
    Ok(Proof {
        core_gkr: std::array::from_fn(copy),
        semantic_gkr: std::array::from_fn(|index| copy(CORE_COUNT + index)),
        opening_batches: std::array::from_fn(|index| copy(CORE_COUNT + SEMANTIC_COUNT + index)),
    })
}

fn bind_common(transcript: &mut Transcript, expected: &ExpectedStatement) {
    transcript.append_bytes(b"root", &expected.root);
    transcript.append_bytes(b"total-work-be28", &expected.total_be28);
    transcript.append_bytes(b"setup-id", &expected.setup_id);
    transcript.append_bytes(b"input-commitment", &expected.commitment);
}

/// Exact retained H4 preamble. Index fixes bank, copy count, and embedding.
pub fn core_transcript(expected: &ExpectedStatement, index: usize) -> Result<Transcript, String> {
    expected.validate()?;
    let (start, copies) = if index < 4 {
        (0, 8)
    } else if index < CORE_COUNT {
        (CORE_STARTS[index - 4], 4)
    } else {
        return Err("H4 core role outside fixed roster".into());
    };
    let mut transcript = Transcript::new(b"nipopow-v2-h4-core-gkr-analytic-v3");
    transcript.append_bytes(b"profile", b"h4-composed-seven-core-roster-analytic-v3");
    bind_common(&mut transcript, expected);
    transcript.append_u64(b"core-claim-index", index as u64);
    transcript.append_u64(b"bank-start", start as u64);
    transcript.append_u64(b"repeated-core-copies", copies);
    Ok(transcript)
}

pub fn boundary_transcript(expected: &ExpectedStatement) -> Result<Transcript, String> {
    expected.validate()?;
    let mut transcript = Transcript::new(b"nipopow-v2-h4-retained-header-boundary-analytic-v3");
    transcript.append_bytes(
        b"profile",
        b"h4-retained-header-boundary-mainnet-analytic-v3",
    );
    transcript.append_bytes(b"relation-role", SEMANTIC_ROLES[0]);
    bind_common(&mut transcript, expected);
    Ok(transcript)
}

/// Semantic index zero is the separately framed retained-header boundary.
pub fn semantic_transcript(
    expected: &ExpectedStatement,
    index: usize,
) -> Result<Transcript, String> {
    expected.validate()?;
    if !(1..SEMANTIC_COUNT).contains(&index) {
        return Err("H4 semantic role outside fixed roster".into());
    }
    let mut transcript = Transcript::new(b"nipopow-v2-h4-complete-header-relations-analytic-v3");
    transcript.append_bytes(b"roster-profile", PROFILE.as_bytes());
    transcript.append_bytes(b"relation-role", SEMANTIC_ROLES[index]);
    transcript.append_u64(b"header-count", 4);
    transcript.append_bytes(b"tree-root", &expected.root);
    transcript.append_bytes(b"total-work-be28", &expected.total_be28);
    transcript.append_bytes(b"setup-id", &expected.setup_id);
    transcript.append_bytes(b"input-commitment", &expected.commitment);
    Ok(transcript)
}

fn hash(bytes: &[u8]) -> [u8; 32] {
    Blake2b::<U32>::digest(bytes).into()
}

fn batch_statement(
    expected: &ExpectedStatement,
    claims: [Claim; opening_batch::CLAIMS],
    corpus_id: [u8; 32],
) -> Result<Statement, String> {
    expected.validate()?;
    if claims.iter().any(|claim| claim.point.len() != GLOBAL_LOG) {
        return Err("H4 derived opening claim dimension mismatch".into());
    }
    Ok(Statement {
        log_n: GLOBAL_LOG,
        setup_id: expected.setup_id,
        commitment: pcs::decode_commitment(&expected.commitment)?,
        corpus_id: Some(corpus_id),
        claims,
    })
}

pub fn core_batch_statement(
    expected: &ExpectedStatement,
    claims: &[Claim; CORE_COUNT],
) -> Result<Statement, String> {
    let mut corpus = b"nipopow-v2/h4-mainnet-roster/analytic-v3\0".to_vec();
    corpus.extend_from_slice(&expected.root);
    corpus.extend_from_slice(&expected.total_be28);
    batch_statement(expected, claims.clone(), hash(&corpus))
}

pub fn semantic_batch_statement(
    expected: &ExpectedStatement,
    claims: &[Claim; SEMANTIC_COUNT],
) -> Result<Statement, String> {
    let mut corpus = b"nipopow-v2/h4-complete-header-openings/analytic-v3\0".to_vec();
    corpus.extend_from_slice(&expected.root);
    corpus.extend_from_slice(&expected.total_be28);
    corpus.extend_from_slice(&expected.setup_id);
    corpus.extend_from_slice(&expected.commitment);
    corpus.extend_from_slice(&(SEMANTIC_COUNT as u64).to_le_bytes());
    for (index, role) in SEMANTIC_ROLES.iter().enumerate() {
        corpus.extend_from_slice(&(index as u64).to_le_bytes());
        corpus.extend_from_slice(role);
    }
    batch_statement(expected, claims.clone(), hash(&corpus))
}

#[derive(Debug, Serialize)]
pub struct Metrics {
    pub scope: &'static str,
    pub profile: &'static str,
    pub proof_bytes: usize,
    pub witness_supplied: bool,
    pub key_admission_seconds: f64,
    pub circuit_construction_seconds: f64,
    pub gkr_decode_seconds: [f64; CORE_COUNT + SEMANTIC_COUNT],
    pub gkr_verify_seconds: [f64; CORE_COUNT + SEMANTIC_COUNT],
    pub opening_decode_seconds: [f64; 2],
    pub opening_verify_seconds: [f64; 2],
    pub verification_seconds: f64,
}

/// This API consumes only caller-owned expected values and bounded proof bytes.
/// No producer setup, packed witness, header frame or header fixture is loaded.
pub fn verify(expected: &ExpectedStatement, proof: &Proof) -> Result<Metrics, String> {
    let start = Instant::now();
    validate_proof_shape(proof)?;
    expected.validate()?;
    // Existing header/point constructors have a bounded-stack calling contract.
    let mut metrics = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("h4-packet-verifier".into())
            .stack_size(32 * 1024 * 1024)
            .spawn_scoped(scope, || verify_inner(expected, proof))
            .map_err(|e| e.to_string())?
            .join()
            .map_err(|_| "H4 verifier worker panicked".to_string())?
    })?;
    metrics.verification_seconds = start.elapsed().as_secs_f64();
    Ok(metrics)
}

fn verify_inner(expected: &ExpectedStatement, proof: &Proof) -> Result<Metrics, String> {
    let mut metrics = Metrics {
        scope: SCOPE,
        profile: PROFILE,
        proof_bytes: PROOF_CAP,
        witness_supplied: false,
        key_admission_seconds: 0.0,
        circuit_construction_seconds: 0.0,
        gkr_decode_seconds: [0.0; CORE_COUNT + SEMANTIC_COUNT],
        gkr_verify_seconds: [0.0; CORE_COUNT + SEMANTIC_COUNT],
        opening_decode_seconds: [0.0; 2],
        opening_verify_seconds: [0.0; 2],
        verification_seconds: 0.0,
    };
    let start = Instant::now();
    let key = verifier_key::admit(
        GLOBAL_LOG,
        include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),
    )?;
    if key.id() != &expected.setup_id {
        return Err("H4 admitted setup identity mismatch".into());
    }
    metrics.key_admission_seconds = start.elapsed().as_secs_f64();
    let start = Instant::now();
    let engine = fixed::engine()?;
    let plan = h4_analytic::Plan::new(expected.root, expected.total_be28)?;
    let headers = header_compact_links::build(None)?;
    let hash_link = header_compact_links::hash_relation(4, expected.tip)?;
    let metadata_link = header_compact_links::metadata_relation(4, expected.tip_time)?;
    let shape = |c: &sparse::Circuit| (c.input_len, c.row_count, c.terms.len());
    if shape(&engine.core) != (65_536, 131_072, 172_480)
        || shape(&headers.base.base.base.serializer.circuit) != (131_072, 262_144, 315_546)
        || shape(&headers.base.base.points.circuit) != (8192, 16_384, 288_158)
        || shape(&headers.base.order.circuit) != (1024, 2048, 2081)
        || hash_link.input_log() != 11
        || hash_link.row_count() != 2048
        || metadata_link.input_log() != 11
        || metadata_link.row_count() != 2048
    {
        return Err("H4 frozen circuit shape drift".into());
    }
    metrics.circuit_construction_seconds = start.elapsed().as_secs_f64();

    let mut core_claims = Vec::with_capacity(CORE_COUNT);
    for index in 0..CORE_COUNT {
        let h = if index < 4 { 3 } else { 2 };
        let start = Instant::now();
        let decoded = sparse::decode_proof(&engine.core, h, &proof.core_gkr[index])?;
        metrics.gkr_decode_seconds[index] = start.elapsed().as_secs_f64();
        let start = Instant::now();
        let checked = sparse::verify(
            &engine.core,
            h,
            &decoded,
            &mut core_transcript(expected, index)?,
        )
        .map_err(|e| format!("H4 core GKR {index} rejected: {e}"))?;
        metrics.gkr_verify_seconds[index] = start.elapsed().as_secs_f64();
        let point = if index < 4 {
            let mut point = checked.point;
            point.push(Fr::zero());
            point.extend((0..2).map(|bit| Fr::from(((index >> bit) & 1) as u64)));
            point
        } else {
            layout::embed_bank(CORE_STARTS[index - 4], 1 << 16, 2, &checked.point)?
        };
        core_claims.push(Claim {
            point,
            value: checked.value,
        });
    }
    let core_claims: [Claim; CORE_COUNT] = core_claims
        .try_into()
        .map_err(|_| "H4 core derived roster length mismatch")?;

    let mut semantic_claims = Vec::with_capacity(SEMANTIC_COUNT);
    for index in 0..SEMANTIC_COUNT {
        let local = match index {
            2 => Some((&headers.base.base.base.serializer.circuit, 2)),
            3 => Some((&headers.base.base.points.circuit, 2)),
            4 => Some((&headers.base.order.circuit, 2)),
            _ => None,
        };
        let start = Instant::now();
        let decoded = if index <= 1 {
            plan.decode(&proof.semantic_gkr[index])
                .map_err(|e| format!("H4 semantic GKR {index} decode rejected: {e}"))?
        } else if let Some((c, h)) = local {
            sparse::decode_proof(c, h, &proof.semantic_gkr[index])
                .map_err(|e| format!("H4 semantic GKR {index} decode rejected: {e}"))?
        } else if index == 5 {
            hash_link
                .decode_proof(&proof.semantic_gkr[index])
                .map_err(|e| format!("H4 semantic GKR {index} decode rejected: {e}"))?
        } else {
            metadata_link
                .decode_proof(&proof.semantic_gkr[index])
                .map_err(|e| format!("H4 semantic GKR {index} decode rejected: {e}"))?
        };
        metrics.gkr_decode_seconds[CORE_COUNT + index] = start.elapsed().as_secs_f64();
        let start = Instant::now();
        let mut transcript = if index == 0 {
            boundary_transcript(expected)?
        } else {
            semantic_transcript(expected, index)?
        };
        let checked = if index == 0 {
            plan.verify_headers(&decoded, &mut transcript)
        } else if index == 1 {
            plan.verify_tree(&decoded, &mut transcript)
        } else if let Some((c, h)) = local {
            sparse::verify(c, h, &decoded, &mut transcript).map_err(|e| e.to_string())
        } else if index == 5 {
            hash_link
                .verify(&decoded, &mut transcript)
                .map_err(|e| e.to_string())
        } else {
            metadata_link
                .verify(&decoded, &mut transcript)
                .map_err(|e| e.to_string())
        }
        .map_err(|e| format!("H4 semantic GKR {index} rejected: {e}"))?;
        metrics.gkr_verify_seconds[CORE_COUNT + index] = start.elapsed().as_secs_f64();
        let point = match index {
            2 => segment_relation::embed(1, 2, &checked.point)?,
            3 => segment_points::embed(3, 2, &checked.point)?,
            4 => header_order::embed(4, 2, &checked.point)?,
            _ => checked.point,
        };
        semantic_claims.push(Claim {
            point,
            value: checked.value,
        });
    }
    let semantic_claims: [Claim; SEMANTIC_COUNT] = semantic_claims
        .try_into()
        .map_err(|_| "H4 semantic derived roster length mismatch")?;
    let statements = [
        core_batch_statement(expected, &core_claims)?,
        semantic_batch_statement(expected, &semantic_claims)?,
    ];
    for (index, statement) in statements.iter().enumerate() {
        let start = Instant::now();
        let decoded = opening_batch::decode_proof(&proof.opening_batches[index], GLOBAL_LOG)?;
        metrics.opening_decode_seconds[index] = start.elapsed().as_secs_f64();
        let start = Instant::now();
        opening_batch::verify_admitted(statement, &key, &decoded)
            .map_err(|e| format!("H4 opening batch {index} rejected: {e}"))?;
        metrics.opening_verify_seconds[index] = start.elapsed().as_secs_f64();
    }
    Ok(metrics)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::One;

    fn statement() -> ExpectedStatement {
        ExpectedStatement::new([1; 32], [2; 28], [3; 32], 4, &ArkGT::default()).unwrap()
    }
    fn packet() -> Proof {
        Proof {
            core_gkr: std::array::from_fn(|i| vec![0; section_size(i).unwrap()]),
            semantic_gkr: std::array::from_fn(|i| vec![0; section_size(CORE_COUNT + i).unwrap()]),
            opening_batches: std::array::from_fn(|i| {
                vec![0; section_size(CORE_COUNT + SEMANTIC_COUNT + i).unwrap()]
            }),
        }
    }
    #[test]
    fn statement_admission_is_canonical_and_profile_fixed() {
        let s = statement();
        let encoded = encode_statement(&s).unwrap();
        assert_eq!(decode_statement(&encoded).unwrap(), s);
        let mut wrong = s.clone();
        wrong.setup_id[0] ^= 1;
        assert!(encode_statement(&wrong).unwrap_err().contains("identity"));
        wrong = s.clone();
        wrong.commitment.push(0);
        assert!(encode_statement(&wrong).unwrap_err().contains("length"));
        let mut value = serde_json::to_value(&s).unwrap();
        value["header_count"] = 8.into();
        assert!(decode_statement(&serde_json::to_vec_pretty(&value).unwrap()).is_err());
        assert!(decode_statement(&serde_json::to_vec(&s).unwrap())
            .unwrap_err()
            .contains("noncanonical"));
        let mut trailing = encoded;
        trailing.push(b' ');
        assert!(decode_statement(&trailing)
            .unwrap_err()
            .contains("noncanonical"));
        assert!(decode_statement(&vec![b' '; STATEMENT_CAP + 1])
            .unwrap_err()
            .contains("cap"));
    }
    #[test]
    fn packet_roles_lengths_and_eof_are_checked_before_section_allocation() {
        let p = packet();
        let bytes = encode_proof(&p).unwrap();
        assert_eq!(bytes.len(), PROOF_CAP);
        assert_eq!(decode_proof(&bytes).unwrap(), p);
        let mut changed = bytes.clone();
        changed[0] ^= 1;
        assert!(decode_proof(&changed).unwrap_err().contains("header"));
        changed = bytes.clone();
        changed[8] += 1;
        assert!(decode_proof(&changed).unwrap_err().contains("header"));
        let mut at = 9;
        for index in 0..CORE_COUNT + SEMANTIC_COUNT + 2 {
            changed = bytes.clone();
            changed[at] = ((index + 1) % (CORE_COUNT + SEMANTIC_COUNT + 2)) as u8;
            assert!(decode_proof(&changed).unwrap_err().contains("role/order"));
            changed = bytes.clone();
            changed[at + 1..at + 5].copy_from_slice(&u32::MAX.to_le_bytes());
            assert!(decode_proof(&changed)
                .unwrap_err()
                .contains("before allocation"));
            at += 5 + section_size(index).unwrap();
        }
        changed = bytes.clone();
        changed.pop();
        assert!(decode_proof(&changed).unwrap_err().contains("EOF"));
        changed = bytes;
        changed.push(0);
        assert!(decode_proof(&changed).unwrap_err().contains("EOF"));
    }
    #[test]
    fn mandatory_opening_roster_and_role_transcripts_are_derived() {
        let s = statement();
        let claims: [Claim; SEMANTIC_COUNT] = std::array::from_fn(|i| Claim {
            point: vec![Fr::from(i as u64); GLOBAL_LOG],
            value: Fr::from(i as u64),
        });
        let batch = semantic_batch_statement(&s, &claims).unwrap();
        assert_eq!(batch.claims.len(), SEMANTIC_COUNT);
        assert_eq!(batch.claims, claims);
        assert!(core_transcript(&s, CORE_COUNT).is_err());
        assert!(semantic_transcript(&s, 0).is_err());
        assert!(semantic_transcript(&s, SEMANTIC_COUNT - 1).is_ok());
        assert!(semantic_transcript(&s, SEMANTIC_COUNT).is_err());
        let mut a = core_transcript(&s, 0).unwrap();
        let mut b = core_transcript(&s, 1).unwrap();
        assert_ne!(
            a.try_challenge_scalar(b"test").unwrap(),
            b.try_challenge_scalar(b"test").unwrap()
        );
        let mut a = semantic_transcript(&s, 1).unwrap();
        let mut b = semantic_transcript(&s, 2).unwrap();
        assert_ne!(
            a.try_challenge_scalar(b"test").unwrap(),
            b.try_challenge_scalar(b"test").unwrap()
        );
        let mut wrong = claims;
        wrong[0].point.pop();
        assert!(semantic_batch_statement(&s, &wrong)
            .err()
            .unwrap()
            .contains("dimension"));
        let core: [Claim; CORE_COUNT] = std::array::from_fn(|_| Claim {
            point: vec![Fr::one(); GLOBAL_LOG],
            value: Fr::one(),
        });
        assert_ne!(
            core_batch_statement(&s, &core).unwrap().corpus_id,
            batch.corpus_id
        );
    }
}

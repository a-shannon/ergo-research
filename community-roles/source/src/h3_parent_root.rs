//! Bounded H3 proof joining both B1 children to a native root-node hash.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{digest::consts::U32, Blake2b, Digest};
use dory_pcs::backends::arkworks::{ArkDoryProof, ArkGT};
use serde::{Deserialize, Serialize};
use std::time::Instant;

use crate::{
    circuit::{self, CompressionInput},
    gkr::{self, GkrProof, InputClaim},
    packed::{self, PackedCommitted, PackedFile},
    pcs::{self, Setup},
    sparse::{self, Circuit, Term},
    transcript::Transcript,
    verifier_key,
    work_tree_fixed_hash::{self as fixed, FixedProfile, NODE_CORE},
    work_tree_layout::{self as layout, WIDTH},
    work_tree_wiring::{Descriptor, Topology},
};

pub const DOMAIN: &[u8] = b"nipopow-v2-h3-parent-root-hash-composition-v1";
pub const STATEMENT_CAP: usize = 16 * 1024;
/// Exact H3 packet size for the frozen GKR and Dory proof shapes below.
/// GKR scalars: (7*22+3 + 7*16+3)*32 = 8,704 bytes.
/// Dory log-22: 29,421 bytes each; framing: 9 + 4*4 bytes.
pub const PROOF_CAP: usize = 67_571;
pub const GLOBAL_LOG: usize = 22;
pub const GLOBAL_INPUT: usize = 1 << GLOBAL_LOG;
pub const CORE_LEN: usize = 1 << 16;
pub const BOUNDARY_ROWS: usize = 1 << 12;
const MAGIC: &[u8; 8] = b"H3ROOT01";
const VERSION: u8 = 1;
const NATIVE_WORK_SHA256: &str = fixed::NATIVE_WORK_SHA256;
const STAGE_ROSTER: &[u8] = b"boundary-gkr,native-core-gkr,boundary-pcs,native-core-pcs";

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExpectedStatement {
    pub profile: String,
    pub version: u8,
    pub tree: Descriptor,
    pub fixed_profile: FixedProfile,
    pub root: [u8; 32],
    pub global_log: usize,
    pub core_offset: usize,
    pub core_len: usize,
    pub boundary_rows: usize,
    pub boundary_terms: usize,
    pub boundary_terms_blake2b256: String,
    pub core_terms: usize,
    pub core_terms_blake2b256: String,
    pub native_work_sha256: String,
    pub setup_id: [u8; 32],
    pub commitment: Vec<u8>,
    pub stage_roster: String,
}

impl ExpectedStatement {
    pub fn new(root: [u8; 32], setup: &Setup, commitment: &ArkGT) -> Result<Self, String> {
        let engine = fixed::engine()?;
        let boundary = boundary_circuit(root)?;
        let statement = Self {
            profile: "nipopow-v2-h3-parent-root-hash-v1".into(),
            version: VERSION,
            tree: Descriptor::new(3, root)?,
            fixed_profile: FixedProfile::new(3, root)?,
            root,
            global_log: GLOBAL_LOG,
            core_offset: NODE_CORE,
            core_len: CORE_LEN,
            boundary_rows: boundary.row_count,
            boundary_terms: boundary.terms.len(),
            boundary_terms_blake2b256: layout::hash_terms(&boundary.terms),
            core_terms: engine.core.terms.len(),
            core_terms_blake2b256: layout::hash_terms(&engine.core.terms),
            native_work_sha256: NATIVE_WORK_SHA256.into(),
            setup_id: setup.id,
            commitment: pcs::encode_commitment(commitment)?,
            stage_roster: String::from_utf8(STAGE_ROSTER.to_vec()).unwrap(),
        };
        statement.validate()?;
        Ok(statement)
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.profile != "nipopow-v2-h3-parent-root-hash-v1"
            || self.version != VERSION
            || self.tree != Descriptor::new(3, self.root)?
            || self.fixed_profile != FixedProfile::new(3, self.root)?
            || self.global_log != GLOBAL_LOG
            || self.core_offset != NODE_CORE
            || self.core_len != CORE_LEN
            || self.native_work_sha256 != NATIVE_WORK_SHA256
            || self.stage_roster.as_bytes() != STAGE_ROSTER
        {
            return Err("H3 root statement descriptor mismatch".into());
        }
        let boundary = boundary_circuit(self.root)?;
        let core = &fixed::engine()?.core;
        if self.boundary_rows != boundary.row_count
            || self.boundary_terms != boundary.terms.len()
            || self.boundary_terms_blake2b256 != layout::hash_terms(&boundary.terms)
            || self.core_terms != core.terms.len()
            || self.core_terms_blake2b256 != layout::hash_terms(&core.terms)
        {
            return Err("H3 root circuit fingerprint mismatch".into());
        }
        pcs::decode_commitment(&self.commitment)?;
        Ok(())
    }
}

pub fn encode_statement(statement: &ExpectedStatement) -> Result<Vec<u8>, String> {
    statement.validate()?;
    let bytes = serde_json::to_vec_pretty(statement).map_err(|e| e.to_string())?;
    if bytes.len() > STATEMENT_CAP {
        return Err("H3 statement exceeds cap".into());
    }
    Ok(bytes)
}

pub fn decode_statement(bytes: &[u8]) -> Result<ExpectedStatement, String> {
    if bytes.len() > STATEMENT_CAP {
        return Err("H3 statement exceeds cap".into());
    }
    let statement: ExpectedStatement = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    statement.validate()?;
    if encode_statement(&statement)? != bytes {
        return Err("noncanonical H3 statement".into());
    }
    Ok(statement)
}

fn append_family(
    topology: &Topology,
    name: &str,
    row_base: usize,
    terms: &mut Vec<Term>,
) -> Result<usize, String> {
    let family = topology
        .families
        .iter()
        .find(|family| family.name == name)
        .ok_or_else(|| format!("missing topology family {name}"))?;
    let circuit = family.enumerate(&topology.descriptor, 1 << 20)?;
    for term in circuit.terms {
        terms.push(Term {
            row: term
                .row
                .checked_add(row_base)
                .ok_or("boundary row overflow")?,
            gate: term.gate,
        });
    }
    Ok(256)
}

pub fn boundary_circuit(root: [u8; 32]) -> Result<Circuit, String> {
    let engine = fixed::engine()?;
    let profile = FixedProfile::new(3, root)?;
    let topology = Topology::new(engine.base, 3, root)?;
    let mut terms = Vec::with_capacity(4096);
    fixed::emit_slot(engine, &profile, 0, |term| terms.push(term))?;
    let mut next_row = 1_857usize;
    next_row += append_family(&topology, "level_1_child_0", next_row, &mut terms)?;
    next_row += append_family(&topology, "level_1_child_1", next_row, &mut terms)?;
    next_row += append_family(&topology, "public_root", next_row, &mut terms)?;
    let distinct_rows = terms
        .iter()
        .map(|term| term.row)
        .collect::<std::collections::BTreeSet<_>>();
    if next_row != 2_625
        || distinct_rows.len() != 2_625
        || terms.iter().any(|term| {
            term.row >= BOUNDARY_ROWS
                || term.gate.left >= GLOBAL_INPUT
                || term.gate.right >= GLOBAL_INPUT
        })
    {
        return Err("H3 root boundary shape mismatch".into());
    }
    Ok(Circuit {
        input_len: GLOBAL_INPUT,
        row_count: BOUNDARY_ROWS,
        terms,
    })
}

fn starter(statement: &ExpectedStatement) -> Result<Transcript, String> {
    statement.validate()?;
    let mut transcript = Transcript::new(DOMAIN);
    transcript.append_bytes(
        b"h3-root-expected-statement",
        &serde_json::to_vec(statement).map_err(|e| e.to_string())?,
    );
    transcript.append_bytes(b"h3-root-stage-roster", STAGE_ROSTER);
    transcript.append_bytes(
        b"h3-root-source-pins",
        &serde_json::to_vec(&source_pins()).map_err(|e| e.to_string())?,
    );
    Ok(transcript)
}

fn source_pins() -> serde_json::Value {
    serde_json::json!({
        "dyadic_edge_join.rs": layout::hash_bytes(include_bytes!("dyadic_edge_join.rs")),
        "h3_parent_root.rs": layout::hash_bytes(include_bytes!("h3_parent_root.rs")),
        "work_tree_fixed_hash.rs": layout::hash_bytes(include_bytes!("work_tree_fixed_hash.rs")),
        "work_tree_wiring.rs": layout::hash_bytes(include_bytes!("work_tree_wiring.rs")),
        "work_tree_layout.rs": layout::hash_bytes(include_bytes!("work_tree_layout.rs")),
        "sparse.rs": layout::hash_bytes(include_bytes!("sparse.rs")),
        "gkr.rs": layout::hash_bytes(include_bytes!("gkr.rs")),
        "packed.rs": layout::hash_bytes(include_bytes!("packed.rs")),
        "pcs.rs": layout::hash_bytes(include_bytes!("pcs.rs")),
        "transcript.rs": layout::hash_bytes(include_bytes!("transcript.rs")),
        "circuit.rs": layout::hash_bytes(include_bytes!("circuit.rs")),
        "verifier_key.rs": layout::hash_bytes(include_bytes!("verifier_key.rs")),
        "native_work_sha256": NATIVE_WORK_SHA256,
    })
}

fn embed_core_point(point: &[Fr]) -> Result<Vec<Fr>, String> {
    if point.len() != 16 {
        return Err("native core terminal dimension mismatch".into());
    }
    let mut global = point.to_vec();
    global.extend((0..4).map(|bit| Fr::from(((14usize >> bit) & 1) as u64)));
    global.extend([Fr::zero(), Fr::zero()]);
    if global.len() != GLOBAL_LOG {
        return Err("native core PCS embedding length".into());
    }
    Ok(global)
}

fn bind_claim_roster(
    transcript: &mut Transcript,
    boundary: &InputClaim,
    core: &InputClaim,
    core_global_point: &[Fr],
) -> Result<(), String> {
    if boundary.point.len() != GLOBAL_LOG
        || core.point.len() != 16
        || core_global_point.len() != GLOBAL_LOG
    {
        return Err("H3 terminal claim dimensions mismatch".into());
    }
    transcript.append_bytes(b"h3-root-claim-order", b"boundary, native-core");
    for (role, point, value) in [
        (
            b"boundary".as_slice(),
            boundary.point.as_slice(),
            boundary.value,
        ),
        (b"native-core".as_slice(), core_global_point, core.value),
    ] {
        transcript.append_bytes(b"h3-root-opening-role", role);
        transcript.append_u64(b"h3-root-point-length", point.len() as u64);
        for coordinate in point {
            transcript.append_scalar(b"h3-root-point-coordinate", coordinate);
        }
        transcript.append_scalar(b"h3-root-opening-value", &value);
    }
    Ok(())
}

fn read_u32(bytes: &[u8], at: &mut usize) -> Result<usize, String> {
    let end = at.checked_add(4).ok_or("H3 packet offset overflow")?;
    let field = bytes.get(*at..end).ok_or("truncated H3 proof packet")?;
    *at = end;
    Ok(u32::from_le_bytes(field.try_into().unwrap()) as usize)
}

fn take_part<'a>(bytes: &'a [u8], at: &mut usize) -> Result<&'a [u8], String> {
    let len = read_u32(bytes, at)?;
    if len > PROOF_CAP {
        return Err("H3 proof component cap".into());
    }
    let end = at.checked_add(len).ok_or("H3 packet offset overflow")?;
    let part = bytes.get(*at..end).ok_or("truncated H3 proof packet")?;
    *at = end;
    Ok(part)
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub boundary_gkr: GkrProof,
    pub core_gkr: GkrProof,
    pub boundary_pcs: ArkDoryProof,
    pub core_pcs: ArkDoryProof,
}

pub fn encode_proof(proof: &Proof) -> Result<Vec<u8>, String> {
    let components = [
        gkr::encode_proof(&proof.boundary_gkr)?,
        gkr::encode_proof(&proof.core_gkr)?,
        pcs::encode_proof(&proof.boundary_pcs)?,
        pcs::encode_proof(&proof.core_pcs)?,
    ];
    let total = 9usize
        .checked_add(components.iter().map(|part| 4 + part.len()).sum::<usize>())
        .ok_or("H3 proof length overflow")?;
    if total != PROOF_CAP {
        return Err(format!(
            "H3 proof shape length: expected {PROOF_CAP}, got {total}"
        ));
    }
    let mut out = Vec::with_capacity(total);
    out.extend_from_slice(MAGIC);
    out.push(VERSION);
    for part in components {
        let len = u32::try_from(part.len()).map_err(|_| "H3 proof component length")?;
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(&part);
    }
    Ok(out)
}

pub fn decode_proof(statement: &ExpectedStatement, bytes: &[u8]) -> Result<Proof, String> {
    check_packet_size(bytes.len())?;
    let boundary = boundary_circuit(statement.root)?;
    let core = &fixed::engine()?.core;
    if bytes.get(..8) != Some(MAGIC.as_slice()) || bytes.get(8) != Some(&VERSION) {
        return Err("H3 proof magic/version rejected".into());
    }
    let mut at = 9usize;
    let boundary_gkr = sparse::decode_proof(&boundary, 0, take_part(bytes, &mut at)?)?;
    let core_gkr = sparse::decode_proof(core, 0, take_part(bytes, &mut at)?)?;
    let boundary_pcs = pcs::decode_proof(take_part(bytes, &mut at)?, GLOBAL_LOG)?;
    let core_pcs = pcs::decode_proof(take_part(bytes, &mut at)?, GLOBAL_LOG)?;
    if at != bytes.len() {
        return Err("trailing H3 proof bytes".into());
    }
    let proof = Proof {
        boundary_gkr,
        core_gkr,
        boundary_pcs,
        core_pcs,
    };
    if encode_proof(&proof)? != bytes {
        return Err("noncanonical H3 proof packet".into());
    }
    Ok(proof)
}

fn check_packet_size(actual: usize) -> Result<(), String> {
    if actual != PROOF_CAP {
        return Err(format!(
            "H3 proof packet length: expected {PROOF_CAP}, got {actual}"
        ));
    }
    Ok(())
}

pub fn prove(
    source: &PackedFile,
    committed: &PackedCommitted,
    setup: &Setup,
    statement: &ExpectedStatement,
) -> Result<(Proof, serde_json::Value), String> {
    statement.validate()?;
    if source.input_len() != GLOBAL_INPUT
        || setup.log_n != GLOBAL_LOG
        || setup.id != statement.setup_id
        || pcs::encode_commitment(&committed.commitment)? != statement.commitment
    {
        return Err("H3 source/commitment/setup mismatch".into());
    }
    let engine = fixed::engine()?;
    let boundary = boundary_circuit(statement.root)?;
    let mut transcript = starter(statement)?;
    let mut metrics = serde_json::Map::new();

    let before = Instant::now();
    let mut global = Vec::with_capacity(GLOBAL_INPUT);
    for copy in 0..(GLOBAL_INPUT / CORE_LEN) {
        global.extend(source.read_copy(CORE_LEN, copy)?);
    }
    if global.len() != GLOBAL_INPUT {
        return Err("H3 dense witness length mismatch".into());
    }
    metrics.insert(
        "materialize_global_seconds".into(),
        serde_json::json!(before.elapsed().as_secs_f64()),
    );

    transcript.append_bytes(b"h3-root-gkr-stage", b"boundary-gkr");
    let before = Instant::now();
    let (boundary_gkr, boundary_claim) =
        sparse::prove(&boundary, &global, 0, &mut transcript).map_err(|e| e.to_string())?;
    metrics.insert(
        "boundary_gkr_seconds".into(),
        serde_json::json!(before.elapsed().as_secs_f64()),
    );
    drop(global);

    transcript.append_bytes(b"h3-root-gkr-stage", b"native-core-gkr");
    let before = Instant::now();
    let core_input = source.read_copy(CORE_LEN, 14)?;
    let (core_gkr, core_claim) =
        sparse::prove(&engine.core, &core_input, 0, &mut transcript).map_err(|e| e.to_string())?;
    metrics.insert(
        "native_core_gkr_seconds".into(),
        serde_json::json!(before.elapsed().as_secs_f64()),
    );
    let core_global_point = embed_core_point(&core_claim.point)?;
    let boundary_value = source.evaluate(&boundary_claim.point)?;
    let core_value = source.evaluate(&core_global_point)?;
    if boundary_value != boundary_claim.value || core_value != core_claim.value {
        return Err("H3 terminal claim differs from committed source".into());
    }
    bind_claim_roster(
        &mut transcript,
        &boundary_claim,
        &core_claim,
        &core_global_point,
    )?;

    let before = Instant::now();
    let boundary_pcs = packed::open(
        committed,
        source,
        &boundary_claim.point,
        setup,
        &mut transcript,
    )?;
    metrics.insert(
        "boundary_pcs_seconds".into(),
        serde_json::json!(before.elapsed().as_secs_f64()),
    );
    let before = Instant::now();
    let core_pcs = packed::open(
        committed,
        source,
        &core_global_point,
        setup,
        &mut transcript,
    )?;
    metrics.insert(
        "core_pcs_seconds".into(),
        serde_json::json!(before.elapsed().as_secs_f64()),
    );
    let proof = Proof {
        boundary_gkr,
        core_gkr,
        boundary_pcs,
        core_pcs,
    };
    let packet = encode_proof(&proof)?;
    metrics.insert("proof_bytes".into(), serde_json::json!(packet.len()));
    metrics.insert(
        "transcript_challenges".into(),
        serde_json::json!(transcript.challenges()),
    );
    metrics.insert(
        "transcript_raw_queries".into(),
        serde_json::json!(transcript.raw_queries()),
    );
    let mut next_transcript = transcript.clone();
    let next_challenge = next_transcript.challenge_scalar(b"h3-dense-differential-next");
    let mut next_challenge_bytes = Vec::new();
    next_challenge
        .serialize_compressed(&mut next_challenge_bytes)
        .map_err(|e| e.to_string())?;
    metrics.insert(
        "next_challenge_after_both_pcs".into(),
        serde_json::json!(next_challenge_bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()),
    );
    Ok((proof, serde_json::Value::Object(metrics)))
}

pub fn verify(statement: &ExpectedStatement, proof: &Proof) -> Result<serde_json::Value, String> {
    let verify_start = Instant::now();
    statement.validate()?;
    let before = Instant::now();
    let key = verifier_key::admit(
        GLOBAL_LOG,
        include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),
    )?;
    let key_admission_seconds = before.elapsed().as_secs_f64();
    if key.id() != &statement.setup_id {
        return Err("H3 verifier setup id mismatch".into());
    }
    let boundary = boundary_circuit(statement.root)?;
    let core = &fixed::engine()?.core;
    let mut transcript = starter(statement)?;
    transcript.append_bytes(b"h3-root-gkr-stage", b"boundary-gkr");
    let before = Instant::now();
    let boundary_claim = sparse::verify(&boundary, 0, &proof.boundary_gkr, &mut transcript)
        .map_err(|e| format!("boundary GKR rejected: {e}"))?;
    let boundary_gkr_seconds = before.elapsed().as_secs_f64();
    transcript.append_bytes(b"h3-root-gkr-stage", b"native-core-gkr");
    let before = Instant::now();
    let core_claim = sparse::verify(core, 0, &proof.core_gkr, &mut transcript)
        .map_err(|e| format!("native core GKR rejected: {e}"))?;
    let core_gkr_seconds = before.elapsed().as_secs_f64();
    let core_global_point = embed_core_point(&core_claim.point)?;
    bind_claim_roster(
        &mut transcript,
        &boundary_claim,
        &core_claim,
        &core_global_point,
    )?;
    let commitment = pcs::decode_commitment(&statement.commitment)?;
    let before = Instant::now();
    pcs::verify_admitted(
        commitment.clone(),
        boundary_claim.value,
        &boundary_claim.point,
        &proof.boundary_pcs,
        &key,
        &mut transcript,
    )
    .map_err(|e| format!("boundary PCS rejected: {e}"))?;
    let boundary_pcs_seconds = before.elapsed().as_secs_f64();
    let before = Instant::now();
    pcs::verify_admitted(
        commitment,
        core_claim.value,
        &core_global_point,
        &proof.core_pcs,
        &key,
        &mut transcript,
    )
    .map_err(|e| format!("native core PCS rejected: {e}"))?;
    let core_pcs_seconds = before.elapsed().as_secs_f64();
    Ok(
        serde_json::json!({"status":"accepted","key_admission_seconds":key_admission_seconds,
        "boundary_gkr_seconds":boundary_gkr_seconds,
        "native_core_gkr_seconds":core_gkr_seconds,"boundary_pcs_seconds":boundary_pcs_seconds,
        "native_core_pcs_seconds":core_pcs_seconds,"witness_supplied":false,
        "verify_process_seconds":verify_start.elapsed().as_secs_f64(),
        "source_pins":source_pins()}),
    )
}

pub fn fixture_bytes() -> Result<(Vec<u8>, [u8; 32]), String> {
    let leaf0: [u8; 32] = std::array::from_fn(|i| (i * 17 + 3) as u8);
    let leaf1: [u8; 32] = std::array::from_fn(|i| (i * 29 + 11) as u8);
    let mut preimage = Vec::with_capacity(70);
    preimage.extend_from_slice(b"N\x01\x00\x00\x00\x00");
    preimage.extend_from_slice(&leaf0);
    preimage.extend_from_slice(&leaf1);
    let root: [u8; 32] = Blake2b::<U32>::digest(&preimage).into();
    let mut block = [0u8; 128];
    block[..70].copy_from_slice(&preimage);
    let input = CompressionInput {
        state: circuit::blake2b256_initial_state(),
        block,
        counter: 70,
        final_flag: true,
    };
    let compiled = circuit::build_compression(Some(&input))?;
    let core = compiled
        .compiled
        .input
        .ok_or("missing native compression witness")?;
    let engine = fixed::engine()?;
    let native_digest = output_bytes(&core, engine)?;
    if native_digest != root {
        return Err("native compression/Blake2b fixture mismatch".into());
    }

    let mut corpus = vec![0u8; (GLOBAL_INPUT + 7) / 8];
    let endpoints = &engine.base.endpoints;
    put_bytes(&mut corpus, endpoints.leaf[0], &leaf0);
    put_bytes(&mut corpus, WIDTH + endpoints.leaf[0], &leaf1);
    put_bytes(&mut corpus, endpoints.node_left[0], &leaf0);
    put_bytes(&mut corpus, endpoints.node_right[0], &leaf1);
    put_bytes(&mut corpus, endpoints.node[0], &root);
    for (index, value) in core.iter().enumerate() {
        if value.is_one() {
            set_bit(&mut corpus, NODE_CORE + index, true);
        } else if !value.is_zero() {
            return Err("native core witness is non-Boolean".into());
        }
    }
    Ok((corpus, root))
}

fn set_bit(bytes: &mut [u8], bit: usize, value: bool) {
    if value {
        bytes[bit / 8] |= 1 << (bit % 8);
    }
}
fn put_bytes(bytes: &mut [u8], start_bit: usize, value: &[u8; 32]) {
    for (byte_index, byte) in value.iter().enumerate() {
        for bit in 0..8 {
            set_bit(
                bytes,
                start_bit + byte_index * 8 + bit,
                ((byte >> bit) & 1) == 1,
            );
        }
    }
}
fn output_bytes(core: &[Fr], engine: &fixed::Engine) -> Result<[u8; 32], String> {
    let mut out = [0u8; 32];
    for bit in 0..256 {
        let value = core[engine.base.compression.output[bit / 64][bit % 64]];
        if value.is_one() {
            out[bit / 8] |= 1 << (bit % 8);
        } else if !value.is_zero() {
            return Err("native core output is non-Boolean".into());
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_packet_cap_is_exact_and_rejects_adjacent_lengths() {
        assert_eq!(PROOF_CAP, 67_571);
        assert!(check_packet_size(PROOF_CAP).is_ok());
        assert!(check_packet_size(PROOF_CAP - 1).is_err());
        assert!(check_packet_size(PROOF_CAP + 1).is_err());
    }

    #[test]
    fn h3_geometry_preimage_boundary_and_core_embedding_are_exact() {
        let (bytes, root) = fixture_bytes().unwrap();
        assert_eq!(bytes.len(), 524_288);
        let boundary = boundary_circuit(root).unwrap();
        let rows = boundary
            .terms
            .iter()
            .map(|term| term.row)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(boundary.input_len, 1 << 22);
        assert_eq!(boundary.row_count, 4096);
        assert_eq!(rows.len(), 2625);
        assert!(boundary.terms.len() > 2625);
        let point = (0..16)
            .map(|i| Fr::from((i + 3) as u64))
            .collect::<Vec<_>>();
        let embedded = embed_core_point(&point).unwrap();
        assert_eq!(&embedded[..16], point.as_slice());
        assert_eq!(
            &embedded[16..20],
            &[Fr::zero(), Fr::one(), Fr::one(), Fr::one()]
        );
        assert_eq!(&embedded[20..], &[Fr::zero(), Fr::zero()]);
    }

    #[test]
    fn statement_and_packet_reject_framing_and_wrong_external_root() {
        let (bytes, root) = fixture_bytes().unwrap();
        let setup = pcs::generate_setup(GLOBAL_LOG).unwrap();
        let path = std::env::temp_dir().join(format!("h3-root-{}-fixture.bin", std::process::id()));
        std::fs::write(&path, bytes).unwrap();
        let source = PackedFile::open(&path, GLOBAL_LOG).unwrap();
        let committed = packed::commit(&source, &setup).unwrap();
        let statement = ExpectedStatement::new(root, &setup, &committed.commitment).unwrap();
        let encoded = encode_statement(&statement).unwrap();
        assert_eq!(decode_statement(&encoded).unwrap(), statement);
        let mut changed = statement.clone();
        changed.root[0] ^= 1;
        assert!(changed.validate().is_err());
        assert!(decode_statement(&[&encoded[..encoded.len() - 1], b"x"].concat()).is_err());
        drop(source);
        std::fs::remove_file(path).unwrap();
    }
}

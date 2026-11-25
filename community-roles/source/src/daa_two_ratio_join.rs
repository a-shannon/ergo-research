//! Fixed Mainnet Legacy m=2 join for child height 3073.
//!
//! The four serialized headers and their ports are verifier-owned RAW values.
//! This local relation does not establish sampled-header ancestry or PoW.
use crate::{
    daa_count,
    daa_finish::{self, CompiledFinish},
    daa_integer::{Epoch, TwoRatioInputs},
    gkr::Gate,
    segment_adjacency::Relation as Adjacency,
    serializer::{self, Compiled as CompiledSerializer, Fields},
    sparse::{self, Circuit, Term},
    sparse_stream_roster::EdgeTerm,
    transcript::Transcript,
};
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use blake2::{
    digest::{consts::U32, Update, VariableOutput},
    Blake2b, Blake2bVar, Digest,
};
use ergo_header_core::Header;
use num_bigint::BigUint;

pub(crate) const INPUT_LOG: usize = 20;
pub(crate) const ROW_LOG: usize = 22;
pub(crate) const LOCAL_LOG: usize = 17;
pub(crate) const SLOT_LOG: usize = 3;
pub(crate) const ROW_LOCAL_LOG: usize = 19;
pub(crate) const WIDTH: usize = 1 << LOCAL_LOG;
pub(crate) const GLOBAL_LEN: usize = 1 << INPUT_LOG;
pub(crate) const ROW_COUNT: usize = 1 << ROW_LOG;
const SERIALIZER_ROWS: usize = 1 << 18;
const SERIALIZER_TERMS: usize = 315_546;
const ARITH_INPUT_LEN: usize = 1 << 16;
const ARITH_ROWS: usize = 1 << 17;
const ARITH_TERMS: usize = 215_791;
const ADJ_OWNER: usize = 5;
const ARITH_OWNER: usize = 4;
const ALIAS_ROW_START: usize = 1 << 10;
const HEIGHTS: [u32; 4] = [1_024, 2_048, 3_072, 3_073];
const DOMAIN: &[u8] = b"native-common-m2-two-a1-legacy-v1";
const WINDOWS_FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");
const CHILD_FIXTURE: &str = include_str!("../fixtures/mainnet-daa-child-3073-v1.json");
const SOURCE_FRAME_SHA256: &str =
    "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E";
const BASE_FIXTURE_SHA256: &str =
    "E45A23753B39C4CFD415A8F91F1FFE2A994E4A2AE3B12DFAF83869F4C736AA9E";
const CHILD_RAW_SHA256: &str = "2735A3D7A52AAAE6C3BEA4AFDB0262EB0CC222D64215D7E25FC9A5480A6A2CD5";

/// Immutable topology and exact RAW roster for the local 3073 profile.
pub(crate) struct Plan {
    raws: [Vec<u8>; 4],
    fields: [Fields; 4],
    serializer: CompiledSerializer,
    daa: CompiledFinish,
    adjacency: Adjacency,
    aliases: Vec<Term>,
    parent_digest: [u8; 32],
    child_digest: [u8; 32],
    descriptor: [u8; 32],
}

fn decode_hex(value: &str) -> Result<Vec<u8>, String> {
    if value.len() % 2 != 0 {
        return Err("odd-length fixture hex".into());
    }
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let byte = std::str::from_utf8(pair).map_err(|_| "fixture hex is not ASCII")?;
            u8::from_str_radix(byte, 16).map_err(|_| "fixture hex contains a non-hex byte".into())
        })
        .collect()
}

fn expected_raws() -> Result<[Vec<u8>; 4], String> {
    let base: serde_json::Value = serde_json::from_str(WINDOWS_FIXTURE)
        .map_err(|error| format!("base fixture JSON: {error}"))?;
    if base["source_frame"]["sha256"].as_str() != Some(SOURCE_FRAME_SHA256) {
        return Err("M2 base fixture source-frame pin changed".into());
    }
    let headers = base["headers"]
        .as_array()
        .ok_or("M2 fixture header list missing")?;
    let mut samples = Vec::with_capacity(3);
    for height in HEIGHTS[..3].iter().copied() {
        let item = headers
            .iter()
            .find(|item| item["height"].as_u64() == Some(height as u64))
            .ok_or("M2 expected sample height missing from fixture")?;
        samples.push(decode_hex(
            item["raw_hex"].as_str().ok_or("M2 sample raw missing")?,
        )?);
    }
    let child: serde_json::Value = serde_json::from_str(CHILD_FIXTURE)
        .map_err(|error| format!("child fixture JSON: {error}"))?;
    if child["height"].as_u64() != Some(3_073)
        || child["base_fixture_sha256"].as_str() != Some(BASE_FIXTURE_SHA256)
        || child["source_frame_sha256"].as_str() != Some(SOURCE_FRAME_SHA256)
        || child["raw_sha256"].as_str() != Some(CHILD_RAW_SHA256)
    {
        return Err("M2 child fixture identity pin changed".into());
    }
    samples.push(decode_hex(
        child["raw_hex"].as_str().ok_or("M2 child raw missing")?,
    )?);
    samples
        .try_into()
        .map_err(|_| "M2 fixture roster length changed".into())
}

#[cfg(test)]
pub(crate) fn fixture_raws() -> [Vec<u8>; 4] {
    expected_raws().expect("code-owned M2 fixtures")
}

fn eq_at(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, value)| {
            weight
                * if (index >> bit) & 1 == 1 {
                    *value
                } else {
                    Fr::one() - value
                }
        })
}

fn bit(bytes: &[u8; 32], index: usize) -> bool {
    ((bytes[index / 8] >> (index % 8)) & 1) != 0
}

fn add_pin(terms: &mut Vec<Term>, row: usize, owner: usize, wire: usize, value: bool) {
    terms.push(Term {
        row,
        gate: Gate {
            left: owner * WIDTH + wire,
            right: 0,
            c0: if value { -Fr::one() } else { Fr::zero() },
            c1: Fr::one(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    });
}

fn add_alias(
    terms: &mut Vec<Term>,
    row: usize,
    left_owner: usize,
    left: usize,
    right_owner: usize,
    right: usize,
) {
    terms.push(Term {
        row,
        gate: Gate {
            left: left_owner * WIDTH + left,
            right: right_owner * WIDTH + right,
            c0: Fr::zero(),
            c1: Fr::one(),
            c2: -Fr::one(),
            c3: Fr::zero(),
        },
    });
}

fn push_coefficients(out: &mut [Fr; 4], gate: &Gate, weight: Fr) {
    out[0] += weight * gate.c0;
    out[1] += weight * gate.c1;
    out[2] += weight * gate.c2;
    out[3] += weight * gate.c3;
}

fn scan_terms(
    out: &mut [Fr; 4],
    terms: &[Term],
    row_point: &[Fr],
    input_point: &[Fr],
    right_point: &[Fr],
    owner: usize,
) {
    let row_owner = eq_at(&row_point[ROW_LOCAL_LOG..], owner);
    let input_owner = eq_at(&input_point[LOCAL_LOG..], owner);
    let right_owner = eq_at(&right_point[LOCAL_LOG..], owner);
    for term in terms {
        let local_row = term.row;
        let local_left = term.gate.left % WIDTH;
        let local_right = term.gate.right % WIDTH;
        let weight = row_owner
            * eq_at(&row_point[..ROW_LOCAL_LOG], local_row)
            * input_owner
            * eq_at(&input_point[..LOCAL_LOG], local_left)
            * right_owner
            * eq_at(&right_point[..LOCAL_LOG], local_right);
        push_coefficients(out, &term.gate, weight);
    }
}

fn hash_u64(hasher: &mut Blake2bVar, value: usize) {
    hasher.update(&(value as u64).to_le_bytes());
}

fn hash_gate(hasher: &mut Blake2bVar, row: usize, gate: &Gate) {
    hash_u64(hasher, row);
    hash_u64(hasher, gate.left);
    hash_u64(hasher, gate.right);
    for coefficient in [&gate.c0, &gate.c1, &gate.c2, &gate.c3] {
        hasher.update(&coefficient.into_bigint().to_bytes_le());
    }
}

impl Plan {
    pub(crate) fn build(raws: &[Vec<u8>; 4]) -> Result<Self, String> {
        let expected = expected_raws()?;
        if raws != &expected {
            return Err("M2 roster differs from verifier-owned RAW fixture".into());
        }
        let mut fields = Vec::with_capacity(4);
        let mut headers = Vec::with_capacity(4);
        for (index, raw) in raws.iter().enumerate() {
            let header = Header::decode(raw, None)
                .map_err(|error| format!("M2 header decode: {error:?}"))?;
            if header.height != HEIGHTS[index] {
                return Err("M2 RAW height order changed".into());
            }
            fields.push(Fields::from_header(&header)?);
            headers.push(header);
        }
        let fields: [Fields; 4] = fields
            .try_into()
            .map_err(|_| "M2 fields roster length changed")?;
        let parent_digest: [u8; 32] = Blake2b::<U32>::digest(&raws[2]).into();
        let child_digest: [u8; 32] = Blake2b::<U32>::digest(&raws[3]).into();
        if headers[3].parent_id != parent_digest || headers[3].n_bits != 0x0700_a8a7 {
            return Err("M2 child parent/difficulty does not match the fixed RAW edge".into());
        }
        let input = TwoRatioInputs {
            nbits: [fields[1].n_bits, fields[2].n_bits],
            timestamps: [
                fields[0].timestamp,
                fields[1].timestamp,
                fields[2].timestamp,
            ],
        };
        if input.nbits != [0x0601_1765, 0x0613_3b15]
            || input.timestamps != [1_561_986_131_991, 1_561_993_105_670, 1_562_018_260_215]
        {
            return Err("M2 numeric ports differ from the fixed Mainnet rows".into());
        }
        let serializer = serializer::build(None)?;
        if serializer.circuit.input_len != WIDTH
            || serializer.circuit.row_count != SERIALIZER_ROWS
            || serializer.circuit.terms.len() != SERIALIZER_TERMS
        {
            return Err("M2 serializer geometry changed".into());
        }
        let daa = daa_finish::compile_two_finish_with_child(
            &daa_count::q(),
            input,
            fields[3].n_bits,
            true,
        )?;
        let daa_circuit = daa
            .joined
            .joined
            .joined
            .circuit
            .as_ref()
            .ok_or("M2 arithmetic materialization missing")?;
        if daa_circuit.input_len != ARITH_INPUT_LEN
            || daa_circuit.row_count != ARITH_ROWS
            || daa_circuit.terms.len() != ARITH_TERMS
        {
            return Err("M2 arithmetic geometry changed".into());
        }
        let adjacency = Adjacency::new_compact(2, headers[2].parent_id, child_digest)?;
        if adjacency.input_log() != 10 || adjacency.row_count() != 1 << 10 {
            return Err("M2 compact adjacency geometry changed".into());
        }
        let aliases =
            Self::build_aliases(&serializer, &daa, &fields, &parent_digest, &child_digest)?;
        let alias_end = ALIAS_ROW_START
            .checked_add(aliases.len())
            .ok_or("M2 alias row overflow")?;
        if aliases.len() != 17_896 || alias_end > 1 << ROW_LOCAL_LOG {
            return Err("M2 import/pin inventory changed".into());
        }
        let mut plan = Self {
            raws: expected,
            fields,
            serializer,
            daa,
            adjacency,
            aliases,
            parent_digest,
            child_digest,
            descriptor: [0; 32],
        };
        plan.descriptor = plan.compute_descriptor()?;
        Ok(plan)
    }

    fn build_aliases(
        serializer: &CompiledSerializer,
        daa: &CompiledFinish,
        fields: &[Fields; 4],
        parent_digest: &[u8; 32],
        child_digest: &[u8; 32],
    ) -> Result<Vec<Term>, String> {
        let mut terms = Vec::with_capacity(17_896);
        let mut row = ALIAS_ROW_START;
        for (owner, raw) in (0..4).zip(expected_raws()?.iter()) {
            for (byte_index, byte_wires) in serializer.layout.bytes.iter().enumerate() {
                let expected_byte = raw.get(byte_index).copied().unwrap_or(0);
                for (bit_index, wire) in byte_wires.iter().copied().enumerate() {
                    add_pin(
                        &mut terms,
                        row,
                        owner,
                        wire,
                        (expected_byte >> bit_index) & 1 != 0,
                    );
                    row += 1;
                }
            }
            for (bit_index, wire) in serializer.layout.length.iter().copied().enumerate() {
                add_pin(
                    &mut terms,
                    row,
                    owner,
                    wire,
                    (raw.len() >> bit_index) & 1 != 0,
                );
                row += 1;
            }
        }
        let external = &daa.joined.joined.joined.external;
        if external.len() != 2 {
            return Err("M2 A1 external map count changed".into());
        }
        for (instance, serializer_owner) in [(0usize, 1usize), (1, 2)] {
            for bit_index in 0..32 {
                add_alias(
                    &mut terms,
                    row,
                    serializer_owner,
                    serializer.layout.fields.n_bits[bit_index],
                    ARITH_OWNER,
                    external[instance].nbits[bit_index],
                );
                row += 1;
            }
        }
        for (timestamp_index, serializer_owner) in [(0usize, 0usize), (1, 1), (2, 2)] {
            let timestamp = &serializer.layout.fields.timestamp;
            let arithmetic_wires: Vec<usize> = match timestamp_index {
                0 => external[0].start_timestamp.to_vec(),
                1 => vec![external[0].end_timestamp[0]], // replaced by both shared maps below
                _ => external[1].end_timestamp.to_vec(),
            };
            if timestamp_index != 1 {
                for (bit_index, daa_wire) in arithmetic_wires.into_iter().enumerate() {
                    add_alias(
                        &mut terms,
                        row,
                        serializer_owner,
                        timestamp[bit_index],
                        ARITH_OWNER,
                        daa_wire,
                    );
                    row += 1;
                }
            } else {
                for bit_index in 0..64 {
                    add_alias(
                        &mut terms,
                        row,
                        serializer_owner,
                        timestamp[bit_index],
                        ARITH_OWNER,
                        external[0].end_timestamp[bit_index],
                    );
                    row += 1;
                    add_alias(
                        &mut terms,
                        row,
                        serializer_owner,
                        timestamp[bit_index],
                        ARITH_OWNER,
                        external[1].start_timestamp[bit_index],
                    );
                    row += 1;
                }
            }
        }
        let child_nbits = daa.child_nbits.ok_or("M2 child nBits binding missing")?;
        for bit_index in 0..32 {
            add_alias(
                &mut terms,
                row,
                3,
                serializer.layout.fields.n_bits[bit_index],
                ARITH_OWNER,
                child_nbits[bit_index],
            );
            row += 1;
        }
        for bit_index in 0..32 {
            add_alias(
                &mut terms,
                row,
                1,
                serializer.layout.fields.height[bit_index],
                ARITH_OWNER,
                daa.joined.output.x0_bits[bit_index],
            );
            row += 1;
        }
        for bit_index in 0..256 {
            let byte = bit_index / 8;
            let bit_in_byte = bit_index % 8;
            add_alias(
                &mut terms,
                row,
                2,
                serializer.layout.fields.parent_id[byte][bit_in_byte],
                ADJ_OWNER,
                bit_index,
            );
            row += 1;
            add_alias(
                &mut terms,
                row,
                3,
                serializer.layout.fields.parent_id[byte][bit_in_byte],
                ADJ_OWNER,
                512 + bit_index,
            );
            row += 1;
        }
        for bit_index in 0..256 {
            add_pin(
                &mut terms,
                row,
                ADJ_OWNER,
                256 + bit_index,
                bit(parent_digest, bit_index),
            );
            row += 1;
            // The compact relation also fixes the final tip; pinning it here
            // makes the imported adjacency bank explicit in the common witness.
            add_pin(
                &mut terms,
                row,
                ADJ_OWNER,
                768 + bit_index,
                bit(child_digest, bit_index),
            );
            row += 1;
        }
        if row != ALIAS_ROW_START + 17_896 || fields.len() != 4 {
            return Err("M2 alias row schedule changed".into());
        }
        Ok(terms)
    }

    fn compute_descriptor(&self) -> Result<[u8; 32], String> {
        let mut hasher = Blake2bVar::new(32).map_err(|_| "M2 descriptor hasher init failed")?;
        hasher.update(DOMAIN);
        for value in [
            INPUT_LOG,
            ROW_LOG,
            LOCAL_LOG,
            SLOT_LOG,
            ROW_LOCAL_LOG,
            SERIALIZER_ROWS,
            SERIALIZER_TERMS,
            ARITH_ROWS,
            ARITH_TERMS,
            ALIAS_ROW_START,
        ] {
            hash_u64(&mut hasher, value);
        }
        hasher.update(b"epoch-legacy-child-3073");
        for raw in &self.raws {
            hash_u64(&mut hasher, raw.len());
            hasher.update(raw);
        }
        hasher.update(&self.parent_digest);
        hasher.update(&self.child_digest);
        for owner in 0..4 {
            for term in &self.serializer.circuit.terms {
                hash_gate(
                    &mut hasher,
                    owner * (1 << ROW_LOCAL_LOG) + term.row,
                    &Gate {
                        left: owner * WIDTH + term.gate.left,
                        right: owner * WIDTH + term.gate.right,
                        ..term.gate.clone()
                    },
                );
            }
        }
        let arithmetic = self
            .daa
            .joined
            .joined
            .joined
            .circuit
            .as_ref()
            .ok_or("M2 arithmetic circuit missing for descriptor")?;
        for term in &arithmetic.terms {
            hash_gate(
                &mut hasher,
                ARITH_OWNER * (1 << ROW_LOCAL_LOG) + term.row,
                &Gate {
                    left: ARITH_OWNER * WIDTH + term.gate.left,
                    right: ARITH_OWNER * WIDTH + term.gate.right,
                    ..term.gate.clone()
                },
            );
        }
        self.adjacency.visit_terms(|row, gate| {
            hash_gate(
                &mut hasher,
                ADJ_OWNER * (1 << ROW_LOCAL_LOG) + row,
                &Gate {
                    left: ADJ_OWNER * WIDTH + gate.left,
                    right: ADJ_OWNER * WIDTH + gate.right,
                    ..gate
                },
            );
        });
        for term in &self.aliases {
            hash_gate(
                &mut hasher,
                ADJ_OWNER * (1 << ROW_LOCAL_LOG) + term.row,
                &term.gate,
            );
        }
        let mut digest = [0u8; 32];
        hasher
            .finalize_variable(&mut digest)
            .map_err(|_| "M2 descriptor finalize failed")?;
        Ok(digest)
    }

    pub(crate) fn bind(&self, transcript: &mut Transcript, setup_id: &[u8; 32], commitment: &[u8]) {
        transcript.append_bytes(b"profile", DOMAIN);
        transcript.append_bytes(b"descriptor", &self.descriptor);
        transcript.append_u64(b"epoch", Epoch::Legacy.length());
        transcript.append_u64(b"ratio-count", 2);
        transcript.append_u64(b"x0", 2_048);
        transcript.append_u64(b"forecast-point", 4_096);
        transcript.append_u64(b"input-log", INPUT_LOG as u64);
        transcript.append_u64(b"row-log", ROW_LOG as u64);
        transcript.append_u64(b"owner-log", SLOT_LOG as u64);
        transcript.append_u64(b"local-input-log", LOCAL_LOG as u64);
        transcript.append_u64(b"row-local-log", ROW_LOCAL_LOG as u64);
        for height in HEIGHTS {
            transcript.append_u64(b"ordered-height", height as u64);
        }
        for owner in 0..4 {
            transcript.append_u64(b"serializer-owner", owner as u64);
        }
        transcript.append_u64(b"arithmetic-owner", ARITH_OWNER as u64);
        transcript.append_u64(b"adjacency-owner", ADJ_OWNER as u64);
        transcript.append_u64(b"reserved-owner", 6);
        transcript.append_u64(b"reserved-owner", 7);
        for raw in &self.raws {
            transcript.append_bytes(b"ordered-raw-header", raw);
        }
        transcript.append_bytes(b"parent-header-digest", &self.parent_digest);
        transcript.append_bytes(b"child-header-digest", &self.child_digest);
        transcript.append_bytes(b"q", &daa_count::q().to_bytes_be());
        transcript.append_u64(b"a1-owner", ARITH_OWNER as u64);
        transcript.append_u64(b"adjacency-row-owner", ADJ_OWNER as u64);
        transcript.append_u64(b"serializer-terms", SERIALIZER_TERMS as u64);
        transcript.append_u64(b"arithmetic-terms", ARITH_TERMS as u64);
        transcript.append_u64(b"alias-terms", self.aliases.len() as u64);
        self.adjacency.bind(transcript);
        transcript.append_bytes(b"setup-id", setup_id);
        transcript.append_bytes(b"common-commitment", commitment);
    }

    pub(crate) fn descriptor(&self) -> [u8; 32] {
        self.descriptor
    }

    pub(crate) fn term_count(&self) -> usize {
        4 * self.serializer.circuit.terms.len()
            + self
                .daa
                .joined
                .joined
                .joined
                .circuit
                .as_ref()
                .map_or(0, |c| c.terms.len())
            + 768
            + self.aliases.len()
    }

    pub(crate) fn materialize_witness(&self) -> Result<Vec<Fr>, String> {
        let mut witness = vec![Fr::zero(); GLOBAL_LEN];
        for owner in 0..4 {
            let assignment = self.serializer.assign(&self.fields[owner]);
            if assignment.len() != WIDTH {
                return Err("M2 serializer witness width changed".into());
            }
            witness[owner * WIDTH..(owner + 1) * WIDTH].copy_from_slice(&assignment);
        }
        let arithmetic = &self.daa.joined.joined.joined.witness;
        if arithmetic.len() != ARITH_INPUT_LEN {
            return Err("M2 arithmetic witness width changed".into());
        }
        witness[ARITH_OWNER * WIDTH..ARITH_OWNER * WIDTH + ARITH_INPUT_LEN]
            .copy_from_slice(arithmetic);
        let adjacency = &mut witness[ADJ_OWNER * WIDTH..(ADJ_OWNER + 1) * WIDTH];
        for i in 0..256 {
            adjacency[i] = Fr::from(bit(&self.fields[2].parent_id, i) as u64);
            adjacency[256 + i] = Fr::from(bit(&self.parent_digest, i) as u64);
            adjacency[512 + i] = Fr::from(bit(&self.fields[3].parent_id, i) as u64);
            adjacency[768 + i] = Fr::from(bit(&self.child_digest, i) as u64);
        }
        self.check_residuals(&witness)?;
        Ok(witness)
    }

    pub(crate) fn check_residuals(&self, witness: &[Fr]) -> Result<(), String> {
        if witness.len() != GLOBAL_LEN {
            return Err("M2 common witness width mismatch".into());
        }
        for owner in 0..4 {
            check_circuit(
                &self.serializer.circuit,
                &witness[owner * WIDTH..(owner + 1) * WIDTH],
            )?;
        }
        let arithmetic = self
            .daa
            .joined
            .joined
            .joined
            .circuit
            .as_ref()
            .ok_or("M2 arithmetic circuit missing")?;
        check_circuit(
            arithmetic,
            &witness[ARITH_OWNER * WIDTH..ARITH_OWNER * WIDTH + ARITH_INPUT_LEN],
        )?;
        let adjacency = &witness[ADJ_OWNER * WIDTH..ADJ_OWNER * WIDTH + self.adjacency.input_len()];
        if self
            .adjacency
            .residuals(adjacency)?
            .iter()
            .any(|value| !value.is_zero())
        {
            return Err("nonzero M2 compact adjacency residual".into());
        }
        if self
            .aliases
            .iter()
            .any(|term| !term.gate.evaluate(witness).is_zero())
        {
            return Err("nonzero M2 RAW/import alias residual".into());
        }
        Ok(())
    }

    pub(crate) fn visit_endpoint(
        &self,
        left: bool,
        slot: usize,
        sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if slot >= 1 << SLOT_LOG {
            return Err("M2 endpoint owner outside profile".into());
        }
        let mut visit = |term: Term, row_owner: usize, row: usize| -> Result<(), String> {
            let endpoint = if left {
                term.gate.left
            } else {
                term.gate.right
            };
            if endpoint / WIDTH == slot {
                sink(EdgeTerm {
                    source_slot: row_owner,
                    family_row: row,
                    term,
                })?;
            }
            Ok(())
        };
        if slot < 4 {
            for term in &self.serializer.circuit.terms {
                let term = Term {
                    row: term.row,
                    gate: Gate {
                        left: slot * WIDTH + term.gate.left,
                        right: slot * WIDTH + term.gate.right,
                        ..term.gate.clone()
                    },
                };
                visit(term.clone(), slot, term.row)?;
            }
        }
        if slot == ARITH_OWNER {
            let circuit = self
                .daa
                .joined
                .joined
                .joined
                .circuit
                .as_ref()
                .ok_or("M2 arithmetic circuit missing")?;
            for term in &circuit.terms {
                let term = Term {
                    row: term.row,
                    gate: Gate {
                        left: ARITH_OWNER * WIDTH + term.gate.left,
                        right: ARITH_OWNER * WIDTH + term.gate.right,
                        ..term.gate.clone()
                    },
                };
                visit(term.clone(), ARITH_OWNER, term.row)?;
            }
        }
        if slot == ADJ_OWNER {
            let mut adjacency_error = None;
            self.adjacency.visit_terms(|row, gate| {
                let term = Term {
                    row,
                    gate: Gate {
                        left: ADJ_OWNER * WIDTH + gate.left,
                        right: ADJ_OWNER * WIDTH + gate.right,
                        ..gate
                    },
                };
                if adjacency_error.is_none() {
                    if let Err(error) = visit(term, ADJ_OWNER, row) {
                        adjacency_error = Some(error);
                    }
                }
            });
            if let Some(error) = adjacency_error {
                return Err(error);
            }
        }
        for alias in &self.aliases {
            visit(alias.clone(), ADJ_OWNER, alias.row)?;
        }
        Ok(())
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != ROW_LOG || u.len() != INPUT_LOG || v.len() != INPUT_LOG {
            return Err("M2 common coefficient dimensions changed".into());
        }
        let mut out = [Fr::zero(); 4];
        for owner in 0..4 {
            scan_terms(&mut out, &self.serializer.circuit.terms, r, u, v, owner);
        }
        let arithmetic = self
            .daa
            .joined
            .joined
            .joined
            .circuit
            .as_ref()
            .ok_or("M2 arithmetic circuit missing")?;
        scan_terms(&mut out, &arithmetic.terms, r, u, v, ARITH_OWNER);
        let row_owner = eq_at(&r[ROW_LOCAL_LOG..], ADJ_OWNER);
        let input_owner = eq_at(&u[LOCAL_LOG..], ADJ_OWNER);
        let right_owner = eq_at(&v[LOCAL_LOG..], ADJ_OWNER);
        let row_padding = eq_at(&r[10..ROW_LOCAL_LOG], 0);
        let input_padding = eq_at(&u[10..LOCAL_LOG], 0);
        let right_padding = eq_at(&v[10..LOCAL_LOG], 0);
        let mut adjacency = self
            .adjacency
            .wiring_coefficients(&r[..10], &u[..10], &v[..10])
            .map_err(|error| error.to_string())?;
        let factor =
            row_owner * input_owner * right_owner * row_padding * input_padding * right_padding;
        for coefficient in &mut adjacency {
            *coefficient *= factor;
        }
        for i in 0..4 {
            out[i] += adjacency[i];
        }
        let aliases_owner = eq_at(&r[ROW_LOCAL_LOG..], ADJ_OWNER);
        for term in &self.aliases {
            let weight = aliases_owner
                * eq_at(&r[..ROW_LOCAL_LOG], term.row)
                * eq_at(u, term.gate.left)
                * eq_at(v, term.gate.right);
            push_coefficients(&mut out, &term.gate, weight);
        }
        Ok(out)
    }
}

fn check_circuit(circuit: &Circuit, input: &[Fr]) -> Result<(), String> {
    if input.len() != circuit.input_len {
        return Err("M2 circuit input width mismatch".into());
    }
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        rows[term.row] += term.gate.evaluate(input);
    }
    if rows.iter().any(|value| !value.is_zero()) {
        return Err("nonzero M2 circuit residual".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::One;

    #[test]
    fn raw_3073_common_owner_roster_materializes_exact_relations() {
        let plan = Plan::build(&fixture_raws()).unwrap();
        let witness = plan.materialize_witness().unwrap();
        assert_eq!(witness.len(), 1 << 20);
        assert_eq!(plan.term_count(), 1_496_639);
        assert_eq!(plan.adjacency.row_count(), 1 << 10);
        assert_eq!(plan.aliases.len(), 17_896);
        plan.check_residuals(&witness).unwrap();
        assert_ne!(plan.descriptor(), [0; 32]);
    }

    #[test]
    fn raw_pins_and_shared_middle_timestamp_fail_independently() {
        let raws = fixture_raws();
        let plan = Plan::build(&raws).unwrap();
        let valid = plan.materialize_witness().unwrap();

        let mut bad_roster = raws.clone();
        bad_roster[1][0] ^= 1;
        assert!(Plan::build(&bad_roster).is_err());

        let middle = &plan.serializer.layout.fields.timestamp;
        let mut bad_middle = valid.clone();
        let wire = WIDTH + middle[0];
        bad_middle[wire] = if bad_middle[wire].is_zero() {
            Fr::one()
        } else {
            Fr::zero()
        };
        assert!(plan.check_residuals(&bad_middle).is_err());

        let mut bad_child_compact = valid;
        let child_nbits_wire = 3 * WIDTH + plan.serializer.layout.fields.n_bits[0];
        bad_child_compact[child_nbits_wire] = if bad_child_compact[child_nbits_wire].is_zero() {
            Fr::one()
        } else {
            Fr::zero()
        };
        assert!(plan.check_residuals(&bad_child_compact).is_err());
    }

    #[test]
    fn common_owner_stream_and_materialized_topology_have_equal_counts() {
        let plan = Plan::build(&fixture_raws()).unwrap();
        let mut left = 0usize;
        let mut right = 0usize;
        for slot in 0..1 << SLOT_LOG {
            plan.visit_endpoint(true, slot, &mut |_| {
                left += 1;
                Ok(())
            })
            .unwrap();
            plan.visit_endpoint(false, slot, &mut |_| {
                right += 1;
                Ok(())
            })
            .unwrap();
        }
        assert_eq!(left, plan.term_count());
        assert_eq!(right, plan.term_count());
    }

    #[test]
    fn verifier_owned_roster_rejects_reordered_samples_and_child() {
        let mut raws = fixture_raws();
        raws.swap(0, 1);
        assert!(Plan::build(&raws).is_err());
        let mut raws = fixture_raws();
        raws.swap(2, 3);
        assert!(Plan::build(&raws).is_err());
    }

    #[test]
    fn common_owner_coefficients_match_independent_stream_and_single_faults() {
        let plan = Plan::build(&fixture_raws()).unwrap();
        let r = (0..ROW_LOG)
            .map(|i| Fr::from((7 + 11 * i) as u64))
            .collect::<Vec<_>>();
        let u = (0..INPUT_LOG)
            .map(|i| Fr::from((13 + 17 * i) as u64))
            .collect::<Vec<_>>();
        let v = (0..INPUT_LOG)
            .map(|i| Fr::from((19 + 23 * i) as u64))
            .collect::<Vec<_>>();
        // The reference enumerates emitted endpoint terms. The consumer
        // evaluates its own circuits and the analytic adjacency factory.
        let rw = crate::gkr::eq_weights(&r);
        let uw = crate::gkr::eq_weights(&u);
        let vw = crate::gkr::eq_weights(&v);
        let mut expected = [Fr::zero(); 4];
        let mut count = 0;
        for slot in 0..1 << SLOT_LOG {
            plan.visit_endpoint(true, slot, &mut |edge| {
                let row = crate::sparse_stream_roster::global_edge_row(
                    edge.source_slot,
                    edge.family_row,
                    SLOT_LOG,
                    ROW_LOCAL_LOG,
                    0,
                    &[ROW_LOCAL_LOG],
                )?;
                let weight = rw[row] * uw[edge.term.gate.left] * vw[edge.term.gate.right];
                push_coefficients(&mut expected, &edge.term.gate, weight);
                count += 1;
                Ok(())
            })
            .unwrap();
        }
        assert_eq!(count, plan.term_count());
        assert_eq!(plan.coefficients(&r, &u, &v).unwrap(), expected);
        // An omitted alias and a wrong row owner each alter the terminal
        // expression independently, without changing the other families.
        let term = &plan.aliases[4 * (514 * 8 + 10)];
        let row = (ADJ_OWNER << ROW_LOCAL_LOG) + term.row;
        let mut omitted = expected;
        push_coefficients(
            &mut omitted,
            &term.gate,
            -rw[row] * uw[term.gate.left] * vw[term.gate.right],
        );
        assert_ne!(omitted, expected);
        let mut relocated = omitted;
        let wrong_row = ((ADJ_OWNER - 1) << ROW_LOCAL_LOG) + term.row;
        push_coefficients(
            &mut relocated,
            &term.gate,
            rw[wrong_row] * uw[term.gate.left] * vw[term.gate.right],
        );
        assert_ne!(relocated, expected);
        // At a Boolean row the single alias, including its cross-owner
        // endpoints, must be exactly the specified equality gate.
        let boolean = |index: usize, log: usize| {
            (0..log)
                .map(|i| Fr::from(((index >> i) & 1) as u64))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            plan.coefficients(
                &boolean(row, ROW_LOG),
                &boolean(term.gate.left, INPUT_LOG),
                &boolean(term.gate.right, INPUT_LOG)
            )
            .unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
    }

    #[test]
    fn coherent_serializer_and_arithmetic_changes_still_fail_exact_raw_pins() {
        let plan = Plan::build(&fixture_raws()).unwrap();
        let valid = plan.materialize_witness().unwrap();
        const RAW_PINS: usize = 4 * (514 * 8 + 10);
        const IMPORT_END: usize = RAW_PINS + 64 + 256 + 32 + 32;
        let mut negatives = 0;
        for slot in 0..4 {
            for kind in [0, 1, 2] {
                let mut fields = plan.fields.clone();
                match kind {
                    0 => fields[slot].height += 1,
                    1 => fields[slot].timestamp += 1,
                    2 => fields[slot].n_bits ^= 1,
                    _ => unreachable!(),
                }
                let mut witness = valid.clone();
                let ser = plan.serializer.assign(&fields[slot]);
                check_circuit(&plan.serializer.circuit, &ser).unwrap();
                witness[slot * WIDTH..(slot + 1) * WIDTH].copy_from_slice(&ser);
                let arith = daa_finish::compile_two_finish_with_child(
                    &daa_count::q(),
                    TwoRatioInputs {
                        nbits: [fields[1].n_bits, fields[2].n_bits],
                        timestamps: [
                            fields[0].timestamp,
                            fields[1].timestamp,
                            fields[2].timestamp,
                        ],
                    },
                    fields[3].n_bits,
                    true,
                )
                .unwrap();
                let a = &arith.joined.joined.joined;
                witness[ARITH_OWNER * WIDTH..ARITH_OWNER * WIDTH + ARITH_INPUT_LEN]
                    .copy_from_slice(&a.witness);
                // Every imported nBits/timestamp/child value was recomputed
                // consistently. A changed x0 height is deliberately outside
                // this fixed profile and also violates its exact height alias.
                if kind != 0 || slot != 1 {
                    assert!(
                        plan.aliases[RAW_PINS..IMPORT_END]
                            .iter()
                            .all(|t| t.gate.evaluate(&witness).is_zero()),
                        "consistent import slot{slot}/field{kind}"
                    );
                }
                if kind != 2 || slot != 3 {
                    check_circuit(a.circuit.as_ref().unwrap(), &a.witness).unwrap();
                } else {
                    assert!(
                        check_circuit(a.circuit.as_ref().unwrap(), &a.witness).is_err(),
                        "changed child compact must also fail native finish"
                    );
                }
                assert!(
                    plan.aliases[..RAW_PINS]
                        .iter()
                        .any(|t| !t.gate.evaluate(&witness).is_zero()),
                    "exact RAW slot{slot}/field{kind}"
                );
                assert!(plan.check_residuals(&witness).is_err());
                negatives += 1;
            }
        }
        assert_eq!(negatives, 12);
    }

    #[test]
    fn arithmetic_imports_and_four_adjacency_ports_have_isolated_faults() {
        let plan = Plan::build(&fixture_raws()).unwrap();
        let mut witness = plan.materialize_witness().unwrap();
        let a1 = &plan.daa.joined.joined.joined;
        let mut wires = vec![
            ARITH_OWNER * WIDTH + a1.external[0].nbits[0],
            ARITH_OWNER * WIDTH + a1.external[1].nbits[0],
            ARITH_OWNER * WIDTH + a1.external[0].start_timestamp[0],
            ARITH_OWNER * WIDTH + a1.external[0].end_timestamp[0],
            ARITH_OWNER * WIDTH + a1.external[1].end_timestamp[0],
            ARITH_OWNER * WIDTH + plan.daa.child_nbits.unwrap()[0],
            ARITH_OWNER * WIDTH + plan.daa.joined.output.x0_bits[0],
        ];
        for alias in &plan.daa.joined.joined.output.aliases {
            wires.push(ARITH_OWNER * WIDTH + alias.magnitude[0]);
            wires.push(ARITH_OWNER * WIDTH + alias.negative);
        }
        for wire in wires {
            let old = witness[wire];
            witness[wire] = Fr::one() - old;
            assert!(
                plan.check_residuals(&witness).is_err(),
                "arithmetic/import wire{wire}"
            );
            witness[wire] = old;
        }
        for port in [0, 256, 512, 768] {
            for bit in [0, 255] {
                let wire = ADJ_OWNER * WIDTH + port + bit;
                let old = witness[wire];
                witness[wire] = Fr::one() - old;
                assert!(
                    plan.check_residuals(&witness).is_err(),
                    "adjacency port{port}/bit{bit}"
                );
                assert!(
                    plan.aliases
                        .iter()
                        .any(|t| (t.gate.left == wire || t.gate.right == wire)
                            && !t.gate.evaluate(&witness).is_zero()),
                    "adjacency pin/import owns{wire}"
                );
                witness[wire] = old;
            }
        }
        plan.check_residuals(&witness).unwrap();
    }
}

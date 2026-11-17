//! Exact-RAW local Legacy joins for child4097 (m3) and child5121 (m4).
//! These relations bind a fixed sampled RAW roster, its local arithmetic and
//! the direct final-sample-to-child edge. They do not prove history or PoW.
use crate::{
    daa_count,
    daa_finish::{self, CompiledFinish},
    daa_integer::{self, Epoch, ShortLegacyInputs, ShortLegacyProfile},
    gkr::Gate,
    segment_adjacency::Relation as Adjacency,
    serializer::{self, Compiled as CompiledSerializer, Fields},
    sparse::{Circuit, Term},
    sparse_stream_roster::EdgeTerm,
    transcript::Transcript,
};
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use blake2::{digest::{consts::U32, Update, VariableOutput}, Blake2b, Blake2bVar, Digest};
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
const SERIALIZER_INPUT_LEN: usize = 1 << 17;
const SERIALIZER_ROWS: usize = 1 << 18;
const SERIALIZER_TERMS: usize = 315_546;
const ARITH_INPUT_LEN: usize = 1 << 16;
const ARITH_ROWS: usize = 1 << 17;
const ARITH_TERMS: [usize; 2] = [247_837, 278_874];
const ARITH_LIVE_BITS: [usize; 2] = [38_955, 43_402];
const ALIAS_ROW_START: usize = 1 << 10;
const ADJACENCY_ROWS: usize = 1 << 10;
const ADJACENCY_TERMS: usize = 768;
const SOURCE_FRAME_SHA256: &str =
    "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E";
const WINDOWS_FIXTURE_SHA256: &str =
    "E45A23753B39C4CFD415A8F91F1FFE2A994E4A2AE3B12DFAF83869F4C736AA9E";
const RAW_4097_SHA256: &str =
    "F18FA07D54688EDB625AD6CDED2D9B0948D0D0A040DEAD9AF4B0137E4B3D91A1";
const RAW_5121_SHA256: &str =
    "F0D7FC030B9C8AC6BC0597DFA9EABB0630CF23EA00106CD9B40616705AF41C86";
// SHA-256 pins above record received artifact provenance; these independently
// replayed BLAKE2b pins check the exact embedded bytes without a new dependency.
const WINDOWS_FIXTURE_BLAKE2B256: &str =
    "C3281EA19D4A9618E2C9F40D593D97D3D22EBEA1BDDAD1A09E930447E89689A2";
const RAW_4097_BLAKE2B256: &str =
    "708FADDAEC94AAE49D0277FC009FF15DE253604997F66A9C150E511567F86B73";
const RAW_5121_BLAKE2B256: &str =
    "4C1CFBE62B02598A60E2EB5C9E521EB5F5679120D35359363B1AA53CCEB7A298";
const DOMAIN: &[u8] = b"nipopow-short-legacy-m3-m4-exact-raw-v1";
const WINDOWS_FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");
const CHILD_4097: &[u8] = include_bytes!("../fixtures/mainnet-daa-child-4097-v1.raw.bin");
const CHILD_5121: &[u8] = include_bytes!("../fixtures/mainnet-daa-child-5121-v1.raw.bin");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Profile { M3, M4 }

impl Profile {
    pub(crate) fn parse(name: &str) -> Result<Self, String> {
        match name {
            "legacy-short-m3-child4097" => Ok(Self::M3),
            "legacy-short-m4-child5121" => Ok(Self::M4),
            _ => Err("unknown short Legacy RAW profile".into()),
        }
    }
    pub(crate) fn name(self) -> &'static str {
        match self { Self::M3 => "legacy-short-m3-child4097", Self::M4 => "legacy-short-m4-child5121" }
    }
    pub(crate) fn count(self) -> usize { match self { Self::M3 => 3, Self::M4 => 4 } }
    pub(crate) fn child_height(self) -> u32 { match self { Self::M3 => 4097, Self::M4 => 5121 } }
    pub(crate) fn serializer_count(self) -> usize { self.count() + 2 }
    pub(crate) fn arithmetic_owner(self) -> usize { self.count() + 2 }
    pub(crate) fn adjacency_owner(self) -> usize { self.count() + 3 }
    pub(crate) fn expected_arith_terms(self) -> usize { ARITH_TERMS[self.count() - 3] }
    pub(crate) fn expected_live_bits(self) -> usize { ARITH_LIVE_BITS[self.count() - 3] }
    fn sample_heights(self) -> &'static [u32] {
        match self {
            Self::M3 => &[1024, 2048, 3072, 4096],
            Self::M4 => &[1024, 2048, 3072, 4096, 5120],
        }
    }
    fn child_raw(self) -> &'static [u8] { match self { Self::M3 => CHILD_4097, Self::M4 => CHILD_5121 } }
    fn child_sha256(self) -> &'static str { match self { Self::M3 => RAW_4097_SHA256, Self::M4 => RAW_5121_SHA256 } }
    fn child_blake2b256(self) -> &'static str { match self { Self::M3 => RAW_4097_BLAKE2B256, Self::M4 => RAW_5121_BLAKE2B256 } }
    fn child_nbits(self) -> u32 { match self { Self::M3 => 0x0700_be31, Self::M4 => 0x0700_bd4a } }
    pub(crate) fn heights(self) -> Vec<u32> {
        self.sample_heights().iter().copied().chain([self.child_height()]).collect()
    }
}

pub(crate) struct Plan {
    profile: Profile,
    raws: Vec<Vec<u8>>,
    fields: Vec<Fields>,
    serializer: CompiledSerializer,
    daa: CompiledFinish,
    adjacency: Adjacency,
    aliases: Vec<Term>,
    raw_pin_terms: usize,
    parent_digest: [u8; 32],
    child_digest: [u8; 32],
    descriptor: [u8; 32],
}

fn hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{b:02x}")).collect() }
fn decode_hex(value: &str) -> Result<Vec<u8>, String> {
    if value.len() % 2 != 0 { return Err("odd-length fixture hex".into()); }
    value.as_bytes().chunks_exact(2).map(|pair| {
        let pair = std::str::from_utf8(pair).map_err(|_| "fixture hex is not ASCII")?;
        u8::from_str_radix(pair, 16).map_err(|_| "fixture hex contains a non-hex byte".into())
    }).collect()
}
fn bit(bytes: &[u8; 32], index: usize) -> bool { (bytes[index / 8] >> (index % 8)) & 1 != 0 }
fn eq_at(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |weight, (i, value)|
        weight * if (index >> i) & 1 == 1 { *value } else { Fr::one() - value })
}
fn add_pin(terms: &mut Vec<Term>, row: usize, owner: usize, wire: usize, value: bool) {
    terms.push(Term { row, gate: Gate { left: owner * WIDTH + wire, right: 0,
        c0: if value { -Fr::one() } else { Fr::zero() }, c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
}
fn add_alias(terms: &mut Vec<Term>, row: usize, left_owner: usize, left: usize,
    right_owner: usize, right: usize) {
    terms.push(Term { row, gate: Gate { left: left_owner * WIDTH + left,
        right: right_owner * WIDTH + right, c0: Fr::zero(), c1: Fr::one(),
        c2: -Fr::one(), c3: Fr::zero() } });
}
fn push_coefficients(out: &mut [Fr; 4], gate: &Gate, weight: Fr) {
    out[0] += weight * gate.c0; out[1] += weight * gate.c1;
    out[2] += weight * gate.c2; out[3] += weight * gate.c3;
}
fn hash_u64(hasher: &mut Blake2bVar, value: usize) { hasher.update(&(value as u64).to_le_bytes()); }
fn hash_gate(hasher: &mut Blake2bVar, row: usize, gate: &Gate) {
    hash_u64(hasher, row); hash_u64(hasher, gate.left); hash_u64(hasher, gate.right);
    for coefficient in [&gate.c0, &gate.c1, &gate.c2, &gate.c3] {
        hasher.update(&coefficient.into_bigint().to_bytes_le());
    }
}
fn scan_terms(out: &mut [Fr; 4], terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr], owner: usize) {
    let row_owner = eq_at(&r[ROW_LOCAL_LOG..], owner);
    let input_owner = eq_at(&u[LOCAL_LOG..], owner);
    let right_owner = eq_at(&v[LOCAL_LOG..], owner);
    for term in terms {
        let weight = row_owner * eq_at(&r[..ROW_LOCAL_LOG], term.row)
            * input_owner * eq_at(&u[..LOCAL_LOG], term.gate.left % WIDTH)
            * right_owner * eq_at(&v[..LOCAL_LOG], term.gate.right % WIDTH);
        push_coefficients(out, &term.gate, weight);
    }
}

fn expected_raws(profile: Profile) -> Result<Vec<Vec<u8>>, String> {
    let fixture_bytes = WINDOWS_FIXTURE.as_bytes();
    if hex(&Blake2b::<U32>::digest(fixture_bytes)).to_ascii_uppercase() != WINDOWS_FIXTURE_BLAKE2B256 {
        return Err("short Legacy windows fixture BLAKE2b-256 changed".into());
    }
    let fixture: serde_json::Value = serde_json::from_slice(fixture_bytes)
        .map_err(|error| format!("short Legacy windows fixture JSON: {error}"))?;
    if fixture["source_frame"]["sha256"].as_str() != Some(SOURCE_FRAME_SHA256) {
        return Err("short Legacy source-frame pin changed".into());
    }
    let headers = fixture["headers"].as_array().ok_or("short Legacy header fixture missing")?;
    let mut raws = Vec::with_capacity(profile.serializer_count());
    for height in profile.sample_heights() {
        let item = headers.iter().find(|item| item["height"].as_u64() == Some(*height as u64))
            .ok_or("short Legacy sample height missing from fixture")?;
        raws.push(decode_hex(item["raw_hex"].as_str().ok_or("short Legacy sample RAW missing")?)?);
    }
    let child = profile.child_raw();
    if hex(&Blake2b::<U32>::digest(child)).to_ascii_uppercase() != profile.child_blake2b256() {
        return Err("short Legacy child RAW BLAKE2b-256 changed".into());
    }
    raws.push(child.to_vec());
    Ok(raws)
}

#[cfg(test)]
pub(crate) fn fixture_raws(profile: Profile) -> Vec<Vec<u8>> {
    expected_raws(profile).expect("code-owned short Legacy RAW fixtures")
}

impl Plan {
    pub(crate) fn build(profile: Profile, raws: &[Vec<u8>]) -> Result<Self, String> {
        let expected = expected_raws(profile)?;
        if raws != expected.as_slice() { return Err("short Legacy roster differs from verifier-owned RAW fixtures".into()); }
        let heights = profile.heights();
        if raws.len() != profile.serializer_count() || heights.len() != raws.len() {
            return Err("short Legacy code-owned roster shape changed".into());
        }
        let mut headers = Vec::with_capacity(raws.len());
        let mut fields = Vec::with_capacity(raws.len());
        for (index, raw) in raws.iter().enumerate() {
            let header = Header::decode(raw, None).map_err(|error| format!("short Legacy RAW decode: {error:?}"))?;
            if header.height != heights[index] { return Err("short Legacy RAW height/order changed".into()); }
            fields.push(Fields::from_header(&header)?);
            headers.push(header);
        }
        if fields.last().unwrap().n_bits != profile.child_nbits() {
            return Err("short Legacy fixed child nBits changed".into());
        }
        let final_sample = profile.count();
        let parent_digest: [u8; 32] = Blake2b::<U32>::digest(&raws[final_sample]).into();
        let child_digest: [u8; 32] = Blake2b::<U32>::digest(&raws[final_sample + 1]).into();
        if headers[final_sample + 1].parent_id != parent_digest {
            return Err("short Legacy child parent does not match final sample RAW".into());
        }
        let m = profile.count();
        let input = ShortLegacyInputs {
            profile: match profile { Profile::M3 => ShortLegacyProfile::M3, Profile::M4 => ShortLegacyProfile::M4 },
            nbits: fields[1..=m].iter().map(|field| field.n_bits).collect(),
            timestamps: fields[..=m].iter().map(|field| field.timestamp).collect(),
        };
        let serializer = serializer::build(None)?;
        if serializer.circuit.input_len != SERIALIZER_INPUT_LEN
            || serializer.circuit.row_count != SERIALIZER_ROWS || serializer.circuit.terms.len() != SERIALIZER_TERMS {
            return Err("short Legacy serializer geometry changed".into());
        }
        let daa = daa_finish::compile_short_legacy_with_child(&daa_count::q(), input,
            fields[m + 1].n_bits, true)?;
        let arithmetic = daa.joined.joined.joined.circuit.as_ref().ok_or("short Legacy arithmetic materialization missing")?;
        if arithmetic.input_len != ARITH_INPUT_LEN || arithmetic.row_count != ARITH_ROWS
            || arithmetic.terms.len() != profile.expected_arith_terms()
            || daa.joined.joined.joined.count.live_bits != profile.expected_live_bits() {
            return Err("short Legacy arithmetic inventory changed".into());
        }
        let adjacency = Adjacency::new_compact(2, headers[final_sample].parent_id, child_digest)?;
        if adjacency.input_log() != 10 || adjacency.row_count() != ADJACENCY_ROWS {
            return Err("short Legacy direct-edge geometry changed".into());
        }
        let raw_pin_terms = profile.serializer_count() * (514 * 8 + 10);
        let aliases = Self::build_aliases(profile, &serializer, &daa, &fields,
            &parent_digest, &child_digest)?;
        let expected_aliases = match profile { Profile::M3 => 22_274, Profile::M4 => 26_588 };
        if aliases.len() != expected_aliases || ALIAS_ROW_START + aliases.len() > 1 << ROW_LOCAL_LOG {
            return Err("short Legacy import/pin inventory changed".into());
        }
        let mut plan = Self { profile, raws: expected, fields, serializer, daa, adjacency,
            aliases, raw_pin_terms, parent_digest, child_digest, descriptor: [0; 32] };
        plan.descriptor = plan.compute_descriptor()?;
        Ok(plan)
    }

    fn build_aliases(profile: Profile, serializer: &CompiledSerializer, daa: &CompiledFinish,
        fields: &[Fields], parent_digest: &[u8; 32], child_digest: &[u8; 32]) -> Result<Vec<Term>, String> {
        let m = profile.count();
        let roster = profile.serializer_count();
        if fields.len() != roster || daa.joined.joined.joined.external.len() != m {
            return Err("short Legacy serializer/arithmetic roster map changed".into());
        }
        let mut terms = Vec::with_capacity(match profile { Profile::M3 => 22_274, Profile::M4 => 26_588 });
        let mut row = ALIAS_ROW_START;
        let raws = expected_raws(profile)?;
        // Every serialized byte, including zero padding, and all ten length bits is pinned.
        for (owner, raw) in (0..roster).zip(&raws) {
            for (byte_index, byte_wires) in serializer.layout.bytes.iter().enumerate() {
                let expected_byte = raw.get(byte_index).copied().unwrap_or(0);
                for (bit_index, wire) in byte_wires.iter().copied().enumerate() {
                    add_pin(&mut terms, row, owner, wire, (expected_byte >> bit_index) & 1 != 0); row += 1;
                }
            }
            for (bit_index, wire) in serializer.layout.length.iter().copied().enumerate() {
                add_pin(&mut terms, row, owner, wire, (raw.len() >> bit_index) & 1 != 0); row += 1;
            }
        }
        let external = &daa.joined.joined.joined.external;
        // Each Legacy ratio owns its nBits and both timestamp ports. Shared
        // interior timestamps are imported twice, one from each A1 instance.
        for i in 0..m {
            for bit_index in 0..32 {
                add_alias(&mut terms, row, i + 1, serializer.layout.fields.n_bits[bit_index],
                    profile.arithmetic_owner(), external[i].nbits[bit_index]); row += 1;
            }
            for bit_index in 0..64 {
                add_alias(&mut terms, row, i, serializer.layout.fields.timestamp[bit_index],
                    profile.arithmetic_owner(), external[i].start_timestamp[bit_index]); row += 1;
                add_alias(&mut terms, row, i + 1, serializer.layout.fields.timestamp[bit_index],
                    profile.arithmetic_owner(), external[i].end_timestamp[bit_index]); row += 1;
            }
        }
        // Height at each end sample is explicitly tied to its corresponding x grid.
        for i in 0..m {
            for bit_index in 0..32 {
                add_alias(&mut terms, row, i + 1, serializer.layout.fields.height[bit_index],
                    profile.arithmetic_owner(), daa.joined.output.grid_x[i][bit_index]); row += 1;
            }
        }
        let child_nbits = daa.child_nbits.ok_or("short Legacy child nBits binding missing")?;
        for bit_index in 0..32 {
            add_alias(&mut terms, row, roster - 1, serializer.layout.fields.n_bits[bit_index],
                profile.arithmetic_owner(), child_nbits[bit_index]); row += 1;
        }
        for bit_index in 0..32 {
            add_alias(&mut terms, row, 1, serializer.layout.fields.height[bit_index],
                profile.arithmetic_owner(), daa.joined.output.x0_bits[bit_index]); row += 1;
        }
        let final_sample = m;
        let adjacency_owner = profile.adjacency_owner();
        for bit_index in 0..256 {
            let byte = bit_index / 8; let bit_in_byte = bit_index % 8;
            add_alias(&mut terms, row, final_sample, serializer.layout.fields.parent_id[byte][bit_in_byte],
                adjacency_owner, bit_index); row += 1;
            add_alias(&mut terms, row, roster - 1, serializer.layout.fields.parent_id[byte][bit_in_byte],
                adjacency_owner, 512 + bit_index); row += 1;
        }
        for bit_index in 0..256 {
            add_pin(&mut terms, row, adjacency_owner, 256 + bit_index, bit(parent_digest, bit_index)); row += 1;
            add_pin(&mut terms, row, adjacency_owner, 768 + bit_index, bit(child_digest, bit_index)); row += 1;
        }
        let expected = match profile { Profile::M3 => 22_274, Profile::M4 => 26_588 };
        if row != ALIAS_ROW_START + expected { return Err("short Legacy alias row schedule changed".into()); }
        Ok(terms)
    }

    fn compute_descriptor(&self) -> Result<[u8; 32], String> {
        let mut hasher = Blake2bVar::new(32).map_err(|_| "short Legacy descriptor hasher init failed")?;
        hasher.update(DOMAIN); hasher.update(self.profile.name().as_bytes());
        hasher.update(SOURCE_FRAME_SHA256.as_bytes());
        hasher.update(WINDOWS_FIXTURE_SHA256.as_bytes());
        hasher.update(self.profile.child_sha256().as_bytes());
        for value in [INPUT_LOG, ROW_LOG, LOCAL_LOG, SLOT_LOG, ROW_LOCAL_LOG, SERIALIZER_INPUT_LEN,
            SERIALIZER_ROWS, SERIALIZER_TERMS, ARITH_INPUT_LEN, ARITH_ROWS,
            self.profile.expected_arith_terms(), self.aliases.len(), ALIAS_ROW_START] { hash_u64(&mut hasher, value); }
        hash_u64(&mut hasher, self.profile.count());
        hash_u64(&mut hasher, self.profile.arithmetic_owner());
        hash_u64(&mut hasher, self.profile.adjacency_owner());
        for height in self.profile.heights() { hash_u64(&mut hasher, height as usize); }
        for raw in &self.raws { hash_u64(&mut hasher, raw.len()); hasher.update(raw); }
        hasher.update(&self.parent_digest); hasher.update(&self.child_digest);
        for owner in 0..self.profile.serializer_count() {
            for term in &self.serializer.circuit.terms {
                hash_gate(&mut hasher, owner * (1 << ROW_LOCAL_LOG) + term.row, &Gate {
                    left: owner * WIDTH + term.gate.left, right: owner * WIDTH + term.gate.right, ..term.gate.clone() });
            }
        }
        let arithmetic = self.daa.joined.joined.joined.circuit.as_ref().ok_or("short Legacy arithmetic circuit missing for descriptor")?;
        for term in &arithmetic.terms {
            hash_gate(&mut hasher, self.profile.arithmetic_owner() * (1 << ROW_LOCAL_LOG) + term.row, &Gate {
                left: self.profile.arithmetic_owner() * WIDTH + term.gate.left,
                right: self.profile.arithmetic_owner() * WIDTH + term.gate.right, ..term.gate.clone() });
        }
        self.adjacency.visit_terms(|row, gate| hash_gate(&mut hasher,
            self.profile.adjacency_owner() * (1 << ROW_LOCAL_LOG) + row, &Gate {
                left: self.profile.adjacency_owner() * WIDTH + gate.left,
                right: self.profile.adjacency_owner() * WIDTH + gate.right, ..gate }));
        for term in &self.aliases { hash_gate(&mut hasher,
            self.profile.adjacency_owner() * (1 << ROW_LOCAL_LOG) + term.row, &term.gate); }
        let mut descriptor = [0u8; 32];
        hasher.finalize_variable(&mut descriptor).map_err(|_| "short Legacy descriptor finalize failed")?;
        Ok(descriptor)
    }

    pub(crate) fn profile(&self) -> Profile { self.profile }
    pub(crate) fn raws(&self) -> &[Vec<u8>] { &self.raws }
    pub(crate) fn descriptor(&self) -> [u8; 32] { self.descriptor }
    pub(crate) fn alias_count(&self) -> usize { self.aliases.len() }
    pub(crate) fn raw_pin_count(&self) -> usize { self.raw_pin_terms }
    pub(crate) fn term_count(&self) -> usize {
        self.profile.serializer_count() * self.serializer.circuit.terms.len()
            + self.daa.joined.joined.joined.circuit.as_ref().map_or(0, |c| c.terms.len())
            + ADJACENCY_TERMS + self.aliases.len()
    }

    pub(crate) fn bind(&self, transcript: &mut Transcript, setup_id: &[u8; 32], commitment: &[u8]) {
        transcript.append_bytes(b"profile", DOMAIN);
        transcript.append_bytes(b"descriptor", &self.descriptor);
        transcript.append_bytes(b"profile-name", self.profile.name().as_bytes());
        transcript.append_u64(b"ratio-count", self.profile.count() as u64);
        transcript.append_u64(b"legacy-epoch-length", Epoch::Legacy.length());
        transcript.append_u64(b"x0", 2048);
        transcript.append_u64(b"input-log", INPUT_LOG as u64);
        transcript.append_u64(b"row-log", ROW_LOG as u64);
        transcript.append_u64(b"owner-log", SLOT_LOG as u64);
        transcript.append_u64(b"local-input-log", LOCAL_LOG as u64);
        transcript.append_u64(b"row-local-log", ROW_LOCAL_LOG as u64);
        for height in self.profile.heights() { transcript.append_u64(b"ordered-height", height as u64); }
        for owner in 0..self.profile.serializer_count() { transcript.append_u64(b"serializer-owner", owner as u64); }
        transcript.append_u64(b"arithmetic-owner", self.profile.arithmetic_owner() as u64);
        transcript.append_u64(b"adjacency-owner", self.profile.adjacency_owner() as u64);
        if self.profile == Profile::M3 { transcript.append_u64(b"reserved-owner", 7); }
        for raw in &self.raws { transcript.append_bytes(b"ordered-raw-header", raw); }
        transcript.append_bytes(b"final-sample-digest", &self.parent_digest);
        transcript.append_bytes(b"child-digest", &self.child_digest);
        transcript.append_bytes(b"q", &daa_count::q().to_bytes_be());
        transcript.append_u64(b"arithmetic-input-len", ARITH_INPUT_LEN as u64);
        transcript.append_u64(b"arithmetic-rows", ARITH_ROWS as u64);
        transcript.append_u64(b"serializer-terms", SERIALIZER_TERMS as u64);
        transcript.append_u64(b"arithmetic-terms", self.profile.expected_arith_terms() as u64);
        transcript.append_u64(b"alias-terms", self.aliases.len() as u64);
        self.adjacency.bind(transcript);
        transcript.append_bytes(b"setup-id", setup_id);
        transcript.append_bytes(b"common-commitment", commitment);
    }

    pub(crate) fn materialize_witness(&self) -> Result<Vec<Fr>, String> {
        let mut witness = vec![Fr::zero(); GLOBAL_LEN];
        for owner in 0..self.profile.serializer_count() {
            let assignment = self.serializer.assign(&self.fields[owner]);
            if assignment.len() != WIDTH { return Err("short Legacy serializer witness width changed".into()); }
            witness[owner * WIDTH..(owner + 1) * WIDTH].copy_from_slice(&assignment);
        }
        let arithmetic = &self.daa.joined.joined.joined.witness;
        if arithmetic.len() != ARITH_INPUT_LEN { return Err("short Legacy arithmetic witness width changed".into()); }
        let owner = self.profile.arithmetic_owner();
        witness[owner * WIDTH..owner * WIDTH + ARITH_INPUT_LEN].copy_from_slice(arithmetic);
        let owner = self.profile.adjacency_owner();
        let adjacency = &mut witness[owner * WIDTH..owner * WIDTH + self.adjacency.input_len()];
        let final_sample = self.profile.count();
        for i in 0..256 {
            adjacency[i] = Fr::from(bit(&self.fields[final_sample].parent_id, i) as u64);
            adjacency[256 + i] = Fr::from(bit(&self.parent_digest, i) as u64);
            adjacency[512 + i] = Fr::from(bit(&self.fields[final_sample + 1].parent_id, i) as u64);
            adjacency[768 + i] = Fr::from(bit(&self.child_digest, i) as u64);
        }
        self.check_residuals(&witness)?;
        Ok(witness)
    }

    pub(crate) fn check_residuals(&self, witness: &[Fr]) -> Result<(), String> {
        if witness.len() != GLOBAL_LEN { return Err("short Legacy common witness width mismatch".into()); }
        for owner in 0..self.profile.serializer_count() {
            check_circuit(&self.serializer.circuit, &witness[owner * WIDTH..(owner + 1) * WIDTH])?;
        }
        let arithmetic = self.daa.joined.joined.joined.circuit.as_ref().ok_or("short Legacy arithmetic circuit missing")?;
        let owner = self.profile.arithmetic_owner();
        check_circuit(arithmetic, &witness[owner * WIDTH..owner * WIDTH + ARITH_INPUT_LEN])?;
        let owner = self.profile.adjacency_owner();
        let adjacency = &witness[owner * WIDTH..owner * WIDTH + self.adjacency.input_len()];
        if self.adjacency.residuals(adjacency)?.iter().any(|value| !value.is_zero()) {
            return Err("nonzero short Legacy direct-edge residual".into());
        }
        if self.aliases.iter().any(|term| !term.gate.evaluate(witness).is_zero()) {
            return Err("nonzero short Legacy RAW/import alias residual".into());
        }
        Ok(())
    }

    pub(crate) fn visit_endpoint(&self, left: bool, slot: usize,
        sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>) -> Result<(), String> {
        if slot >= 1 << SLOT_LOG { return Err("short Legacy endpoint owner outside profile".into()); }
        let mut visit = |term: Term, row_owner: usize, row: usize| -> Result<(), String> {
            let endpoint = if left { term.gate.left } else { term.gate.right };
            if endpoint / WIDTH == slot { sink(EdgeTerm { source_slot: row_owner, family_row: row, term })?; }
            Ok(())
        };
        if slot < self.profile.serializer_count() {
            let owner = slot;
            for term in &self.serializer.circuit.terms {
                visit(Term { row: term.row, gate: Gate { left: owner * WIDTH + term.gate.left,
                    right: owner * WIDTH + term.gate.right, ..term.gate.clone() } }, owner, term.row)?;
            }
        }
        let arithmetic_owner = self.profile.arithmetic_owner();
        if slot == arithmetic_owner {
            let circuit = self.daa.joined.joined.joined.circuit.as_ref().ok_or("short Legacy arithmetic circuit missing")?;
            for term in &circuit.terms {
                visit(Term { row: term.row, gate: Gate { left: arithmetic_owner * WIDTH + term.gate.left,
                    right: arithmetic_owner * WIDTH + term.gate.right, ..term.gate.clone() } }, arithmetic_owner, term.row)?;
            }
        }
        let adjacency_owner = self.profile.adjacency_owner();
        if slot == adjacency_owner {
            let mut error = None;
            self.adjacency.visit_terms(|row, gate| {
                if error.is_none() { error = visit(Term { row, gate: Gate { left: adjacency_owner * WIDTH + gate.left,
                    right: adjacency_owner * WIDTH + gate.right, ..gate } }, adjacency_owner, row).err(); }
            });
            if let Some(error) = error { return Err(error); }
        }
        for alias in &self.aliases { visit(alias.clone(), adjacency_owner, alias.row)?; }
        Ok(())
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != ROW_LOG || u.len() != INPUT_LOG || v.len() != INPUT_LOG {
            return Err("short Legacy common coefficient dimensions changed".into());
        }
        let mut out = [Fr::zero(); 4];
        for owner in 0..self.profile.serializer_count() { scan_terms(&mut out, &self.serializer.circuit.terms, r, u, v, owner); }
        let arithmetic = self.daa.joined.joined.joined.circuit.as_ref().ok_or("short Legacy arithmetic circuit missing")?;
        scan_terms(&mut out, &arithmetic.terms, r, u, v, self.profile.arithmetic_owner());
        let adjacency_owner = self.profile.adjacency_owner();
        let row_owner = eq_at(&r[ROW_LOCAL_LOG..], adjacency_owner);
        let input_owner = eq_at(&u[LOCAL_LOG..], adjacency_owner);
        let right_owner = eq_at(&v[LOCAL_LOG..], adjacency_owner);
        let row_padding = eq_at(&r[10..ROW_LOCAL_LOG], 0);
        let input_padding = eq_at(&u[10..LOCAL_LOG], 0);
        let right_padding = eq_at(&v[10..LOCAL_LOG], 0);
        let mut adjacency = self.adjacency.wiring_coefficients(&r[..10], &u[..10], &v[..10])
            .map_err(|error| error.to_string())?;
        let factor = row_owner * input_owner * right_owner * row_padding * input_padding * right_padding;
        for coefficient in &mut adjacency { *coefficient *= factor; }
        for i in 0..4 { out[i] += adjacency[i]; }
        let aliases_owner = eq_at(&r[ROW_LOCAL_LOG..], adjacency_owner);
        for term in &self.aliases {
            let weight = aliases_owner * eq_at(&r[..ROW_LOCAL_LOG], term.row)
                * eq_at(u, term.gate.left) * eq_at(v, term.gate.right);
            push_coefficients(&mut out, &term.gate, weight);
        }
        Ok(out)
    }
}

fn check_circuit(circuit: &Circuit, input: &[Fr]) -> Result<(), String> {
    if input.len() != circuit.input_len { return Err("short Legacy circuit input width mismatch".into()); }
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms { rows[term.row] += term.gate.evaluate(input); }
    if rows.iter().any(|value| !value.is_zero()) { return Err("nonzero short Legacy circuit residual".into()); }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::One;

    fn profiles() -> [Profile; 2] { [Profile::M3, Profile::M4] }
    fn arithmetic(profile: Profile, fields: &[Fields]) -> CompiledFinish {
        let m = profile.count();
        let input = ShortLegacyInputs {
            profile: match profile { Profile::M3 => ShortLegacyProfile::M3, Profile::M4 => ShortLegacyProfile::M4 },
            nbits: fields[1..=m].iter().map(|field| field.n_bits).collect(),
            timestamps: fields[..=m].iter().map(|field| field.timestamp).collect(),
        };
        daa_finish::compile_short_legacy_with_child(&daa_count::q(), input, fields[m + 1].n_bits, true).unwrap()
    }
    fn bool_point(index: usize, width: usize) -> Vec<Fr> {
        (0..width).map(|bit| Fr::from(((index >> bit) & 1) as u64)).collect()
    }

    #[test]
    fn short_legacy_profiles_pin_actual_arithmetic_and_owner_inventories() {
        for profile in profiles() {
            let plan = Plan::build(profile, &fixture_raws(profile)).unwrap();
            let m = profile.count();
            let arithmetic = plan.daa.joined.joined.joined.circuit.as_ref().unwrap();
            assert_eq!(plan.serializer.circuit.input_len, 1 << LOCAL_LOG);
            assert_eq!(plan.serializer.circuit.row_count, 1 << 18);
            assert_eq!(plan.serializer.circuit.terms.len(), SERIALIZER_TERMS);
            assert_eq!((arithmetic.input_len, arithmetic.row_count, arithmetic.terms.len()),
                (ARITH_INPUT_LEN, ARITH_ROWS, profile.expected_arith_terms()));
            assert_eq!(plan.daa.joined.joined.joined.count.live_bits, profile.expected_live_bits());
            assert_eq!(plan.alias_count(), if profile == Profile::M3 { 22_274 } else { 26_588 });
            assert_eq!(plan.term_count(), if profile == Profile::M3 { 1_848_609 } else { 2_199_506 });
            let witness = plan.materialize_witness().unwrap();
            assert_eq!(witness.len(), GLOBAL_LEN);
            let mut left = 0usize;
            let mut right = 0usize;
            for slot in 0..1 << SLOT_LOG {
                plan.visit_endpoint(true, slot, &mut |_| { left += 1; Ok(()) }).unwrap();
                plan.visit_endpoint(false, slot, &mut |_| { right += 1; Ok(()) }).unwrap();
            }
            assert_eq!((left, right), (plan.term_count(), plan.term_count()));
            println!("{}", serde_json::json!({
                "profile": profile.name(), "m": m, "raw_headers": profile.serializer_count(),
                "owners": {"serializer": profile.serializer_count(), "arithmetic": profile.arithmetic_owner(),
                    "adjacency": profile.adjacency_owner(), "reserved": if profile == Profile::M3 { Some(7) } else { None }},
                "serializer": {"input_len": plan.serializer.circuit.input_len,
                    "rows": plan.serializer.circuit.row_count, "terms": plan.serializer.circuit.terms.len()},
                "arithmetic": {"input_len": arithmetic.input_len, "rows": arithmetic.row_count,
                    "terms": arithmetic.terms.len(), "live_bits": plan.daa.joined.joined.joined.count.live_bits},
                "adjacency": {"input_len": plan.adjacency.input_len(), "rows": plan.adjacency.row_count(),
                    "terms": ADJACENCY_TERMS},
                "alias_count": plan.alias_count(), "raw_pin_count": plan.raw_pin_count(),
                "total_terms": plan.term_count(), "descriptor": hex(&plan.descriptor())
            }));
        }
    }

    #[test]
    fn verifier_owned_profiles_reject_wrong_count_order_child_and_profile() {
        for profile in profiles() {
            let raws = fixture_raws(profile);
            let mut changed = raws.clone(); changed.swap(0, 1);
            assert!(Plan::build(profile, &changed).is_err(), "{} sample order", profile.name());
            let mut changed = raws.clone(); changed.pop();
            assert!(Plan::build(profile, &changed).is_err(), "{} roster count", profile.name());
            let mut changed = raws.clone(); changed[profile.count() + 1][0] ^= 1;
            assert!(Plan::build(profile, &changed).is_err(), "{} child RAW", profile.name());
            let other = if profile == Profile::M3 { Profile::M4 } else { Profile::M3 };
            assert!(Plan::build(other, &raws).is_err(), "cross-profile roster");
        }
        assert!(Profile::parse("legacy-short-m5-child6145").is_err());
    }

    #[test]
    fn independent_terminal_coefficients_match_emitted_edges_and_alias_ownership() {
        for profile in profiles() {
            let plan = Plan::build(profile, &fixture_raws(profile)).unwrap();
            let r = (0..ROW_LOG).map(|i| Fr::from((7 + 11 * i) as u64)).collect::<Vec<_>>();
            let u = (0..INPUT_LOG).map(|i| Fr::from((13 + 17 * i) as u64)).collect::<Vec<_>>();
            let v = (0..INPUT_LOG).map(|i| Fr::from((19 + 23 * i) as u64)).collect::<Vec<_>>();
            let rw = crate::gkr::eq_weights(&r); let uw = crate::gkr::eq_weights(&u); let vw = crate::gkr::eq_weights(&v);
            let mut expected = [Fr::zero(); 4]; let mut count = 0usize;
            for slot in 0..1 << SLOT_LOG {
                plan.visit_endpoint(true, slot, &mut |edge| {
                    let row = crate::sparse_stream_roster::global_edge_row(edge.source_slot,
                        edge.family_row, SLOT_LOG, ROW_LOCAL_LOG, 0, &[ROW_LOCAL_LOG])?;
                    push_coefficients(&mut expected, &edge.term.gate,
                        rw[row] * uw[edge.term.gate.left] * vw[edge.term.gate.right]);
                    count += 1; Ok(())
                }).unwrap();
            }
            assert_eq!(count, plan.term_count());
            assert_eq!(plan.coefficients(&r, &u, &v).unwrap(), expected);
            let term = &plan.aliases[plan.raw_pin_terms];
            let owner = profile.adjacency_owner();
            let row = (owner << ROW_LOCAL_LOG) + term.row;
            let actual = plan.coefficients(&bool_point(row, ROW_LOG),
                &bool_point(term.gate.left, INPUT_LOG), &bool_point(term.gate.right, INPUT_LOG)).unwrap();
            assert_eq!(actual, [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()],
                "{} imported alias endpoint", profile.name());
            let wrong_owner = if profile == Profile::M3 { 7 } else { owner - 1 };
            assert_ne!(wrong_owner, owner);
            let relocated_row = (wrong_owner << ROW_LOCAL_LOG) + term.row;
            let relocated = plan.coefficients(&bool_point(relocated_row, ROW_LOG),
                &bool_point(term.gate.left, INPUT_LOG), &bool_point(term.gate.right, INPUT_LOG)).unwrap();
            assert_eq!(relocated, [Fr::zero(); 4], "wrong row owner must lose this alias");
            // Corrupt the emitted stream itself, then compare with the unchanged
            // verifier coefficients. Each fault alters exactly one alias event.
            for relocated_owner in [None, Some(wrong_owner)] {
                let mut mutated = [Fr::zero(); 4];
                let mut faults = 0usize;
                for slot in 0..1 << SLOT_LOG {
                    plan.visit_endpoint(true, slot, &mut |mut edge| {
                        if edge.source_slot == owner && edge.family_row == term.row {
                            faults += 1;
                            if let Some(other) = relocated_owner { edge.source_slot = other; }
                            else { return Ok(()); }
                        }
                        let row = crate::sparse_stream_roster::global_edge_row(edge.source_slot,
                            edge.family_row, SLOT_LOG, ROW_LOCAL_LOG, 0, &[ROW_LOCAL_LOG])?;
                        push_coefficients(&mut mutated, &edge.term.gate,
                            rw[row] * uw[edge.term.gate.left] * vw[edge.term.gate.right]);
                        Ok(())
                    }).unwrap();
                }
                assert_eq!(faults, 1, "single emitted alias fault");
                assert_ne!(mutated, expected, "{} emitted alias fault {relocated_owner:?}", profile.name());
            }
        }
    }

    #[test]
    fn coherent_sample_port_changes_still_fail_exact_raw_pins_and_direct_edge() {
        for profile in profiles() {
            let raws = fixture_raws(profile);
            let plan = Plan::build(profile, &raws).unwrap();
            let witness = plan.materialize_witness().unwrap();
            for (owner, field_kind) in [(1usize, 0u8), (2, 1), (2, 2)] {
                let mut fields = plan.fields.clone();
                let mut header = Header::decode(&raws[owner], None).unwrap();
                match field_kind { 0 => header.height += 1, 1 => header.timestamp += 1,
                    2 => header.n_bits ^= 1, _ => unreachable!() }
                fields[owner] = Fields::from_header(&header).unwrap();
                let mut changed = witness.clone();
                let assignment = plan.serializer.assign(&fields[owner]);
                changed[owner * WIDTH..(owner + 1) * WIDTH].copy_from_slice(&assignment);
                let changed_arithmetic = arithmetic(profile, &fields);
                let compiled = &changed_arithmetic.joined.joined.joined;
                let circuit = compiled.circuit.as_ref().unwrap();
                check_circuit(circuit, &compiled.witness).unwrap();
                let a = profile.arithmetic_owner();
                changed[a * WIDTH..a * WIDTH + ARITH_INPUT_LEN].copy_from_slice(&compiled.witness);
                check_circuit(&plan.serializer.circuit, &changed[owner * WIDTH..(owner + 1) * WIDTH]).unwrap();
                assert!(plan.aliases[..plan.raw_pin_terms].iter().any(|term| !term.gate.evaluate(&changed).is_zero()),
                    "{} RAW owner{owner} field{field_kind}", profile.name());
                if field_kind != 0 {
                    assert!(plan.aliases[plan.raw_pin_terms..].iter().all(|term| term.gate.evaluate(&changed).is_zero()),
                        "{} coherent arithmetic ports owner{owner} field{field_kind}", profile.name());
                }
                assert!(plan.check_residuals(&changed).is_err(), "{} exact RAW pin", profile.name());
            }
            let owner = profile.adjacency_owner();
            let mut changed = witness.clone();
            changed[owner * WIDTH + 512] = Fr::one() - changed[owner * WIDTH + 512];
            assert!(plan.adjacency.residuals(&changed[owner * WIDTH..owner * WIDTH + plan.adjacency.input_len()])
                .unwrap().iter().any(|residual| !residual.is_zero()), "{} child direct edge", profile.name());
            assert!(plan.check_residuals(&changed).is_err(), "{} direct edge/import", profile.name());
        }
    }

    #[test]
    fn quotient_alias_magnitude_sign_and_descriptor_faults_reject() {
        for profile in profiles() {
            let mut plan = Plan::build(profile, &fixture_raws(profile)).unwrap();
            let mut witness = plan.materialize_witness().unwrap();
            let owner = profile.arithmetic_owner();
            let alias = &plan.daa.joined.joined.output.aliases[0];
            for wire in [alias.magnitude[0], alias.negative] {
                let global = owner * WIDTH + wire;
                witness[global] = Fr::one() - witness[global];
                assert!(plan.check_residuals(&witness).is_err(), "{} quotient alias wire{wire}", profile.name());
                witness[global] = Fr::one() - witness[global];
            }
            let mut honest = Transcript::new(b"short-legacy-descriptor-binding-test-v1");
            plan.bind(&mut honest, &[7; 32], &[11; 384]);
            let honest_challenge = honest.challenge_scalar(b"first-challenge");
            plan.descriptor[0] ^= 1;
            let mut changed = Transcript::new(b"short-legacy-descriptor-binding-test-v1");
            plan.bind(&mut changed, &[7; 32], &[11; 384]);
            assert_ne!(changed.challenge_scalar(b"first-challenge"), honest_challenge,
                "{} changed descriptor must change the actual transcript", profile.name());
        }
    }
}

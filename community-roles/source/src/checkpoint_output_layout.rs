//! Public checkpoint bytes and audit-floor work from existing history wires.
//! This role does not certify the history/work producers or authenticate its
//! returned GKR claim to PCS. Production maturity is fixed at 64 headers.

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    gkr::{self, Gate, GkrError, GkrProof, InputClaim},
    sparse::Term,
    transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self as layout, WIDTH},
};

const RAW_BITS: usize = 514 * 8;
const LENGTH_BITS: usize = 10;
const WORK_BITS: usize = 224;
const WORK_ROW: usize = RAW_BITS + LENGTH_BITS;
const TERMS: usize = WORK_ROW + WORK_BITS;
const ROW_LOG: usize = 13;
const PRODUCTION_DOMAIN: &[u8] = b"checkpoint-output-native-k64-v1";
#[cfg(test)]
const DIAGNOSTIC_DOMAIN: &[u8] = b"checkpoint-output-n3n4-diagnostic-k1-v1";

#[derive(Clone, Debug)]
pub(crate) struct CheckpointPublic {
    pub(crate) raw: Vec<u8>,
    pub(crate) floor_work: [u8; 28],
    pub(crate) audit_work: [u8; 28],
}

/// Construction is mandatory on the verifier's expected public statement.
/// All coordinates and expected bits are immutable and compiler-owned.
pub(crate) struct CheckpointOutputLayout<'a> {
    parent: &'a WorkTreeHistoryPlan,
    h: u64,
    f: u64,
    depth: u64,
    domain: &'static [u8],
    public: CheckpointPublic,
    sources: Vec<usize>,
    expected: Vec<bool>,
    map_fingerprint: String,
}

fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |acc, (bit, value)| {
        acc * if (index >> bit) & 1 == 1 { *value } else { Fr::one() - value }
    })
}

/// Fixed-width unsigned subtraction. Neither field reduction nor a repaired
/// caller value can stand in for this check.
fn checked_difference(total: &[u8; 28], floor: &[u8; 28]) -> Result<[u8; 28], String> {
    if floor >= total {
        return Err("checkpoint audit work requires floor < total".into());
    }
    let mut result = [0u8; 28];
    let mut borrow = 0i16;
    for index in (0..28).rev() {
        let value = i16::from(total[index]) - i16::from(floor[index]) - borrow;
        if value < 0 { result[index] = (value + 256) as u8; borrow = 1; }
        else { result[index] = value as u8; borrow = 0; }
    }
    if borrow != 0 { return Err("checkpoint audit work subtraction underflow".into()); }
    Ok(result)
}

impl<'a> CheckpointOutputLayout<'a> {
    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan, h: u64, public: CheckpointPublic)
        -> Result<Self, String>
    {
        Self::compile(parent, h, public, 64, PRODUCTION_DOMAIN)
    }

    #[cfg(test)]
    fn diagnostic(parent: &'a WorkTreeHistoryPlan, h: u64, public: CheckpointPublic)
        -> Result<Self, String>
    {
        if !matches!(parent.headers(), 3 | 4) || parent.slot_log() != 2 || parent.slots() != 4 {
            return Err("checkpoint diagnostic requires N3/N4/S4".into());
        }
        Self::compile(parent, h, public, 1, DIAGNOSTIC_DOMAIN)
    }

    fn compile(parent: &'a WorkTreeHistoryPlan, h: u64, public: CheckpointPublic,
        depth: u64, domain: &'static [u8]) -> Result<Self, String>
    {
        let s = parent.slot_log();
        if WIDTH != 1 << 20 || !(2..=21).contains(&s)
            || parent.slots() != 1usize << s
            || parent.headers().checked_next_power_of_two() != Some(parent.slots() as u64)
            || parent.headers() > i32::MAX as u64
            || 1usize.checked_shl((20 + s) as u32).is_none()
        { return Err("checkpoint parent geometry rejected".into()); }
        if h < 2 { return Err("checkpoint query requires h >= 2".into()); }
        let required = h.checked_add(depth).ok_or("checkpoint eligibility overflow")?;
        let f = required.checked_sub(1).ok_or("checkpoint floor overflow")?;
        if parent.headers() < required { return Err("checkpoint query is immature".into()); }
        let header_owner = usize::try_from(h - 1).map_err(|_| "checkpoint header owner overflow")?;
        let floor_leaf = usize::try_from(f.checked_sub(2).ok_or("checkpoint floor below 2")?)
            .map_err(|_| "checkpoint floor leaf overflow")?;
        if header_owner as u64 >= parent.headers()
            || floor_leaf as u64 >= parent.headers() - 1
        { return Err("checkpoint source outside genuine history".into()); }
        if public.raw.len() > 514 { return Err("checkpoint RAW exceeds local 514-byte representation".into()); }
        let decoded = ergo_header_core::Header::decode(&public.raw, None)
            .map_err(|e| format!("checkpoint RAW canonical decode: {e:?}"))?;
        let encoded = decoded.encode().map_err(|e| format!("checkpoint RAW encode: {e:?}"))?;
        if encoded != public.raw { return Err("checkpoint RAW is not canonical".into()); }
        if u64::from(decoded.height) != h { return Err("checkpoint RAW height differs from query".into()); }
        let difference = checked_difference(&parent.work_profile().total_be28, &public.floor_work)?;
        if difference != public.audit_work { return Err("checkpoint supplied audit work differs from checked difference".into()); }

        // All inexpensive public admission precedes the shared template lookup.
        let baseline = layout::shared_baseline()?;
        if baseline.header_alias_wires.len() != RAW_BITS + LENGTH_BITS + 64
            || baseline.endpoints.upper.len() != WORK_BITS
        { return Err("checkpoint producer map widths changed".into()); }
        let header_base = header_owner.checked_mul(WIDTH).ok_or("checkpoint header base overflow")?;
        let floor_base = floor_leaf.checked_mul(WIDTH).ok_or("checkpoint floor base overflow")?;
        let input_len = 1usize << (20 + s);
        let mut sources = Vec::with_capacity(TERMS);
        for (&wire, base) in baseline.header_alias_wires[..WORK_ROW].iter().map(|w| (w, header_base))
            .chain(baseline.endpoints.upper.iter().map(|w| (w, floor_base)))
        {
            if wire >= WIDTH { return Err("checkpoint local source outside bank".into()); }
            let source = base.checked_add(wire).filter(|v| *v < input_len)
                .ok_or("checkpoint translated source outside input")?;
            sources.push(source);
        }
        let mut expected = Vec::with_capacity(TERMS);
        for byte in 0..514 {
            let value = public.raw.get(byte).copied().unwrap_or(0);
            for bit in 0..8 { expected.push((value >> bit) & 1 == 1); }
        }
        for bit in 0..LENGTH_BITS { expected.push((public.raw.len() >> bit) & 1 == 1); }
        for bit in 0..WORK_BITS { expected.push((public.floor_work[27 - bit / 8] >> (bit % 8)) & 1 == 1); }
        let mut map_bytes = b"checkpoint-output-source-map-v1".to_vec();
        for (row, source) in sources.iter().enumerate() {
            map_bytes.extend_from_slice(&(row as u64).to_le_bytes());
            map_bytes.extend_from_slice(&(*source as u64).to_le_bytes());
        }
        Ok(Self { parent, h, f, depth, domain, public, sources, expected,
            map_fingerprint: layout::hash_bytes(&map_bytes) })
    }

    pub(crate) fn input_log(&self) -> usize { 20 + self.parent.slot_log() }
    pub(crate) fn row_log(&self) -> usize { ROW_LOG }

    pub(crate) fn visit_terms(&self, mut sink: impl FnMut(Term) -> Result<(), String>)
        -> Result<usize, String>
    {
        for (row, (&source, &bit)) in self.sources.iter().zip(&self.expected).enumerate() {
            sink(Term { row, gate: Gate { left: source, right: 0, c0: -Fr::from(bit as u64),
                c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } })?;
        }
        Ok(TERMS)
    }

    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"checkpoint-output-profile", self.domain);
        for (tag, value) in [
            (b"checkpoint-output-version".as_slice(), 1),
            (b"checkpoint-output-h".as_slice(), self.h),
            (b"checkpoint-output-f".as_slice(), self.f),
            (b"checkpoint-output-depth".as_slice(), self.depth),
            (b"checkpoint-output-n".as_slice(), self.parent.headers()),
            (b"checkpoint-output-input-log".as_slice(), self.input_log() as u64),
            (b"checkpoint-output-row-log".as_slice(), ROW_LOG as u64),
            (b"checkpoint-output-term-count".as_slice(), TERMS as u64),
            (b"checkpoint-output-raw-length".as_slice(), self.public.raw.len() as u64),
        ] { transcript.append_u64(tag, value); }
        transcript.append_bytes(b"checkpoint-output-raw", &self.public.raw);
        transcript.append_bytes(b"checkpoint-output-floor-work-be28", &self.public.floor_work);
        transcript.append_bytes(b"checkpoint-output-audit-work-be28", &self.public.audit_work);
        transcript.append_bytes(b"checkpoint-output-map-fingerprint", self.map_fingerprint.as_bytes());
        self.parent.bind(transcript);
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != ROW_LOG || u.len() != self.input_log() || v.len() != self.input_log() {
            return Err("checkpoint coefficient point dimensions rejected".into());
        }
        let header = eq(&u[20..], (self.h - 1) as usize);
        let floor = eq(&u[20..], (self.f - 2) as usize);
        let right = eq(v, 0);
        let mut result = [Fr::zero(); 4];
        for (row, (&source, &bit)) in self.sources.iter().zip(&self.expected).enumerate() {
            let owner = if row < WORK_ROW { header } else { floor };
            let weight = eq(r, row) * eq(&u[..20], source % WIDTH) * owner * right;
            result[0] -= Fr::from(bit as u64) * weight;
            result[1] += weight;
        }
        Ok(result)
    }

    /// Returns a terminal input claim. The caller must authenticate that claim
    /// to the same commitment as every required history role before admission.
    pub(crate) fn verify(&self, proof: &GkrProof, transcript: &mut Transcript)
        -> Result<InputClaim, GkrError>
    {
        gkr::verify_with_wiring(&[self.input_log()], 1 << ROW_LOG, proof, transcript,
            |t| self.bind(t), |_layer, r, u, v|
                self.coefficients(r, u, v).map_err(|_| GkrError::PointDimension))
    }
}

/// Internal row placement only; this descriptor admits no public statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CheckpointRole4Descriptor {
    pub(crate) root: [u8; 32],
    pub(crate) total: [u8; 28],
    pub(crate) headers: u64,
    pub(crate) slot_log: usize,
    pub(crate) h: u64,
    pub(crate) f: u64,
    pub(crate) depth: u64,
    pub(crate) input_log: usize,
    pub(crate) row_log: usize,
    pub(crate) base: usize,
    pub(crate) live_rows: usize,
    pub(crate) map_fingerprint: String,
    pub(crate) public_fingerprint: String,
}

/// A row-only embedding into role4's unused family0 range. X is unchanged.
pub(crate) struct CheckpointRole4Lane<'a> {
    checkpoint: CheckpointOutputLayout<'a>,
    descriptor: CheckpointRole4Descriptor,
}

impl<'a> CheckpointRole4Lane<'a> {
    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan, h: u64, public: CheckpointPublic)
        -> Result<Self, String>
    {
        let s = parent.slot_log();
        if !(7..=21).contains(&s) { return Err("checkpoint role4 requires s7..s21".into()); }
        let checkpoint = CheckpointOutputLayout::new(parent, h, public)?;
        let base = 1usize.checked_shl((6 + s).max(ROW_LOG) as u32)
            .ok_or("checkpoint role4 base overflow")?;
        let daa_base = 1usize.checked_shl((19 + s) as u32)
            .ok_or("checkpoint role4 DAA base overflow")?;
        if base % (1 << ROW_LOG) != 0
            || base.checked_add(TERMS).is_none_or(|end| end > daa_base)
            || base.checked_add(TERMS - 1).is_none_or(|last| last >> 19 != base >> 19)
        { return Err("checkpoint role4 row overlap".into()); }
        let mut public_bytes = b"checkpoint-role4-expected-public-v1".to_vec();
        public_bytes.extend_from_slice(&(checkpoint.public.raw.len() as u64).to_le_bytes());
        public_bytes.extend_from_slice(&checkpoint.public.raw);
        public_bytes.extend_from_slice(&checkpoint.public.floor_work);
        public_bytes.extend_from_slice(&checkpoint.public.audit_work);
        let descriptor = CheckpointRole4Descriptor { root: parent.descriptor().root,
            total: parent.work_profile().total_be28, headers: parent.headers(), slot_log: s,
            h: checkpoint.h, f: checkpoint.f, depth: checkpoint.depth,
            input_log: 20 + s, row_log: 20 + s, base, live_rows: TERMS,
            map_fingerprint: checkpoint.map_fingerprint.clone(),
            public_fingerprint: layout::hash_bytes(&public_bytes) };
        Ok(Self { checkpoint, descriptor })
    }

    pub(crate) fn descriptor(&self) -> CheckpointRole4Descriptor { self.descriptor.clone() }

    pub(crate) fn validate_descriptor(&self, requested: &CheckpointRole4Descriptor) -> Result<(), String> {
        if requested != &self.descriptor { return Err("checkpoint role4 descriptor mismatch".into()); }
        Ok(())
    }

    pub(crate) fn bind(&self, transcript: &mut Transcript) -> Result<(), String> {
        if transcript.challenges() != 0 { return Err("checkpoint role4 binding after challenge".into()); }
        transcript.append_bytes(b"checkpoint-role4-internal", b"checkpoint-role4-lane-k64-v1");
        let d = &self.descriptor;
        for value in [d.base, d.live_rows, d.input_log, d.row_log, ROW_LOG, 19, 0] {
            transcript.append_u64(b"checkpoint-role4-geometry", value as u64);
        }
        transcript.append_bytes(b"checkpoint-role4-mapping", b"row-only;family0;original-X;global-right-zero");
        transcript.append_bytes(b"checkpoint-role4-root", &d.root);
        transcript.append_bytes(b"checkpoint-role4-total", &d.total);
        transcript.append_bytes(b"checkpoint-role4-public", d.public_fingerprint.as_bytes());
        self.checkpoint.bind(transcript);
        Ok(())
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let d = &self.descriptor;
        if r.len() != d.row_log || u.len() != d.input_log || v.len() != d.input_log {
            return Err("checkpoint role4 coefficient dimensions".into());
        }
        let owner = eq(&r[ROW_LOG..], d.base >> ROW_LOG);
        Ok(self.checkpoint.coefficients(&r[..ROW_LOG], u, v)?.map(|value| owner * value))
    }

    fn translated(&self, mut term: Term) -> Result<Term, String> {
        if term.row >= TERMS || term.gate.right != 0 {
            return Err("checkpoint role4 local row or global zero".into());
        }
        term.row = self.descriptor.base.checked_add(term.row).ok_or("checkpoint role4 row overflow")?;
        Ok(term)
    }

    pub(crate) fn visit_owner_terms(&self, requested: &CheckpointRole4Descriptor, owner: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<usize, String>
    {
        self.validate_descriptor(requested)?;
        if owner >= self.checkpoint.parent.slots() { return Err("checkpoint role4 row owner".into()); }
        if owner != self.descriptor.base >> 19 { return Ok(0); }
        let mut count = 0;
        self.checkpoint.visit_terms(|term| {
            let term = self.translated(term)?;
            if term.row >> 19 == owner { sink(term)?; count += 1; }
            Ok(())
        })?;
        Ok(count)
    }

    /// Inverse X endpoints, independent of the row owner. No history scan.
    pub(crate) fn visit_endpoint(&self, requested: &CheckpointRole4Descriptor, left: bool, owner: usize,
        mut sink: impl FnMut(crate::sparse_stream_roster::EdgeTerm) -> Result<(), String>)
        -> Result<usize, String>
    {
        self.validate_descriptor(requested)?;
        if owner >= self.checkpoint.parent.slots() { return Err("checkpoint role4 endpoint owner".into()); }
        if if left { owner != (self.checkpoint.h - 1) as usize && owner != (self.checkpoint.f - 2) as usize }
            else { owner != 0 }
        { return Ok(0); }
        let mut count = 0;
        self.checkpoint.visit_terms(|term| {
            let endpoint = if left { term.gate.left } else { term.gate.right };
            if endpoint / WIDTH == owner {
                let term = self.translated(term)?;
                let edge = crate::sparse_stream_roster::EdgeTerm { source_slot: term.row >> 19,
                    family_row: term.row & ((1 << 19) - 1), term };
                if crate::sparse_stream_roster::global_edge_row(edge.source_slot, edge.family_row,
                    self.descriptor.slot_log, 19, 1, &[19, 19])? != edge.term.row
                { return Err("checkpoint role4 endpoint row packing".into()); }
                sink(edge)?; count += 1;
            }
            Ok(())
        })?;
        Ok(count)
    }
}

#[cfg(test)]
#[path = "checkpoint_output_tests.rs"]
mod tests;

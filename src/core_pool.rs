//! Bounded tensor view over the eleven fixed compression banks.
//!
//! This module proves only the admitted single-slot producer (`h = 0`).
//! Larger dimensions are represented for verifier shape analysis and tiny
//! differential fixtures; they never cause the real history loader to run.

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    gkr::{self, GkrError, GkrProof, InputClaim},
    sparse::{self, Circuit, Shape, Term},
    sparse_stream_roster,
    transcript::Transcript,
    work_tree_fixed_hash as fixed, work_tree_layout as layout,
};

const LOCAL_INPUT_BITS: usize = 16;
const LOCAL_ROW_BITS: usize = 17;
const BANK_BITS: usize = 4;
const FAMILY_BITS: usize = 4;
const FAMILY_COUNT: usize = 11;
const CORE_TERMS: usize = 172_480;
const MAX_COPY_BITS: usize = 21;
const PRODUCER_COPY_BITS: usize = 0;
const PROFILE: &[u8] = b"work-tree-eleven-core-pool-v1";
const FIELD_BYTES: usize = 32;
const ENTRY_BYTES: usize = 40;
const DESCRIPTOR_BYTES: usize = 72;
const CACHE_BOUND_AT_H0: usize = 337_119_464;

/// Checked arithmetic-only estimates; these are not execution measurements.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CostReport {
    pub copy_bits: usize,
    pub global_terms: usize,
    pub packed_trace_bytes: usize,
    pub gkr_proof_bytes: usize,
    pub cache_bound_bytes: usize,
    pub full_input_field_bytes: usize,
    pub field_bytes: usize,
    pub sparse_entry_bytes: usize,
    pub slot_descriptor_bytes: usize,
}

/// A frozen view of the code-owned compression template and its bank map.
/// All dimensions and commitment material are private to this module.
pub(crate) struct Plan {
    engine: &'static fixed::Engine,
    copy_bits: usize,
    input_log: usize,
    row_log: usize,
    input_len: usize,
    row_count: usize,
    total_terms: usize,
    core_shape: Shape,
    core_hash: String,
    descriptor_hash: String,
}

/// Not caller-constructible: only a checked OLD Plan issues this authority.
#[cfg(test)]
pub(crate) struct PackedCoreAuthority<'a> {
    plan: &'a Plan,
    view: crate::packed::PackedOwnerView<'a>,
}

#[cfg(test)]
impl PackedCoreAuthority<'_> {
    pub(crate) fn core(&self) -> &Circuit { &self.plan.engine.core }
    pub(crate) fn banks(&self) -> [usize; 11] {
        layout::CORE_OFFSETS.map(|offset| offset / layout::CORE)
    }
    pub(crate) fn view(&self) -> &crate::packed::PackedOwnerView<'_> { &self.view }
    pub(crate) fn bind(&self, transcript: &mut Transcript) { self.plan.bind(transcript); }
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        self.plan.coefficients(r, u, v).map_err(|error| error.to_string())
    }
}

/// Distinct h2 authority; the h0 factory and its logical range stay unchanged.
#[cfg(test)]
pub(crate) struct PackedFourOwnerAuthority<'a> {
    plan: &'a Plan,
    view: crate::packed::PackedFourOwnerView<'a>,
}

#[cfg(test)]
impl PackedFourOwnerAuthority<'_> {
    pub(crate) fn core(&self) -> &Circuit { &self.plan.engine.core }
    pub(crate) fn banks(&self) -> [usize; 11] { layout::CORE_OFFSETS.map(|offset| offset / layout::CORE) }
    pub(crate) fn view(&self) -> &crate::packed::PackedFourOwnerView<'_> { &self.view }
    pub(crate) fn bind(&self, transcript: &mut Transcript) { self.plan.bind(transcript); }
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        self.plan.coefficients(r, u, v).map_err(|e| e.to_string())
    }
    /// Private transport context, never appended to the GKR transcript.
    pub(crate) fn spool_descriptor(&self) -> [u8; 64] {
        use blake2::{Blake2b512, Digest};
        let mut h = Blake2b512::new();
        h.update(b"private-real-old-h2-phase-v1");
        for value in [PROFILE, layout::BASELINE_ID.as_bytes(), layout::CONTRACT_SHA256.as_bytes(),
            self.plan.core_hash.as_bytes(), self.plan.descriptor_hash.as_bytes()] {
            h.update((value.len() as u64).to_le_bytes()); h.update(value);
        }
        for value in [self.plan.copy_bits, self.plan.input_log, self.plan.row_log,
            self.plan.input_len, self.plan.total_terms] { h.update((value as u64).to_le_bytes()); }
        for bank in self.banks() { h.update((bank as u64).to_le_bytes()); }
        h.finalize().into()
    }
}

/// Exact h12 packed-source authority for the native role0 diagnostic only.
#[cfg(test)]
pub(crate) struct PackedNativeRole0Authority<'a> {
    plan: &'a Plan,
    view: crate::packed::PackedNativeRole0View<'a>,
}

#[cfg(test)]
impl PackedNativeRole0Authority<'_> {
    pub(crate) fn core(&self) -> &Circuit { &self.plan.engine.core }
    pub(crate) fn banks(&self) -> [usize; 11] {
        layout::CORE_OFFSETS.map(|offset| offset / layout::CORE)
    }
    pub(crate) fn view(&self) -> &crate::packed::PackedNativeRole0View<'_> { &self.view }
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        self.plan.coefficients(r, u, v).map_err(|error| error.to_string())
    }
}

impl Plan {
    /// Construct a checked tensor shape. Only `h=0` is admitted by `prove`.
    pub(crate) fn new(copy_bits: usize) -> Result<Self, String> {
        if copy_bits > MAX_COPY_BITS {
            return Err("core-pool copy dimension exceeds verifier limit".into());
        }
        let input_log = 20usize
            .checked_add(copy_bits)
            .ok_or("core-pool input dimension overflow")?;
        let row_log = 21usize
            .checked_add(copy_bits)
            .ok_or("core-pool row dimension overflow")?;
        let input_len = 1usize
            .checked_shl(input_log as u32)
            .ok_or("core-pool input width overflow")?;
        let row_count = 1usize
            .checked_shl(row_log as u32)
            .ok_or("core-pool row count overflow")?;
        let copies = 1usize
            .checked_shl(copy_bits as u32)
            .ok_or("core-pool slot count overflow")?;
        let total_terms = CORE_TERMS
            .checked_mul(FAMILY_COUNT)
            .and_then(|count| count.checked_mul(copies))
            .ok_or("core-pool term count overflow")?;

        let engine = fixed::engine()?;
        let core_shape = validate_template(engine)?;
        Ok(Self {
            engine,
            copy_bits,
            input_log,
            row_log,
            input_len,
            row_count,
            total_terms,
            core_shape,
            core_hash: engine.base.inventory.core.terms_blake2b256.clone(),
            descriptor_hash: engine.base.inventory.descriptor_blake2b256.clone(),
        })
    }

    #[cfg(test)]
    pub(crate) fn require_native_role0_shape(&self) -> Result<(), String> {
        if self.copy_bits != 12 || self.input_log != 32 || self.row_log != 33
            || self.input_len != 1usize << 32 || self.row_count != 1usize << 33
            || self.total_terms != 7_771_258_880 {
            return Err("native role0 producer requires exact S12 h12 shape".into());
        }
        Ok(())
    }

    pub(crate) fn input_log(&self) -> usize {
        self.input_log
    }
    pub(crate) fn row_log(&self) -> usize {
        self.row_log
    }
    pub(crate) fn input_len(&self) -> usize {
        self.input_len
    }
    pub(crate) fn row_count(&self) -> usize {
        self.row_count
    }
    pub(crate) fn term_count(&self) -> usize {
        self.total_terms
    }
    pub(crate) fn copy_bits(&self) -> usize {
        self.copy_bits
    }

    pub(crate) fn cost_report(&self) -> Result<CostReport, String> {
        let copies = 1usize
            .checked_shl(self.copy_bits as u32)
            .ok_or("core-pool cost slot count overflow")?;
        let packed_trace_bytes = self
            .input_len
            .checked_div(8)
            .ok_or("core-pool packed trace size overflow")?;
        let proof_scalars = self
            .input_log
            .checked_mul(7)
            .and_then(|count| count.checked_add(3))
            .ok_or("core-pool GKR scalar count overflow")?;
        let gkr_proof_bytes = proof_scalars
            .checked_mul(FIELD_BYTES)
            .ok_or("core-pool GKR proof byte count overflow")?;
        let cache_bound_bytes = CACHE_BOUND_AT_H0
            .checked_mul(copies)
            .ok_or("core-pool cache bound overflow")?;
        let full_input_field_bytes = self
            .input_len
            .checked_mul(FIELD_BYTES)
            .ok_or("core-pool full input byte count overflow")?;
        Ok(CostReport {
            copy_bits: self.copy_bits,
            global_terms: self.total_terms,
            packed_trace_bytes,
            gkr_proof_bytes,
            cache_bound_bytes,
            full_input_field_bytes,
            field_bytes: FIELD_BYTES,
            sparse_entry_bytes: ENTRY_BYTES,
            slot_descriptor_bytes: DESCRIPTOR_BYTES,
        })
    }

    /// Bind the public template, bank inventory, and exact tensor dimensions.
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"core-pool-profile", PROFILE);
        transcript.append_bytes(b"core-pool-baseline", layout::BASELINE_ID.as_bytes());
        transcript.append_bytes(b"core-pool-contract", layout::CONTRACT_SHA256.as_bytes());
        transcript.append_bytes(b"core-pool-template-hash", self.core_hash.as_bytes());
        transcript.append_bytes(b"core-pool-inventory-hash", self.descriptor_hash.as_bytes());
        gkr::append_usize(transcript, b"core-pool-copy-bits", self.copy_bits);
        gkr::append_usize(transcript, b"core-pool-input-log", self.input_log);
        gkr::append_usize(transcript, b"core-pool-row-log", self.row_log);
        gkr::append_usize(
            transcript,
            b"core-pool-core-terms",
            self.engine.core.terms.len(),
        );
        gkr::append_usize(transcript, b"core-pool-total-terms", self.total_terms);
        gkr::append_usize(transcript, b"core-pool-family-count", FAMILY_COUNT);
        for (family, offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
            gkr::append_usize(transcript, b"core-pool-family", family);
            gkr::append_usize(transcript, b"core-pool-bank-offset", offset);
        }
    }

    /// Evaluate the pooled wiring polynomial at possibly non-Boolean points.
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], GkrError> {
        if r.len() != self.row_log || u.len() != self.input_log || v.len() != self.input_log {
            return Err(GkrError::PointDimension);
        }
        let mut coefficients = sparse::wiring(
            &self.engine.core,
            &self.core_shape,
            &r[..LOCAL_ROW_BITS],
            &u[..LOCAL_INPUT_BITS],
            &v[..LOCAL_INPUT_BITS],
        )?;
        let slot_r = &r[LOCAL_ROW_BITS..LOCAL_ROW_BITS + self.copy_bits];
        let slot_u = &u[LOCAL_INPUT_BITS + BANK_BITS..];
        let slot_v = &v[LOCAL_INPUT_BITS + BANK_BITS..];
        let family_r = &r[LOCAL_ROW_BITS + self.copy_bits..];
        let bank_u = &u[LOCAL_INPUT_BITS..LOCAL_INPUT_BITS + BANK_BITS];
        let bank_v = &v[LOCAL_INPUT_BITS..LOCAL_INPUT_BITS + BANK_BITS];

        let slot_factor =
            slot_r
                .iter()
                .zip(slot_u)
                .zip(slot_v)
                .fold(Fr::one(), |acc, ((row, left), right)| {
                    acc * ((Fr::one() - row) * (Fr::one() - left) * (Fr::one() - right)
                        + *row * left * right)
                });
        let mut family_bank_factor = Fr::zero();
        for (family, offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
            let bank = offset / layout::CORE;
            family_bank_factor += eq_weight_at(family_r, family)
                * eq_weight_at(bank_u, bank)
                * eq_weight_at(bank_v, bank);
        }
        let factor = slot_factor * family_bank_factor;
        for coefficient in &mut coefficients {
            *coefficient *= factor;
        }
        Ok(coefficients)
    }

    /// Prove the real eleven-bank relation for one slot only.
    pub(crate) fn prove(
        &self,
        load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        if self.copy_bits != PRODUCER_COPY_BITS {
            return Err("core-pool production is admitted only for h=0".into());
        }
        let mut emit = |copy: usize, sink: &mut dyn FnMut(Term) -> Result<(), String>| {
            self.emit_copy(copy, sink)
        };
        let bind_plan = self;
        sparse_stream_roster::prove(
            20,
            self.copy_bits,
            LOCAL_ROW_BITS,
            FAMILY_BITS,
            &[LOCAL_ROW_BITS; FAMILY_COUNT],
            load_copy,
            transcript,
            |t| bind_plan.bind(t),
            &mut emit,
            |r, u, v| bind_plan.coefficients(r, u, v).map_err(|e| e.to_string()),
        )
    }

    #[cfg(test)]
    pub(crate) fn prove_replay_for_test(
        &self,
        load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim, usize), String> {
        if self.copy_bits != PRODUCER_COPY_BITS {
            return Err("core-pool production is admitted only for h=0".into());
        }
        let mut emitter_passes = 0usize;
        let mut emit = |copy: usize, sink: &mut dyn FnMut(Term) -> Result<(), String>| {
            emitter_passes = emitter_passes
                .checked_add(1)
                .ok_or("core-pool emitter pass counter overflow")?;
            self.emit_copy(copy, sink)
        };
        let result = sparse_stream_roster::prove_with_cache_budget_for_test(
            20,
            self.copy_bits,
            LOCAL_ROW_BITS,
            FAMILY_BITS,
            &[LOCAL_ROW_BITS; FAMILY_COUNT],
            Some(0),
            load_copy,
            transcript,
            |t| self.bind(t),
            &mut emit,
            |r, u, v| self.coefficients(r, u, v).map_err(|e| e.to_string()),
        )?;
        drop(emit);
        Ok((result.0, result.1, emitter_passes))
    }

    #[cfg(test)]
    pub(crate) fn prove_boolean_for_test(
        &self,
        load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        if self.copy_bits != PRODUCER_COPY_BITS {
            return Err("core-pool production is admitted only for h=0".into());
        }
        let banks: Vec<_> = layout::CORE_OFFSETS
            .iter()
            .map(|offset| offset / layout::CORE)
            .collect();
        crate::core_pool_boolean::prove_single_slot(
            &self.engine.core,
            BANK_BITS,
            &banks,
            load_copy,
            transcript,
            |t| self.bind(t),
            |r, u, v| self.coefficients(r, u, v).map_err(|e| e.to_string()),
        )
    }

    #[cfg(test)]
    pub(crate) fn prove_packed_boolean_for_test(
        &self,
        source: &crate::packed::PackedFile,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        if self.copy_bits != 0 || self.input_log != 20 || self.row_log != 21
            || self.input_len != 1usize << 20 || self.total_terms != 11 * CORE_TERMS {
            return Err("packed core-pool production is admitted only for exact OLD h0".into());
        }
        let authority = PackedCoreAuthority { plan: self, view: source.h0_boolean_view()? };
        crate::core_pool_boolean::prove_packed_single_slot(&authority, transcript)
    }

    /// Independent unchanged generic Fr algorithm, zero-cache, h2 only.
    #[cfg(test)]
    pub(crate) fn prove_four_owner_reference_for_test(
        &self,
        load: impl FnMut(usize) -> Result<Vec<Fr>, String>,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        if self.copy_bits != 2 || self.input_log != 22 || self.row_log != 23
            || self.total_terms != 44 * CORE_TERMS {
            return Err("four-owner generic reference requires exact OLD h2".into());
        }
        // Roster callbacks are owner-local; it inserts copy coordinates.
        sparse_stream_roster::prove_with_cache_budget_for_test(
            20, 2, LOCAL_ROW_BITS, FAMILY_BITS, &[LOCAL_ROW_BITS; FAMILY_COUNT], Some(0),
            load, transcript, |t| self.bind(t), |owner, sink| self.emit_copy(owner, sink),
            |r, u, v| self.coefficients(r, u, v).map_err(|e| e.to_string()),
        )
    }

    #[cfg(test)]
    pub(crate) fn prove_packed_four_owners_for_test(
        &self,
        source: &crate::packed::PackedFile,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        if self.copy_bits != 2 || self.input_log != 22 || self.row_log != 23
            || self.input_len != 1usize << 22 || self.total_terms != 44 * CORE_TERMS {
            return Err("packed four-owner production requires exact OLD h2".into());
        }
        let authority = PackedFourOwnerAuthority { plan: self, view: source.h2_boolean_view()? };
        crate::core_pool_boolean::prove_packed_four_owners(&authority, transcript)
    }

    #[cfg(test)]
    pub(crate) fn prove_packed_native_role0_for_test(
        &self,
        source: &crate::packed::PackedFile,
        transcript: &mut Transcript,
        bind: impl FnOnce(&mut Transcript) -> Result<(), String>,
        wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>,
    ) -> Result<(GkrProof, InputClaim), String> {
        self.require_native_role0_shape()?;
        let view = source.native_role0_view()?;
        let authority = PackedNativeRole0Authority { plan: self, view };
        crate::core_pool_boolean::prove_packed_native_role0(&authority, transcript, bind, wiring)
    }

    #[cfg(test)]
    pub(crate) fn prove_packed_four_owners_spooled_for_test(
        &self, source: &crate::packed::PackedFile,
        evidence: &mut crate::high_phase_spool::RealEvidence,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        if self.copy_bits != 2 || self.input_log != 22 || self.row_log != 23
            || self.input_len != 1usize << 22 || self.total_terms != 44 * CORE_TERMS {
            return Err("packed four-owner production requires exact OLD h2".into());
        }
        let authority = PackedFourOwnerAuthority { plan: self, view: source.h2_boolean_view()? };
        crate::core_pool_boolean::prove_spooled_four_owners(&authority, evidence, transcript)
    }

    #[cfg(test)]
    pub(crate) fn prove_boolean_two_slots_for_test(
        &self,
        load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        if self.copy_bits != 1 {
            return Err("two-slot boolean reference requires h=1".into());
        }
        let banks: Vec<_> = layout::CORE_OFFSETS
            .iter()
            .map(|offset| offset / layout::CORE)
            .collect();
        crate::core_pool_boolean::prove_with_copy_bits_for_test(
            &self.engine.core,
            BANK_BITS,
            &banks,
            1,
            load_copy,
            transcript,
            |t| self.bind(t),
            |r, u, v| self.coefficients(r, u, v).map_err(|e| e.to_string()),
        )
    }

    #[cfg(test)]
    pub(crate) fn prove_two_slot_reference_for_test(
        &self,
        load_copy: impl FnMut(usize) -> Result<Vec<Fr>, String>,
        transcript: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim, usize), String> {
        if self.copy_bits != 1 {
            return Err("two-slot reference requires h=1".into());
        }
        let mut emitter_passes = 0usize;
        let mut emit = |copy: usize, sink: &mut dyn FnMut(Term) -> Result<(), String>| {
            emitter_passes = emitter_passes
                .checked_add(1)
                .ok_or("core-pool emitter pass counter overflow")?;
            self.emit_copy(copy, sink)
        };
        let result = sparse_stream_roster::prove(
            20,
            1,
            LOCAL_ROW_BITS,
            FAMILY_BITS,
            &[LOCAL_ROW_BITS; FAMILY_COUNT],
            load_copy,
            transcript,
            |t| self.bind(t),
            &mut emit,
            |r, u, v| self.coefficients(r, u, v).map_err(|e| e.to_string()),
        )?;
        drop(emit);
        Ok((result.0, result.1, emitter_passes))
    }

    pub(crate) fn verify(
        &self,
        proof: &GkrProof,
        transcript: &mut Transcript,
    ) -> Result<InputClaim, GkrError> {
        gkr::verify_with_wiring(
            &[self.input_log],
            self.row_count,
            proof,
            transcript,
            |t| self.bind(t),
            |_index, r, u, v| self.coefficients(r, u, v),
        )
    }

    pub(crate) fn decode(&self, bytes: &[u8]) -> Result<GkrProof, String> {
        gkr::decode_dimensions(&[self.input_log], bytes)
    }

    fn emit_copy(
        &self,
        copy: usize,
        sink: &mut dyn FnMut(Term) -> Result<(), String>,
    ) -> Result<(), String> {
        if copy >= (1usize << self.copy_bits) {
            return Err("core-pool slot outside declared dimensions".into());
        }
        let core = &self.engine.core;
        for (family, offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
            let row_offset = family
                .checked_shl(LOCAL_ROW_BITS as u32)
                .ok_or("core-pool family row offset overflow")?;
            for term in &core.terms {
                let row = term
                    .row
                    .checked_add(row_offset)
                    .ok_or("core-pool row overflow")?;
                // Both coordinates are shifted even when their coefficient is
                // zero, preserving the exact physical bank embedding.
                let left = offset
                    .checked_add(term.gate.left)
                    .ok_or("core-pool left wire overflow")?;
                let right = offset
                    .checked_add(term.gate.right)
                    .ok_or("core-pool right wire overflow")?;
                if row >= (1usize << (LOCAL_ROW_BITS + self.copy_bits + FAMILY_BITS))
                    || left >= self.input_len
                    || right >= self.input_len
                {
                    return Err("core-pool emitted coordinate exceeds declared shape".into());
                }
                sink(Term {
                    row,
                    gate: gkr::Gate {
                        left,
                        right,
                        c0: term.gate.c0,
                        c1: term.gate.c1,
                        c2: term.gate.c2,
                        c3: term.gate.c3,
                    },
                })?;
            }
        }
        Ok(())
    }
}

fn validate_template(engine: &fixed::Engine) -> Result<Shape, String> {
    if engine.base.inventory.baseline_id != layout::BASELINE_ID
        || engine.base.inventory.contract_sha256 != layout::CONTRACT_SHA256
        || engine.core.input_len != layout::CORE
        || engine.core.row_count != 1usize << LOCAL_ROW_BITS
        || engine.core.terms.len() != CORE_TERMS
        || engine
            .core
            .terms
            .windows(2)
            .any(|pair| pair[0].row > pair[1].row)
        || layout::CORE_OFFSETS.len() != FAMILY_COUNT
    {
        return Err("core-pool fixed template or inventory shape drift".into());
    }
    let computed_hash = layout::hash_terms(&engine.core.terms);
    if computed_hash != engine.base.inventory.core.terms_blake2b256 {
        return Err("core-pool compression template hash mismatch".into());
    }
    let mut seen = [false; layout::WIDTH / layout::CORE];
    for offset in layout::CORE_OFFSETS {
        let bank = offset / layout::CORE;
        let end = offset
            .checked_add(layout::CORE)
            .ok_or("core-pool bank end overflow")?;
        if offset % layout::CORE != 0 || end > layout::WIDTH || seen[bank] {
            return Err("core-pool physical bank inventory mismatch".into());
        }
        seen[bank] = true;
    }
    sparse::validate(&engine.core, 0).map_err(|error| error.to_string())
}

fn eq_weight_at(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, coordinate)| {
            weight
                * if index >> bit & 1 == 1 {
                    *coordinate
                } else {
                    Fr::one() - coordinate
                }
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn transcript() -> Transcript {
        Transcript::new(b"core-pool-tests-v1")
    }

    fn large_stack<T: Send + 'static>(run: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(run)
            .unwrap()
            .join()
            .unwrap()
    }

    #[test]
    fn shape_costs_are_checked_and_only_zero_slot_proof_is_admitted() {
        assert!(Plan::new(22).is_err());
        assert!(Plan::new(usize::MAX).is_err());
        large_stack(|| {
            let h0 = Plan::new(0).unwrap();
            assert_eq!(
                (h0.input_log(), h0.row_log(), h0.term_count()),
                (20, 21, 1_897_280)
            );
            let h0_cost = h0.cost_report().unwrap();
            assert_eq!(h0_cost.packed_trace_bytes, 1 << 17);
            assert_eq!(h0_cost.gkr_proof_bytes, (7 * 20 + 3) * 32);
            assert_eq!(h0_cost.cache_bound_bytes, 337_119_464);
            assert!(h0_cost.cache_bound_bytes < 512 * 1024 * 1024);
            let h2 = Plan::new(2).unwrap();
            assert_eq!(
                (h2.input_log(), h2.row_log(), h2.term_count()),
                (22, 23, 7_589_120)
            );
            let h2_cost = h2.cost_report().unwrap();
            assert_eq!(h2_cost.packed_trace_bytes, 1 << 19);
            assert_eq!(h2_cost.gkr_proof_bytes, (7 * 22 + 3) * 32);
            assert_eq!(h2_cost.cache_bound_bytes, 1_348_477_856);
            assert!(h2_cost.cache_bound_bytes > 512 * 1024 * 1024);
            let h21 = Plan::new(21).unwrap();
            assert_eq!((h21.input_log(), h21.row_log()), (41, 42));
            let report = h21.cost_report().unwrap();
            assert_eq!(report.global_terms, 11 * CORE_TERMS * (1usize << 21));
            assert_eq!(report.packed_trace_bytes, 1usize << 38);
            assert_eq!(report.gkr_proof_bytes, (7 * 41 + 3) * 32);
            assert_eq!(report.cache_bound_bytes, CACHE_BOUND_AT_H0 * (1usize << 21));
            assert_eq!(report.full_input_field_bytes, (1usize << 41) * 32);

            let mut called = false;
            let error = h2
                .prove(
                    |_| {
                        called = true;
                        Err("unexpected loader call".into())
                    },
                    &mut transcript(),
                )
                .unwrap_err();
            assert!(error.contains("h=0"));
            assert!(
                !called,
                "nonzero-slot admission must fail before the witness loader"
            );
        });
    }

    #[test]
    fn pooled_coefficients_match_explicit_bank_and_slot_sum_at_non_boolean_points() {
        large_stack(|| {
            let plan = Plan::new(2).unwrap();
            let engine = &plan.engine;
            let values = |n: usize, salt: usize| -> Vec<Fr> {
                (0..n)
                    .map(|i| Fr::from((i * 7 + salt + 2) as u64))
                    .collect()
            };
            let r = values(plan.row_log, 3);
            let u = values(plan.input_log, 5);
            let v = values(plan.input_log, 11);
            let row_weights = gkr::eq_weights(&r[..17]);
            let left_weights = gkr::eq_weights(&u[..16]);
            let right_weights = gkr::eq_weights(&v[..16]);
            let mut expected = [Fr::zero(); 4];
            for family in 0..FAMILY_COUNT {
                let bank = layout::CORE_OFFSETS[family] / layout::CORE;
                let family_weight = eq_weight_at(&r[19..23], family)
                    * eq_weight_at(&u[16..20], bank)
                    * eq_weight_at(&v[16..20], bank);
                for slot in 0..4 {
                    let mut slot_weight = Fr::one();
                    for bit in 0..2 {
                        let (a, b, c) = (r[17 + bit], u[20 + bit], v[20 + bit]);
                        slot_weight *= if slot >> bit & 1 == 1 {
                            a * b * c
                        } else {
                            (Fr::one() - a) * (Fr::one() - b) * (Fr::one() - c)
                        };
                    }
                    let selector = family_weight * slot_weight;
                    for term in &engine.core.terms {
                        let weight = selector
                            * row_weights[term.row]
                            * left_weights[term.gate.left]
                            * right_weights[term.gate.right];
                        expected[0] += weight * term.gate.c0;
                        expected[1] += weight * term.gate.c1;
                        expected[2] += weight * term.gate.c2;
                        expected[3] += weight * term.gate.c3;
                    }
                }
            }
            assert_eq!(plan.coefficients(&r, &u, &v).unwrap(), expected);
            assert_eq!(
                plan.coefficients(&r[..plan.row_log - 1], &u, &v),
                Err(GkrError::PointDimension)
            );
        });
    }

    #[test]
    fn emitter_maps_all_terms_to_each_exact_physical_bank() {
        large_stack(|| {
            let plan = Plan::new(0).unwrap();
            let mut seen = 0usize;
            plan.emit_copy(0, &mut |actual| {
                let family = actual.row >> LOCAL_ROW_BITS;
                let local_row = actual.row & ((1 << LOCAL_ROW_BITS) - 1);
                let offset = layout::CORE_OFFSETS[family];
                let expected_index = seen % CORE_TERMS;
                let expected = &plan.engine.core.terms[expected_index];
                assert_eq!(local_row, expected.row);
                assert_eq!(actual.gate.left, offset + expected.gate.left);
                assert_eq!(actual.gate.right, offset + expected.gate.right);
                assert_eq!(actual.gate.c0, expected.gate.c0);
                assert_eq!(actual.gate.c1, expected.gate.c1);
                assert_eq!(actual.gate.c2, expected.gate.c2);
                assert_eq!(actual.gate.c3, expected.gate.c3);
                seen += 1;
                Ok(())
            })
            .unwrap();
            assert_eq!(seen, plan.term_count());
        });
    }

    fn toy_terms() -> Vec<Term> {
        let mut out = Vec::new();
        for row in 0..4 {
            let left = row % 4;
            let right = (row + 1) % 4;
            let c1 = Fr::from((row + 2) as u64);
            let c2 = Fr::from((row + 5) as u64);
            let c3 = Fr::from((row + 3) as u64);
            let x = [
                Fr::from(2u64),
                Fr::from(3u64),
                Fr::from(5u64),
                Fr::from(7u64),
            ];
            let c0 = -(c1 * x[left] + c2 * x[right] + c3 * x[left] * x[right]);
            out.push(Term {
                row,
                gate: gkr::Gate {
                    left,
                    right,
                    c0,
                    c1,
                    c2,
                    c3,
                },
            });
        }
        out
    }

    #[test]
    fn toy_roster_stream_matches_resident_proof_with_default_and_zero_cache() {
        for h in [1usize, 2] {
            let copies = 1usize << h;
            let terms = toy_terms();
            let load = |_| {
                Ok(vec![
                    Fr::from(2u64),
                    Fr::from(3u64),
                    Fr::from(5u64),
                    Fr::from(7u64),
                ])
            };
            let visit = |copy: usize, sink: &mut dyn FnMut(Term) -> Result<(), String>| {
                if copy >= copies {
                    return Err("toy copy outside range".into());
                }
                for term in &terms {
                    sink(term.clone())?;
                }
                Ok(())
            };
            let bind = |t: &mut Transcript| {
                t.append_bytes(b"toy-core-pool", b"same public statement");
                gkr::append_usize(t, b"toy-copy-bits", h);
            };
            let mut resident = Vec::new();
            for copy in 0..copies {
                for term in &terms {
                    let mut expanded = term.clone();
                    expanded.row += copy * 4;
                    expanded.gate.left += copy * 4;
                    expanded.gate.right += copy * 4;
                    resident.push(expanded);
                }
            }
            let circuit = Circuit {
                input_len: 4 * copies,
                row_count: 4 * copies,
                terms: resident,
            };
            let resident_shape = sparse::validate(&circuit, 0).unwrap();
            let wiring = |r: &[Fr], u: &[Fr], v: &[Fr]| -> Result<[Fr; 4], String> {
                let local = Circuit {
                    input_len: 4,
                    row_count: 4,
                    terms: terms.clone(),
                };
                let local_shape = sparse::validate(&local, 0).map_err(|e| e.to_string())?;
                let mut coefficients =
                    sparse::wiring(&local, &local_shape, &r[..2], &u[..2], &v[..2])
                        .map_err(|e| e.to_string())?;
                let copy_factor = r[2..].iter().zip(&u[2..]).zip(&v[2..]).fold(
                    Fr::one(),
                    |acc, ((row, left), right)| {
                        acc * ((Fr::one() - row) * (Fr::one() - left) * (Fr::one() - right)
                            + *row * left * right)
                    },
                );
                for coefficient in &mut coefficients {
                    *coefficient *= copy_factor;
                }
                let explicit = sparse::wiring(&circuit, &resident_shape, r, u, v)
                    .map_err(|e| e.to_string())?;
                if coefficients != explicit || coefficients.iter().all(|x| x.is_zero()) {
                    return Err(
                        "toy pooled coefficients differ from expanded nonzero reference".into(),
                    );
                }
                Ok(coefficients)
            };
            let point = |n: usize, salt: usize| {
                (0..n)
                    .map(|i| Fr::from((i + salt + 2) as u64))
                    .collect::<Vec<_>>()
            };
            let sample_r = point(2 + h, 3);
            let sample_u = point(2 + h, 5);
            let sample_v = point(2 + h, 7);
            assert!(wiring(&sample_r, &sample_u, &sample_v)
                .unwrap()
                .iter()
                .any(|x| !x.is_zero()));
            let mut default_t = transcript();
            let default = sparse_stream_roster::prove(
                2,
                h,
                2,
                0,
                &[2],
                load,
                &mut default_t,
                bind,
                visit,
                wiring,
            )
            .unwrap();
            let mut zero_t = transcript();
            let zero = sparse_stream_roster::prove_with_cache_budget_for_test(
                2,
                h,
                2,
                0,
                &[2],
                Some(0),
                load,
                &mut zero_t,
                bind,
                visit,
                wiring,
            )
            .unwrap();
            assert_eq!(
                gkr::encode_proof(&default.0).unwrap(),
                gkr::encode_proof(&zero.0).unwrap()
            );
            assert_eq!(default.1, zero.1);
            assert_eq!(
                (
                    default_t.challenges(),
                    default_t.raw_queries(),
                    default_t.bytes_absorbed()
                ),
                (
                    zero_t.challenges(),
                    zero_t.raw_queries(),
                    zero_t.bytes_absorbed()
                )
            );

            let input = (0..copies)
                .flat_map(|_| {
                    [
                        Fr::from(2u64),
                        Fr::from(3u64),
                        Fr::from(5u64),
                        Fr::from(7u64),
                    ]
                })
                .collect::<Vec<_>>();
            let mut resident_t = transcript();
            let expected =
                sparse::prove_with_binding(&circuit, &input, 0, &mut resident_t, bind).unwrap();
            assert_eq!(
                gkr::encode_proof(&default.0).unwrap(),
                gkr::encode_proof(&expected.0).unwrap()
            );
            assert_eq!(default.1, expected.1);
            assert_eq!(
                (
                    default_t.challenges(),
                    default_t.raw_queries(),
                    default_t.bytes_absorbed()
                ),
                (
                    resident_t.challenges(),
                    resident_t.raw_queries(),
                    resident_t.bytes_absorbed()
                )
            );
        }
    }

    // C570 helpers are confined to this existing cfg(test) module.
    struct C570Bits { owners: Vec<crate::packed::PackedOwnerBits> }
    impl C570Bits {
        fn c570_bit(&self, global: usize, overlay: Option<usize>) -> Result<bool, String> {
            if global >= 1usize << 22 { return Err(format!("C570 input coordinate {global}")); }
            let owner = global >> 20; let local = global & ((1 << 20) - 1);
            if owner >= 4 || self.owners.len() != 4 || local >= 1 << 20 {
                return Err("C570 packed owner/local bounds".into());
            }
            let bit = self.owners[owner].bit_at(local);
            Ok(if overlay == Some(global) { !bit } else { bit })
        }
        fn c570_value(&self, term: &Term, owner: Option<usize>, overlay: Option<usize>)
            -> Result<(Fr, usize, usize), String>
        {
            let map = |wire: usize| -> Result<usize, String> {
                match owner {
                    Some(slot) => {
                        if slot >= 4 || wire >= 1 << 20 { return Err("C570 LOCAL Core coordinate".into()); }
                        slot.checked_mul(1 << 20).and_then(|x| x.checked_add(wire)).ok_or("C570 wire overflow".into())
                    }
                    None => {
                        if wire >= 1 << 22 { return Err("C570 global Tree coordinate".into()); }
                        Ok(wire)
                    }
                }
            };
            // Validate/read BOTH addresses even when their coefficient is zero.
            let left = map(term.gate.left)?; let right = map(term.gate.right)?;
            let a = self.c570_bit(left, overlay)?; let b = self.c570_bit(right, overlay)?;
            let mut value = term.gate.c0;
            if a { value += term.gate.c1; } if b { value += term.gate.c2; }
            if a && b { value += term.gate.c3; }
            Ok((value, left, right))
        }
    }

    struct C570Rows { values: Vec<Fr>, wires: Vec<(usize, usize)> }
    impl C570Rows {
        fn c570_new() -> Result<Self, String> {
            let n = 1usize << 17;
            if n.checked_mul(std::mem::size_of::<Fr>()) != Some(4 << 20) {
                return Err("C570 Fr buffer size".into());
            }
            let mut values = Vec::new(); values.try_reserve_exact(n).map_err(|e| format!("C570 row reserve: {e}"))?;
            values.resize(n, Fr::zero());
            let mut wires = Vec::new(); wires.try_reserve_exact(n).map_err(|e| format!("C570 diagnostic reserve: {e}"))?;
            wires.resize(n, (usize::MAX, usize::MAX));
            if values.capacity().checked_mul(std::mem::size_of::<Fr>()).filter(|n| *n <= 4 << 20).is_none()
                || wires.capacity().checked_mul(std::mem::size_of::<(usize, usize)>()).filter(|n| *n <= 2 << 20).is_none() {
                return Err("C570 allocated row/diagnostic capacity".into());
            }
            Ok(Self { values, wires })
        }
        fn c570_clear(&mut self, n: usize) -> Result<(), String> {
            if n > self.values.len() { return Err("C570 row buffer bound".into()); }
            self.values[..n].fill(Fr::zero()); self.wires[..n].fill((usize::MAX, usize::MAX)); Ok(())
        }
        fn c570_add(&mut self, row: usize, n: usize, value: Fr, left: usize, right: usize) -> Result<(), String> {
            if row >= n || n > self.values.len() { return Err("C570 residual row domain".into()); }
            if !value.is_zero() && self.wires[row].0 == usize::MAX { self.wires[row] = (left, right); }
            self.values[row] += value; Ok(())
        }
        fn c570_zero(&self, n: usize, label: &str, row_base: usize) -> Result<(), String> {
            if n > self.values.len() { return Err("C570 flush bound".into()); }
            if let Some(row) = self.values[..n].iter().position(|x| !x.is_zero()) {
                let (left, right) = self.wires[row];
                return Err(format!("C570 {label} row{} owner{} left{left} right{right}",
                    row_base.checked_add(row).ok_or("C570 diagnostic row overflow")?, left >> 20));
            }
            Ok(())
        }
    }

    struct C570Spec { name: String, row_log: usize, terms: usize }
    fn c570_usize(value: u64) -> Result<usize, String> {
        usize::try_from(value).map_err(|_| "C570 count conversion".into())
    }
    fn c570_specs(parent: &crate::work_tree_history_plan::WorkTreeHistoryPlan, local: bool)
        -> Result<(Vec<C570Spec>, usize), String>
    {
        use crate::work_tree_wiring as wiring;
        let dimensions = if local { wiring::full_split_local_tensor_dimensions(parent.topology(), parent.work_boundary())? }
            else { wiring::full_split_cross_tensor_dimensions(parent.topology(), parent.work_boundary())? };
        let member_bits = if local { wiring::full_split_local_tensor_member_row_bits(parent.topology(), parent.work_boundary())? }
            else { wiring::full_split_cross_tensor_member_row_bits(parent.topology(), parent.work_boundary())? };
        if dimensions.0 != 20 || dimensions.1 != 2 || dimensions.2 > 14 || dimensions.3 > 5 || member_bits.len() > 32 {
            return Err("C570 Tree tensor geometry".into());
        }
        let global_bits = dimensions.2.checked_add(2).ok_or("C570 Tree stride overflow")?;
        let mut specs = Vec::new(); specs.try_reserve_exact(32).map_err(|e| format!("C570 specs reserve: {e}"))?;
        for family in &parent.topology().families {
            if matches!(family.mapping, wiring::Mapping::Same { .. }) == local {
                let count = family.count(parent.descriptor())?;
                specs.push(C570Spec { name: family.name.clone(), row_log: count.row_log, terms: c570_usize(count.terms)? });
            }
        }
        if local {
            let engine = fixed::engine()?;
            let b2 = fixed::count(engine, parent.fixed_profile())?.total_boundary_terms;
            let b3 = crate::work_tree_leaf_hash::count(engine, parent.leaf_boundary())?["new_boundary_terms"]
                .as_u64().ok_or("C570 B3 gross census")?;
            let b4 = crate::work_tree_work::count(parent.work_boundary())?["new_local_terms"]
                .as_u64().ok_or("C570 B4 gross census")?;
            for (name, bits, count) in [("B2", 13, b2), ("B3", 16, b3), ("B4", 13, b4)] {
                specs.push(C570Spec { name: name.into(), row_log: bits, terms: c570_usize(count)? });
            }
        } else {
            for family in parent.work_boundary().links() {
                let count = family.count(parent.descriptor())?;
                specs.push(C570Spec { name: family.name.clone(), row_log: count.row_log, terms: c570_usize(count.terms)? });
            }
        }
        if specs.len() != member_bits.len() || specs.len() > 1usize << dimensions.3
            || specs.iter().zip(member_bits).any(|(s, b)| s.row_log != b + 2 || s.row_log > global_bits) {
            return Err("C570 exact Tree member ordinals/widths".into());
        }
        let total = specs.iter().try_fold(0usize, |sum, s| sum.checked_add(s.terms).ok_or("C570 Tree count overflow"))?;
        if total > 1 << 20 { return Err("C570 existing per-split term cap".into()); }
        Ok((specs, global_bits))
    }

    fn c570_family(
        family: &crate::work_tree_wiring::Family, descriptor: &crate::work_tree_wiring::Descriptor,
        bits: &C570Bits, rows: &mut C570Rows, overlay: Option<usize>,
    ) -> Result<usize, String> {
        let count = family.count(descriptor)?; let expected = c570_usize(count.terms)?;
        if count.row_log > 16 || expected > 1 << 20 { return Err("C570 direct family bound".into()); }
        let n = 1usize << count.row_log; rows.c570_clear(n)?; let mut seen = 0usize;
        family.emit_terms(descriptor, |term| {
            if seen >= expected || term.row >= n { return Err("C570 direct count/row before evaluation".into()); }
            let (value, left, right) = bits.c570_value(&term, None, overlay)?;
            rows.c570_add(term.row, n, value, left, right)?; seen += 1; Ok(())
        })?;
        if seen != expected { return Err("C570 incomplete direct family".into()); }
        Ok(n)
    }

    fn c570_tree(
        parent: &crate::work_tree_history_plan::WorkTreeHistoryPlan, local: bool,
        specs: &[C570Spec], width: usize, bits: &C570Bits, rows: &mut C570Rows,
    ) -> Result<usize, String> {
        if width > 16 { return Err("C570 Tree row buffer width".into()); }
        let n = 1usize << width; rows.c570_clear(n)?;
        let mut counts = Vec::new(); counts.try_reserve_exact(specs.len()).map_err(|e| format!("C570 counts reserve: {e}"))?;
        counts.resize(specs.len(), 0usize); let mut active = None; let mut total = 0usize;
        crate::work_tree_wiring::full_split_visit_terms(parent.topology(), fixed::engine()?,
            parent.fixed_profile(), parent.leaf_boundary(), parent.work_boundary(), local, &mut |term| {
                let tag = term.row >> width; let row = term.row & (n - 1);
                if total >= 1 << 20 || tag >= specs.len() || row >= 1usize << specs[tag].row_log
                    || counts[tag] >= specs[tag].terms {
                    return Err("C570 Tree domain/count before evaluation".into());
                }
                if let Some(previous) = active {
                    if tag < previous { return Err("C570 Tree member order".into()); }
                    if tag != previous {
                        if counts[previous] != specs[previous].terms { return Err("C570 Tree prior member count".into()); }
                        rows.c570_zero(n, &format!("Tree local{local}/{}", specs[previous].name), previous << width)?;
                        rows.c570_clear(n)?;
                    }
                }
                active = Some(tag);
                let (value, left, right) = bits.c570_value(&term, None, None)?;
                rows.c570_add(row, n, value, left, right)?;
                counts[tag] += 1; total += 1; Ok(())
            })?;
        if let Some(tag) = active { rows.c570_zero(n, &format!("Tree local{local}/{}", specs[tag].name), tag << width)?; }
        for (count, spec) in counts.iter().zip(specs) {
            if *count != spec.terms { return Err(format!("C570 missing/empty Tree ordinal {}", spec.name)); }
        }
        Ok(total)
    }

    fn c570_core_term(
        term: &Term, slot: usize, family: usize, bits: &C570Bits, overlay: Option<usize>,
    ) -> Result<(usize, Fr, usize, usize), String> {
        if slot >= 4 || family >= 11 || term.row >> 17 != family { return Err("C570 Core slot/family".into()); }
        let offset = layout::CORE_OFFSETS[family];
        if term.gate.left < offset || term.gate.left >= offset + layout::CORE
            || term.gate.right < offset || term.gate.right >= offset + layout::CORE {
            return Err("C570 actual Core physical bank map".into());
        }
        let (value, left, right) = bits.c570_value(term, Some(slot), overlay)?;
        Ok((term.row & ((1 << 17) - 1), value, left, right))
    }
    fn c570_pool(pool: &Plan, bits: &C570Bits, rows: &mut C570Rows) -> Result<usize, String> {
        let n = 1 << 17; let mut total = 0usize;
        for slot in 0..4 {
            rows.c570_clear(n)?; let mut active = 0usize; let mut counts = [0usize; 11];
            pool.emit_copy(slot, &mut |term| {
                let family = term.row >> 17;
                if total >= 7_589_120 || family >= 11 || counts[family] >= 172_480 || family < active {
                    return Err("C570 Core cap/order before evaluation".into());
                }
                if family != active {
                    if counts[active] != 172_480 { return Err("C570 skipped Core bank".into()); }
                    rows.c570_zero(n, &format!("Core slot{slot}/family{active}"), (active << 19) | (slot << 17))?;
                    rows.c570_clear(n)?; active = family;
                }
                let (row, value, left, right) = c570_core_term(&term, slot, family, bits, None)?;
                rows.c570_add(row, n, value, left, right)?; counts[family] += 1; total += 1; Ok(())
            })?;
            rows.c570_zero(n, &format!("Core final slot{slot}/family{active}"), (active << 19) | (slot << 17))?;
            if counts != [172_480; 11] { return Err("C570 complete eleven-bank census".into()); }
        }
        if total != 7_589_120 { return Err("C570 complete44 census".into()); } Ok(total)
    }

    fn c570_named<'a>(families: &'a [crate::work_tree_wiring::Family], name: &str)
        -> Result<&'a crate::work_tree_wiring::Family, String>
    {
        let mut found = families.iter().filter(|f| f.name == name);
        let value = found.next().ok_or_else(|| format!("C570 absent family {name}"))?;
        if found.next().is_some() { return Err(format!("C570 duplicate family {name}")); }
        Ok(value)
    }
    fn c570_first_term(family: &crate::work_tree_wiring::Family,
        d: &crate::work_tree_wiring::Descriptor) -> Result<Term, String>
    {
        let mut first = None; let mut seen = 0usize; let expected = c570_usize(family.count(d)?.terms)?;
        family.emit_terms(d, |t| {
            if seen >= expected || expected > 1 << 20 { return Err("C570 witness emission cap".into()); }
            if first.is_none() && t.gate.left != t.gate.right { first = Some(t); }
            seen += 1; Ok(())
        })?;
        if seen != expected { return Err("C570 witness census".into()); }
        first.ok_or("C570 no distinct-endpoint witness".into())
    }
    fn c570_mapped(term: &Term, family: usize) -> Result<Term, String> {
        if family >= 11 || term.row >= 1 << 17
            || term.gate.left >= 1 << 16 || term.gate.right >= 1 << 16 {
            return Err("C570 template mapping domain".into());
        }
        let mut out = term.clone();
        out.row = term.row.checked_add(family << 17).ok_or("C570 mapped row overflow")?;
        out.gate.left = term.gate.left.checked_add(layout::CORE_OFFSETS[family]).ok_or("C570 mapped left overflow")?;
        out.gate.right = term.gate.right.checked_add(layout::CORE_OFFSETS[family]).ok_or("C570 mapped right overflow")?;
        Ok(out)
    }
    fn c570_affine(core: &Circuit) -> Result<(usize, usize, Fr), String> {
        let mut a = 0usize;
        while a < core.terms.len() {
            let row = core.terms[a].row; let z = core.terms.partition_point(|t| t.row <= row);
            let group = &core.terms[a..z];
            if group.len() <= 2048 && group.iter().all(|t| t.gate.c3.is_zero()) {
                for term in group {
                    for (wire, coefficient) in [(term.gate.left, term.gate.c1), (term.gate.right, term.gate.c2)] {
                        if coefficient.is_zero() { continue; }
                        let combined = group.iter().fold(Fr::zero(), |mut sum, t| {
                            if t.gate.left == wire { sum += t.gate.c1; }
                            if t.gate.right == wire { sum += t.gate.c2; } sum
                        });
                        if !combined.is_zero() { return Ok((row, wire, combined)); }
                    }
                }
            }
            a = z;
        }
        Err("C570 no actual affine constrained-wire witness".into())
    }
    fn c570_core_negatives(pool: &Plan, bits: &C570Bits, rows: &mut C570Rows) -> Result<usize, String> {
        let (witness_row, wire, coefficient) = c570_affine(&pool.engine.core)?;
        let mut visits = 0usize;
        for slot in 0..4 {
            for family in 0..11 {
                let target = (slot << 20) + layout::CORE_OFFSETS[family] + wire;
                let delta = if bits.c570_bit(target, None)? { -coefficient } else { coefficient };
                if delta.is_zero() { return Err("C570 vacuous affine flip".into()); }
                rows.c570_clear(1 << 17)?; let mut seen = 0usize;
                for template in &pool.engine.core.terms {
                    if seen >= 172_480 || visits >= 7_589_120 { return Err("C570 targeted negative cap".into()); }
                    let term = c570_mapped(template, family)?;
                    let (row, value, left, right) = c570_core_term(&term, slot, family, bits, Some(target))?;
                    rows.c570_add(row, 1 << 17, value, left, right)?; seen += 1; visits += 1;
                }
                if seen != 172_480 || rows.values[witness_row] != delta
                    || rows.c570_zero(1 << 17, "Core negative", (family << 19) | (slot << 17)).is_ok() {
                    return Err(format!("C570 unobserved overlay slot{slot}/family{family}/wire{target}/row{witness_row}"));
                }
                // Exact local overlay-miss differential, not another whole-bank replay.
                let wrong_owner = (((slot + 1) % 4) << 20) + layout::CORE_OFFSETS[family] + wire;
                let wrong_bank = (slot << 20) + layout::CORE_OFFSETS[(family + 1) % 11] + wire;
                for routed in [wrong_owner, wrong_bank] {
                    if routed == target || bits.c570_bit(routed, Some(target))? != bits.c570_bit(routed, None)? {
                        return Err("C570 wrong-routing overlay-miss witness".into());
                    }
                }
            }
        }
        if visits != 7_589_120 { return Err("C57044 targeted negative census".into()); } Ok(visits)
    }
    fn c570_cancellation(pool: &Plan, bits: &C570Bits, rows: &mut C570Rows) -> Result<(), String> {
        let core = &pool.engine.core; let mut a = 0usize; let mut selected = None;
        while a < core.terms.len() {
            let row = core.terms[a].row; let z = core.terms.partition_point(|t| t.row <= row);
            let mut sum = Fr::zero(); let mut nonzero = 0usize; let mut chosen = None;
            for index in a..z {
                let term = c570_mapped(&core.terms[index], 0)?;
                let (_, value, _, _) = c570_core_term(&term, 0, 0, bits, None)?;
                sum += value;
                if !value.is_zero() { nonzero += 1; chosen = Some((index, value)); }
            }
            if nonzero >= 2 && sum.is_zero() { selected = Some((a, z, chosen.ok_or("C570 cancellation selection")?)); break; }
            a = z;
        }
        let (a, z, (chosen, contribution)) = selected.ok_or("C570 no actual cancelling Term row")?;
        let row = core.terms[chosen].row; let target_row = (row + 1) % (1 << 17);
        if target_row == row || contribution.is_zero() { return Err("C570 vacuous valid-row retag".into()); }
        for mode in 0..3 {
            rows.c570_clear(1 << 17)?;
            for index in a..z {
                if mode == 1 && index == chosen { continue; }
                let term = c570_mapped(&core.terms[index], 0)?;
                let (original, value, left, right) = c570_core_term(&term, 0, 0, bits, None)?;
                let assigned = if mode == 2 && index == chosen { target_row } else { original };
                rows.c570_add(assigned, 1 << 17, value, left, right)?;
            }
            if mode == 0 { rows.c570_zero(1 << 17, "actual cancelling baseline", 0)?; }
            else if mode == 1 {
                if rows.values[row] != -contribution { return Err("C570 omission multiplicity".into()); }
                if rows.c570_zero(1 << 17, "omission", 0).is_ok() { return Err("C570 omitted nonzero Term survived".into()); }
            } else {
                let sum = rows.values.iter().fold(Fr::zero(), |sum, x| sum + *x);
                if !sum.is_zero() || rows.values[row] != -contribution || rows.values[target_row] != contribution
                    || rows.c570_zero(1 << 17, "valid-row retag", 0).is_ok() {
                    return Err("C570 retag did not preserve total while breaking separate rows".into());
                }
            }
        }
        Ok(())
    }
    fn c570_parameter(
        before: &crate::work_tree_wiring::Family, before_d: &crate::work_tree_wiring::Descriptor,
        after: &crate::work_tree_wiring::Family, after_d: &crate::work_tree_wiring::Descriptor,
        expected: usize, bits: &C570Bits, rows: &mut C570Rows,
    ) -> Result<(), String> {
        if expected > 256 { return Err("C570 public parameter bound".into()); }
        let mut old = Vec::new(); old.try_reserve_exact(expected).map_err(|e| format!("C570 parameter reserve: {e}"))?;
        let mut new = Vec::new(); new.try_reserve_exact(expected).map_err(|e| format!("C570 parameter reserve: {e}"))?;
        before.emit_terms(before_d, |t| { if old.len() >= expected { return Err("C570 parameter old cap".into()); } old.push(t); Ok(()) })?;
        after.emit_terms(after_d, |t| { if new.len() >= expected { return Err("C570 parameter new cap".into()); } new.push(t); Ok(()) })?;
        if old.len() != expected || new.len() != expected { return Err("C570 public parameter census".into()); }
        let mut changed = None;
        for (index, (a, b)) in old.iter().zip(&new).enumerate() {
            if a.row != b.row || a.gate.left != b.gate.left || a.gate.right != b.gate.right
                || a.gate.c1 != b.gate.c1 || a.gate.c2 != b.gate.c2 || a.gate.c3 != b.gate.c3 {
                return Err("C570 public discriminator changed another map/coefficient".into());
            }
            if a.gate.c0 != b.gate.c0 {
                let delta = b.gate.c0 - a.gate.c0;
                if index != 0 || changed.is_some() || !(delta == Fr::one() || delta == -Fr::one()) {
                    return Err("C570 public LSB/bit0 isolated delta".into());
                }
                changed = Some((a.row, delta));
            }
        }
        let (row, delta) = changed.ok_or("C570 public parameter mutation vacuous")?;
        let n = c570_family(before, before_d, bits, rows, None)?; rows.c570_zero(n, &before.name, 0)?;
        let n2 = c570_family(after, after_d, bits, rows, None)?;
        if n != n2 || rows.values[row] != delta
            || rows.values[..n].iter().filter(|x| !x.is_zero()).count() != 1 {
            return Err(format!("C570 literal public discriminator {} row{row}", after.name));
        }
        Ok(())
    }

    fn c570_run() -> Result<(), String> {
        let path = std::path::PathBuf::from(std::env::var_os("C570_SOURCE").ok_or("C570_SOURCE required")?);
        if !path.is_absolute() { return Err("C570 exact absolute source path required".into()); }
        let metadata = std::fs::metadata(&path).map_err(|e| e.to_string())?;
        if metadata.len() != 524288 || !metadata.permissions().readonly() { return Err("C570 fixed RO source extent".into()); }
        let source = crate::packed::PackedFile::open(&path, 22)?;
        let view = source.h2_boolean_view()?; view.require_same_source(&source)?;
        let mut owners = Vec::new(); owners.try_reserve_exact(4).map_err(|e| format!("C570 snapshots reserve: {e}"))?;
        let mut capacity = 0usize;
        for owner in 0..4 {
            let snapshot = view.read_copy(owner)?;
            if snapshot.len() != 1 << 20 || snapshot.capacity_bytes() > 131072 { return Err("C570 packed BITS/byte capacity".into()); }
            capacity = capacity.checked_add(snapshot.capacity_bytes()).ok_or("C570 snapshot capacity overflow")?;
            if capacity > 524288 { return Err("C570 four packed capacity".into()); }
            owners.push(snapshot);
        }
        view.require_same_source(&source)?;
        let bits = C570Bits { owners };
        let headers = crate::historical_prefix_witness::retained_headers().map_err(|e| e.to_string())?;
        let native = crate::packed_owner_assembly::NativePrefix::from_raw_iter(3,
            headers.iter().map(|h| h.encode().map_err(|e| format!("{e:?}"))))?;
        let parent = crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(3, 2, native.root(), native.total_be28())?;
        let d = parent.descriptor();
        if native.header_count() != 3 || native.slot_count() != 4
            || parent.headers() != 3 || parent.slot_log() != 2 || parent.slots() != 4
            || d.genuine != 2 || d.leaves != 2 || d.slots != 4 || d.root != native.root()
            || &parent.topology().descriptor != d || &parent.fixed_profile().tree != d
            || &parent.leaf_profile().tree != d || &parent.leaf_boundary().profile.tree != d
            || &parent.work_profile().tree != d || &parent.work_boundary().profile().tree != d
            || parent.work_profile().total_be28 != native.total_be28() {
            return Err("C570 same-native-parent descriptor/root/N/H/total".into());
        }
        let pool = parent.core_pool();
        if pool.input_log() != 22 || pool.row_log() != 23 || pool.copy_bits() != 2
            || pool.term_count() != 7_589_120 || pool.engine.core.terms.len() != 172_480 {
            return Err("C570 existing complete CorePool shape".into());
        }
        let (local, local_width) = c570_specs(&parent, true)?;
        let (cross, cross_width) = c570_specs(&parent, false)?;
        let mut rows = C570Rows::c570_new()?;
        let inactive = c570_named(&parent.topology().families, "inactive_tree_endpoints")?;
        if !matches!(&inactive.mapping, crate::work_tree_wiring::Mapping::FixedRight { lo: 2, hi: 4, target: 0 })
            || inactive.left_wires.len() != 8192
            || inactive.left_wires.iter().enumerate().any(|(i, wire)| *wire != 983040 + i)
            || inactive.right_wires.len() != 8192 || inactive.right_wires.iter().any(|x| *x != 0)
            || !inactive.constants.as_ref().is_some_and(|x| x.len() == 8192 && x.iter().all(|x| *x == 0))
            || inactive.count(d)?.terms != 16384 {
            return Err("C570 exact first inactive predicate".into());
        }
        let n = c570_family(inactive, d, &bits, &mut rows, None)?;
        rows.c570_zero(n, "FIRST inactive_tree_endpoints", 0)?;
        let local_terms = c570_tree(&parent, true, &local, local_width, &bits, &mut rows)?;
        let cross_terms = c570_tree(&parent, false, &cross, cross_width, &bits, &mut rows)?;
        let core_terms = c570_pool(pool, &bits, &mut rows)?;
        // All baseline members/counts are closed before any overlay or parameter change.
        let first = c570_first_term(inactive, d)?;
        if first.row != 16384 || first.gate.left != 3_080_192 { return Err("C570 direct inactive row namespace".into()); }
        let n = c570_family(inactive, d, &bits, &mut rows, Some(first.gate.left))?;
        if rows.values[first.row] != Fr::one() || rows.c570_zero(n, "inactive overlay", 0).is_ok() {
            return Err("C570 first inactive overlay missed".into());
        }
        for name in ["node_profile_output_core_alias", "profile_digest_fanout"] {
            let family = c570_named(&parent.topology().families, name)?;
            let witness = c570_first_term(family, d)?;
            if witness.gate.c1 != Fr::one() || witness.gate.c2 != -Fr::one() || !witness.gate.c3.is_zero() {
                return Err("C570 actual local/cross equality witness".into());
            }
            let n = c570_family(family, d, &bits, &mut rows, None)?; rows.c570_zero(n, name, 0)?;
            let n = c570_family(family, d, &bits, &mut rows, Some(witness.gate.left))?;
            if rows.c570_zero(n, name, 0).is_ok() { return Err(format!("C570 Tree overlay missed {name}")); }
        }
        c570_cancellation(pool, &bits, &mut rows)?;
        let core_negative_terms = c570_core_negatives(pool, &bits, &mut rows)?;
        let mut profile = parent.work_profile().clone(); profile.total_be28[27] ^= 1;
        let mut restored = profile.clone(); restored.total_be28 = parent.work_profile().total_be28;
        if &restored != parent.work_profile() { return Err("C570 total changed another parameter".into()); }
        let changed_work = crate::work_tree_work::compile(&pool.engine.base, profile)?;
        c570_parameter(c570_named(parent.work_boundary().links(), "work_public_total")?, d,
            c570_named(changed_work.links(), "work_public_total")?, d, 224, &bits, &mut rows)?;
        let mut root = d.root; root[0] ^= 1;
        let changed_topology = crate::work_tree_wiring::Topology::new(&pool.engine.base, 3, root)?;
        let mut restored = changed_topology.descriptor.clone(); restored.root = d.root;
        if &restored != d { return Err("C570 root changed another descriptor parameter".into()); }
        c570_parameter(c570_named(&parent.topology().families, "public_root")?, d,
            c570_named(&changed_topology.families, "public_root")?, &changed_topology.descriptor,
            256, &bits, &mut rows)?;
        println!("C570_TREE_POOL_RESIDUAL_PASS inactive=16384 local_terms={local_terms} cross_terms={cross_terms} core_terms={core_terms} core_negative_terms={core_negative_terms} embeddings=44 setup=0 commit=0 proof=0");
        Ok(())
    }

    #[test]
    #[ignore = "C570 literal original-X N3 Tree/44-Core residuals; separately reviewed controller holds exact C570_SOURCE"]
    fn c570_native_n3_original_x_tree_pool_residuals() {
        c570_run().unwrap();
    }


}

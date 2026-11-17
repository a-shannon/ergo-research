//! Complete native M1 image in one existing free header-slot interval.
//! Structural mapping does not establish arithmetic or historical validity.
use crate::{
    daa_history_layout,
    daa_one_ratio_finish::CompiledOne,
    sparse::{Circuit, Term},
    work_tree_layout,
};
use ark_bn254::Fr;
use ark_ff::Zero;
use blake2::{digest::consts::U32, Blake2b, Digest};
use std::sync::OnceLock;

pub(crate) const SOURCE_INPUT_LEN: usize = 8192;
pub(crate) const MAPPED_INPUT_LOG: usize = 20;
pub(crate) const ARITHMETIC_ROW_LOG: usize = 14;
pub(crate) const IMAGE_START: usize = 819200;
pub(crate) const IMAGE_END: usize = 827392;
const LIVE_LEN: usize = 6414;
const RESIDUAL_ROWS: usize = 12554;
const TERMS: usize = 44729;
const CANONICAL_HEADER_FINGERPRINT: &str =
    "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76";

pub(crate) struct MappedM1 {
    circuit: Circuit,
    witness: Vec<Fr>,
    identity: [u8; 32],
}

impl MappedM1 {
    /// This freezes geometry and maps the assignment. OneDaaLayout separately
    /// admits the complete native relation and its typed handle ledger.
    pub(crate) fn compile(compiled: &CompiledOne) -> Result<Self, String> {
        let arithmetic = &compiled.arithmetic;
        let source = arithmetic
            .circuit
            .as_ref()
            .ok_or("M1 source not materialized")?;
        let count = &arithmetic.count;
        if count.live_bits != LIVE_LEN
            || count.input_bits != LIVE_LEN
            || count.padded_input_bits != SOURCE_INPUT_LEN
            || count.padding_bits != SOURCE_INPUT_LEN - LIVE_LEN
            || count.residual_rows != RESIDUAL_ROWS
            || count.padded_rows != 1 << ARITHMETIC_ROW_LOG
            || count.terms != TERMS
            || source.input_len != SOURCE_INPUT_LEN
            || source.row_count != count.padded_rows
            || source.terms.len() != TERMS
            || arithmetic.witness.len() != SOURCE_INPUT_LEN
        {
            return Err("M1 source geometry mismatch".into());
        }
        if source.terms.iter().any(|term| {
            term.row >= RESIDUAL_ROWS
                || term.gate.left >= SOURCE_INPUT_LEN
                || term.gate.right >= SOURCE_INPUT_LEN
        }) {
            return Err("M1 source term escapes owned domain".into());
        }
        if arithmetic.witness[LIVE_LEN..]
            .iter()
            .any(|value| !value.is_zero())
        {
            return Err("M1 source padding is nonzero".into());
        }
        check_image_ownership()?;
        let mut terms = Vec::with_capacity(TERMS);
        for term in &source.terms {
            let mut gate = term.gate.clone();
            gate.left = translate(gate.left)?;
            gate.right = translate(gate.right)?;
            terms.push(Term {
                row: term.row,
                gate,
            });
        }
        let circuit = Circuit {
            input_len: 1 << MAPPED_INPUT_LOG,
            row_count: 1 << ARITHMETIC_ROW_LOG,
            terms,
        };
        let mut witness = vec![Fr::zero(); circuit.input_len];
        // Every source cell, including dummy endpoints and native padding,
        // has one distinct destination. No outside-image slack is reserved.
        witness[IMAGE_START..IMAGE_END].copy_from_slice(&arithmetic.witness);
        let mut hash = Blake2b::<U32>::new();
        hash.update(b"legacy-m1-complete-native-exact-image-v1");
        for value in [
            IMAGE_START,
            IMAGE_END,
            SOURCE_INPUT_LEN,
            MAPPED_INPUT_LOG,
            ARITHMETIC_ROW_LOG,
            LIVE_LEN,
            RESIDUAL_ROWS,
            TERMS,
        ] {
            hash.update((value as u64).to_le_bytes());
        }
        hash.update(count.topology_blake2b256);
        hash.update(work_tree_layout::hash_terms(&circuit.terms).as_bytes());
        let identity = hash.finalize().into();
        Ok(Self {
            circuit,
            witness,
            identity,
        })
    }
    pub(crate) fn mapped_wire(&self, source: usize) -> Result<usize, String> {
        translate(source)
    }
    pub(crate) fn circuit(&self) -> &Circuit {
        &self.circuit
    }
    pub(crate) fn witness(&self) -> &[Fr] {
        &self.witness
    }
    pub(crate) fn identity(&self) -> [u8; 32] {
        self.identity
    }
}

fn translate(source: usize) -> Result<usize, String> {
    if source >= SOURCE_INPUT_LEN {
        return Err("M1 source wire outside image".into());
    }
    let mapped = IMAGE_START
        .checked_add(source)
        .ok_or("M1 mapped wire overflow")?;
    if mapped >= IMAGE_END {
        return Err("M1 mapped wire outside image".into());
    }
    Ok(mapped)
}

fn check_image_ownership() -> Result<(), String> {
    // The compiled canonical program is immutable within this process. Cache
    // the deciding allocation scan, not a producer-supplied ownership claim.
    static CHECK: OnceLock<Result<(), String>> = OnceLock::new();
    CHECK
        .get_or_init(|| {
            if IMAGE_START.checked_add(SOURCE_INPUT_LEN) != Some(IMAGE_END)
                || IMAGE_END > 1 << MAPPED_INPUT_LOG
            {
                return Err("M1 image geometry mismatch".into());
            }
            let baseline = work_tree_layout::shared_baseline()?;
            require_free_image(&baseline.inventory.free_ranges)?;
            let canonical = daa_history_layout::full_header_boundary(None)?;
            let header = &canonical.base.base.base.boundary;
            if header.input_len != 1 << MAPPED_INPUT_LOG
                || header.row_count != 1 << 19
                || header.terms.len() != 474755
                || work_tree_layout::hash_terms(&header.terms) != CANONICAL_HEADER_FINGERPRINT
            {
                return Err("M1 canonical header allocation changed".into());
            }
            require_no_header_use(&header.terms)
        })
        .clone()
}

fn require_free_image(free: &[(usize, usize)]) -> Result<(), String> {
    if !free
        .iter()
        .any(|&(start, end)| start <= IMAGE_START && IMAGE_END <= end)
    {
        return Err("M1 image is not in frozen free inventory".into());
    }
    Ok(())
}
fn require_no_header_use(terms: &[Term]) -> Result<(), String> {
    if terms.iter().any(|term| {
        (IMAGE_START..IMAGE_END).contains(&term.gate.left)
            || (IMAGE_START..IMAGE_END).contains(&term.gate.right)
    }) {
        return Err("M1 image conflicts with canonical header ownership".into());
    }
    Ok(())
}

#[cfg(test)]
#[path = "mapped_one_daa_tests.rs"]
mod tests;

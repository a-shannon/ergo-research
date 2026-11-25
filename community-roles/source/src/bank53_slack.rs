//! Production source for the fixed Bank53 zero tail, shared with diagnostics.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::Gate, sparse::Term};
use crate::bank53_map::{context_ok, owner_input_base, ROW_STRIDE, CONTEXT_ROW_BASE, CONTEXT_INPUT_BASE};

pub(crate) const SLACK_INPUT_START: usize = 7_805;
pub(crate) const SLACK_INPUT_END: usize = 8_192;
pub(crate) const SLACK_ZERO_COUNT: usize = SLACK_INPUT_END - SLACK_INPUT_START;
// The original W-alias row offset 28,672 plus its 224 physical bits.
pub(crate) const SLACK_ROW_OFFSET: usize = 28_672 + 224;

/// The zero tail is available independently of Score, including modern owners
/// whose Score witness is not yet admissible.
pub(crate) fn slack_zero_terms(owner: usize, context: usize) -> Result<Vec<Term>, String> {
    context_ok(context)?;
    if owner >= (1usize << 21) { return Err("bank53 slack owner".into()); }
    let row_base = owner.checked_mul(ROW_STRIDE)
        .and_then(|base| base.checked_add(CONTEXT_ROW_BASE + context * 32_768 + SLACK_ROW_OFFSET))
        .ok_or("bank53 slack row base overflow")?;
    let input_base = owner_input_base(owner as u64)?
        .checked_add(CONTEXT_INPUT_BASE + context * 8_192)
        .ok_or("bank53 slack input base overflow")?;
    let mut out = Vec::with_capacity(SLACK_ZERO_COUNT);
    for offset in 0..SLACK_ZERO_COUNT {
        let row = row_base.checked_add(offset).ok_or("bank53 slack row overflow")?;
        let left = input_base.checked_add(SLACK_INPUT_START + offset)
            .ok_or("bank53 slack input overflow")?;
        out.push(Term { row, gate: Gate { left, right: 0,
            c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() }});
    }
    Ok(out)
}

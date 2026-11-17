//! Native Legacy one-ratio finish for positive increasing signed timestamps.
//! Full-history authentication and the global DAA roster remain separate.
use crate::{
    daa_finish,
    daa_integer::{self, Builder, Compiled, Epoch, ExternalBits, Inputs, OutputBits},
    daa_regression::{Increment, Progress},
};
use ark_bn254::Fr;
use ark_ff::One;
use num_bigint::BigUint;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Output {
    pub(crate) timestamp_rows: [usize; 4],
    pub(crate) delta_nonzero: usize,
    pub(crate) use_quotient: usize,
    pub(crate) selected: Vec<usize>,
    pub(crate) numeric_result: Vec<usize>,
    pub(crate) child_nbits: [usize; 32],
    pub(crate) before: Progress,
    pub(crate) after_profile: Progress,
    pub(crate) after_fallback: Progress,
    pub(crate) before_child: Progress,
    pub(crate) increment: Increment,
}

pub(crate) struct CompiledOne {
    pub(crate) arithmetic: Compiled,
    pub(crate) output: Output,
}

/// Profile checks are also appended as constraints below; a host rejection
/// alone would not enforce the profile on a committed witness.
pub(crate) fn compile(
    q: &BigUint,
    input: Inputs,
    child_nbits: u32,
    materialize: bool,
) -> Result<CompiledOne, String> {
    if input.start_timestamp < 0 || input.end_timestamp <= input.start_timestamp {
        return Err("M1 requires nonnegative increasing signed timestamps".into());
    }
    let (arithmetic, output) = daa_integer::compile_extended(
        Epoch::Legacy,
        q,
        input,
        materialize,
        |builder, external, a1| append(builder, external, a1, q, child_nbits),
    )?;
    Ok(CompiledOne { arithmetic, output })
}

pub(crate) fn append(
    builder: &mut Builder,
    external: &ExternalBits,
    a1: &OutputBits,
    q: &BigUint,
    child_nbits: u32,
) -> Result<Output, String> {
    if a1.wrapped_delta.len() != 64 || a1.quotient_magnitude.len() != Epoch::Legacy.numerator_bits()
    {
        return Err("M1 A1 output geometry drift".into());
    }
    let before = Progress::from(builder.progress());
    let start_row = builder.progress().1;
    builder.assert_zero(external.start_timestamp[63]);
    let end_row = builder.progress().1;
    builder.assert_zero(external.end_timestamp[63]);
    let direction_row = builder.progress().1;
    builder.assert_zero(a1.wrapped_delta[63]);
    let delta_nonzero = builder.nonzero_unasserted(&a1.wrapped_delta);
    let nonzero_row = builder.progress().1;
    builder.assert_one(delta_nonzero);
    let after_profile = Progress::from(builder.progress());

    let nonzero = builder.nonzero_unasserted(&a1.quotient_magnitude);
    let nonnegative = builder.not(a1.quotient_negative);
    let use_quotient = builder.and(nonzero, nonnegative);
    let initial = BigUint::parse_bytes(daa_finish::INITIAL_DIFFICULTY_HEX.as_bytes(), 16)
        .ok_or("invalid pinned Mainnet initial difficulty")?;
    if initial.bits() > a1.quotient_magnitude.len() as u64 {
        return Err("M1 fallback exceeds quotient width".into());
    }
    let initial_bytes = initial.to_bytes_le();
    let selected = a1
        .quotient_magnitude
        .iter()
        .enumerate()
        .map(|(bit, &source)| {
            let constant = initial_bytes
                .get(bit / 8)
                .is_some_and(|byte| (byte >> (bit % 8)) & 1 == 1);
            let value = if builder.value(use_quotient) {
                builder.value(source)
            } else {
                constant
            };
            let out = builder.bit(value);
            let mut gates = vec![
                Builder::linear(out, Fr::one()),
                Builder::product(use_quotient, source, -Fr::one()),
            ];
            if constant {
                gates.push(Builder::constant(-Fr::one()));
                gates.push(Builder::linear(use_quotient, Fr::one()));
            }
            builder.row(gates);
            out
        })
        .collect::<Vec<_>>();
    let after_fallback = Progress::from(builder.progress());
    let numeric_result = daa_finish::compact_positive(builder, &selected);
    let before_child = Progress::from(builder.progress());
    let child_nbits =
        daa_integer::bind_child_nbits_to_result(builder, child_nbits, q, &numeric_result)?;
    let after = Progress::from(builder.progress());
    Ok(Output {
        timestamp_rows: [start_row, end_row, direction_row, nonzero_row],
        delta_nonzero,
        use_quotient,
        selected,
        numeric_result,
        child_nbits,
        before,
        after_profile,
        after_fallback,
        before_child,
        increment: Increment {
            before,
            after,
            added_live_bits: after.live_bits - before.live_bits,
            added_rows: after.rows - before.rows,
            added_terms: after.terms - before.terms,
        },
    })
}

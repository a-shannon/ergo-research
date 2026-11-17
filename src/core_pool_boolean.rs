//! Boolean-input producer for one slot across selected physical core banks.
//!
//! This is a producer optimization only. It preserves the sparse roster's
//! public binding, output coordinates, sumcheck messages, claim, and line proof.
//! Production admission is single-slot; the small copy tensor is test-only.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use rayon::prelude::*;

use crate::{
    gkr::{self, GkrError, GkrProof, InputClaim, LayerProof},
    sparse::{self, Circuit, Shape, Term},
    transcript::Transcript,
};

mod raw_sealed { pub(super) trait Sealed {} }

/// Only validated dense copies and opaque locked-file snapshots implement this
/// internal interface. Monomorphization removes per-bit enum/dyn dispatch.
trait RawBooleanCopy: raw_sealed::Sealed + Sync {
    const PROFILE_PREFIX: &'static str = "core_pool_boolean_phases";
    fn len(&self) -> usize;
    fn bit(&self, index: usize) -> bool;
    fn validate(&self, copy: usize, width: usize) -> Result<(), String> {
        let _ = copy;
        if self.len() != width { return Err(GkrError::InvalidInputWidth.to_string()); }
        Ok(())
    }
    // A raw span cannot assert that the complete original Fr input was
    // checked. Only the two whole-copy implementations opt into Candidate.
    #[cfg(test)]
    fn validate_candidate_original(&self, _copy: usize, _width: usize) -> Result<(), String> {
        Err("candidate requires a complete original Boolean copy".into())
    }
    fn line(&self, u: &[Fr], v: &[Fr]) -> Result<Vec<Fr>, String> {
        line_from_bits(self, u, v)
    }
}

struct DenseBooleanCopy { values: Vec<Fr> }
impl raw_sealed::Sealed for DenseBooleanCopy {}
impl RawBooleanCopy for DenseBooleanCopy {
    fn len(&self) -> usize { self.values.len() }
    fn bit(&self, index: usize) -> bool { self.values[index].is_one() }
    fn validate(&self, copy: usize, width: usize) -> Result<(), String> {
        if self.len() != width { return Err(GkrError::InvalidInputWidth.to_string()); }
        if let Some(index) = self.values.iter().position(|x| !x.is_zero() && !x.is_one()) {
            return Err(format!("non-Boolean input at copy {copy}, coordinate {index}"));
        }
        Ok(())
    }
    #[cfg(test)]
    fn validate_candidate_original(&self, copy: usize, width: usize) -> Result<(), String> {
        self.validate(copy, width)
    }
    fn line(&self, u: &[Fr], v: &[Fr]) -> Result<Vec<Fr>, String> {
        Ok(gkr::line_polynomial(&self.values, u, v))
    }
}

#[cfg(test)]
impl raw_sealed::Sealed for crate::packed::PackedOwnerBits {}
#[cfg(test)]
impl RawBooleanCopy for crate::packed::PackedOwnerBits {
    const PROFILE_PREFIX: &'static str = "core_pool_packed_boolean_phases";
    fn len(&self) -> usize { self.len() }
    fn bit(&self, index: usize) -> bool { self.bit_at(index) }
    fn validate_candidate_original(&self, copy: usize, width: usize) -> Result<(), String> {
        self.validate(copy, width)
    }
}

struct BooleanSpan<'a, T: RawBooleanCopy + ?Sized> { input: &'a T, start: usize, width: usize }
impl<T: RawBooleanCopy + ?Sized> raw_sealed::Sealed for BooleanSpan<'_, T> {}
impl<T: RawBooleanCopy + ?Sized> RawBooleanCopy for BooleanSpan<'_, T> {
    fn len(&self) -> usize { self.width }
    fn bit(&self, index: usize) -> bool { self.input.bit(self.start + index) }
}
fn bank_span<T: RawBooleanCopy>(input: &T, start: usize, width: usize) -> Result<BooleanSpan<'_, T>, String> {
    if start.checked_add(width).is_none_or(|end| end > input.len()) {
        return Err(GkrError::InvalidInputWidth.to_string());
    }
    Ok(BooleanSpan { input, start, width })
}

/// Exact first LSB fold of the legacy line, followed by its unchanged Fr
/// recurrence. Folded entries are never converted back to Boolean values.
fn line_from_bits<T: RawBooleanCopy + ?Sized>(input: &T, u: &[Fr], v: &[Fr]) -> Result<Vec<Fr>, String> {
    if input.len() > 1usize << 20 { return Err("packed Boolean line capacity".into()); }
    if input.len() == 0 || !input.len().is_power_of_two() || u.len() != v.len()
        || u.len() >= usize::BITS as usize
        || 1usize.checked_shl(u32::try_from(u.len()).map_err(|_| GkrError::PointDimension.to_string())?) != Some(input.len()) {
        return Err(GkrError::PointDimension.to_string());
    }
    if u.is_empty() { return Ok(vec![if input.bit(0) { Fr::one() } else { Fr::zero() }]); }
    let mut table = vec![Fr::zero(); input.len()];
    if table.capacity() != input.len() {
        return Err("packed Boolean line capacity".into());
    }
    for pair in 0..input.len() / 2 {
        let (a, b) = (input.bit(2 * pair), input.bit(2 * pair + 1));
        let (constant, linear) = match (a, b) {
            (false, false) => (Fr::zero(), Fr::zero()),
            (false, true) => (u[0], v[0] - u[0]),
            (true, false) => (Fr::one() - u[0], u[0] - v[0]),
            (true, true) => (Fr::one(), Fr::zero()),
        };
        table[2 * pair] = constant;
        table[2 * pair + 1] = linear;
    }
    let mut entries = input.len() / 2;
    let mut stride = 2;
    for coordinate in 1..u.len() {
        let next_entries = entries / 2;
        let next_stride = coordinate + 2;
        let mut next = vec![Fr::zero(); next_entries * next_stride];
        if next.capacity() != next_entries * next_stride {
            return Err("packed Boolean line step capacity".into());
        }
        for pair in 0..next_entries {
            let left = 2 * pair * stride;
            let right = left + stride;
            let output = pair * next_stride;
            for degree in 0..=coordinate {
                let difference = table[right + degree] - table[left + degree];
                next[output + degree] += table[left + degree] + u[coordinate] * difference;
                next[output + degree + 1] += (v[coordinate] - u[coordinate]) * difference;
            }
        }
        table = next;
        entries = next_entries;
        stride = next_stride;
    }
    Ok(table)
}

/// Tiny differentials from an actual admitted packed snapshot; no synthetic
/// byte constructor can enter the producer. All arithmetic below stays Fr.
#[cfg(test)]
pub(crate) fn packed_math_controls(bits: &crate::packed::PackedOwnerBits) -> usize {
    let mut checks = 0;
    let u = [Fr::from(2u64), Fr::from(3u64), Fr::from(5u64)];
    let v = [Fr::from(7u64), Fr::from(11u64), Fr::from(13u64)];
    for bank in 0..16 {
        let span = bank_span(bits, bank * 65536, 8).unwrap();
        let raw: Vec<Fr> = (0..8).map(|i| if span.bit(i) { Fr::one() } else { Fr::zero() }).collect();
        for prefix in 0..=3 {
            let weights = gkr::eq_weights(&u[..prefix]);
            let actual = boolean_prefix(&span, &weights).unwrap();
            let mut reference = raw.clone();
            for challenge in &u[..prefix] { gkr::fold(&mut reference, *challenge); }
            assert_eq!(actual, reference, "physical bank {bank}, prefix {prefix}");
            checks += 1;
        }
        assert_eq!(line_from_bits(&span, &u, &v).unwrap(), gkr::line_polynomial(&raw, &u, &v));
        checks += 1;
    }
    // The excluded bank has only bit7 set in this byte: folded value30 is not
    // Boolean, and must not be truncated to an is_one/packed-bit predicate.
    let span = bank_span(bits, 8 * 65536, 8).unwrap();
    assert_eq!(boolean_prefix(&span, &gkr::eq_weights(&u)).unwrap(), vec![Fr::from(30u64)]);
    checks += 1;
    for (a, b) in [(false, false), (false, true), (true, false), (true, true)] {
        let first = (0..bits.len() / 2).find(|pair| bits.bit_at(2 * pair) == a && bits.bit_at(2 * pair + 1) == b)
            .expect("actual fixture must contain each first-fold Boolean pair");
        let pair = bank_span(bits, first * 2, 2).unwrap();
        let reference = match (a, b) {
            (false, false) => vec![Fr::zero(), Fr::zero()],
            (false, true) => vec![u[0], v[0] - u[0]],
            (true, false) => vec![Fr::one() - u[0], u[0] - v[0]],
            (true, true) => vec![Fr::one(), Fr::zero()],
        };
        assert_eq!(line_from_bits(&pair, &u[..1], &v[..1]).unwrap(), reference);
        checks += 1;
    }
    let span = bank_span(bits, 0, 8).unwrap();
    for (left, right) in [(&u[..2], &v[..3]), (&u[..3], &v[..2])] {
        assert_eq!(line_from_bits(&span, left, right).err(), Some(GkrError::PointDimension.to_string()));
        checks += 1;
    }
    assert_eq!(boolean_prefix(&span, &[]).err(), Some(GkrError::PointDimension));
    checks += 1;
    assert_eq!(quadratic_scaled_d(&[Fr::from(5u64), Fr::from(7u64)],
        &[Fr::from(11u64), Fr::from(13u64)], &[Fr::from(17u64), Fr::from(19u64)], Fr::zero()),
        vec![Fr::from(85u64), Fr::from(44u64), Fr::from(4u64)]);
    checks += 1;
    assert_eq!(checks, 89);
    checks
}

#[derive(Clone, Copy)]
struct Edge {
    left: usize,
    right: usize,
    coefficient: Fr,
}

struct FirstPhase {
    a_constant: Vec<Fr>,
    b_constant: Vec<Fr>,
    a_edges: Vec<Edge>,
    b_edges: Vec<Edge>,
}

impl FirstPhase {
    fn new(core: &Circuit, rows: &[Fr]) -> Self {
        let mut tables = Self {
            a_constant: vec![Fr::zero(); core.input_len],
            b_constant: vec![Fr::zero(); core.input_len],
            a_edges: Vec::new(),
            b_edges: Vec::new(),
        };
        for term in &core.terms {
            let gate = &term.gate;
            let rho = rows[term.row];
            if !gate.c1.is_zero() {
                tables.a_constant[gate.left] += rho * gate.c1;
            }
            if !gate.c0.is_zero() {
                tables.b_constant[gate.left] += rho * gate.c0;
            }
            if !gate.c3.is_zero() {
                tables.a_edges.push(Edge {
                    left: gate.left,
                    right: gate.right,
                    coefficient: rho * gate.c3,
                });
            }
            if !gate.c2.is_zero() {
                tables.b_edges.push(Edge {
                    left: gate.left,
                    right: gate.right,
                    coefficient: rho * gate.c2,
                });
            }
        }
        tables
    }

    fn vectors<T: RawBooleanCopy>(&self, boolean_input: &T) -> (Vec<Fr>, Vec<Fr>) {
        let mut a = self.a_constant.clone();
        let mut b = self.b_constant.clone();
        for edge in &self.a_edges {
            if boolean_input.bit(edge.right) {
                a[edge.left] += edge.coefficient;
            }
        }
        for edge in &self.b_edges {
            if boolean_input.bit(edge.right) {
                b[edge.left] += edge.coefficient;
            }
        }
        (a, b)
    }

    fn bind_low(&mut self, challenge: Fr) {
        gkr::fold(&mut self.a_constant, challenge);
        gkr::fold(&mut self.b_constant, challenge);
        let complement = Fr::one() - challenge;
        for edge in self.a_edges.iter_mut().chain(&mut self.b_edges) {
            edge.coefficient *= if edge.left & 1 == 1 {
                challenge
            } else {
                complement
            };
            edge.left >>= 1;
        }
    }
}

fn read_copy<T: RawBooleanCopy>(
    load: &mut impl FnMut(usize) -> Result<T, String>,
    copy: usize,
    width: usize,
) -> Result<T, String> {
    let values = load(copy)?;
    values.validate(copy, width)?;
    Ok(values)
}

#[cfg(test)]
struct ValidatedCandidateCopy<T: RawBooleanCopy> { input: T }
#[cfg(test)]
struct ValidatedCandidateSpan<'a, T: RawBooleanCopy> { span: BooleanSpan<'a, T> }

// The Checked branch still calls the unchanged read_copy. Candidate performs
// one strong validation per load, then owns that exact immutable allocation.
enum LocalCopy<T: RawBooleanCopy> {
    Checked(T),
    #[cfg(test)] Candidate(ValidatedCandidateCopy<T>),
}
impl<T: RawBooleanCopy> LocalCopy<T> {
    fn raw(&self) -> &T {
        match self { Self::Checked(input) => input,
            #[cfg(test)] Self::Candidate(checked) => &checked.input }
    }
    #[cfg(test)]
    fn candidate_u0_span(&self, prefix: &[Fr], start: usize, width: usize)
        -> Result<Option<ValidatedCandidateSpan<'_, T>>, String> {
        if !prefix.is_empty() { return Ok(None); }
        if width < 2 || !width.is_power_of_two() || start % width != 0 {
            return Err(GkrError::PointDimension.to_string());
        }
        match self {
            Self::Checked(_) => Ok(None),
            Self::Candidate(checked) => Ok(Some(ValidatedCandidateSpan {
                span: bank_span(&checked.input, start, width)?,
            })),
        }
    }
}
fn read_local_copy<T: RawBooleanCopy>(load: &mut impl FnMut(usize) -> Result<T, String>,
    copy: usize, width: usize, policy: &ResidualPolicy) -> Result<LocalCopy<T>, String> {
    match policy {
        ResidualPolicy::Checked => read_copy(load, copy, width).map(LocalCopy::Checked),
        #[cfg(test)] ResidualPolicy::Candidate => {
            let input = load(copy)?;
            input.validate_candidate_original(copy, width)?;
            Ok(LocalCopy::Candidate(ValidatedCandidateCopy { input }))
        }
    }
}

/// First-U message for a span of one already validated ORIGINAL copy. A/B
/// remain arbitrary Fr; only X's two LSB-ordered original bits select a case.
#[cfg(test)]
fn candidate_u0_message<T: RawBooleanCopy>(a: &[Fr], b: &[Fr], input: &ValidatedCandidateSpan<'_, T>)
    -> Result<Vec<Fr>, String> {
    let n = input.span.len();
    if n < 2 || !n.is_power_of_two() || a.len() != n || b.len() != n {
        return Err(GkrError::PointDimension.to_string());
    }
    let mut message = vec![Fr::zero(); 3];
    for low in (0..n).step_by(2) {
        let a0 = a[low]; let b0 = b[low];
        let da = a[low + 1] - a0; let db = b[low + 1] - b0;
        match (input.span.bit(low), input.span.bit(low + 1)) {
            (false, false) => { message[0] += b0; message[1] += db; }
            (false, true) => { message[0] += b0; message[1] += a0 + db; message[2] += da; }
            (true, false) => { message[0] += a0 + b0; message[1] += da - a0 + db; message[2] -= da; }
            (true, true) => { message[0] += a0 + b0; message[1] += da + db; }
        }
    }
    Ok(message)
}

fn candidate_phase_trace(policy: &ResidualPolicy, phase: &str, edge: &str,
    round: Option<usize>, rounds: usize) -> Result<(), String> {
    #[cfg(test)]
    if matches!(policy, ResidualPolicy::Candidate) {
        use std::io::Write;
        if let Some(round) = round {
            println!("CORE_POOL_CANDIDATE_PHASE phase={phase} edge={edge} round={round} rounds={rounds}");
        } else {
            println!("CORE_POOL_CANDIDATE_PHASE phase={phase} edge={edge} rounds={rounds}");
        }
        std::io::stdout().flush().map_err(|e| format!("candidate phase trace: {e}"))?;
    }
    #[cfg(not(test))]
    let _ = (policy, phase, edge, round, rounds);
    Ok(())
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, x)| {
            weight
                * if index >> bit & 1 == 1 {
                    *x
                } else {
                    Fr::one() - x
                }
        })
}

/// Fold the low Boolean coordinates by one shared equality table.
fn boolean_prefix<T: RawBooleanCopy>(input: &T, prefix_weights: &[Fr]) -> Result<Vec<Fr>, GkrError> {
    if prefix_weights.is_empty()
        || !prefix_weights.len().is_power_of_two()
        || input.len() == 0
        || input.len() % prefix_weights.len() != 0
    {
        return Err(GkrError::PointDimension);
    }
    let mut folded = Vec::with_capacity(input.len() / prefix_weights.len());
    for start in (0..input.len()).step_by(prefix_weights.len()) {
        folded.push(prefix_weights.iter().enumerate()
            .filter(|(offset, _)| input.bit(start + *offset))
            .map(|(_, weight)| *weight).sum());
    }
    Ok(folded)
}

fn send_round(
    polynomial: Vec<Fr>,
    claim: &mut Fr,
    rounds: &mut Vec<Vec<Fr>>,
    transcript: &mut Transcript,
) -> Result<Fr, GkrError> {
    if polynomial[0] + gkr::eval_polynomial(&polynomial, Fr::one()) != *claim {
        return Err(GkrError::SumcheckIdentity);
    }
    gkr::append_polynomial(transcript, b"gkr-sumcheck-polynomial", &polynomial);
    let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
    *claim = gkr::eval_polynomial(&polynomial, challenge);
    rounds.push(polynomial);
    Ok(challenge)
}

fn quadratic_scaled_d(a: &[Fr], d: &[Fr], x: &[Fr], sigma: Fr) -> Vec<Fr> {
    let mut polynomial = vec![Fr::zero(); 3];
    let (mut d_constant, mut d_linear) = (Fr::zero(), Fr::zero());
    for pair in 0..a.len() / 2 {
        let low = 2 * pair;
        let da = a[low + 1] - a[low];
        let dx = x[low + 1] - x[low];
        polynomial[0] += a[low] * x[low];
        polynomial[1] += a[low] * dx + da * x[low];
        polynomial[2] += da * dx;
        d_constant += d[low];
        d_linear += d[low + 1] - d[low];
    }
    polynomial[0] += sigma * d_constant;
    polynomial[1] += sigma * d_linear;
    polynomial
}

fn multiply_polynomials(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
    let mut out = vec![Fr::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += *x * *y;
        }
    }
    out
}

fn copy_line_selector(copy: usize, u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let mut polynomial = vec![Fr::one()];
    for (bit, (a, b)) in u.iter().zip(v).enumerate() {
        let linear = if copy >> bit & 1 == 1 {
            [*a, *b - *a]
        } else {
            [Fr::one() - *a, *a - *b]
        };
        polynomial = multiply_polynomials(&polynomial, &linear);
    }
    polynomial
}

/// Production entry point: one loaded slot, selected physical banks only.
pub(crate) fn prove_single_slot(
    core: &Circuit,
    bank_bits: usize,
    physical_banks: &[usize],
    load: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript),
    wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>,
) -> Result<(GkrProof, InputClaim), String> {
    prove_tensor(
        core,
        bank_bits,
        physical_banks,
        0,
        load,
        transcript,
        bind,
        wiring,
    )
}

#[cfg(test)]
pub(crate) fn prove_with_copy_bits_for_test(
    core: &Circuit,
    bank_bits: usize,
    physical_banks: &[usize],
    copy_bits: usize,
    load: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript),
    wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>,
) -> Result<(GkrProof, InputClaim), String> {
    if copy_bits > 2 {
        return Err("test copy dimension exceeds 2".into());
    }
    prove_tensor(
        core,
        bank_bits,
        physical_banks,
        copy_bits,
        load,
        transcript,
        bind,
        wiring,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_tensor(
    core: &Circuit,
    bank_bits: usize,
    physical_banks: &[usize],
    copy_bits: usize,
    mut load: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript),
    wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>,
) -> Result<(GkrProof, InputClaim), String> {
    prove_tensor_inner(core, bank_bits, physical_banks, copy_bits,
        |copy| load(copy).map(|values| DenseBooleanCopy { values }), transcript, bind, wiring)
}

/// Separate private diagnostic H3 admission; old copy/H12 entries stay intact.
#[cfg(test)]
pub(crate) fn prove_h3_for_test(
    core:&Circuit,bank_bits:usize,physical_banks:&[usize],copy_bits:usize,
    mut load:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim),String>{
    let expected:Vec<_>=crate::work_tree_layout::CORE_OFFSETS.iter().map(|n|n/crate::work_tree_layout::CORE).collect();
    if bank_bits!=4 || copy_bits!=3 || physical_banks!=expected.as_slice() || expected.len()!=11
        || core.input_len!=65536 || core.row_count!=131072 {
        return Err("scaling41 core policy".into());
    }
    prove_tensor_with_limits(core,bank_bits,physical_banks,copy_bits,
        |owner|load(owner).map(|values|DenseBooleanCopy{values}),transcript,|t|{bind(t);Ok(())},
        wiring,&mut DenseHigh,3,128)
}

/// The authority can only be issued by the private fields of an OLD h0 Plan.
#[cfg(test)]
pub(crate) fn prove_packed_single_slot(
    authority: &crate::core_pool::PackedCoreAuthority<'_>,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), String> {
    let banks = authority.banks();
    prove_tensor_inner(authority.core(), 4, &banks, 0,
        |copy| authority.view().read_copy(copy), transcript,
        |t| authority.bind(t), |r, u, v| authority.coefficients(r, u, v))
}

/// Separate h2 entry, with the unchanged static Boolean tensor loop.
#[cfg(test)]
pub(crate) fn prove_packed_four_owners(
    authority: &crate::core_pool::PackedFourOwnerAuthority<'_>,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), String> {
    let banks = authority.banks();
    prove_tensor_inner(authority.core(), 4, &banks, 2,
        |owner| authority.view().read_copy(owner), transcript,
        |t| authority.bind(t), |r, u, v| authority.coefficients(r, u, v))
}

/// Exact test-only native role0 shape, reusing the packed tensor and DenseHigh path.
#[cfg(test)]
pub(crate) fn prove_packed_native_role0(
    authority: &crate::core_pool::PackedNativeRole0Authority<'_>,
    transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript) -> Result<(), String>,
    wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>,
) -> Result<(GkrProof, InputClaim), String> {
    let banks = authority.banks();
    if banks.len() != 11 || banks != crate::work_tree_layout::CORE_OFFSETS
        .map(|offset| offset / crate::work_tree_layout::CORE) {
        return Err("native role0 physical bank authority".into());
    }
    prove_tensor_with_limits(authority.core(), 4, &banks, 12,
        |owner| authority.view().read_copy(owner), transcript, bind, wiring,
        &mut DenseHigh, 12, 65536)
}

/// Unverified producer output. This is neither a native authority nor a
/// verifier-success token; its claim still requires independent GKR/PCS checks.
#[cfg(test)]
pub(crate) struct CandidateRole0Proof { proof:GkrProof,claim:InputClaim }
#[cfg(test)]
impl CandidateRole0Proof {
    pub(crate) fn into_parts(self)->(GkrProof,InputClaim) {(self.proof,self.claim)}
}

/// Closed N3073/H12 candidate entry over the actual locked source. The existing
/// Plan pins the template and axes, but does not assert zero residuals here.
#[cfg(test)]
pub(crate) fn prove_packed_native_role0_candidate(
    plan:&crate::core_pool::Plan,source:&crate::packed::PackedFile,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<CandidateRole0Proof,String> {
    plan.require_native_role0_shape()?;
    let view=source.native_role0_view()?;view.require_same_source(source)?;
    let core=&crate::work_tree_fixed_hash::engine()?.core;
    let banks=crate::work_tree_layout::CORE_OFFSETS.map(|offset|offset/crate::work_tree_layout::CORE);
    let(proof,claim)=prove_tensor_with_policy(core,4,&banks,12,
        |owner|view.read_copy(owner),transcript,bind,wiring,&mut DenseHigh,12,65536,
        ResidualPolicy::Candidate)?;
    Ok(CandidateRole0Proof {proof,claim})
}

#[allow(clippy::too_many_arguments)]
fn prove_tensor_inner<T: RawBooleanCopy>(
    core: &Circuit,
    bank_bits: usize,
    physical_banks: &[usize],
    copy_bits: usize,
    mut load: impl FnMut(usize) -> Result<T, String>,
    transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript),
    wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>,
) -> Result<(GkrProof, InputClaim), String> {
    prove_tensor_with_high(core, bank_bits, physical_banks, copy_bits, load,
        transcript, bind, wiring, &mut DenseHigh)
}

mod high_rows_seal { pub(super) trait Sealed {} }

#[derive(Clone, Copy, Default)]
pub(crate) struct HighSourceMetrics {
    pub(crate) passes: u64,
    pub(crate) owner_loads: u64,
    pub(crate) records: u64,
}

/// Only the live U/V boundary constructors can issue a real producer.
pub(crate) trait HighRows: high_rows_seal::Sealed {
    fn records(&self) -> usize;
    fn record_limit(&self) -> usize;
    fn metrics(&self) -> HighSourceMetrics;
    fn pass(&mut self, visitor: &mut dyn FnMut(usize, [Fr; 3]) -> Result<(), String>)
        -> Result<(), String>;
}
enum HighCoefficients<'a> {
    U { kernels: FirstPhase, copy_weights: &'a [Fr], family_weights: &'a [Fr] },
    V { tau: Vec<Fr>, c: Fr, d: Fr },
}
struct HighProducer<'a, T, F> {
    load: &'a mut F,
    coefficients: HighCoefficients<'a>,
    banks: &'a [usize],
    copies: usize,
    bank_count: usize,
    local_width: usize,
    base_width: usize,
    prefix_weights: Vec<Fr>,
    metrics: HighSourceMetrics,
    record_limit: usize,
    marker: std::marker::PhantomData<T>,
}
impl<T, F> high_rows_seal::Sealed for HighProducer<'_, T, F> {}
impl<T: RawBooleanCopy, F: FnMut(usize) -> Result<T, String>> HighRows
    for HighProducer<'_, T, F>
{
    fn records(&self) -> usize { self.copies * self.bank_count }
    fn record_limit(&self) -> usize { self.record_limit }
    fn metrics(&self) -> HighSourceMetrics { self.metrics }
    fn pass(&mut self, visitor: &mut dyn FnMut(usize, [Fr; 3]) -> Result<(), String>)
        -> Result<(), String> {
        if self.metrics.passes >= 2 || self.bank_count > 16 || self.records() > self.record_limit
            || self.record_limit == 0 || self.prefix_weights.len() != self.local_width
            || self.prefix_weights.capacity() != self.local_width {
            return Err("high producer shape/capacity/pass".into());
        }
        self.metrics.passes += 1;
        for copy in 0..self.copies {
            let input = read_copy(self.load, copy, self.base_width)?;
            self.metrics.owner_loads += 1;
            // Preserve selected-family A/B reads before all physical-bank X reads.
            let mut ab = [[Fr::zero(); 2]; 16];
            for (family, bank) in self.banks.iter().copied().enumerate() {
                if bank >= self.bank_count { return Err("high producer bank".into()); }
                match &self.coefficients {
                    HighCoefficients::U { kernels, copy_weights, family_weights } => {
                        let raw = bank_span(&input, bank * self.local_width, self.local_width)?;
                        let (a, b) = kernels.vectors(&raw);
                        if a.len() != 1 || b.len() != 1 || a.capacity() != 1 || b.capacity() != 1 {
                            return Err(GkrError::PointDimension.to_string());
                        }
                        let scale = copy_weights[copy] * family_weights[family];
                        ab[bank][0] += scale * a[0]; ab[bank][1] += scale * b[0];
                    }
                    HighCoefficients::V { tau, c, d } => {
                        if tau.len() != self.banks.len() * self.copies {
                            return Err("high producer tau".into());
                        }
                        let scale = tau[family * self.copies + copy];
                        ab[bank][0] += scale * *c; ab[bank][1] += scale * *d;
                    }
                }
            }
            for bank in 0..self.bank_count {
                let raw = bank_span(&input, bank * self.local_width, self.local_width)?;
                let folded = boolean_prefix(&raw, &self.prefix_weights)
                    .map_err(|e| e.to_string())?;
                if folded.len() != 1 || folded.capacity() != 1 {
                    return Err(GkrError::PointDimension.to_string());
                }
                visitor(copy * self.bank_count + bank, [ab[bank][0], ab[bank][1], folded[0]])?;
                self.metrics.records += 1;
            }
            // No owner survives into the next copy, pass, or high challenge.
            drop(input);
        }
        Ok(())
    }
}

trait HighStrategy {
    fn begin_v(&mut self,_claim:Fr)->Result<(),String>{Ok(())}
    fn phase<P: HighRows>(&mut self, phase: u32, prefix: &[Fr], rows: P,
        claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript)
        -> Result<(Vec<Fr>, Fr), String>;
}
struct DenseHigh;
impl HighStrategy for DenseHigh {
    fn phase<P: HighRows>(&mut self, _phase: u32, _prefix: &[Fr], mut rows: P,
        claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript)
        -> Result<(Vec<Fr>, Fr), String> {
        let n = rows.records();
        if n == 0 || n > rows.record_limit() { return Err("dense high producer shape".into()); }
        let mut a=Vec::with_capacity(n);let mut b=Vec::with_capacity(n);let mut x=Vec::with_capacity(n);
        rows.pass(&mut |index,row| {
            if index != a.len() || index >= n { return Err("dense high producer order".into()); }
            a.push(row[0]);b.push(row[1]);x.push(row[2]);Ok(())
        })?;
        if a.len()!=n || a.capacity()!=n || b.capacity()!=n || x.capacity()!=n {
            return Err("dense high producer capacity".into());
        }
        drop(rows);
        gkr::prove_phase(a, b, &x, claim, rounds, transcript).map_err(|e| e.to_string())
    }
}

/// Fields are private; this token owns the producer, not initial row arrays.
#[cfg(test)]
pub(crate) struct RealHighPhase<'context, 'source, P: HighRows> {
    authority: &'context crate::core_pool::PackedFourOwnerAuthority<'source>,
    phase: u32, prefix: Vec<Fr>, producer: P, claim: Fr,
}
#[cfg(test)]
impl<'context, 'source, P: HighRows> RealHighPhase<'context, 'source, P> {
    pub(crate) fn into_parts(self) -> (&'context crate::core_pool::PackedFourOwnerAuthority<'source>,
        u32, Vec<Fr>, P, Fr) {
        (self.authority, self.phase, self.prefix, self.producer, self.claim)
    }
}

#[cfg(test)]
struct RealSpoolHigh<'context, 'source, 'evidence> {
    authority: &'context crate::core_pool::PackedFourOwnerAuthority<'source>,
    evidence: &'evidence mut crate::high_phase_spool::RealEvidence,
    next_phase: u32,
}
#[cfg(test)]
impl HighStrategy for RealSpoolHigh<'_, '_, '_> {
    fn begin_v(&mut self,claim:Fr)->Result<(),String>{self.evidence.begin_v(claim)}
    fn phase<P: HighRows>(&mut self, phase: u32, prefix: &[Fr], producer: P,
        claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript)
        -> Result<(Vec<Fr>, Fr), String> {
        if phase != self.next_phase || phase > 1 || prefix.len() != 16 || producer.records()!=64 {
            return Err("real high boundary shape/order".into());
        }
        let token = if phase == 0 {
            RealHighPhase { authority:self.authority, phase:0, prefix:prefix.to_vec(), producer,claim:*claim }
        } else {
            RealHighPhase { authority:self.authority, phase:1, prefix:prefix.to_vec(), producer,claim:*claim }
        };
        let result = self.evidence.prove_real(token, claim, rounds, transcript)?;
        self.next_phase += 1; Ok(result)
    }
}

#[cfg(test)]
pub(crate) fn prove_spooled_four_owners(
    authority: &crate::core_pool::PackedFourOwnerAuthority<'_>,
    evidence: &mut crate::high_phase_spool::RealEvidence, transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), String> {
    let banks=authority.banks();
    let mut strategy=RealSpoolHigh {authority,evidence,next_phase:0};
    let result=prove_tensor_with_high(authority.core(),4,&banks,2,
        |owner| authority.view().read_copy(owner), transcript,
        |t|authority.bind(t),|r,u,v|authority.coefficients(r,u,v),&mut strategy)?;
    if strategy.next_phase!=2 {return Err("real high phases incomplete".into());}
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
fn prove_tensor_with_high<T: RawBooleanCopy, H: HighStrategy>(
    core: &Circuit, bank_bits: usize, physical_banks: &[usize], copy_bits: usize,
    mut load: impl FnMut(usize) -> Result<T, String>, transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript),
    wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>, high: &mut H,
) -> Result<(GkrProof, InputClaim), String> {
    prove_tensor_with_limits(core, bank_bits, physical_banks, copy_bits, load,
        transcript, |t| { bind(t); Ok(()) }, wiring, high, 2, 64)
}

#[allow(clippy::too_many_arguments)]
fn prove_tensor_with_limits<T: RawBooleanCopy, H: HighStrategy>(
    core: &Circuit, bank_bits: usize, physical_banks: &[usize], copy_bits: usize,
    mut load: impl FnMut(usize) -> Result<T, String>, transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript) -> Result<(), String>,
    wiring: impl Fn(&[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], String>, high: &mut H,
    max_copy_bits: usize, max_high_records: usize,
) -> Result<(GkrProof, InputClaim), String> {
    prove_tensor_with_policy(core,bank_bits,physical_banks,copy_bits,load,transcript,
        bind,wiring,high,max_copy_bits,max_high_records,ResidualPolicy::Checked)
}

enum ResidualPolicy { Checked, #[cfg(test)] Candidate }

#[allow(clippy::too_many_arguments)]
fn prove_tensor_with_policy<T: RawBooleanCopy,H:HighStrategy>(
    core:&Circuit,bank_bits:usize,physical_banks:&[usize],copy_bits:usize,
    mut load:impl FnMut(usize)->Result<T,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,high:&mut H,
    max_copy_bits:usize,max_high_records:usize,residual_policy:ResidualPolicy,
)->Result<(GkrProof,InputClaim),String> {
    if bank_bits > 4 || copy_bits > max_copy_bits {
        return Err("core-pool boolean dimensions exceed admitted limits".into());
    }
    #[cfg(test)]
    let profile_started = std::time::Instant::now();
    let shape = sparse::validate(core, 0).map_err(|error| error.to_string())?;
    if shape.input_bits > 16 || shape.row_bits > 17 {
        return Err("core-pool boolean local shape exceeds limits".into());
    }
    if physical_banks.is_empty() {
        return Err("core-pool bank map is empty".into());
    }
    let bank_count = 1usize
        .checked_shl(bank_bits as u32)
        .ok_or("core-pool physical bank width overflow")?;
    let copies = 1usize
        .checked_shl(copy_bits as u32)
        .ok_or("core-pool slot count overflow")?;
    let high_records = bank_count.checked_mul(copies).ok_or("core-pool high record overflow")?;
    if high_records > max_high_records || max_high_records == 0 {
        return Err("core-pool high record admission".into());
    }
    let family_bits = if physical_banks.len() <= 1 {
        0
    } else {
        usize::BITS as usize - (physical_banks.len() - 1).leading_zeros() as usize
    };
    let family_count = 1usize
        .checked_shl(family_bits as u32)
        .ok_or("core-pool family count overflow")?;
    if physical_banks.len() > family_count {
        return Err("core-pool family encoding overflow".into());
    }
    let mut seen_banks = vec![false; bank_count];
    for bank in physical_banks {
        if *bank >= bank_count || seen_banks[*bank] {
            return Err("core-pool physical bank map is duplicate or out of range".into());
        }
        seen_banks[*bank] = true;
    }

    let local_width = core.input_len;
    let base_width = local_width
        .checked_mul(bank_count)
        .ok_or("core-pool input width overflow")?;
    let input_bits = shape
        .input_bits
        .checked_add(bank_bits)
        .ok_or("core-pool input dimension overflow")?;
    let input_log = input_bits
        .checked_add(copy_bits)
        .ok_or("core-pool input dimension overflow")?;
    let output_bits = shape
        .row_bits
        .checked_add(copy_bits)
        .and_then(|bits| bits.checked_add(family_bits))
        .ok_or("core-pool row dimension overflow")?;
    let output_width = core
        .row_count
        .checked_mul(copies)
        .and_then(|rows| rows.checked_mul(family_count))
        .ok_or("core-pool output width overflow")?;
    let expanded_input_width = base_width
        .checked_mul(copies)
        .ok_or("core-pool expanded input width overflow")?;
    if 1usize.checked_shl(input_log as u32) != Some(expanded_input_width)
        || 1usize.checked_shl(output_bits as u32) != Some(output_width)
    {
        return Err("core-pool boolean tensor dimensions are not exact powers of two".into());
    }

    // Every entry validates all input coordinates before binding. Only the
    // separate candidate policy omits the redundant residual calculation;
    // selected/excluded bank bits, framing and protocol claim zero stay fixed.
    #[cfg(test)]
    let validation_started = std::time::Instant::now();
    let mut residuals = match residual_policy {
        ResidualPolicy::Checked=>Some(vec![Fr::zero();core.row_count]),
        #[cfg(test)] ResidualPolicy::Candidate=>None,
    };
    for copy in 0..copies {
        let checked_input = read_local_copy(&mut load, copy, base_width, &residual_policy)?;
        let input = checked_input.raw();
        for bank in physical_banks {
            let bank_input = bank_span(input, bank * local_width, local_width)?;
            if let Some(residuals)=residuals.as_mut() {
            residuals.fill(Fr::zero());
            for term in &core.terms {
                let gate = &term.gate;
                let left = bank_input.bit(gate.left);
                let right = bank_input.bit(gate.right);
                let mut value = gate.c0;
                if left {
                    value += gate.c1;
                }
                if right {
                    value += gate.c2;
                }
                if left && right {
                    value += gate.c3;
                }
                residuals[term.row] += value;
            }
            if residuals.iter().any(|value| !value.is_zero()) {
                return Err(GkrError::NonzeroOutput.to_string());
            }
            }
        }
    }
    drop(residuals);

    #[cfg(test)]
    let validation_seconds = validation_started.elapsed().as_secs_f64();
    #[cfg(test)]
    let binding_kernel_started = std::time::Instant::now();

    bind(transcript)?;
    let r = gkr::output_point(output_width, transcript);
    gkr::append_usize(transcript, b"gkr-layer-index", 0);
    let row_weights = gkr::eq_weights(&r[..shape.row_bits]);
    let copy_weights = gkr::eq_weights(&r[shape.row_bits..shape.row_bits + copy_bits]);
    let family_weights = gkr::eq_weights(&r[shape.row_bits + copy_bits..]);
    let mut kernels = FirstPhase::new(core, &row_weights);
    #[cfg(test)]
    let binding_kernel_seconds = binding_kernel_started.elapsed().as_secs_f64();
    #[cfg(test)]
    let u_started = std::time::Instant::now();
    let mut claim = Fr::zero();
    let mut rounds = Vec::with_capacity(2 * input_log);

    // Phase u: fold local input bits first. The raw right wires stay Boolean;
    // only the left coordinates and their coefficient tables are folded.
    let mut u_local = Vec::with_capacity(shape.input_bits);
    candidate_phase_trace(&residual_policy, "u_local", "begin", None, shape.input_bits)?;
    for _ in 0..shape.input_bits {
        candidate_phase_trace(&residual_policy, "u_local", "begin", Some(u_local.len()), shape.input_bits)?;
        let prefix_weights = gkr::eq_weights(&u_local);
        let mut polynomial = vec![Fr::zero(); 3];
        for copy in 0..copies {
            let checked_input = read_local_copy(&mut load, copy, base_width, &residual_policy)?;
            let input = checked_input.raw();
            let contributions = physical_banks
                .par_iter()
                .copied()
                .enumerate()
                .map(|(family, bank)| {
                    let start = bank * local_width;
                    let bank_input = bank_span(input, start, local_width)?;
                    let (a, b) = kernels.vectors(&bank_input);
                    let scale = copy_weights[copy] * family_weights[family];
                    #[cfg(test)]
                    let message = if let Some(original) = checked_input.candidate_u0_span(&u_local, start, local_width)? {
                        candidate_u0_message(&a, &b, &original)?
                    } else {
                        let x = boolean_prefix(&bank_input, &prefix_weights).map_err(|error| error.to_string())?;
                        gkr::quadratic_message(&a, &b, &x)
                    };
                    #[cfg(not(test))]
                    let message = {
                        let x = boolean_prefix(&bank_input, &prefix_weights).map_err(|error| error.to_string())?;
                        gkr::quadratic_message(&a, &b, &x)
                    };
                    if message.len() != 3 {
                        return Err(GkrError::PointDimension.to_string());
                    }
                    Ok([scale * message[0], scale * message[1], scale * message[2]])
                })
                .collect::<Vec<Result<[Fr; 3], String>>>();
            for contribution in contributions {
                let contribution = contribution?;
                for (sum, coefficient) in polynomial.iter_mut().zip(contribution) {
                    *sum += coefficient;
                }
            }
        }
        let challenge = send_round(polynomial, &mut claim, &mut rounds, transcript)
            .map_err(|error| error.to_string())?;
        kernels.bind_low(challenge);
        candidate_phase_trace(&residual_policy, "u_local", "end", Some(u_local.len()), shape.input_bits)?;
        u_local.push(challenge);
    }
    candidate_phase_trace(&residual_policy, "u_local", "end", None, shape.input_bits)?;

    #[cfg(test)]
    let u_local_duration = u_started.elapsed();

    let u_rows=HighProducer {
        load:&mut load,coefficients:HighCoefficients::U {kernels,copy_weights:&copy_weights,
            family_weights:&family_weights},banks:physical_banks,copies,bank_count,local_width,base_width,
        prefix_weights:gkr::eq_weights(&u_local),metrics:HighSourceMetrics::default(),
        record_limit:max_high_records,marker:std::marker::PhantomData::<T>,
    };
    // Consuming strategy drops kernels and prefix weights before high folding.
    candidate_phase_trace(&residual_policy, "u_high", "begin", None, input_bits + copy_bits - shape.input_bits)?;
    let (u_high, left_value) = high.phase(0, &u_local, u_rows,
        &mut claim, &mut rounds, transcript)?;
    candidate_phase_trace(&residual_policy, "u_high", "end", None, u_high.len())?;
    let mut u = u_local;
    u.extend(u_high);

    #[cfg(test)]
    let u_duration = u_started.elapsed();
    #[cfg(test)]
    let u_seconds = u_duration.as_secs_f64();
    #[cfg(test)]
    let u_local_seconds = u_local_duration.as_secs_f64();
    #[cfg(test)]
    let u_high_seconds = u_duration.checked_sub(u_local_duration)
        .expect("monotonic U phase measurement").as_secs_f64();
    #[cfg(test)]
    let v_started = std::time::Instant::now();

    // The whole V phase inherits U's final claim, before its 16 local rounds.
    candidate_phase_trace(&residual_policy, "v", "begin", None, input_log)?;
    high.begin_v(claim)?;
    // Phase v local coefficients are independent of family and slot. Their
    // selector sum is retained as sigma so a zero sigma needs no division.
    let u_local_weights = gkr::eq_weights(&u[..shape.input_bits]);
    let mut c = vec![Fr::zero(); local_width];
    let mut d = vec![Fr::zero(); local_width];
    for term in &core.terms {
        let gate = &term.gate;
        let weight = row_weights[term.row] * u_local_weights[gate.left];
        c[gate.right] += weight * (gate.c2 + gate.c3 * left_value);
        d[gate.right] += weight * (gate.c0 + gate.c1 * left_value);
    }
    drop(u_local_weights);
    let u_bank = &u[shape.input_bits..input_bits];
    let u_copy = &u[input_bits..];
    let mut tau = vec![Fr::zero(); physical_banks.len() * copies];
    let mut sigma = Fr::zero();
    for (family, bank) in physical_banks.iter().copied().enumerate() {
        let bank_weight = eq_index(u_bank, bank);
        for copy in 0..copies {
            let value =
                copy_weights[copy] * family_weights[family] * bank_weight * eq_index(u_copy, copy);
            tau[family * copies + copy] = value;
            sigma += value;
        }
    }

    let mut x_bar = vec![Fr::zero(); local_width];
    for copy in 0..copies {
        let input = read_copy(&mut load, copy, base_width)?;
        for (family, bank) in physical_banks.iter().copied().enumerate() {
            let scale = tau[family * copies + copy];
            let start = bank * local_width;
            for local in 0..local_width {
                if input.bit(start + local) {
                    x_bar[local] += scale;
                }
            }
        }
    }

    let mut v_local = Vec::with_capacity(shape.input_bits);
    candidate_phase_trace(&residual_policy, "v_local", "begin", None, shape.input_bits)?;
    for _ in 0..shape.input_bits {
        let polynomial = quadratic_scaled_d(&c, &d, &x_bar, sigma);
        let challenge = send_round(polynomial, &mut claim, &mut rounds, transcript)
            .map_err(|error| error.to_string())?;
        gkr::fold(&mut c, challenge);
        gkr::fold(&mut d, challenge);
        gkr::fold(&mut x_bar, challenge);
        v_local.push(challenge);
    }
    candidate_phase_trace(&residual_policy, "v_local", "end", None, v_local.len())?;
    #[cfg(test)]
    let v_local_duration = v_started.elapsed();
    let c_value = c[0];
    let d_value = d[0];
    drop(c);
    drop(d);
    drop(x_bar);

    let v_rows=HighProducer {
        load:&mut load,coefficients:HighCoefficients::V {tau,c:c_value,d:d_value},
        banks:physical_banks,copies,bank_count,local_width,base_width,
        prefix_weights:gkr::eq_weights(&v_local),metrics:HighSourceMetrics::default(),
        record_limit:max_high_records,marker:std::marker::PhantomData::<T>,
    };
    // Tau survives both source passes, then drops before high folding.
    candidate_phase_trace(&residual_policy, "v_high", "begin", None, input_bits + copy_bits - shape.input_bits)?;
    let (v_high, right_value) = high.phase(1, &v_local, v_rows,
        &mut claim, &mut rounds, transcript)?;
    candidate_phase_trace(&residual_policy, "v_high", "end", None, v_high.len())?;
    let mut v = v_local;
    v.extend(v_high);
    candidate_phase_trace(&residual_policy, "v", "end", None, v.len())?;

    #[cfg(test)]
    let v_duration = v_started.elapsed();
    #[cfg(test)]
    let v_seconds = v_duration.as_secs_f64();
    #[cfg(test)]
    let v_local_seconds = v_local_duration.as_secs_f64();
    #[cfg(test)]
    let v_high_seconds = v_duration.checked_sub(v_local_duration)
        .expect("monotonic V phase measurement").as_secs_f64();
    #[cfg(test)]
    let wiring_started = std::time::Instant::now();

    let coefficients = wiring(&r, &u, &v)?;
    if coefficients[0]
        + coefficients[1] * left_value
        + coefficients[2] * right_value
        + coefficients[3] * left_value * right_value
        != claim
    {
        return Err(GkrError::TerminalExpression.to_string());
    }

    #[cfg(test)]
    let wiring_seconds = wiring_started.elapsed().as_secs_f64();
    #[cfg(test)]
    let line_started = std::time::Instant::now();

    let base_bits = shape.input_bits + bank_bits;
    candidate_phase_trace(&residual_policy, "line", "begin", None, input_log + 1)?;
    let mut line = vec![Fr::zero(); input_log + 1];
    for copy in 0..copies {
        let input = read_copy(&mut load, copy, base_width)?;
        let local = input.line(&u[..base_bits], &v[..base_bits])?;
        let selector = copy_line_selector(copy, &u[base_bits..], &v[base_bits..]);
        for (sum, coefficient) in line.iter_mut().zip(multiply_polynomials(&local, &selector)) {
            *sum += coefficient;
        }
    }
    if line[0] != left_value || gkr::eval_polynomial(&line, Fr::one()) != right_value {
        return Err(GkrError::LineEndpoints.to_string());
    }
    transcript.append_scalar(b"gkr-left-value", &left_value);
    transcript.append_scalar(b"gkr-right-value", &right_value);
    gkr::append_polynomial(transcript, b"gkr-line-polynomial", &line);
    let challenge = transcript.challenge_scalar(b"gkr-line-challenge");
    let point = gkr::line_point(&u, &v, challenge);
    let value = gkr::eval_polynomial(&line, challenge);
    candidate_phase_trace(&residual_policy, "line", "end", None, line.len())?;
    #[cfg(test)]
    if std::env::var_os("NIPOPOW_CORE_POOL_PROFILE").is_some() {
        println!(
            "{} {}", T::PROFILE_PREFIX,
            serde_json::json!({
                "scope": "initialized Boolean producer phases; no historical measurement",
                "copy_bits": copy_bits, "slots": copies, "input_log": input_log,
                "validation_seconds": validation_seconds,
                "binding_and_kernel_seconds": binding_kernel_seconds,
                "u_seconds": u_seconds, "v_seconds": v_seconds,
                "u_local_seconds": u_local_seconds, "u_high_seconds": u_high_seconds,
                "v_local_seconds": v_local_seconds, "v_high_seconds": v_high_seconds,
                "terminal_wiring_seconds": wiring_seconds,
                "line_and_finish_seconds": line_started.elapsed().as_secs_f64(),
                "total_before_report_seconds": profile_started.elapsed().as_secs_f64(),
                "phase_scope": "phase intervals include their witness loading and validation"
            })
        );
    }
    Ok((
        GkrProof {
            layers: vec![LayerProof {
                rounds,
                left_value,
                right_value,
                line_coefficients: line,
            }],
        },
        InputClaim { point, value },
    ))
}

#[cfg(test)]
pub(crate) fn dense_dispatch_controls() {
    tests::exact_stream_cacheless_and_resident_proofs_match_for_small_copy_tensors();
}

#[cfg(test)]
#[path="core_pool_boolean_candidate_tests.rs"]
mod candidate_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{gkr::Gate, sparse_stream_roster};

    fn s(value: u64) -> Fr {
        Fr::from(value)
    }

    fn transcript() -> Transcript {
        Transcript::new(b"core-pool-boolean-parity-v1")
    }

    pub(super) fn fixture() -> Circuit {
        let mut terms = vec![
            Term {
                row: 0,
                gate: Gate {
                    left: 0,
                    right: 3,
                    c0: -s(1),
                    c1: -s(1),
                    c2: s(1),
                    c3: s(1),
                },
            },
            Term {
                row: 1,
                gate: Gate {
                    left: 1,
                    right: 1,
                    c0: Fr::zero(),
                    c1: -s(1),
                    c2: Fr::zero(),
                    c3: s(1),
                },
            },
            Term {
                row: 2,
                gate: Gate {
                    left: 2,
                    right: 1,
                    c0: Fr::zero(),
                    c1: s(1),
                    c2: -s(1),
                    c3: Fr::zero(),
                },
            },
            Term {
                row: 3,
                gate: Gate {
                    left: 0,
                    right: 3,
                    c0: -s(3),
                    c1: -s(2),
                    c2: s(3),
                    c3: s(2),
                },
            },
        ];
        let cancellation = Gate {
            left: 2,
            right: 0,
            c0: s(5),
            c1: s(7),
            c2: s(11),
            c3: s(13),
        };
        terms.push(Term {
            row: 3,
            gate: cancellation.clone(),
        });
        terms.push(Term {
            row: 3,
            gate: Gate {
                c0: -cancellation.c0,
                c1: -cancellation.c1,
                c2: -cancellation.c2,
                c3: -cancellation.c3,
                ..cancellation
            },
        });
        Circuit {
            input_len: 4,
            row_count: 4,
            terms,
        }
    }

    fn input_for(copy: usize) -> Vec<Fr> {
        let mut input = vec![Fr::zero(); 16];
        for bank in [0usize, 2, 3] {
            let x0 = (bank + copy) & 1;
            let x1 = ((bank >> 1) ^ copy) & 1;
            input[bank * 4] = Fr::from(x0 as u64);
            input[bank * 4 + 1] = Fr::from(x1 as u64);
            input[bank * 4 + 2] = Fr::from(x1 as u64);
            input[bank * 4 + 3] = Fr::one();
        }
        for bit in 0..4 {
            input[4 + bit] = Fr::from(((copy >> (bit & 1)) & 1) as u64);
        }
        input
    }

    fn expanded(core: &Circuit, h: usize) -> Circuit {
        let banks = [0usize, 2, 3];
        let copies = 1usize << h;
        let mut terms = Vec::new();
        for family in 0..banks.len() {
            for copy in 0..copies {
                for term in &core.terms {
                    terms.push(Term {
                        row: (family << (2 + h)) | (copy << 2) | term.row,
                        gate: Gate {
                            left: copy * 16 + banks[family] * 4 + term.gate.left,
                            right: copy * 16 + banks[family] * 4 + term.gate.right,
                            ..term.gate.clone()
                        },
                    });
                }
            }
        }
        Circuit {
            input_len: 16 * copies,
            row_count: 4 * (1usize << (2 + h)),
            terms,
        }
    }

    fn roster_terms(
        core: &Circuit,
        copy: usize,
        sink: &mut dyn FnMut(Term) -> Result<(), String>,
    ) -> Result<(), String> {
        if copy >= 4 {
            return Err("test copy outside range".into());
        }
        for (family, bank) in [0usize, 2, 3].into_iter().enumerate() {
            for term in &core.terms {
                sink(Term {
                    row: (family << 2) | term.row,
                    gate: Gate {
                        left: bank * 4 + term.gate.left,
                        right: bank * 4 + term.gate.right,
                        ..term.gate.clone()
                    },
                })?;
            }
        }
        Ok(())
    }

    fn ledger(t: &Transcript) -> (u64, u64, u64) {
        (t.challenges(), t.raw_queries(), t.bytes_absorbed())
    }

    #[test]
    pub(super) fn exact_stream_cacheless_and_resident_proofs_match_for_small_copy_tensors() {
        let core = fixture();
        let banks = [0usize, 2, 3];
        for h in 0..=2 {
            let copies = 1usize << h;
            let circuit = expanded(&core, h);
            let resident_shape = sparse::validate(&circuit, 0).unwrap();
            let load = |copy| Ok(input_for(copy));
            let bind = |t: &mut Transcript| {
                t.append_bytes(b"test-core-pool", b"same-published-statement");
                gkr::append_usize(t, b"test-copy-bits", h);
            };
            let wiring = |r: &[Fr], u: &[Fr], v: &[Fr]| {
                sparse::wiring(&circuit, &resident_shape, r, u, v).map_err(|e| e.to_string())
            };

            let point = |n: usize, salt: usize| {
                (0..n).map(|i| s((i + salt + 2) as u64)).collect::<Vec<_>>()
            };
            let non_boolean = wiring(&point(4 + h, 3), &point(4 + h, 5), &point(4 + h, 7)).unwrap();
            assert!(non_boolean.iter().any(|coefficient| !coefficient.is_zero()));

            let mut boolean_t = transcript();
            let boolean = if h == 0 {
                prove_single_slot(&core, 2, &banks, load, &mut boolean_t, bind, wiring).unwrap()
            } else {
                prove_with_copy_bits_for_test(
                    &core,
                    2,
                    &banks,
                    h,
                    load,
                    &mut boolean_t,
                    bind,
                    wiring,
                )
                .unwrap()
            };

            let mut roster_t = transcript();
            let roster = sparse_stream_roster::prove(
                4,
                h,
                2,
                2,
                &[2; 3],
                load,
                &mut roster_t,
                bind,
                |copy, sink| roster_terms(&core, copy, sink),
                wiring,
            )
            .unwrap();
            let mut replay_t = transcript();
            let replay = sparse_stream_roster::prove_with_cache_budget_for_test(
                4,
                h,
                2,
                2,
                &[2; 3],
                Some(0),
                load,
                &mut replay_t,
                bind,
                |copy, sink| roster_terms(&core, copy, sink),
                wiring,
            )
            .unwrap();
            let flat = (0..copies).flat_map(input_for).collect::<Vec<_>>();
            let mut resident_t = transcript();
            let resident =
                sparse::prove_with_binding(&circuit, &flat, 0, &mut resident_t, bind).unwrap();

            let expected_bytes = gkr::encode_proof(&resident.0).unwrap();
            assert_eq!(gkr::encode_proof(&boolean.0).unwrap(), expected_bytes);
            assert_eq!(gkr::encode_proof(&roster.0).unwrap(), expected_bytes);
            assert_eq!(gkr::encode_proof(&replay.0).unwrap(), expected_bytes);
            assert_eq!(boolean.1, resident.1);
            assert_eq!(roster.1, resident.1);
            assert_eq!(replay.1, resident.1);
            for current in [&boolean_t, &roster_t, &replay_t] {
                assert_eq!(ledger(current), ledger(&resident_t));
            }
            for current in [&boolean_t, &roster_t, &replay_t] {
                let mut current_cont = current.clone();
                let mut resident_cont = resident_t.clone();
                assert_eq!(
                    current_cont.challenge_scalar(b"continuation"),
                    resident_cont.challenge_scalar(b"continuation")
                );
            }
        }
    }

    #[test]
    fn boolean_prefix_and_sigma_zero_polynomial_match_dense_folds() {
        let raw = (0..16).map(|i| s((i & 1) as u64)).collect::<Vec<_>>();
        for prefix_len in 0..=4 {
            let point = (0..prefix_len)
                .map(|i| s((i + 2) as u64))
                .collect::<Vec<_>>();
            let weights = gkr::eq_weights(&point);
            let actual = boolean_prefix(&DenseBooleanCopy { values: raw.clone() }, &weights).unwrap();
            let mut expected = raw.clone();
            for coordinate in &point {
                gkr::fold(&mut expected, *coordinate);
            }
            assert_eq!(actual, expected);
        }
        let a = (0..8).map(|i| s((i + 2) as u64)).collect::<Vec<_>>();
        let d = (0..8).map(|i| s((i * 3 + 1) as u64)).collect::<Vec<_>>();
        let x = (0..8).map(|i| s((i * 5 + 2) as u64)).collect::<Vec<_>>();
        for sigma in [Fr::zero(), s(9)] {
            let mut dense_d = d.clone();
            for value in &mut dense_d {
                *value *= sigma;
            }
            assert_eq!(
                quadratic_scaled_d(&a, &d, &x, sigma),
                gkr::quadratic_message(&a, &dense_d, &x)
            );
        }
    }

    #[test]
    fn first_phase_kernels_match_dense_tables_at_every_left_prefix() {
        let core = fixture();
        let rows = [s(3), s(5), s(7), s(11)];
        let raw = vec![Fr::one(), Fr::zero(), Fr::one(), Fr::zero()];
        let mut dense_a = vec![Fr::zero(); core.input_len];
        let mut dense_b = vec![Fr::zero(); core.input_len];
        for term in &core.terms {
            let gate = &term.gate;
            dense_a[gate.left] += rows[term.row] * (gate.c1 + gate.c3 * raw[gate.right]);
            dense_b[gate.left] += rows[term.row] * (gate.c0 + gate.c2 * raw[gate.right]);
        }
        let mut kernel = FirstPhase::new(&core, &rows);
        let mut prefix = Vec::new();
        for depth in 0..=2 {
            let (actual_a, actual_b) = kernel.vectors(&DenseBooleanCopy { values: raw.clone() });
            let mut expected_a = dense_a.clone();
            let mut expected_b = dense_b.clone();
            for challenge in &prefix {
                gkr::fold(&mut expected_a, *challenge);
                gkr::fold(&mut expected_b, *challenge);
            }
            assert_eq!(actual_a.len(), core.input_len >> depth);
            assert_eq!(actual_b.len(), core.input_len >> depth);
            assert_eq!(actual_a, expected_a);
            assert_eq!(actual_b, expected_b);
            if depth < 2 {
                let challenge = s((depth + 13) as u64);
                kernel.bind_low(challenge);
                prefix.push(challenge);
            }
        }
    }

    #[test]
    fn rejects_bad_maps_non_boolean_excluded_bits_and_late_reader_errors() {
        let core = fixture();
        let banks = [0usize, 2, 3];
        let mut t = transcript();
        let initial_ledger = ledger(&t);
        let err = prove_single_slot(
            &core,
            2,
            &[0, 0],
            |_| panic!("duplicate map must fail first"),
            &mut t,
            |_| panic!("duplicate map must not bind"),
            |_, _, _| unreachable!(),
        )
        .unwrap_err();
        assert!(err.contains("duplicate"));
        assert_eq!(ledger(&t), initial_ledger);

        let mut non_boolean_t = transcript();
        let non_boolean_initial_ledger = ledger(&non_boolean_t);
        let non_boolean = prove_single_slot(
            &core,
            2,
            &banks,
            |_| {
                let mut input = input_for(0);
                input[4] = s(2);
                Ok(input)
            },
            &mut non_boolean_t,
            |_| panic!("non-Boolean read must precede binding"),
            |_, _, _| unreachable!(),
        )
        .unwrap_err();
        assert!(non_boolean.contains("non-Boolean input at copy 0, coordinate 4"));
        assert_eq!(ledger(&non_boolean_t), non_boolean_initial_ledger);

        let mut calls = 0usize;
        let mut late_t = transcript();
        let late_initial_ledger = ledger(&late_t);
        let late = prove_single_slot(
            &core,
            2,
            &banks,
            |_| {
                calls += 1;
                if calls == 2 {
                    return Err("late source failure".into());
                }
                Ok(input_for(0))
            },
            &mut late_t,
            |_| {},
            |_, _, _| unreachable!(),
        )
        .unwrap_err();
        assert_eq!(late, "late source failure");
        assert!(late_t.bytes_absorbed() > late_initial_ledger.2);
        assert!(late_t.challenges() > late_initial_ledger.0);
    }

    #[test]
    fn rejects_non_boolean_excluded_bank_on_every_h0_reread() {
        let core = fixture();
        let banks = [0usize, 2, 3];
        let circuit = expanded(&core, 0);
        let shape = sparse::validate(&circuit, 0).unwrap();
        // h0 reads once for preflight, twice during local-u rounds, then once
        // for each of high-u, x-bar, high-v, and the line polynomial.
        for failure_call in 1..=7 {
            let mut calls = 0usize;
            let mut t = transcript();
            let initial_ledger = ledger(&t);
            let error = prove_single_slot(
                &core,
                2,
                &banks,
                |_| {
                    calls += 1;
                    let mut input = input_for(0);
                    if calls == failure_call {
                        input[4] = s(2); // physical bank 1 is excluded
                    }
                    Ok(input)
                },
                &mut t,
                |_| {},
                |r, u, v| {
                    sparse::wiring(&circuit, &shape, r, u, v).map_err(|error| error.to_string())
                },
            )
            .unwrap_err();
            assert!(
                error.contains("non-Boolean input at copy 0, coordinate 4"),
                "read {failure_call} returned {error}"
            );
            assert_eq!(calls, failure_call);
            if failure_call == 1 {
                assert_eq!(ledger(&t), initial_ledger);
            } else {
                assert!(t.bytes_absorbed() > initial_ledger.2);
                assert!(t.challenges() > initial_ledger.0);
            }
        }
    }
}

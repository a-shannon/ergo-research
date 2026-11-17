//! Streaming producer for the identical sparse proof/transcript.
//! The callback MUST read one immutable snapshot shared with PCS commitment and
//! opening. Length checks do not authenticate an arbitrary callback's contents.
//! Each phase uses b local scans plus one post-challenge handoff scan. Three
//! copy-indexed field arrays are then folded in place; no full input table exists.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self, GkrError, GkrProof, InputClaim, LayerProof}, sparse::{self, Circuit}, transcript::Transcript};

fn read_copy(load: &mut impl FnMut(usize) -> Result<Vec<Fr>, GkrError>, index: usize, width: usize)
    -> Result<Vec<Fr>, GkrError>
{
    let values = load(index)?;
    if values.len() != width { return Err(GkrError::InvalidInputWidth); }
    Ok(values)
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |acc, (bit, value)| {
        acc * if (index >> bit) & 1 == 1 { *value } else { Fr::one() - value }
    })
}

fn send_round(polynomial: Vec<Fr>, claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript)
    -> Result<Fr, GkrError>
{
    if polynomial[0] + gkr::eval_polynomial(&polynomial, Fr::one()) != *claim {
        return Err(GkrError::SumcheckIdentity);
    }
    gkr::append_polynomial(transcript, b"gkr-sumcheck-polynomial", &polynomial);
    let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
    *claim = gkr::eval_polynomial(&polynomial, challenge);
    rounds.push(polynomial);
    Ok(challenge)
}

fn phase(
    circuit: &Circuit, shape: &sparse::Shape,
    load: &mut impl FnMut(usize) -> Result<Vec<Fr>, GkrError>,
    vectors: impl Fn(usize, &[Fr]) -> (Vec<Fr>, Vec<Fr>),
    claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript,
) -> Result<(Vec<Fr>, Fr), GkrError> {
    let mut point = Vec::with_capacity(shape.input_bits + shape.copies.trailing_zeros() as usize);
    for _ in 0..shape.input_bits {
        let mut polynomial = vec![Fr::zero(); 3];
        for copy in 0..shape.copies {
            let mut x = read_copy(load, copy, circuit.input_len)?;
            let (mut a, mut b) = vectors(copy, &x);
            for coordinate in &point {
                gkr::fold(&mut a, *coordinate); gkr::fold(&mut b, *coordinate); gkr::fold(&mut x, *coordinate);
            }
            for (sum, contribution) in polynomial.iter_mut().zip(gkr::quadratic_message(&a, &b, &x)) {
                *sum += contribution;
            }
        }
        point.push(send_round(polynomial, claim, rounds, transcript)?);
    }
    // The final local challenge is now known. This extra scan avoids retaining
    // six endpoint arrays before it is sampled. Exactly three high arrays live.
    let mut high_a = Vec::with_capacity(shape.copies);
    let mut high_b = Vec::with_capacity(shape.copies);
    let mut high_x = Vec::with_capacity(shape.copies);
    for copy in 0..shape.copies {
        let mut x = read_copy(load, copy, circuit.input_len)?;
        let (mut a, mut b) = vectors(copy, &x);
        for coordinate in &point {
            gkr::fold(&mut a, *coordinate); gkr::fold(&mut b, *coordinate); gkr::fold(&mut x, *coordinate);
        }
        high_a.push(a[0]); high_b.push(b[0]); high_x.push(x[0]);
    }
    while high_x.len() > 1 {
        let polynomial = gkr::quadratic_message(&high_a, &high_b, &high_x);
        let challenge = send_round(polynomial, claim, rounds, transcript)?;
        gkr::fold(&mut high_a, challenge); gkr::fold(&mut high_b, challenge); gkr::fold(&mut high_x, challenge);
        point.push(challenge);
    }
    Ok((point, high_x[0]))
}

fn multiply_polynomials(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
    let mut out = vec![Fr::zero(); a.len() + b.len() - 1];
    for (i, left) in a.iter().enumerate() { for (j, right) in b.iter().enumerate() {
        out[i + j] += *left * right;
    }}
    out
}

fn copy_line_selector(copy: usize, u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let mut polynomial = vec![Fr::one()];
    for (bit, (left, right)) in u.iter().zip(v).enumerate() {
        let linear = if (copy >> bit) & 1 == 1 {
            [*left, *right - left]
        } else {
            [Fr::one() - left, *left - right]
        };
        polynomial = multiply_polynomials(&polynomial, &linear);
    }
    polynomial
}

/// Produce precisely the resident sparse proof using repeated immutable-copy
/// reads. Total copy scans: one validation, 2*(b+1) sumcheck, and one line scan.
pub fn prove(
    circuit: &Circuit, log_copies: usize,
    mut load_copy: impl FnMut(usize) -> Result<Vec<Fr>, GkrError>,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), GkrError> {
    let shape = sparse::validate(circuit, log_copies)?;
    let mut residuals = vec![Fr::zero(); circuit.row_count];
    for copy in 0..shape.copies {
        let input = read_copy(&mut load_copy, copy, circuit.input_len)?;
        residuals.fill(Fr::zero());
        for term in &circuit.terms { residuals[term.row] += term.gate.evaluate(&input); }
        if residuals.iter().any(|value| !value.is_zero()) { return Err(GkrError::NonzeroOutput); }
    }
    drop(residuals);
    sparse::bind(circuit, log_copies, transcript);
    let r = gkr::output_point(shape.row_count, transcript);
    gkr::append_usize(transcript, b"gkr-layer-index", 0);
    let row_weights = gkr::eq_weights(&r[..shape.row_bits]);
    let r_high = &r[shape.row_bits..];
    let mut claim = Fr::zero();
    let mut rounds = Vec::new();
    let (u, left_value) = phase(circuit, &shape, &mut load_copy, |copy, input| {
        let omega = eq_index(r_high, copy);
        let mut a = vec![Fr::zero(); circuit.input_len];
        let mut b = vec![Fr::zero(); circuit.input_len];
        for term in &circuit.terms {
            let gate = &term.gate; let weight = omega * row_weights[term.row];
            a[gate.left] += weight * (gate.c1 + gate.c3 * input[gate.right]);
            b[gate.left] += weight * (gate.c0 + gate.c2 * input[gate.right]);
        }
        (a, b)
    }, &mut claim, &mut rounds, transcript)?;
    let u_low_weights = gkr::eq_weights(&u[..shape.input_bits]);
    let u_high = &u[shape.input_bits..];
    let mut c0 = vec![Fr::zero(); circuit.input_len];
    let mut d0 = vec![Fr::zero(); circuit.input_len];
    for term in &circuit.terms {
        let gate = &term.gate; let weight = row_weights[term.row] * u_low_weights[gate.left];
        c0[gate.right] += weight * (gate.c2 + gate.c3 * left_value);
        d0[gate.right] += weight * (gate.c0 + gate.c1 * left_value);
    }
    let (v, right_value) = phase(circuit, &shape, &mut load_copy, |copy, _input| {
        let tau = eq_index(r_high, copy) * eq_index(u_high, copy);
        (c0.iter().map(|value| *value * tau).collect(), d0.iter().map(|value| *value * tau).collect())
    }, &mut claim, &mut rounds, transcript)?;
    drop(c0); drop(d0);
    let coefficients = sparse::wiring(circuit, &shape, &r, &u, &v)?;
    if coefficients[0] + coefficients[1] * left_value + coefficients[2] * right_value
        + coefficients[3] * left_value * right_value != claim { return Err(GkrError::TerminalExpression); }
    let mut line_coefficients = vec![Fr::zero(); shape.input_bits + log_copies + 1];
    for copy in 0..shape.copies {
        let input = read_copy(&mut load_copy, copy, circuit.input_len)?;
        let local = gkr::line_polynomial(&input, &u[..shape.input_bits], &v[..shape.input_bits]);
        let selector = copy_line_selector(copy, u_high, &v[shape.input_bits..]);
        for (sum, contribution) in line_coefficients.iter_mut().zip(multiply_polynomials(&local, &selector)) {
            *sum += contribution;
        }
    }
    if line_coefficients[0] != left_value || gkr::eval_polynomial(&line_coefficients, Fr::one()) != right_value {
        return Err(GkrError::LineEndpoints);
    }
    transcript.append_scalar(b"gkr-left-value", &left_value);
    transcript.append_scalar(b"gkr-right-value", &right_value);
    gkr::append_polynomial(transcript, b"gkr-line-polynomial", &line_coefficients);
    let challenge = transcript.challenge_scalar(b"gkr-line-challenge");
    let point = gkr::line_point(&u, &v, challenge);
    let value = gkr::eval_polynomial(&line_coefficients, challenge);
    let proof = GkrProof { layers: vec![LayerProof { rounds, left_value, right_value, line_coefficients }] };
    Ok((proof, InputClaim { point, value }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sparse::Term;
    fn transcript() -> Transcript { Transcript::new(b"stream-exact-parity") }

    fn fixture(width: usize, copies: usize) -> (Circuit, Vec<Vec<Fr>>) {
        let values: Vec<Vec<Fr>> = (0..copies).map(|copy| (0..width).map(|i| {
            if i == width - 1 { Fr::one() } else { Fr::from((copy * 13 + i + 2) as u64) }
        }).collect()).collect();
        let mut terms = Vec::new();
        // (x+1)*(y-1)=0, with y last input fixed to one. All four gate
        // coefficients nonzero; repeated terms cancel within a second row.
        let gate = gkr::Gate { left: 0, right: width - 1,
            c0: -Fr::one(), c1: -Fr::one(), c2: Fr::one(), c3: Fr::one() };
        terms.push(Term { row: 0, gate: gate.clone() });
        terms.push(Term { row: 1, gate: gate.clone() });
        terms.push(Term { row: 1, gate: gkr::Gate { c0: -gate.c0, c1: -gate.c1, c2: -gate.c2, c3: -gate.c3, ..gate } });
        (Circuit { input_len: width, row_count: 4, terms }, values)
    }

    #[test]
    fn streaming_proof_bytes_and_challenge_schedule_equal_resident() {
        for width in [1usize, 2, 8, 16] { for h in 0..=3 {
            let (circuit, copies) = fixture(width, 1 << h);
            let input: Vec<_> = copies.iter().flatten().copied().collect();
            let mut resident_t = transcript();
            let resident = sparse::prove(&circuit, &input, h, &mut resident_t).unwrap();
            let mut streamed_t = transcript(); let mut reads = 0usize;
            let streamed = prove(&circuit, h, |copy| { reads += 1; Ok(copies[copy].clone()) }, &mut streamed_t).unwrap();
            assert_eq!(streamed, resident);
            assert_eq!(gkr::encode_proof(&streamed.0).unwrap(), gkr::encode_proof(&resident.0).unwrap());
            assert_eq!(streamed_t.raw_queries(), resident_t.raw_queries());
            assert_eq!(streamed_t.bytes_absorbed(), resident_t.bytes_absorbed());
            assert_eq!(streamed_t.challenge_scalar(b"after-proof"), resident_t.challenge_scalar(b"after-proof"));
            assert_eq!(reads, (2 * width.trailing_zeros() as usize + 4) * (1 << h));
            let accepted = sparse::verify(&circuit, h, &streamed.0, &mut transcript()).unwrap();
            assert_eq!(accepted, streamed.1);
            assert_eq!(accepted.value, gkr::mle(&input, &accepted.point).unwrap());
        }}
    }

    #[test]
    fn malformed_or_failed_source_and_nonzero_rows_rejected() {
        let (circuit, copies) = fixture(2, 2);
        assert_eq!(prove(&circuit, 1, |_| Ok(vec![]), &mut transcript()), Err(GkrError::InvalidInputWidth));
        assert_eq!(prove(&circuit, 1, |_| Err(GkrError::InvalidInputWidth), &mut transcript()), Err(GkrError::InvalidInputWidth));
        let mut reads = 0;
        assert_eq!(prove(&circuit, 1, |copy| {
            reads += 1;
            if reads > 2 { Ok(vec![]) } else { Ok(copies[copy].clone()) }
        }, &mut transcript()), Err(GkrError::InvalidInputWidth));
        let mut invalid = copies;
        invalid[1][1] = Fr::from(2);
        assert_eq!(prove(&circuit, 1, |copy| Ok(invalid[copy].clone()), &mut transcript()), Err(GkrError::NonzeroOutput));
    }
}

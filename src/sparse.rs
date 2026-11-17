//! One-layer sumcheck for independently checked sparse residual rows.
//! Rows may contain many bilinear terms; zero padding is part of the statement.
//! Copy indices are high bits. The verifier scans base terms, not expanded copies.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::gkr::{self, Gate, GkrError, GkrProof, InputClaim, LayerProof};
use crate::transcript::Transcript;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term {
    pub row: usize,
    pub gate: Gate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Circuit {
    pub input_len: usize,
    pub row_count: usize,
    pub terms: Vec<Term>,
}

const MAX_LOG_COPIES: usize = 3;
const MAX_DIMENSION: usize = 24;
const MAX_BASE_TERMS: usize = 1 << 20;
pub(crate) const H21_POINT_WINDOW_LOG_COPIES: usize = 4;

pub(crate) struct Shape {
    pub(crate) input_bits: usize,
    pub(crate) row_bits: usize,
    pub(crate) copies: usize,
    pub(crate) input_len: usize,
    pub(crate) row_count: usize,
}

pub(crate) fn validate(circuit: &Circuit, log_copies: usize) -> Result<Shape, GkrError> {
    if log_copies > MAX_LOG_COPIES { return Err(GkrError::RepetitionLimit); }
    let input_bits = gkr::log_width(circuit.input_len)?;
    let row_bits = gkr::log_width(circuit.row_count).map_err(|_| GkrError::InvalidLayerWidth)?;
    if input_bits.checked_add(log_copies).ok_or(GkrError::RepeatedSizeLimit)? > MAX_DIMENSION
        || row_bits.checked_add(log_copies).ok_or(GkrError::RepeatedSizeLimit)? > MAX_DIMENSION
        || circuit.terms.len() > MAX_BASE_TERMS {
        return Err(GkrError::RepeatedSizeLimit);
    }
    if circuit.terms.iter().any(|term| term.row >= circuit.row_count
        || term.gate.left >= circuit.input_len || term.gate.right >= circuit.input_len) {
        return Err(GkrError::InvalidWireIndex);
    }
    let copies = 1usize.checked_shl(log_copies as u32).ok_or(GkrError::RepeatedSizeLimit)?;
    let input_len = circuit.input_len.checked_mul(copies).ok_or(GkrError::RepeatedSizeLimit)?;
    let row_count = circuit.row_count.checked_mul(copies).ok_or(GkrError::RepeatedSizeLimit)?;
    Ok(Shape { input_bits, row_bits, copies, input_len, row_count })
}

/// A separate, bounded physical H21 point-bank experiment. The ordinary sparse
/// admission above retains its small-profile limits. The caller must use the
/// canonical point-membership circuit; dimensions and term count alone do not
/// identify a relation.
pub(crate) fn validate_h21_point_window(circuit: &Circuit) -> Result<Shape, GkrError> {
    if circuit.input_len != 1 << 13 || circuit.row_count != 1 << 14
        || circuit.terms.len() != 288_158 {
        return Err(GkrError::RepeatedSizeLimit);
    }
    let canonical = crate::point_membership::build().map_err(|_| GkrError::InvalidWireIndex)?;
    if canonical.circuit != *circuit { return Err(GkrError::InvalidWireIndex); }
    let copies = 1usize << H21_POINT_WINDOW_LOG_COPIES;
    let input_len = circuit.input_len.checked_mul(copies).ok_or(GkrError::RepeatedSizeLimit)?;
    let row_count = circuit.row_count.checked_mul(copies).ok_or(GkrError::RepeatedSizeLimit)?;
    // Each known live component is far below the unchanged 512-MiB producer
    // component policy. This is not a whole-Job or all-owner memory bound.
    const COMPONENT_LIMIT: usize = 512 << 20;
    let terms_bytes = circuit.terms.len().checked_mul(std::mem::size_of::<Term>())
        .ok_or(GkrError::RepeatedSizeLimit)?;
    let fields_bytes = input_len.checked_mul(std::mem::size_of::<Fr>())
        .ok_or(GkrError::RepeatedSizeLimit)?;
    if terms_bytes >= COMPONENT_LIMIT || fields_bytes >= COMPONENT_LIMIT
        || row_count.checked_mul(std::mem::size_of::<Fr>()).ok_or(GkrError::RepeatedSizeLimit)? >= COMPONENT_LIMIT {
        return Err(GkrError::RepeatedSizeLimit);
    }
    Ok(Shape { input_bits: 13, row_bits: 14, copies, input_len, row_count })
}

pub(crate) fn bind(circuit: &Circuit, log_copies: usize, transcript: &mut Transcript) {
    transcript.append_bytes(b"sparse-profile", b"bilinear-residual-rows-high-copies-v1");
    gkr::append_usize(transcript, b"sparse-log-copies", log_copies);
    gkr::append_usize(transcript, b"sparse-input-width", circuit.input_len);
    gkr::append_usize(transcript, b"sparse-row-count", circuit.row_count);
    gkr::append_usize(transcript, b"sparse-term-count", circuit.terms.len());
    for term in &circuit.terms {
        gkr::append_usize(transcript, b"sparse-row-index", term.row);
        gkr::append_usize(transcript, b"sparse-left-wire", term.gate.left);
        gkr::append_usize(transcript, b"sparse-right-wire", term.gate.right);
        transcript.append_scalar(b"sparse-c0", &term.gate.c0);
        transcript.append_scalar(b"sparse-c1", &term.gate.c1);
        transcript.append_scalar(b"sparse-c2", &term.gate.c2);
        transcript.append_scalar(b"sparse-c3", &term.gate.c3);
    }
}

fn check_residuals(circuit: &Circuit, input: &[Fr], shape: &Shape) -> Result<(), GkrError> {
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for copy_input in input.chunks_exact(circuit.input_len).take(shape.copies) {
        rows.fill(Fr::zero());
        for term in &circuit.terms { rows[term.row] += term.gate.evaluate(copy_input); }
        if rows.iter().any(|value| !value.is_zero()) { return Err(GkrError::NonzeroOutput); }
    }
    Ok(())
}

pub(crate) fn wiring(circuit: &Circuit, shape: &Shape, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], GkrError> {
    let copy_bits = shape.copies.trailing_zeros() as usize;
    if r.len() != shape.row_bits + copy_bits || u.len() != shape.input_bits + copy_bits
        || v.len() != shape.input_bits + copy_bits { return Err(GkrError::PointDimension); }
    let (r_low, r_high) = r.split_at(shape.row_bits);
    let (u_low, u_high) = u.split_at(shape.input_bits);
    let (v_low, v_high) = v.split_at(shape.input_bits);
    let row_weights = gkr::eq_weights(r_low);
    let left_weights = gkr::eq_weights(u_low);
    let right_weights = gkr::eq_weights(v_low);
    let mut coefficients = [Fr::zero(); 4];
    for term in &circuit.terms {
        let gate = &term.gate;
        let weight = row_weights[term.row] * left_weights[gate.left] * right_weights[gate.right];
        coefficients[0] += weight * gate.c0;
        coefficients[1] += weight * gate.c1;
        coefficients[2] += weight * gate.c2;
        coefficients[3] += weight * gate.c3;
    }
    let copy_factor = r_high.iter().zip(u_high).zip(v_high).fold(Fr::one(), |acc, ((r, u), v)| {
        acc * ((Fr::one() - r) * (Fr::one() - u) * (Fr::one() - v) + *r * u * v)
    });
    for coefficient in &mut coefficients { *coefficient *= copy_factor; }
    Ok(coefficients)
}

/// Prove every residual row in every copy equals zero. Sumcheck and line
/// construction reuse the GKR core; no expanded term list is materialized.
pub fn prove(circuit: &Circuit, input: &[Fr], log_copies: usize, transcript: &mut Transcript)
    -> Result<(GkrProof, InputClaim), GkrError>
{
    prove_with_binding(circuit,input,log_copies,transcript,|transcript| bind(circuit,log_copies,transcript))
}

/// Test/prototype entry point for a canonical compact statement binding. The
/// producer still consumes the materialized sparse circuit; only transcript
/// binding is supplied by the caller.
pub(crate) fn prove_with_binding(
    circuit: &Circuit, input: &[Fr], log_copies: usize, transcript: &mut Transcript,
    bind_statement: impl FnOnce(&mut Transcript),
) -> Result<(GkrProof, InputClaim), GkrError> {
    let shape = validate(circuit, log_copies)?;
    if input.len() != shape.input_len { return Err(GkrError::InvalidInputWidth); }
    check_residuals(circuit, input, &shape)?;
    bind_statement(transcript);
    let output_point = gkr::output_point(shape.row_count, transcript);
    gkr::append_usize(transcript, b"gkr-layer-index", 0);
    let row_weights = gkr::eq_weights(&output_point[..shape.row_bits]);
    let copy_weights = gkr::eq_weights(&output_point[shape.row_bits..]);
    let mut claim = Fr::zero();
    let mut a = vec![Fr::zero(); shape.input_len];
    let mut b = vec![Fr::zero(); shape.input_len];
    for (copy, copy_weight) in copy_weights.iter().enumerate() {
        let offset = copy * circuit.input_len;
        for term in &circuit.terms {
            let gate = &term.gate;
            let weight = *copy_weight * row_weights[term.row];
            let right = input[offset + gate.right];
            a[offset + gate.left] += weight * (gate.c1 + gate.c3 * right);
            b[offset + gate.left] += weight * (gate.c0 + gate.c2 * right);
        }
    }
    let mut rounds = Vec::new();
    // The row-weight table is no longer needed while folding the left
    // sumcheck. Rebuild it for the right phase instead of keeping another
    // 128 MiB live beside the input and the two interpolation tables on H3.
    drop(row_weights);
    let (u, left_value) = gkr::prove_phase(a, b, input, &mut claim, &mut rounds, transcript)?;
    let row_weights = gkr::eq_weights(&output_point[..shape.row_bits]);
    let left_weights = gkr::eq_weights(&u);
    let mut c = vec![Fr::zero(); shape.input_len];
    let mut d = vec![Fr::zero(); shape.input_len];
    for (copy, copy_weight) in copy_weights.iter().enumerate() {
        let offset = copy * circuit.input_len;
        for term in &circuit.terms {
            let gate = &term.gate;
            let weight = *copy_weight * row_weights[term.row] * left_weights[offset + gate.left];
            c[offset + gate.right] += weight * (gate.c2 + gate.c3 * left_value);
            d[offset + gate.right] += weight * (gate.c0 + gate.c1 * left_value);
        }
    }
    let (v, right_value) = gkr::prove_phase(c, d, input, &mut claim, &mut rounds, transcript)?;
    let coefficients = wiring(circuit, &shape, &output_point, &u, &v)?;
    if coefficients[0] + coefficients[1] * left_value + coefficients[2] * right_value
        + coefficients[3] * left_value * right_value != claim { return Err(GkrError::TerminalExpression); }
    let line_coefficients = gkr::line_polynomial(input, &u, &v);
    transcript.append_scalar(b"gkr-left-value", &left_value);
    transcript.append_scalar(b"gkr-right-value", &right_value);
    gkr::append_polynomial(transcript, b"gkr-line-polynomial", &line_coefficients);
    let challenge = transcript.challenge_scalar(b"gkr-line-challenge");
    let point = gkr::line_point(&u, &v, challenge);
    let value = gkr::eval_polynomial(&line_coefficients, challenge);
    let proof = GkrProof { layers: vec![LayerProof { rounds, left_value, right_value, line_coefficients }] };
    Ok((proof, InputClaim { point, value }))
}

/// Verify one sparse sumcheck and return the claim that the PCS must bind.
pub fn verify(circuit: &Circuit, log_copies: usize, proof: &GkrProof, transcript: &mut Transcript)
    -> Result<InputClaim, GkrError>
{
    let shape = validate(circuit, log_copies)?;
    gkr::verify_with_wiring(&[shape.input_bits + log_copies], shape.row_count, proof, transcript,
        |transcript| bind(circuit, log_copies, transcript),
        |_index, r, u, v| wiring(circuit, &shape, r, u, v))
}

/// One fixed-shape layer: exactly 7*log(total input width)+3 field elements.
pub fn decode_proof(circuit: &Circuit, log_copies: usize, bytes: &[u8]) -> Result<GkrProof, String> {
    let shape = validate(circuit, log_copies).map_err(|e| e.to_string())?;
    gkr::decode_dimensions(&[shape.input_bits + log_copies], bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn s(value: u64) -> Fr { Fr::from(value) }
    fn gate(left: usize, right: usize, coefficients: [Fr; 4]) -> Gate {
        Gate { left, right, c0: coefficients[0], c1: coefficients[1], c2: coefficients[2], c3: coefficients[3] }
    }
    fn transcript() -> Transcript { Transcript::new(b"sparse-core-tests-v1") }

    fn zero_rows(input: &[Fr], row_count: usize) -> Circuit {
        let mut terms = Vec::new();
        for row in 0..row_count.saturating_sub(1).max(1) {
            let mut residual = Fr::zero();
            // Repeated input pairs and mixed constants/linear/bilinear terms.
            for i in 0..3 {
                let g = gate(row % input.len(), (row + 1) % input.len(),
                    [s((i + 2) as u64), s((i + 3) as u64), s((i + 5) as u64), s((i + 7) as u64)]);
                residual += g.evaluate(input);
                terms.push(Term { row, gate: g });
            }
            terms.push(Term { row, gate: gate(0, 0, [-residual, Fr::zero(), Fr::zero(), Fr::zero()]) });
        }
        Circuit { input_len: input.len(), row_count, terms }
    }

    fn brute_wiring(circuit: &Circuit, h: usize, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let wr = gkr::eq_weights(r); let wu = gkr::eq_weights(u); let wv = gkr::eq_weights(v);
        let mut coefficients = [Fr::zero(); 4];
        for copy in 0..1usize << h {
            for term in &circuit.terms {
                let g = &term.gate;
                let weight = wr[copy * circuit.row_count + term.row]
                    * wu[copy * circuit.input_len + g.left] * wv[copy * circuit.input_len + g.right];
                for (out, coefficient) in coefficients.iter_mut().zip([g.c0, g.c1, g.c2, g.c3]) {
                    *out += weight * coefficient;
                }
            }
        }
        coefficients
    }

    #[test]
    fn sparse_coefficients_equal_expanded_sum_for_all_terms_and_copies() {
        for input_len in [1usize, 4, 8] {
            for row_count in [1usize, 2, 16] {
                let input: Vec<_> = (0..input_len).map(|i| s((i + 2) as u64)).collect();
                let circuit = zero_rows(&input, row_count);
                for h in 0..=3 {
                    let shape = validate(&circuit, h).unwrap();
                    let r: Vec<_> = (0..shape.row_bits + h).map(|i| s((i + 2) as u64)).collect();
                    let u: Vec<_> = (0..shape.input_bits + h).map(|i| s((i + 11) as u64)).collect();
                    let v: Vec<_> = (0..shape.input_bits + h).map(|i| s((i + 23) as u64)).collect();
                    assert_eq!(wiring(&circuit, &shape, &r, &u, &v).unwrap(), brute_wiring(&circuit, h, &r, &u, &v));
                }
            }
        }
    }

    #[test]
    fn sparse_toy_proofs_preserve_rows_padding_and_actual_input_mle() {
        for input_len in [1usize, 2, 8] {
            let input: Vec<_> = (0..input_len).map(|i| s((i + 2) as u64)).collect();
            for rows in [1usize, 4, 16] {
                let circuit = zero_rows(&input, rows);
                for h in 0..=3 {
                    let expanded = input.repeat(1 << h);
                    let (proof, claim) = prove(&circuit, &expanded, h, &mut transcript()).unwrap();
                    let bytes = gkr::encode_proof(&proof).unwrap();
                    let restored = decode_proof(&circuit, h, &bytes).unwrap();
                    let actual = verify(&circuit, h, &restored, &mut transcript()).unwrap();
                    assert_eq!(actual, claim);
                    assert_eq!(actual.value, gkr::mle(&expanded, &actual.point).unwrap());
                    assert!(decode_proof(&circuit, (h + 1) % 4, &bytes).is_err());
                    assert!(verify(&circuit, (h + 1) % 4, &proof, &mut transcript()).is_err());
                }
            }
        }
        // Distinct copy inputs all satisfy (x+1)*(y-1)=0; all c_i nonzero.
        let circuit = Circuit { input_len: 2, row_count: 2,
            terms: vec![Term { row: 0, gate: gate(0, 1, [-Fr::one(), -Fr::one(), Fr::one(), Fr::one()]) }] };
        let input: Vec<_> = (0..8).flat_map(|copy| [s(copy + 3), Fr::one()]).collect();
        let (proof, claim) = prove(&circuit, &input, 3, &mut transcript()).unwrap();
        assert_eq!(verify(&circuit, 3, &proof, &mut transcript()).unwrap(), claim);
        assert_eq!(claim.value, gkr::mle(&input, &claim.point).unwrap());
    }

    #[test]
    fn sparse_does_not_merge_opposite_false_rows() {
        let plus = Term { row: 0, gate: gate(0, 0, [Fr::one(), Fr::zero(), Fr::zero(), Fr::zero()]) };
        let minus = Term { row: 1, gate: gate(0, 0, [-Fr::one(), Fr::zero(), Fr::zero(), Fr::zero()]) };
        let wrong = Circuit { input_len: 1, row_count: 2, terms: vec![plus, minus] };
        assert_eq!(prove(&wrong, &[s(9)], 0, &mut transcript()), Err(GkrError::NonzeroOutput));
        let mut same_row = wrong.clone(); same_row.terms[1].row = 0;
        let (proof, claim) = prove(&same_row, &[s(9)], 0, &mut transcript()).unwrap();
        assert_eq!(verify(&same_row, 0, &proof, &mut transcript()).unwrap(), claim);
        assert!(verify(&wrong, 0, &proof, &mut transcript()).is_err());
        let empty = Circuit { input_len: 1, row_count: 4, terms: vec![] };
        let (proof, claim) = prove(&empty, &[s(7)], 0, &mut transcript()).unwrap();
        assert_eq!(verify(&empty, 0, &proof, &mut transcript()).unwrap(), claim);
    }

    #[test]
    fn sparse_shape_codec_and_dimensions_fail_closed() {
        let input = [s(2), s(3)]; let circuit = zero_rows(&input, 4);
        let (proof, _) = prove(&circuit, &input, 0, &mut transcript()).unwrap();
        let mut wrong = proof.clone(); wrong.layers[0].rounds[0].push(Fr::zero());
        assert_eq!(verify(&circuit, 0, &wrong, &mut transcript()), Err(GkrError::SumcheckDegree));
        let mut wrong = proof.clone(); wrong.layers[0].line_coefficients.push(Fr::zero());
        assert_eq!(verify(&circuit, 0, &wrong, &mut transcript()), Err(GkrError::LineDegree));
        let mut wrong = proof.clone(); wrong.layers[0].left_value += Fr::one();
        assert!(verify(&circuit, 0, &wrong, &mut transcript()).is_err());
        let mut bytes = gkr::encode_proof(&proof).unwrap(); bytes.push(0);
        assert!(decode_proof(&circuit, 0, &bytes).is_err());
        bytes.pop(); bytes[..32].fill(255);
        assert!(decode_proof(&circuit, 0, &bytes).is_err());
        let mut invalid = circuit.clone(); invalid.terms[0].row = invalid.row_count;
        assert_eq!(verify(&invalid, 0, &proof, &mut transcript()), Err(GkrError::InvalidWireIndex));
        let mut invalid = circuit.clone(); invalid.terms[0].gate.left = invalid.input_len;
        assert_eq!(verify(&invalid, 0, &proof, &mut transcript()), Err(GkrError::InvalidWireIndex));
        assert_eq!(verify(&circuit, usize::MAX, &proof, &mut transcript()), Err(GkrError::RepetitionLimit));
        let oversized = Circuit { input_len: 1 << 24, row_count: 1, terms: vec![] };
        assert_eq!(verify(&oversized, 1, &proof, &mut transcript()), Err(GkrError::RepeatedSizeLimit));
        let oversized = Circuit { input_len: 1, row_count: 1 << 24, terms: vec![] };
        assert_eq!(verify(&oversized, 1, &proof, &mut transcript()), Err(GkrError::RepeatedSizeLimit));
    }
}

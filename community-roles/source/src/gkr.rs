//! Bounded sparse-wiring GKR, with the final input claim left to the PCS.
//!
//! MLE coordinates consume gate-index bits least-significant first. Layers are
//! supplied input-to-output; proof layers run in the reverse order. The caller
//! must bind its public statement and PCS commitment before calling this module.
//!
//! Delta from the standard GKR description: sum the Boolean output-gate variable
//! out exactly, using eq(r, gate). A layer then has 2*log(input width) quadratic
//! sumcheck rounds, followed by the standard degree-log(width) line merger.
//! Constants and linear terms preserve individual degree <= 2. A false output
//! vector escapes its initial MLE check with probability <= log(output width)/|S|;
//! each layer contributes <= 5*log(input width)/|S| on one path. The original-query
//! global bound is q*max(2, log(output width), max log(input width))/|S|, where S
//! is the transcript's scalar sample set (F_p* here, so |S|=p-1). Complete prefixes
//! and the fixed input commitment are required. This verifier scans every gate
//! to evaluate wiring MLEs; no polylogarithmic full-history verifier claim follows.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::transcript::Transcript;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gate {
    pub left: usize,
    pub right: usize,
    pub c0: Fr,
    pub c1: Fr,
    pub c2: Fr,
    pub c3: Fr,
}

impl Gate {
    pub fn evaluate(&self, input: &[Fr]) -> Fr {
        let a = input[self.left];
        let b = input[self.right];
        self.c0 + self.c1 * a + self.c2 * b + self.c3 * a * b
    }
}

pub type Layer = Vec<Gate>;

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct LayerProof {
    /// Exactly 2*log(input width) messages, each with exactly three coefficients.
    pub rounds: Vec<Vec<Fr>>,
    pub left_value: Fr,
    pub right_value: Fr,
    /// Exactly log(input width)+1 coefficients, including leading zero padding.
    pub line_coefficients: Vec<Fr>,
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct GkrProof {
    pub layers: Vec<LayerProof>,
}

/// Fixed-shape scalar stream, without attacker-supplied collection lengths.
/// Decoding requires the same validated circuit. This is the wire codec; the
/// derived ark serialization is used only by in-process differential tests.
pub fn encode_proof(proof: &GkrProof) -> Result<Vec<u8>, String> {
    let mut encoded = Vec::new();
    for layer in &proof.layers {
        if layer.rounds.iter().any(|round| round.len() != 3) || layer.line_coefficients.is_empty() {
            return Err("invalid GKR proof shape".into());
        }
        for coefficient in layer.rounds.iter().flatten()
            .chain([&layer.left_value, &layer.right_value])
            .chain(&layer.line_coefficients)
        {
            coefficient.serialize_compressed(&mut encoded).map_err(|e| e.to_string())?;
        }
    }
    Ok(encoded)
}

/// Reject the exact byte length before allocating any proof vectors. Scalar
/// decoding checks canonical field representatives; trailing bytes are rejected.
pub fn decode_proof(input_len: usize, layers: &[Layer], bytes: &[u8]) -> Result<GkrProof, String> {
    validate_circuit(input_len, layers).map_err(|e| e.to_string())?;
    let dimensions = layer_dimensions(input_len, layers, 0).map_err(|e| e.to_string())?;
    decode_dimensions(&dimensions, bytes)
}

pub(crate) fn decode_dimensions(dimensions: &[usize], bytes: &[u8]) -> Result<GkrProof, String> {
    let scalar_bytes = Fr::zero().compressed_size();
    let mut total_scalars = 0usize;
    for dimension in dimensions {
        let count = dimension.checked_mul(7).and_then(|n| n.checked_add(3))
            .ok_or("GKR scalar count overflow")?;
        total_scalars = total_scalars.checked_add(count).ok_or("GKR scalar count overflow")?;
    }
    let expected_bytes = total_scalars.checked_mul(scalar_bytes).ok_or("GKR byte count overflow")?;
    if bytes.len() != expected_bytes {
        return Err(format!("GKR proof length: expected {expected_bytes}, received {}", bytes.len()));
    }
    let mut reader = bytes;
    let mut proof_layers = Vec::with_capacity(dimensions.len());
    for &dimension in dimensions.iter().rev() {
        let mut read_scalar = || Fr::deserialize_compressed(&mut reader).map_err(|e| e.to_string());
        let mut rounds = Vec::with_capacity(2 * dimension);
        for _ in 0..2 * dimension {
            rounds.push(vec![read_scalar()?, read_scalar()?, read_scalar()?]);
        }
        let left_value = read_scalar()?;
        let right_value = read_scalar()?;
        let line_coefficients = (0..=dimension).map(|_| read_scalar()).collect::<Result<Vec<_>, _>>()?;
        proof_layers.push(LayerProof { rounds, left_value, right_value, line_coefficients });
    }
    if !reader.is_empty() {
        return Err("GKR proof has trailing bytes".into());
    }
    Ok(GkrProof { layers: proof_layers })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputClaim {
    pub point: Vec<Fr>,
    pub value: Fr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GkrError {
    InvalidInputWidth,
    EmptyCircuit,
    InvalidLayerWidth,
    InvalidWireIndex,
    NonzeroOutput,
    ProofLayerCount,
    SumcheckRoundCount,
    SumcheckDegree,
    LineDegree,
    SumcheckIdentity,
    TerminalExpression,
    LineEndpoints,
    PointDimension,
    RepetitionLimit,
    RepeatedSizeLimit,
}

impl std::fmt::Display for GkrError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "GKR error: {self:?}")
    }
}

impl std::error::Error for GkrError {}

pub(crate) fn log_width(width: usize) -> Result<usize, GkrError> {
    if !width.is_power_of_two() {
        return Err(GkrError::InvalidInputWidth);
    }
    Ok(width.trailing_zeros() as usize)
}

fn validate_circuit(input_len: usize, layers: &[Layer]) -> Result<(), GkrError> {
    log_width(input_len)?;
    if layers.is_empty() {
        return Err(GkrError::EmptyCircuit);
    }
    let mut width = input_len;
    for layer in layers {
        if !layer.len().is_power_of_two() {
            return Err(GkrError::InvalidLayerWidth);
        }
        if layer.iter().any(|g| g.left >= width || g.right >= width) {
            return Err(GkrError::InvalidWireIndex);
        }
        width = layer.len();
    }
    Ok(())
}

const MAX_LOG_COPIES: usize = 3;
const MAX_REPEATED_INPUT_LOG: usize = 24;
const MAX_REPEATED_GATES: usize = 32 * 1024 * 1024;

fn layer_dimensions(input_len: usize, layers: &[Layer], extra_bits: usize) -> Result<Vec<usize>, GkrError> {
    (0..layers.len()).map(|index| {
        let width = if index == 0 { input_len } else { layers[index - 1].len() };
        log_width(width)?.checked_add(extra_bits).ok_or(GkrError::RepeatedSizeLimit)
    }).collect()
}

/// Admission before any expanded allocation. Copy indices occupy high bits.
fn validate_repeated(base_input_len: usize, base_layers: &[Layer], log_copies: usize) -> Result<usize, GkrError> {
    if log_copies > MAX_LOG_COPIES { return Err(GkrError::RepetitionLimit); }
    let total_input_log = log_width(base_input_len)?.checked_add(log_copies)
        .ok_or(GkrError::RepeatedSizeLimit)?;
    if total_input_log > MAX_REPEATED_INPUT_LOG { return Err(GkrError::RepeatedSizeLimit); }
    let copies = 1usize.checked_shl(log_copies as u32).ok_or(GkrError::RepeatedSizeLimit)?;
    let mut total_gates = 0usize;
    for layer in base_layers {
        let expanded = layer.len().checked_mul(copies).ok_or(GkrError::RepeatedSizeLimit)?;
        total_gates = total_gates.checked_add(expanded).ok_or(GkrError::RepeatedSizeLimit)?;
        if total_gates > MAX_REPEATED_GATES { return Err(GkrError::RepeatedSizeLimit); }
    }
    validate_circuit(base_input_len, base_layers)?;
    base_input_len.checked_mul(copies).ok_or(GkrError::RepeatedSizeLimit)
}

fn bind_repeated(base_input_len: usize, base_layers: &[Layer], log_copies: usize, transcript: &mut Transcript) {
    transcript.append_bytes(b"gkr-repeat-profile", b"independent-copies-high-bits-v1");
    append_usize(transcript, b"gkr-log-copies", log_copies);
    bind_circuit(base_input_len, base_layers, transcript);
}

// Producer-only materialization. All widths and total allocation were admitted.
fn expand_layers(base_input_len: usize, base_layers: &[Layer], log_copies: usize) -> Vec<Layer> {
    let copies = 1usize << log_copies;
    let mut previous_width = base_input_len;
    let mut expanded = Vec::with_capacity(base_layers.len());
    for layer in base_layers {
        let mut next = Vec::with_capacity(layer.len() * copies);
        for copy in 0..copies {
            let offset = copy * previous_width;
            next.extend(layer.iter().map(|gate| Gate {
                left: gate.left + offset, right: gate.right + offset,
                c0: gate.c0, c1: gate.c1, c2: gate.c2, c3: gate.c3,
            }));
        }
        expanded.push(next);
        previous_width = layer.len();
    }
    expanded
}

/// Decode against implicit expanded widths; no expanded circuit is allocated.
pub fn decode_repeated_proof(base_input_len: usize, base_layers: &[Layer], log_copies: usize, bytes: &[u8]) -> Result<GkrProof, String> {
    validate_repeated(base_input_len, base_layers, log_copies).map_err(|e| e.to_string())?;
    let dimensions = layer_dimensions(base_input_len, base_layers, log_copies).map_err(|e| e.to_string())?;
    decode_dimensions(&dimensions, bytes)
}

/// Evaluate the circuit, retaining input and every intermediate layer.
pub fn evaluate(input: &[Fr], layers: &[Layer]) -> Result<Vec<Vec<Fr>>, GkrError> {
    validate_circuit(input.len(), layers)?;
    let mut values = Vec::with_capacity(layers.len() + 1);
    values.push(input.to_vec());
    for layer in layers {
        let previous = values.last().expect("input layer exists");
        let next = layer.iter().map(|gate| gate.evaluate(previous)).collect();
        values.push(next);
    }
    Ok(values)
}

/// Evaluate a Boolean-table MLE in LSB-first coordinate order.
pub fn mle(values: &[Fr], point: &[Fr]) -> Result<Fr, GkrError> {
    if log_width(values.len())? != point.len() {
        return Err(GkrError::PointDimension);
    }
    let mut folded = values.to_vec();
    for coordinate in point {
        fold(&mut folded, *coordinate);
    }
    Ok(folded[0])
}

pub(crate) fn eq_weights(point: &[Fr]) -> Vec<Fr> {
    let mut weights = vec![Fr::one()];
    for coordinate in point {
        let old_len = weights.len();
        weights.resize(2 * old_len, Fr::zero());
        for index in 0..old_len {
            let old = weights[index];
            weights[index] = old * (Fr::one() - coordinate);
            weights[index + old_len] = old * coordinate;
        }
    }
    weights
}

pub(crate) fn fold(values: &mut Vec<Fr>, coordinate: Fr) {
    let half = values.len() / 2;
    for index in 0..half {
        let low = values[2 * index];
        let high = values[2 * index + 1];
        values[index] = low + coordinate * (high - low);
    }
    values.truncate(half);
}

pub(crate) fn eval_polynomial(coefficients: &[Fr], point: Fr) -> Fr {
    coefficients.iter().rev().fold(Fr::zero(), |value, c| value * point + c)
}

pub(crate) fn append_usize(transcript: &mut Transcript, label: &[u8], value: usize) {
    // The prototype runs on platforms whose usize fits in u64.
    transcript.append_bytes(label, &(value as u64).to_le_bytes());
}

pub(crate) fn append_polynomial(transcript: &mut Transcript, label: &[u8], coefficients: &[Fr]) {
    append_usize(transcript, label, coefficients.len());
    for coefficient in coefficients {
        transcript.append_scalar(b"gkr-polynomial-coefficient", coefficient);
    }
}

fn bind_circuit(input_len: usize, layers: &[Layer], transcript: &mut Transcript) {
    transcript.append_bytes(b"gkr-profile", b"sparse-bilinear-lsb-zero-output-v1");
    append_usize(transcript, b"gkr-input-width", input_len);
    append_usize(transcript, b"gkr-layer-count", layers.len());
    for layer in layers {
        append_usize(transcript, b"gkr-layer-width", layer.len());
        for gate in layer {
            append_usize(transcript, b"gkr-left-wire", gate.left);
            append_usize(transcript, b"gkr-right-wire", gate.right);
            transcript.append_scalar(b"gkr-c0", &gate.c0);
            transcript.append_scalar(b"gkr-c1", &gate.c1);
            transcript.append_scalar(b"gkr-c2", &gate.c2);
            transcript.append_scalar(b"gkr-c3", &gate.c3);
        }
    }
}

pub(crate) fn output_point(width: usize, transcript: &mut Transcript) -> Vec<Fr> {
    (0..width.trailing_zeros())
        .map(|_| transcript.challenge_scalar(b"gkr-output-coordinate"))
        .collect()
}

/// Sumcheck message for sum_i A(i)*X(i)+B(i), binding the next low index bit.
pub(crate) fn quadratic_message(a: &[Fr], b: &[Fr], x: &[Fr]) -> Vec<Fr> {
    let mut coefficients = vec![Fr::zero(); 3];
    for index in 0..a.len() / 2 {
        let low = 2 * index;
        let da = a[low + 1] - a[low];
        let dx = x[low + 1] - x[low];
        let db = b[low + 1] - b[low];
        coefficients[0] += a[low] * x[low] + b[low];
        coefficients[1] += a[low] * dx + da * x[low] + db;
        coefficients[2] += da * dx;
    }
    coefficients
}

pub(crate) fn prove_phase(
    mut a: Vec<Fr>,
    mut b: Vec<Fr>,
    input: &[Fr],
    claim: &mut Fr,
    rounds: &mut Vec<Vec<Fr>>,
    transcript: &mut Transcript,
) -> Result<(Vec<Fr>, Fr), GkrError> {
    let mut x = input.to_vec();
    let mut point = Vec::new();
    while x.len() > 1 {
        let polynomial = quadratic_message(&a, &b, &x);
        if polynomial[0] + eval_polynomial(&polynomial, Fr::one()) != *claim {
            return Err(GkrError::SumcheckIdentity);
        }
        append_polynomial(transcript, b"gkr-sumcheck-polynomial", &polynomial);
        let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        *claim = eval_polynomial(&polynomial, challenge);
        fold(&mut a, challenge);
        fold(&mut b, challenge);
        fold(&mut x, challenge);
        rounds.push(polynomial);
        point.push(challenge);
    }
    Ok((point, x[0]))
}

/// Coefficients of MLE(input, u+t*(v-u)), by polynomial folding.
/// At stage j, each remaining entry has degree <=j; total arithmetic is O(N).
pub(crate) fn line_polynomial(input: &[Fr], u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let mut table = input.to_vec();
    let mut entries = input.len();
    let mut stride = 1usize;
    for (coordinate, (u_i, v_i)) in u.iter().zip(v).enumerate() {
        let next_entries = entries / 2;
        let next_stride = coordinate + 2;
        let mut next = vec![Fr::zero(); next_entries * next_stride];
        for pair in 0..next_entries {
            let left = (2 * pair) * stride;
            let right = left + stride;
            let output = pair * next_stride;
            for degree in 0..=coordinate {
                let difference = table[right + degree] - table[left + degree];
                next[output + degree] += table[left + degree] + *u_i * difference;
                next[output + degree + 1] += (*v_i - u_i) * difference;
            }
        }
        table = next;
        entries = next_entries;
        stride = next_stride;
    }
    let last = entries.checked_sub(1).expect("validated nonempty power-of-two input");
    if last == 0 { table } else { table.split_off(last * stride) }
}

pub(crate) fn line_point(u: &[Fr], v: &[Fr], challenge: Fr) -> Vec<Fr> {
    u.iter().zip(v).map(|(a, b)| *a + challenge * (*b - a)).collect()
}

fn wiring_coefficients(layer: &Layer, weights: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let left_weights = eq_weights(u);
    let right_weights = eq_weights(v);
    let mut coefficients = [Fr::zero(); 4];
    for (gate, weight) in layer.iter().zip(weights) {
        let contribution = *weight * left_weights[gate.left] * right_weights[gate.right];
        coefficients[0] += contribution * gate.c0;
        coefficients[1] += contribution * gate.c1;
        coefficients[2] += contribution * gate.c2;
        coefficients[3] += contribution * gate.c3;
    }
    coefficients
}

/// Produce a proof that every output residual is zero.
/// Caller binds the instance and input commitment into `transcript` first.
pub fn prove(
    input: &[Fr],
    layers: &[Layer],
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), GkrError> {
    prove_with_binding(input, layers, transcript, |transcript| bind_circuit(input.len(), layers, transcript))
}

/// Prove independent copies of one base circuit. The bounded producer may
/// materialize gates; the transcript binds only the repeat descriptor and base.
pub fn prove_repeated(
    input: &[Fr], base_input_len: usize, base_layers: &[Layer], log_copies: usize,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim), GkrError> {
    let expected_input = validate_repeated(base_input_len, base_layers, log_copies)?;
    if input.len() != expected_input { return Err(GkrError::InvalidInputWidth); }
    let expanded = expand_layers(base_input_len, base_layers, log_copies);
    prove_with_binding(input, &expanded, transcript, |transcript| {
        bind_repeated(base_input_len, base_layers, log_copies, transcript)
    })
}

pub(crate) fn prove_with_binding(
    input: &[Fr], layers: &[Layer], transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript),
) -> Result<(GkrProof, InputClaim), GkrError> {
    let values = evaluate(input, layers)?;
    if values.last().expect("nonempty circuit").iter().any(|v| !v.is_zero()) {
        return Err(GkrError::NonzeroOutput);
    }
    bind(transcript);
    let mut point = output_point(layers.last().expect("validated circuit").len(), transcript);
    let mut claim = Fr::zero();
    let mut proof = GkrProof { layers: Vec::with_capacity(layers.len()) };

    for layer_index in (0..layers.len()).rev() {
        append_usize(transcript, b"gkr-layer-index", layer_index);
        let layer = &layers[layer_index];
        let previous = &values[layer_index];
        let weights = eq_weights(&point);
        let mut a = vec![Fr::zero(); previous.len()];
        let mut b = vec![Fr::zero(); previous.len()];
        for (gate, weight) in layer.iter().zip(&weights) {
            a[gate.left] += *weight * (gate.c1 + gate.c3 * previous[gate.right]);
            b[gate.left] += *weight * (gate.c0 + gate.c2 * previous[gate.right]);
        }
        let mut rounds = Vec::new();
        let (u, left_value) = prove_phase(a, b, previous, &mut claim, &mut rounds, transcript)?;

        let left_weights = eq_weights(&u);
        let mut c = vec![Fr::zero(); previous.len()];
        let mut d = vec![Fr::zero(); previous.len()];
        for (gate, weight) in layer.iter().zip(&weights) {
            let weighted_left = *weight * left_weights[gate.left];
            c[gate.right] += weighted_left * (gate.c2 + gate.c3 * left_value);
            d[gate.right] += weighted_left * (gate.c0 + gate.c1 * left_value);
        }
        let (v, right_value) = prove_phase(c, d, previous, &mut claim, &mut rounds, transcript)?;
        let coefficients = wiring_coefficients(layer, &weights, &u, &v);
        if coefficients[0] + coefficients[1] * left_value + coefficients[2] * right_value
            + coefficients[3] * left_value * right_value != claim
        {
            return Err(GkrError::TerminalExpression);
        }
        let line_coefficients = line_polynomial(previous, &u, &v);
        transcript.append_scalar(b"gkr-left-value", &left_value);
        transcript.append_scalar(b"gkr-right-value", &right_value);
        append_polynomial(transcript, b"gkr-line-polynomial", &line_coefficients);
        let merge_challenge = transcript.challenge_scalar(b"gkr-line-challenge");
        point = line_point(&u, &v, merge_challenge);
        claim = eval_polynomial(&line_coefficients, merge_challenge);
        proof.layers.push(LayerProof { rounds, left_value, right_value, line_coefficients });
    }
    Ok((proof, InputClaim { point, value: claim }))
}

/// Verify all GKR reductions and return the claim that MUST be checked by the PCS.
/// This is not standalone acceptance of the committed-input computation.
pub fn verify(
    input_len: usize,
    layers: &[Layer],
    proof: &GkrProof,
    transcript: &mut Transcript,
) -> Result<InputClaim, GkrError> {
    validate_circuit(input_len, layers)?;
    let dimensions = layer_dimensions(input_len, layers, 0)?;
    verify_with_wiring(&dimensions, layers.last().expect("validated circuit").len(), proof, transcript,
        |transcript| bind_circuit(input_len, layers, transcript),
        |index, point, u, v| Ok(wiring_coefficients(&layers[index], &eq_weights(point), u, v)))
}

fn repeated_wiring_coefficients(
    base_layer: &Layer, base_input_len: usize, log_copies: usize,
    point: &[Fr], u: &[Fr], v: &[Fr],
) -> Result<[Fr; 4], GkrError> {
    let output_bits = log_width(base_layer.len())?;
    let input_bits = log_width(base_input_len)?;
    if point.len() != output_bits + log_copies || u.len() != input_bits + log_copies
        || v.len() != input_bits + log_copies { return Err(GkrError::PointDimension); }
    let (r_low, r_high) = point.split_at(output_bits);
    let (u_low, u_high) = u.split_at(input_bits);
    let (v_low, v_high) = v.split_at(input_bits);
    let mut coefficients = wiring_coefficients(base_layer, &eq_weights(r_low), u_low, v_low);
    let factor = r_high.iter().zip(u_high).zip(v_high).fold(Fr::one(), |acc, ((r, u), v)| {
        acc * ((Fr::one() - r) * (Fr::one() - u) * (Fr::one() - v) + *r * u * v)
    });
    for coefficient in &mut coefficients { *coefficient *= factor; }
    Ok(coefficients)
}

/// Verify repeated wiring using base-layer tables and a product over copy bits.
/// No expanded gates or high-bit equality tables are constructed here.
pub fn verify_repeated(
    base_input_len: usize, base_layers: &[Layer], log_copies: usize,
    proof: &GkrProof, transcript: &mut Transcript,
) -> Result<InputClaim, GkrError> {
    validate_repeated(base_input_len, base_layers, log_copies)?;
    let dimensions = layer_dimensions(base_input_len, base_layers, log_copies)?;
    let output_width = base_layers.last().expect("validated circuit").len()
        .checked_mul(1usize << log_copies).ok_or(GkrError::RepeatedSizeLimit)?;
    verify_with_wiring(&dimensions, output_width, proof, transcript,
        |transcript| bind_repeated(base_input_len, base_layers, log_copies, transcript),
        |index, point, u, v| {
            let base_width = if index == 0 { base_input_len } else { base_layers[index - 1].len() };
            repeated_wiring_coefficients(&base_layers[index], base_width, log_copies, point, u, v)
        })
}

pub(crate) fn verify_with_wiring(
    dimensions: &[usize], output_width: usize, proof: &GkrProof, transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript),
    wiring: impl Fn(usize, &[Fr], &[Fr], &[Fr]) -> Result<[Fr; 4], GkrError>,
) -> Result<InputClaim, GkrError> {
    if proof.layers.len() != dimensions.len() {
        return Err(GkrError::ProofLayerCount);
    }
    // Validate every message length before hashing or interpreting proof scalars.
    for (&dimension, layer_proof) in dimensions.iter().rev().zip(&proof.layers) {
        if layer_proof.rounds.len() != 2 * dimension {
            return Err(GkrError::SumcheckRoundCount);
        }
        if layer_proof.rounds.iter().any(|round| round.len() != 3) {
            return Err(GkrError::SumcheckDegree);
        }
        if layer_proof.line_coefficients.len() != dimension + 1 {
            return Err(GkrError::LineDegree);
        }
    }
    bind(transcript);
    let mut point = output_point(output_width, transcript);
    let mut claim = Fr::zero();
    for (layer_index, layer_proof) in (0..dimensions.len()).rev().zip(&proof.layers) {
        append_usize(transcript, b"gkr-layer-index", layer_index);
        let dimension = layer_proof.rounds.len() / 2;
        let mut challenges = Vec::with_capacity(2 * dimension);
        for polynomial in &layer_proof.rounds {
            if polynomial[0] + eval_polynomial(polynomial, Fr::one()) != claim {
                return Err(GkrError::SumcheckIdentity);
            }
            append_polynomial(transcript, b"gkr-sumcheck-polynomial", polynomial);
            let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
            claim = eval_polynomial(polynomial, challenge);
            challenges.push(challenge);
        }
        let (u, v) = challenges.split_at(dimension);
        let coefficients = wiring(layer_index, &point, u, v)?;
        let a = layer_proof.left_value;
        let b = layer_proof.right_value;
        if coefficients[0] + coefficients[1] * a + coefficients[2] * b
            + coefficients[3] * a * b != claim
        {
            return Err(GkrError::TerminalExpression);
        }
        let line = &layer_proof.line_coefficients;
        if line[0] != a || eval_polynomial(line, Fr::one()) != b {
            return Err(GkrError::LineEndpoints);
        }
        transcript.append_scalar(b"gkr-left-value", &a);
        transcript.append_scalar(b"gkr-right-value", &b);
        append_polynomial(transcript, b"gkr-line-polynomial", line);
        let merge_challenge = transcript.challenge_scalar(b"gkr-line-challenge");
        point = line_point(u, v, merge_challenge);
        claim = eval_polynomial(line, merge_challenge);
    }
    Ok(InputClaim { point, value: claim })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar(value: u64) -> Fr { Fr::from(value) }
    fn gate(left: usize, right: usize, c0: Fr, c1: Fr, c2: Fr, c3: Fr) -> Gate {
        Gate { left, right, c0, c1, c2, c3 }
    }
    fn transcript() -> Transcript { Transcript::new(b"gkr-core-test-v1") }

    fn zero_circuit(input: &[Fr], widths: &[usize]) -> Vec<Layer> {
        let mut layers = Vec::new();
        let mut values = input.to_vec();
        for (index, width) in widths.iter().enumerate() {
            let layer: Layer = (0..*width).map(|j| {
                let left = (3 * j + index) % values.len();
                let right = (7 * j + index + 1) % values.len();
                let mut g = gate(left, right, scalar((j + 3) as u64),
                    scalar((index + 2) as u64), scalar((j + 1) as u64), scalar(5));
                if index + 1 == widths.len() {
                    g.c0 -= g.evaluate(&values);
                }
                g
            }).collect();
            values = layer.iter().map(|g| g.evaluate(&values)).collect();
            layers.push(layer);
        }
        layers
    }

    #[test]
    fn tiny_circuits_differential_and_serialization() {
        for input_width in [1, 2, 4, 8, 16] {
            let input: Vec<Fr> = (0..input_width).map(|i| scalar((i * i + 2) as u64)).collect();
            for widths in [vec![1], vec![2, 1], vec![8, 4, 2], vec![1, 8, 1]] {
                let circuit = zero_circuit(&input, &widths);
                let values = evaluate(&input, &circuit).unwrap();
                assert!(values.last().unwrap().iter().all(Zero::is_zero));
                let (proof, expected) = prove(&input, &circuit, &mut transcript()).unwrap();
                let mut bytes = Vec::new();
                proof.serialize_compressed(&mut bytes).unwrap();
                let restored = GkrProof::deserialize_compressed(bytes.as_slice()).unwrap();
                assert_eq!(proof, restored);
                let wire_bytes = encode_proof(&proof).unwrap();
                assert_eq!(decode_proof(input.len(), &circuit, &wire_bytes).unwrap(), proof);
                let actual = verify(input.len(), &circuit, &restored, &mut transcript()).unwrap();
                assert_eq!(expected, actual);
                assert_eq!(actual.value, mle(&input, &actual.point).unwrap());
            }
        }
    }

    #[test]
    fn line_polynomial_matches_independent_mle() {
        let input: Vec<Fr> = (0..16).map(|i| scalar(i * i + 7)).collect();
        let u = vec![scalar(2), scalar(3), scalar(5), scalar(7)];
        let v = vec![scalar(11), scalar(13), scalar(17), scalar(19)];
        let h = line_polynomial(&input, &u, &v);
        for t in [0, 1, 2, 7, 21] {
            let point = line_point(&u, &v, scalar(t));
            // Direct equality-basis formula is independent of line folding.
            let expected: Fr = eq_weights(&point).iter().zip(&input).map(|(w, x)| *w * x).sum();
            assert_eq!(eval_polynomial(&h, scalar(t)), expected);
        }
        assert_eq!(line_polynomial(&input, &u, &u)[0], mle(&input, &u).unwrap());
    }

    #[test]
    fn degree_round_endpoint_and_sumcheck_fail_closed() {
        let input = vec![scalar(2), scalar(5), scalar(7), scalar(11)];
        let circuit = zero_circuit(&input, &[4, 2]);
        let (proof, _) = prove(&input, &circuit, &mut transcript()).unwrap();
        let mut mutant = proof.clone();
        mutant.layers[0].rounds[0].push(Fr::zero());
        assert_eq!(verify(4, &circuit, &mutant, &mut transcript()), Err(GkrError::SumcheckDegree));
        let mut mutant = proof.clone();
        mutant.layers[0].rounds.pop();
        assert_eq!(verify(4, &circuit, &mutant, &mut transcript()), Err(GkrError::SumcheckRoundCount));
        let mut mutant = proof.clone();
        mutant.layers[0].line_coefficients.push(Fr::zero());
        assert_eq!(verify(4, &circuit, &mutant, &mut transcript()), Err(GkrError::LineDegree));
        let mut mutant = proof.clone();
        mutant.layers[0].line_coefficients[0] += Fr::one();
        assert_eq!(verify(4, &circuit, &mutant, &mut transcript()), Err(GkrError::LineEndpoints));
        let mut mutant = proof;
        mutant.layers[0].rounds[0][0] += Fr::one();
        assert_eq!(verify(4, &circuit, &mutant, &mut transcript()), Err(GkrError::SumcheckIdentity));
    }

    #[test]
    fn wrong_terminal_input_requires_pcs_rejection() {
        let input = vec![-Fr::one(), Fr::one()];
        let circuit = vec![vec![gate(0, 1, Fr::zero(), Fr::one(), Fr::one(), Fr::zero())]];
        let (proof, _) = prove(&input, &circuit, &mut transcript()).unwrap();
        let claim = verify(2, &circuit, &proof, &mut transcript()).unwrap();
        assert_eq!(claim.value, mle(&input, &claim.point).unwrap());
        // Both inputs satisfy the circuit. GKR alone cannot bind which was committed.
        let other_input = vec![Fr::zero(); 2];
        assert_ne!(claim.value, mle(&other_input, &claim.point).unwrap());
    }

    #[test]
    fn incorrect_terminal_expression_rejected_without_probabilistic_cancellation() {
        let input = vec![scalar(2)];
        let circuit = vec![vec![gate(0, 0, -scalar(2), Fr::one(), Fr::zero(), Fr::zero())]];
        let (mut proof, _) = prove(&input, &circuit, &mut transcript()).unwrap();
        proof.layers[0].left_value += Fr::one();
        assert_eq!(verify(1, &circuit, &proof, &mut transcript()), Err(GkrError::TerminalExpression));
    }

    #[test]
    fn nonzero_output_and_invalid_wires_rejected() {
        let input = vec![scalar(2), scalar(5)];
        let circuit = vec![vec![gate(0, 1, Fr::zero(), Fr::one(), Fr::one(), Fr::zero())]];
        assert_eq!(prove(&input, &circuit, &mut transcript()), Err(GkrError::NonzeroOutput));
        let invalid = vec![vec![gate(2, 0, Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero())]];
        assert_eq!(evaluate(&input, &invalid), Err(GkrError::InvalidWireIndex));
        assert_eq!(evaluate(&[], &circuit), Err(GkrError::InvalidInputWidth));
    }

    #[test]
    fn wire_codec_rejects_size_and_noncanonical_scalar_before_verification() {
        let input = vec![scalar(2), scalar(5), scalar(7), scalar(11)];
        let circuit = zero_circuit(&input, &[4, 2]);
        let (proof, _) = prove(&input, &circuit, &mut transcript()).unwrap();
        let bytes = encode_proof(&proof).unwrap();
        assert!(decode_proof(4, &circuit, &bytes[..bytes.len() - 1]).is_err());
        let mut extended = bytes.clone();
        extended.push(0);
        assert!(decode_proof(4, &circuit, &extended).is_err());
        let mut noncanonical = bytes;
        noncanonical[..32].fill(255);
        assert!(decode_proof(4, &circuit, &noncanonical).is_err());
    }

    #[test]
    fn repeated_all_wiring_coefficients_match_expanded_circuits() {
        for base_input_width in [1usize, 2, 8] {
            for base_output_width in [1usize, 4, 16] {
                let base: Layer = (0..base_output_width).map(|index| {
                    gate(index % base_input_width, (3 * index + 1) % base_input_width,
                        scalar((index + 2) as u64), scalar((2 * index + 3) as u64),
                        scalar((3 * index + 5) as u64), scalar((5 * index + 7) as u64))
                }).collect();
                for h in 0..=3 {
                    let expanded = expand_layers(base_input_width, &[base.clone()], h);
                    let r: Vec<_> = (0..log_width(base_output_width).unwrap() + h)
                        .map(|i| scalar((2 + i) as u64)).collect();
                    let u: Vec<_> = (0..log_width(base_input_width).unwrap() + h)
                        .map(|i| scalar((11 + i) as u64)).collect();
                    let v: Vec<_> = (0..log_width(base_input_width).unwrap() + h)
                        .map(|i| scalar((23 + i) as u64)).collect();
                    let brute = wiring_coefficients(&expanded[0], &eq_weights(&r), &u, &v);
                    let compact = repeated_wiring_coefficients(&base, base_input_width, h, &r, &u, &v).unwrap();
                    assert_eq!(compact, brute, "widths {base_input_width}->{base_output_width}, h={h}");
                }
            }
        }
        // Deterministic single-fault mutant: removing the copy factor fails all
        // four coefficients, with no random transcript or cancellation needed.
        let base = vec![gate(0, 0, scalar(2), scalar(3), scalar(5), scalar(7))];
        let actual = repeated_wiring_coefficients(&base, 1, 1, &[scalar(2)], &[scalar(3)], &[scalar(5)]).unwrap();
        let omitted_factor = wiring_coefficients(&base, &[Fr::one()], &[], &[]);
        for index in 0..4 { assert_ne!(actual[index], omitted_factor[index]); }
        assert_eq!(actual, omitted_factor.map(|coefficient| coefficient * scalar(22)));
    }

    #[test]
    fn repeated_proofs_match_expanded_verifier_and_actual_input_mle() {
        for base_input_width in [1usize, 4] {
            let base_input: Vec<_> = (0..base_input_width).map(|i| scalar((i + 2) as u64)).collect();
            for widths in [vec![1], vec![1, 8, 2], vec![8, 1, 4]] {
                let base = zero_circuit(&base_input, &widths);
                for h in 0..=3 {
                    let input = base_input.repeat(1 << h);
                    let expanded = expand_layers(base_input_width, &base, h);
                    let (proof, expected) = prove_repeated(&input, base_input_width, &base, h, &mut transcript()).unwrap();
                    let wire = encode_proof(&proof).unwrap();
                    let decoded = decode_repeated_proof(base_input_width, &base, h, &wire).unwrap();
                    assert_eq!(decoded, proof);
                    let compact = verify_repeated(base_input_width, &base, h, &decoded, &mut transcript()).unwrap();
                    let dimensions = layer_dimensions(input.len(), &expanded, 0).unwrap();
                    let brute = verify_with_wiring(&dimensions, expanded.last().unwrap().len(), &proof, &mut transcript(),
                        |t| bind_repeated(base_input_width, &base, h, t),
                        |index, r, u, v| Ok(wiring_coefficients(&expanded[index], &eq_weights(r), u, v))).unwrap();
                    assert_eq!(compact, brute);
                    assert_eq!(compact, expected);
                    assert_eq!(compact.value, mle(&input, &compact.point).unwrap());
                    assert!(verify_repeated(base_input_width, &base, (h + 1) % 4, &proof, &mut transcript()).is_err());
                    assert!(decode_repeated_proof(base_input_width, &base, (h + 1) % 4, &wire).is_err());
                }
            }
        }
    }

    #[test]
    fn repeated_distinct_copy_inputs_and_omitted_factor_verifier_rejected() {
        // (x+1)*(y-1), all four coefficients nonzero; x differs by copy.
        let base = vec![vec![gate(0, 1, -Fr::one(), -Fr::one(), Fr::one(), Fr::one())]];
        for h in 0..=3 {
            let input: Vec<_> = (0..1usize << h).flat_map(|copy| [scalar((copy + 2) as u64), Fr::one()]).collect();
            let (proof, expected) = prove_repeated(&input, 2, &base, h, &mut transcript()).unwrap();
            let actual = verify_repeated(2, &base, h, &proof, &mut transcript()).unwrap();
            assert_eq!(actual, expected);
            assert_eq!(actual.value, mle(&input, &actual.point).unwrap());
            if h > 0 {
                let dimensions = layer_dimensions(2, &base, h).unwrap();
                let mutant = verify_with_wiring(&dimensions, 1 << h, &proof, &mut transcript(),
                    |t| bind_repeated(2, &base, h, t),
                    |index, _r, u, v| Ok(wiring_coefficients(&base[index], &[Fr::one()], &u[..1], &v[..1])));
                assert_eq!(mutant, Err(GkrError::TerminalExpression));
            }
        }
    }

    #[test]
    fn repeated_descriptor_and_admission_fail_closed() {
        let input = vec![scalar(2), scalar(3), scalar(5), scalar(7)];
        let base = zero_circuit(&input, &[2]);
        let mut bindings = Vec::new();
        let mut lengths = Vec::new();
        for h in 0..=3 {
            let mut t = transcript(); bind_repeated(4, &base, h, &mut t);
            lengths.push(t.bytes_absorbed()); bindings.push(t.challenge_scalar(b"after-binding"));
        }
        assert!(lengths.iter().all(|size| *size == lengths[0]), "base binding must not expand with copies");
        for i in 0..4 { for j in 0..i { assert_ne!(bindings[i], bindings[j]); } }
        let (legacy, _) = prove(&input, &base, &mut transcript()).unwrap();
        assert!(verify_repeated(4, &base, 0, &legacy, &mut transcript()).is_err());
        assert_eq!(prove_repeated(&input, 4, &base, 1, &mut transcript()), Err(GkrError::InvalidInputWidth));
        assert_eq!(validate_repeated(4, &base, usize::MAX), Err(GkrError::RepetitionLimit));
        assert_eq!(validate_repeated(1usize << 24, &base, 1), Err(GkrError::RepeatedSizeLimit));
        assert!(decode_repeated_proof(4, &base, 1, &[]).is_err());
        let (proof, _) = prove_repeated(&input.repeat(2), 4, &base, 1, &mut transcript()).unwrap();
        let mut bytes = encode_proof(&proof).unwrap(); bytes.push(0);
        assert!(decode_repeated_proof(4, &base, 1, &bytes).is_err());
    }
}

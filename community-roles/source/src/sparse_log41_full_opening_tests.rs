//! Sparse synthetic PCS kernel diagnostic, independent of the H21 relation.
use crate::{pcs, transcript::Transcript};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::{
    ArkDoryProof, ArkFr, ArkG1, ArkGT, ArkworksPolynomial, BN254, G1Routines, G2Routines,
};
use dory_pcs::error::DoryError;
use dory_pcs::primitives::{arithmetic::{DoryRoutines, Group, PairingCurve},
    poly::MultilinearLagrange, transcript::Transcript as DoryTranscript, DorySerialize};
use dory_pcs::{Polynomial, ProverSetup, Transparent};
use std::io::{self, Write};
use std::cell::Cell;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

const LOG_N: usize = 41;
const NU: usize = 20;
const SIGMA: usize = 21;
const ROWS: usize = 1 << NU;
const WIDTH: usize = 1 << SIGMA;
const ROW_BYTES: usize = WIDTH / 8;
const DOMAIN: &[u8] = b"candidate84-sparse-log41-full-opening-v1";
const VK: &[u8] = include_bytes!("../fixtures/verifier-keys-v1/log41.vk");

fn phase(text: &str) {
    let millis = SystemTime::now().duration_since(UNIX_EPOCH).expect("clock").as_millis();
    println!("CANDIDATE84_PHASE unix_ms={millis} {text}");
    io::stdout().flush().expect("phase flush");
}

fn phase85(text: &str) {
    let millis = SystemTime::now().duration_since(UNIX_EPOCH).expect("clock").as_millis();
    println!("CANDIDATE85_PHASE unix_ms={millis} {text}");
    io::stdout().flush().expect("phase flush");
}

#[derive(Clone)]
struct SparseRows {
    log_n: usize,
    // Canonical strictly increasing row indices, full-width LSB-first bytes.
    // Every row absent from this list is the all-zero row at that index.
    rows: Vec<(usize, Vec<u8>)>,
}

impl SparseRows {
    fn new(log_n: usize, rows: Vec<(usize, Vec<u8>)>) -> Result<Self, String> {
        if !(3..=LOG_N).contains(&log_n) { return Err("unsupported sparse geometry".into()); }
        let nu = log_n / 2;
        let width = 1usize << log_n.div_ceil(2);
        if rows.is_empty() { return Err("empty explicit sparse roster".into()); }
        let mut previous = None;
        for (index, bytes) in &rows {
            if *index >= 1usize << nu || previous.is_some_and(|p| p >= *index) {
                return Err("row position out of range, duplicate, or unordered".into());
            }
            if bytes.len() != width / 8 || bytes.iter().all(|b| *b == 0) {
                return Err("noncanonical explicit row width or zero row".into());
            }
            previous = Some(*index);
        }
        Ok(Self { log_n, rows })
    }

    fn for_each_bit(&self, mut visit: impl FnMut(usize, usize)) {
        for (row, bytes) in &self.rows {
            for (byte_index, byte) in bytes.iter().copied().enumerate() {
                let mut pending = byte;
                while pending != 0 {
                    let bit = pending.trailing_zeros() as usize;
                    visit(*row, 8 * byte_index + bit);
                    pending &= pending - 1;
                }
            }
        }
    }

    // Independent evaluation oracle: a product over the 41 Boolean coordinates
    // for each set bit. It does not call the vendor basis or vector product.
    fn direct_value(&self, point: &[Fr]) -> Fr {
        assert_eq!(point.len(), self.log_n);
        let sigma = self.log_n.div_ceil(2);
        let mut value = Fr::zero();
        self.for_each_bit(|row, col| {
            let index = (row << sigma) | col;
            value += point.iter().enumerate().fold(Fr::one(), |term, (bit, r)|
                term * if (index >> bit) & 1 == 1 { *r } else { Fr::one() - r });
        });
        value
    }

    fn indexed_commitments(&self, setup: &pcs::Setup) -> Vec<ArkG1> {
        assert_eq!(setup.log_n, self.log_n);
        self.indexed_commitments_with_g1(&setup.prover.g1_vec)
    }

    fn indexed_commitments_with_g1(&self, g1: &[ArkG1]) -> Vec<ArkG1> {
        assert_eq!(g1.len(), 1usize << self.log_n.div_ceil(2));
        let mut rows = vec![ArkG1::identity(); 1usize << (self.log_n / 2)];
        self.for_each_bit(|row, col| { rows[row] = rows[row] + g1[col]; });
        rows
    }

    // A bounded reference for the full indexed tier-two kernel. It still
    // commits every set bit using the coordinates of its own row and column.
    fn direct_commitment(&self, setup: &pcs::Setup) -> ArkGT {
        assert_eq!(setup.log_n, self.log_n);
        self.rows.iter().fold(ArkGT::identity(), |sum, (row, bytes)| {
            let mut row_commitment = ArkG1::identity();
            for (byte_index, byte) in bytes.iter().copied().enumerate() {
                for bit in 0..8 {
                    if (byte >> bit) & 1 == 1 {
                        row_commitment = row_commitment + setup.prover.g1_vec[8 * byte_index + bit];
                    }
                }
            }
            sum + BN254::pair(&row_commitment, &setup.prover.g2_vec[*row])
        })
    }
}

// Cheap producer-to-PCS boundary check: uses the real owner-pair row, a
// deterministically regenerated G1 prefix, and an independent direct sum.
fn direct_g1_row(bytes: &[u8], g1: &[ArkG1]) -> ArkG1 {
    let mut sum = ArkG1::identity();
    for (byte_index, byte) in bytes.iter().copied().enumerate() {
        for bit in 0..8 {
            if (byte >> bit) & 1 == 1 { sum = sum + g1[byte_index * 8 + bit]; }
        }
    }
    sum
}

pub(crate) fn real_row_boundary_preproof(row_index: usize, bytes: &[u8]) {
    assert_eq!((row_index, bytes.len()), (420_863, ROW_BYTES));
    let set_bits: usize = bytes.iter().map(|byte| byte.count_ones() as usize).sum();
    let nonzero_windows: usize = bytes.iter().map(|byte| {
        usize::from(byte & 0x0f != 0) + usize::from(byte >> 4 != 0)
    }).sum();
    assert_eq!(set_bits, 741_308);
    assert_eq!(nonzero_windows, 346_328);
    let source = SparseRows::new(LOG_N, vec![(row_index, bytes.to_vec())]).unwrap();
    let point: Vec<_> = (0..LOG_N).map(|i| Fr::from(i as u64 + 2)).collect();
    let point_ark: Vec<_> = point.iter().copied().map(ArkFr).collect();
    let value = source.direct_value(&point);
    assert_eq!(source.evaluate(&point_ark).0, value);

    let (g1, _) = pcs::g1_primary_prefix_for_width_test(LOG_N, WIDTH).unwrap();
    let rows = source.indexed_commitments_with_g1(&g1);
    let direct = direct_g1_row(bytes, &g1);
    assert_eq!(rows[row_index], direct);
    assert_eq!(rows.iter().filter(|row| **row != ArkG1::identity()).count(), 1);
    let mut flipped_bytes = bytes.to_vec();
    flipped_bytes[ROW_BYTES - 1] ^= 0x80;
    let flipped_source = SparseRows::new(LOG_N, vec![(row_index, flipped_bytes.clone())]).unwrap();
    let flipped_rows = flipped_source.indexed_commitments_with_g1(&g1);
    let flipped_direct = direct_g1_row(&flipped_bytes, &g1);
    assert_eq!(flipped_rows[row_index], flipped_direct);
    let last_bit_delta = g1[WIDTH - 1];
    let expected_flipped = if bytes[ROW_BYTES - 1] & 0x80 != 0 {
        direct - last_bit_delta
    } else {
        direct + last_bit_delta
    };
    assert_eq!(flipped_direct, expected_flipped);
    let flipped_value = flipped_source.direct_value(&point);
    assert_ne!(flipped_value, value);
    assert_eq!(flipped_source.evaluate(&point_ark).0, flipped_value);
    println!("CANDIDATE85_REAL_ROW_BOUNDARY_PASS row={row_index} log_n=41 nu=20 sigma=21 packed_bytes={} set_bits={set_bits} nonzero_windows={nonzero_windows} nonidentity_rows=1 implicit_zero_rows=1048575 direct_g1_parity=true full_h21_witness=false",
        bytes.len());
    io::stdout().flush().unwrap();
}

// Full log41 PCS opening over exactly one real owner-pair row; every other
// row is represented as an implicit zero by SparseRows.
pub(crate) fn real_row_full_opening(row_index: usize, bytes: Vec<u8>) {
    let start = Instant::now();
    assert_eq!((row_index, bytes.len()), (420_863, ROW_BYTES));
    let set_bits: usize = bytes.iter().map(|byte| byte.count_ones() as usize).sum();
    let nonzero_windows: usize = bytes.iter().map(|byte| {
        usize::from(byte & 0x0f != 0) + usize::from(byte >> 4 != 0)
    }).sum();
    assert_eq!((set_bits, nonzero_windows), (741_308, 346_328));
    phase85("real-row-start explicit_rows=1 full_h21_witness=false");
    let source = SparseRows::new(LOG_N, vec![(row_index, bytes)]).unwrap();
    let point: Vec<_> = (0..LOG_N).map(|i| Fr::from(i as u64 + 2)).collect();
    let value = source.direct_value(&point);
    let point_ark: Vec<_> = point.iter().copied().map(ArkFr).collect();
    assert_eq!(source.evaluate(&point_ark).0, value);

    let setup = pcs::regenerate_log41_prover_for_sparse_test(phase85).unwrap();
    phase85("tier-one-start");
    let rows = source.indexed_commitments(&setup);
    assert_eq!(rows.len(), ROWS);
    assert_eq!(rows.iter().filter(|row| **row != ArkG1::identity()).count(), 1);
    phase85("tier-one-done tier-two-start");
    let commitment = BN254::multi_pair_g2_setup(&rows, &setup.prover.g2_vec[..ROWS]);
    let reference = source.direct_commitment(&setup);
    assert_eq!(commitment, reference);
    phase85("tier-two-done");

    let row_weight = |row: usize| point[SIGMA..].iter().enumerate().fold(Fr::one(), |v, (bit, r)|
        v * if (row >> bit) & 1 == 1 { *r } else { Fr::one() - r });
    let column_value = |col: usize| {
        let mut result = Fr::zero();
        source.for_each_bit(|r, c| { if c == col { result += row_weight(r); } });
        result
    };
    let expected_c_g1 = rows[row_index].scale(&ArkFr(column_value(row_index)));
    let expected_c = BN254::pair(&expected_c_g1, &setup.prover.g2_vec[0]);
    let original = rows[row_index];
    let moved = commitment - BN254::pair(&original, &setup.prover.g2_vec[row_index])
        + BN254::pair(&original, &setup.prover.g2_vec[row_index + 1]);
    let omitted = commitment - BN254::pair(&original, &setup.prover.g2_vec[row_index]);
    let final_bit_delta = BN254::pair(&setup.prover.g1_vec[WIDTH - 1], &setup.prover.g2_vec[row_index]);
    let final_bit_set = source.rows[0].1[ROW_BYTES - 1] & 0x80 != 0;
    let flipped = if final_bit_set {
        commitment - final_bit_delta
    } else {
        commitment + final_bit_delta
    };
    assert_ne!(moved, commitment);
    assert_ne!(omitted, commitment);
    assert_ne!(flipped, commitment);

    let mut transcript = Transcript::new(DOMAIN);
    pcs::bind_statement(&setup, &commitment, &value, &point, &mut transcript).unwrap();
    let mut transcript = MarkedTranscript { inner: transcript, beta: 0, alpha: 0 };
    phase85("prove-start rounds=21");
    PADDING_CHECK.with(|state| state.set(Some((ROWS, WIDTH, false))));
    let (proof, blind) = dory_pcs::prove::<_, BN254, PaddingCheckedG1, G2Routines, _, _, Transparent>(
        &source, &point_ark, rows, ArkFr(Fr::zero()), NU, SIGMA, &setup.prover, &mut transcript).unwrap();
    assert_eq!(PADDING_CHECK.with(|state| state.replace(None)), Some((ROWS, WIDTH, true)));
    assert!(blind.is_none());
    assert_eq!((proof.nu, proof.sigma, proof.first_messages.len(), proof.second_messages.len()), (NU, SIGMA, 21, 21));
    assert_eq!((transcript.beta, transcript.alpha), (21, 21));
    assert_eq!(proof.vmv_message.c, expected_c);
    phase85("prove-done encode-start");
    let encoded = pcs::encode_proof(&proof).unwrap();
    phase85("encode-done fresh-verify-start");
    let mut verified = fresh_verify(commitment, value, &point, &encoded).unwrap();
    assert_eq!(verified.challenges(), transcript.inner.challenges());
    assert_eq!(verified.bytes_absorbed(), transcript.inner.bytes_absorbed());
    assert_eq!(verified.challenge_scalar(b"candidate84-continuation"), transcript.inner.challenge_scalar(b"candidate84-continuation"));
    phase85("fresh-verify-done negatives-start");

    let mut negatives = 0;
    for alternate in [moved, omitted, flipped] {
        assert!(fresh_verify(alternate, value, &point, &encoded).is_err());
        negatives += 1;
    }
    let mut moved_rows = source.rows.clone();
    moved_rows[0].0 = row_index + 1;
    let moved_source = SparseRows::new(LOG_N, moved_rows).unwrap();
    let flipped_bytes = {
        let mut changed = source.rows[0].1.clone();
        changed[ROW_BYTES - 1] ^= 0x80;
        changed
    };
    let flipped_source = SparseRows::new(LOG_N, vec![(row_index, flipped_bytes)]).unwrap();
    for (mutant, alternate) in [(&moved_source, moved), (&flipped_source, flipped)] {
        assert_eq!(mutant.direct_commitment(&setup), alternate);
        let alternate_value = mutant.direct_value(&point);
        assert_ne!(alternate_value, value);
        assert_eq!(mutant.evaluate(&point_ark).0, alternate_value);
        assert!(fresh_verify(alternate, alternate_value, &point, &encoded).is_err());
        negatives += 1;
    }
    let vmv_delta = BN254::pair(&setup.prover.g1_vec[0], &setup.prover.g2_vec[0]);
    assert_ne!(vmv_delta, ArkGT::identity());
    let mut bad_vmv_c: ArkDoryProof = proof.clone();
    bad_vmv_c.vmv_message.c = bad_vmv_c.vmv_message.c + vmv_delta;
    assert!(fresh_verify(commitment, value, &point, &pcs::encode_proof(&bad_vmv_c).unwrap()).is_err());
    negatives += 1;
    assert!(fresh_verify(commitment, value + Fr::one(), &point, &encoded).is_err()); negatives += 1;
    let mut bad_point = point.clone(); bad_point[0] += Fr::one();
    assert!(fresh_verify(commitment, value, &bad_point, &encoded).is_err()); negatives += 1;
    let mut short_point = point.clone(); short_point.pop();
    assert!(fresh_verify(commitment, value, &short_point, &encoded).is_err()); negatives += 1;
    let mut truncated = encoded.clone(); truncated.pop();
    assert!(fresh_verify(commitment, value, &point, &truncated).is_err()); negatives += 1;
    assert_eq!(negatives, 10);
    phase85("negatives-done");
    println!("CANDIDATE85_REAL_ROW_SPARSE_LOG41_FULL_OPENING_PASS log_n=41 nu=20 sigma=21 rounds=21 row={row_index} explicit_rows=1 implicit_zero_rows=1048575 packed_bytes=262144 set_bits={set_bits} nonzero_windows={nonzero_windows} negatives={negatives} proof_bytes={} elapsed_s={:.6} setup_id=ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6 full_h21_witness=false fresh_process=false",
        encoded.len(), start.elapsed().as_secs_f64());
    io::stdout().flush().unwrap();
}

impl Polynomial<ArkFr> for SparseRows {
    fn num_vars(&self) -> usize { self.log_n }
    fn evaluate(&self, point: &[ArkFr]) -> ArkFr {
        assert_eq!(point.len(), self.log_n);
        let nu = self.log_n / 2;
        let sigma = self.log_n.div_ceil(2);
        let (left, right) = self.compute_evaluation_vectors(point, nu, sigma);
        let product = self.vector_matrix_product(&left, nu, sigma);
        ArkFr(product.iter().zip(right).fold(Fr::zero(), |sum, (v, r)| sum + v.0 * r.0))
    }
    fn commit<E, Mo, M1>(&self, _nu: usize, _sigma: usize, _setup: &ProverSetup<E>)
        -> Result<(E::GT, Vec<E::G1>, ArkFr), DoryError>
    where E: PairingCurve, Mo: dory_pcs::Mode, M1: DoryRoutines<E::G1>,
        E::G1: Group<Scalar = ArkFr>, E::GT: Group<Scalar = ArkFr> {
        // The caller must use indexed_commitments and the actual tier-two kernel.
        Err(DoryError::InvalidSize { expected: self.len(), actual: 0 })
    }
}

impl MultilinearLagrange<ArkFr> for SparseRows {
    fn vector_matrix_product(&self, left: &[ArkFr], nu: usize, sigma: usize) -> Vec<ArkFr> {
        assert_eq!((nu, sigma), (self.log_n / 2, self.log_n.div_ceil(2)));
        assert_eq!(left.len(), 1usize << nu);
        if self.log_n == LOG_N { phase("vector-product-start"); }
        let mut product = vec![ArkFr(Fr::zero()); 1usize << sigma];
        self.for_each_bit(|row, col| { product[col].0 += left[row].0; });
        if self.log_n == LOG_N { phase("vector-product-done"); }
        product
    }
}

// Instrument only the existing transcript's calls; no extra bytes/challenges
// enter Fiat-Shamir. The beta marker is after the round's first-message work;
// alpha is after its second-message work and before folding.
struct MarkedTranscript { inner: Transcript, beta: usize, alpha: usize }
impl DoryTranscript for MarkedTranscript {
    type Curve = BN254;
    fn append_bytes(&mut self, label: &[u8], bytes: &[u8]) { DoryTranscript::append_bytes(&mut self.inner, label, bytes); }
    fn append_field(&mut self, label: &[u8], x: &ArkFr) { DoryTranscript::append_field(&mut self.inner, label, x); }
    fn append_group<G: Group>(&mut self, label: &[u8], g: &G) { DoryTranscript::append_group(&mut self.inner, label, g); }
    fn append_serde<S: DorySerialize>(&mut self, label: &[u8], s: &S) {
        DoryTranscript::append_serde(&mut self.inner, label, s);
        if label == b"vmv_e1" { phase("vmv-done fixed-base-v2-and-first-round-next"); }
    }
    fn challenge_scalar(&mut self, label: &[u8]) -> ArkFr {
        if label == b"beta" { self.beta += 1; phase(&format!("round={}-first-message-done", self.beta)); }
        if label == b"alpha" { self.alpha += 1; phase(&format!("round={}-second-message-done", self.alpha)); }
        DoryTranscript::challenge_scalar(&mut self.inner, label)
    }
    fn reset(&mut self, domain: &[u8]) {
        self.inner = Transcript::new(domain); self.beta = 0; self.alpha = 0;
    }
}

thread_local! {
    static PADDING_CHECK: Cell<Option<(usize, usize, bool)>> = const { Cell::new(None) };
}

// Observe the actual padded vector at the first VMV MSM, then delegate every
// operation to the production backend unchanged. Thread-local state keeps the
// two selectors independent even if libtest schedules them concurrently.
struct PaddingCheckedG1;
fn validate_initial_padding(bases: &[ArkG1], scalar_count: usize, rows: usize, width: usize) -> Result<(), String> {
    if rows >= width || bases.len() != width || scalar_count != width {
        return Err("initial padding geometry mismatch".into());
    }
    if bases[rows..].iter().any(|p| *p != ArkG1::identity()) {
        return Err("nonidentity odd-log padding row".into());
    }
    Ok(())
}
impl DoryRoutines<ArkG1> for PaddingCheckedG1 {
    fn msm(bases: &[ArkG1], scalars: &[ArkFr]) -> ArkG1 {
        PADDING_CHECK.with(|state| {
            let (rows, width, checked) = state.get().expect("padding check armed");
            if !checked {
                validate_initial_padding(bases, scalars.len(), rows, width).unwrap();
                state.set(Some((rows, width, true)));
            }
        });
        G1Routines::msm(bases, scalars)
    }
    fn fixed_base_vector_scalar_mul(base: &ArkG1, scalars: &[ArkFr]) -> Vec<ArkG1> {
        G1Routines::fixed_base_vector_scalar_mul(base, scalars)
    }
    fn fixed_scalar_mul_bases_then_add(bases: &[ArkG1], vs: &mut [ArkG1], scalar: &ArkFr) {
        G1Routines::fixed_scalar_mul_bases_then_add(bases, vs, scalar)
    }
    fn fixed_scalar_mul_vs_then_add(vs: &mut [ArkG1], addends: &[ArkG1], scalar: &ArkFr) {
        G1Routines::fixed_scalar_mul_vs_then_add(vs, addends, scalar)
    }
    fn fold_field_vectors(left: &mut [ArkFr], right: &[ArkFr], scalar: &ArkFr) {
        G1Routines::fold_field_vectors(left, right, scalar)
    }
}

// Public inputs only. Each invocation re-admits the exact release-pinned key,
// decodes canonical proof bytes, and starts a fresh verifier transcript.
fn fresh_verify(commitment: ArkGT, value: Fr, point: &[Fr], encoded: &[u8]) -> Result<Transcript, String> {
    let key = crate::verifier_key::admit(LOG_N, VK)?;
    let proof = pcs::decode_proof(encoded, LOG_N)?;
    let mut transcript = Transcript::new(DOMAIN);
    pcs::verify_admitted(commitment, value, point, &proof, &key, &mut transcript)?;
    Ok(transcript)
}

fn packed_row(width: usize, columns: &[usize]) -> Vec<u8> {
    let mut bytes = vec![0; width / 8];
    for col in columns { assert!(*col < width); bytes[col / 8] |= 1 << (col % 8); }
    bytes
}

#[test]
fn sparse_oddlog_source_matches_dense_reference() {
    let sparse = SparseRows::new(9, vec![
        (0, packed_row(32, &[0, 1, 7, 8, 31])),
        (7, packed_row(32, &[3, 16, 30])),
        (15, packed_row(32, &[0, 17, 31])),
    ]).unwrap();
    let mut dense = vec![ArkFr(Fr::zero()); 512];
    sparse.for_each_bit(|r, c| dense[r * 32 + c] = ArkFr(Fr::one()));
    let dense = ArkworksPolynomial::new(dense);
    let point: Vec<_> = (0..9).map(|i| ArkFr(Fr::from(i + 2u64))).collect();
    let (left, _) = sparse.compute_evaluation_vectors(&point, 4, 5);
    assert_eq!(sparse.vector_matrix_product(&left, 4, 5), dense.vector_matrix_product(&left, 4, 5));
    assert_eq!(sparse.evaluate(&point), dense.evaluate(&point));
    assert_eq!(sparse.direct_value(&point.iter().map(|r| r.0).collect::<Vec<_>>()), dense.evaluate(&point).0);
    let setup = pcs::generate_setup(9).unwrap();
    let rows = sparse.indexed_commitments(&setup);
    let (commitment, dense_rows, _) = dense.commit::<BN254, Transparent, G1Routines>(4, 5, &setup.prover).unwrap();
    assert_eq!(rows, dense_rows);
    let mut padding_control = rows.clone(); padding_control.resize(32, ArkG1::identity());
    validate_initial_padding(&padding_control, 32, 16, 32).unwrap();
    padding_control[16] = setup.prover.g1_vec[0];
    assert!(validate_initial_padding(&padding_control, 32, 16, 32).unwrap_err().contains("nonidentity"));
    assert_eq!(BN254::multi_pair_g2_setup(&rows, &setup.prover.g2_vec[..16]), commitment);
    assert_eq!(sparse.direct_commitment(&setup), commitment);
    let point_fr: Vec<_> = point.iter().map(|r| r.0).collect();
    let value = sparse.direct_value(&point_fr);
    let mut dense_transcript = Transcript::new(DOMAIN);
    pcs::bind_statement(&setup, &commitment, &value, &point_fr, &mut dense_transcript).unwrap();
    let mut sparse_transcript = MarkedTranscript { inner: dense_transcript.clone(), beta: 0, alpha: 0 };
    let (dense_proof, dense_blind) = dory_pcs::prove::<_, BN254, G1Routines, G2Routines, _, _, Transparent>(
        &dense, &point, dense_rows, ArkFr(Fr::zero()), 4, 5, &setup.prover, &mut dense_transcript).unwrap();
    PADDING_CHECK.with(|state| state.set(Some((16, 32, false))));
    let (sparse_proof, sparse_blind) = dory_pcs::prove::<_, BN254, PaddingCheckedG1, G2Routines, _, _, Transparent>(
        &sparse, &point, rows, ArkFr(Fr::zero()), 4, 5, &setup.prover, &mut sparse_transcript).unwrap();
    assert_eq!(PADDING_CHECK.with(|state| state.replace(None)), Some((16, 32, true)));
    assert!(dense_blind.is_none() && sparse_blind.is_none());
    assert_eq!(pcs::encode_proof(&dense_proof).unwrap(), pcs::encode_proof(&sparse_proof).unwrap());
    assert_eq!((sparse_transcript.beta, sparse_transcript.alpha), (5, 5));
    assert_eq!(dense_transcript.challenge_scalar(b"continuation"), sparse_transcript.inner.challenge_scalar(b"continuation"));
    pcs::verify(commitment, value, &point_fr, &sparse_proof, &setup, &mut Transcript::new(DOMAIN)).unwrap();
    assert!(SparseRows::new(9, vec![(16, packed_row(32, &[1]))]).is_err());
    assert!(SparseRows::new(9, vec![(0, vec![1; 3])]).is_err());
    assert!(SparseRows::new(9, vec![(0, vec![0; 4])]).is_err());
    assert!(SparseRows::new(9, vec![(1, packed_row(32, &[1])), (1, packed_row(32, &[2]))]).is_err());
    assert!(SparseRows::new(9, vec![(2, packed_row(32, &[1])), (1, packed_row(32, &[2]))]).is_err());
}

#[test]
#[ignore = "actual log41 full-width Dory PCS kernel; capped one-use runner required"]
fn sparse_log41_complete_opening_under_admitted_key() {
    let start = Instant::now();
    phase("start sparse-synthetic=true full_h21_witness=false");
    assert_eq!((ROWS, WIDTH, ROW_BYTES), (1_048_576, 2_097_152, 262_144));
    let source = SparseRows::new(LOG_N, vec![
        (0, packed_row(WIDTH, &[0, 1, 7, 8, 255, 65536, WIDTH - 1])),
        (420863, packed_row(WIDTH, &[3, 16, 1023, 1 << NU, WIDTH - 2])),
        (ROWS - 1, packed_row(WIDTH, &[0, 17, 1048575, WIDTH - 1])),
    ]).unwrap();
    let point: Vec<_> = (0..LOG_N).map(|i| Fr::from(i as u64 + 2)).collect();
    let value = source.direct_value(&point);
    let point_ark: Vec<_> = point.iter().copied().map(ArkFr).collect();
    assert_eq!(source.evaluate(&point_ark).0, value);
    let setup = pcs::regenerate_log41_prover_for_sparse_test(phase).unwrap();
    phase("tier-one-start");
    let rows = source.indexed_commitments(&setup);
    assert_eq!(rows.len(), ROWS);
    assert_eq!(rows.iter().filter(|row| **row != ArkG1::identity()).count(), 3);
    phase("tier-one-done tier-two-start");
    // Use the actual full-prefix backend path, including every zero position.
    let commitment = BN254::multi_pair_g2_setup(&rows, &setup.prover.g2_vec[..ROWS]);
    let reference = source.direct_commitment(&setup);
    assert_eq!(commitment, reference);
    phase("tier-two-done");

    // Compute the expected positive VMV C independently, without a width-sized
    // vector product: only the three nonzero row positions can contribute.
    let row_weight = |row: usize| point[SIGMA..].iter().enumerate().fold(Fr::one(), |v, (bit, r)|
        v * if (row >> bit) & 1 == 1 { *r } else { Fr::one() - r });
    let column_value = |col: usize| {
        let mut value = Fr::zero();
        source.for_each_bit(|r, c| { if c == col { value += row_weight(r); } });
        value
    };
    let expected_c_g1 = source.rows.iter().fold(ArkG1::identity(), |sum, (i, _)|
        sum + rows[*i].scale(&ArkFr(column_value(*i))));
    let expected_c = BN254::pair(&expected_c_g1, &setup.prover.g2_vec[0]);
    let row0 = rows[0];
    let last_row = rows[ROWS - 1];
    // Isolated altered public commitments, derived before rows move to prover.
    let moved = commitment - BN254::pair(&row0, &setup.prover.g2_vec[0])
        + BN254::pair(&row0, &setup.prover.g2_vec[1]);
    let omitted = commitment - BN254::pair(&last_row, &setup.prover.g2_vec[ROWS - 1]);
    let final_bit_delta = BN254::pair(&setup.prover.g1_vec[WIDTH - 1], &setup.prover.g2_vec[ROWS - 1]);
    let flipped = commitment - final_bit_delta;
    assert_ne!(moved, commitment); assert_ne!(omitted, commitment); assert_ne!(flipped, commitment);

    let mut transcript = Transcript::new(DOMAIN);
    pcs::bind_statement(&setup, &commitment, &value, &point, &mut transcript).unwrap();
    let mut transcript = MarkedTranscript { inner: transcript, beta: 0, alpha: 0 };
    phase("prove-start rounds=21");
    PADDING_CHECK.with(|state| state.set(Some((ROWS, WIDTH, false))));
    let (proof, blind) = dory_pcs::prove::<_, BN254, PaddingCheckedG1, G2Routines, _, _, Transparent>(
        &source, &point_ark, rows, ArkFr(Fr::zero()), NU, SIGMA, &setup.prover, &mut transcript).unwrap();
    assert_eq!(PADDING_CHECK.with(|state| state.replace(None)), Some((ROWS, WIDTH, true)));
    assert!(blind.is_none());
    assert_eq!((proof.nu, proof.sigma, proof.first_messages.len(), proof.second_messages.len()), (NU, SIGMA, 21, 21));
    assert_eq!((transcript.beta, transcript.alpha), (21, 21));
    assert_eq!(proof.vmv_message.c, expected_c);
    phase("prove-done encode-start");
    let encoded = pcs::encode_proof(&proof).unwrap();
    phase("encode-done fresh-verify-start");
    let mut verified = fresh_verify(commitment, value, &point, &encoded).unwrap();
    assert_eq!(verified.challenges(), transcript.inner.challenges());
    assert_eq!(verified.bytes_absorbed(), transcript.inner.bytes_absorbed());
    assert_eq!(verified.challenge_scalar(b"candidate84-continuation"), transcript.inner.challenge_scalar(b"candidate84-continuation"));
    phase("fresh-verify-done negatives-start");
    let mut negatives = 0;
    for alternate in [moved, omitted, flipped] {
        assert!(fresh_verify(alternate, value, &point, &encoded).is_err()); negatives += 1;
    }
    // Each algebraic negative above is also joined to a separately mutated
    // packed source, including its evaluation and actual vector-product path.
    let mut moved_rows = source.rows.clone(); moved_rows[0].0 = 1;
    let moved_source = SparseRows::new(LOG_N, moved_rows).unwrap();
    let mut omitted_rows = source.rows.clone(); omitted_rows.pop();
    let omitted_source = SparseRows::new(LOG_N, omitted_rows).unwrap();
    let mut flipped_rows = source.rows.clone();
    flipped_rows.last_mut().unwrap().1[ROW_BYTES - 1] ^= 0x80;
    let flipped_source = SparseRows::new(LOG_N, flipped_rows).unwrap();
    for (mutant, alternate) in [(&moved_source, moved), (&omitted_source, omitted), (&flipped_source, flipped)] {
        assert_eq!(mutant.direct_commitment(&setup), alternate);
        let alternate_value = mutant.direct_value(&point);
        assert_ne!(alternate_value, value);
        assert_eq!(mutant.evaluate(&point_ark).0, alternate_value);
        assert!(fresh_verify(alternate, alternate_value, &point, &encoded).is_err());
        negatives += 1;
    }
    // A nonidentity row in the padded upper half contributes this nonzero
    // term to VMV C. Mutate only that message, keeping the public statement and
    // all other proof fields fixed. This is a message-level padding negative.
    let padding_delta = BN254::pair(&setup.prover.g1_vec[0].scale(&ArkFr(column_value(WIDTH - 1))), &setup.prover.g2_vec[0]);
    assert_ne!(padding_delta, ArkGT::identity());
    let mut bad_padding: ArkDoryProof = proof.clone();
    bad_padding.vmv_message.c = bad_padding.vmv_message.c + padding_delta;
    assert!(fresh_verify(commitment, value, &point, &pcs::encode_proof(&bad_padding).unwrap()).is_err()); negatives += 1;
    assert!(fresh_verify(commitment, value + Fr::one(), &point, &encoded).is_err()); negatives += 1;
    let mut bad_point = point.clone(); bad_point[0] += Fr::one();
    assert!(fresh_verify(commitment, value, &bad_point, &encoded).is_err()); negatives += 1;
    let mut short_point = point.clone(); short_point.pop();
    assert!(fresh_verify(commitment, value, &short_point, &encoded).is_err()); negatives += 1;
    let mut truncated = encoded.clone(); truncated.pop();
    assert!(fresh_verify(commitment, value, &point, &truncated).is_err()); negatives += 1;
    assert_eq!(negatives, 11);
    phase("negatives-done");
    println!("CANDIDATE84_SPARSE_LOG41_FULL_OPENING_PASS log_n=41 nu=20 sigma=21 rounds=21 explicit_rows=3 implicit_zero_rows=1048573 packed_bytes=786432 negatives=11 proof_bytes={} elapsed_s={:.6} setup_id=ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6 full_h21_witness=false fresh_process=false", encoded.len(), start.elapsed().as_secs_f64());
    io::stdout().flush().unwrap();
}

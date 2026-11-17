//! Private bounded producer: ordered sparse rows, immutable Boolean input, and
//! sumcheck coefficient windows. The ordinary statement and proof codec remain
//! unchanged. Dense golden/verifier tables are outside this producer's lifetime.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self, GkrError, GkrProof, InputClaim, LayerProof}, sparse::{self, Circuit}, transcript::Transcript};

pub(super) const PAIRS: usize = 16384;
pub(super) const WINDOW: usize = 2 * PAIRS;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Error { Circuit(GkrError), Scope, ScalarWidth, Framing, Order(usize), Residual(usize), Identity, Terminal, Endpoints }

#[derive(Clone)]
pub(super) struct Bits { bytes: Box<[u8]>, width: usize }
impl Bits {
    pub(super) fn new(bytes: Box<[u8]>, width: usize) -> Result<Self, Error> {
        let d = gkr::log_width(width).map_err(Error::Circuit)?;
        if d > 18 { return Err(Error::Scope); }
        if bytes.len() != width.div_ceil(8) || (width < 8 && bytes[0] >> width != 0) { return Err(Error::Framing); }
        Ok(Self { bytes, width })
    }
    pub(super) fn bytes(&self) -> &[u8] { &self.bytes }
    pub(super) fn bit(&self, i: usize) -> Fr { Fr::from(((self.bytes[i >> 3] >> (i & 7)) & 1) as u64) }
}

#[derive(Clone, Debug, Default)]
pub(super) struct Work {
    pub residual_terms: u64, pub source_visits: u64, pub weighted_terms: u64,
    pub terminal_terms: u64, pub fold_leaves: u64, pub fold_muls: u64,
    pub line_bits: u64, pub line_ones: u64, pub line_updates: u64,
    pub cache_muls: u64, pub cache_peak_bytes: u64, pub window_bytes: u64,
}
fn add(value: &mut u64, n: usize) { *value = value.checked_add(u64::try_from(n).expect("bounded count")).expect("work count overflow"); }

pub(super) fn admit(c: &Circuit, log_copies: usize) -> Result<(usize, usize), Error> {
    // This scope gate precedes bit reads, allocations, caches and transcript binding.
    if log_copies != 0 { return Err(Error::Scope); }
    let input = gkr::log_width(c.input_len).map_err(Error::Circuit)?;
    let rows = gkr::log_width(c.row_count).map_err(Error::Circuit)?;
    if input > 18 || rows > 19 { return Err(Error::Scope); }
    if input == 0 { return Err(Error::ScalarWidth); }
    sparse::validate(c, 0).map_err(Error::Circuit)?;
    for (i, pair) in c.terms.windows(2).enumerate() {
        if pair[0].row > pair[1].row { return Err(Error::Order(i + 1)); }
    }
    Ok((input, rows))
}

pub(super) fn check(c: &Circuit, bits: &Bits, work: &mut Work) -> Result<(), Error> {
    admit(c, 0)?;
    if bits.width != c.input_len { return Err(Error::Framing); }
    let mut row = None;
    let mut residual = Fr::zero();
    for t in &c.terms {
        if row != Some(t.row) {
            if !residual.is_zero() { return Err(Error::Residual(row.expect("nonempty row"))); }
            row = Some(t.row); residual = Fr::zero();
        }
        let g = &t.gate;
        let l = bits.bit(g.left); let r = bits.bit(g.right);
        residual += g.c0 + g.c1 * l + g.c2 * r + g.c3 * l * r;
        add(&mut work.residual_terms, 1);
    }
    if !residual.is_zero() { return Err(Error::Residual(row.expect("nonempty row"))); }
    Ok(())
}

/// Each table has at most 512 scalars; empty points have no table and weight one.
pub(super) struct EqCache { tables: Vec<Box<[Fr]>>, bits: usize }
impl EqCache {
    pub(super) fn new(point: &[Fr], work: &mut Work) -> Self {
        assert!(point.len() <= 19);
        let mut tables = Vec::with_capacity(point.len().div_ceil(9));
        for chunk in point.chunks(9) {
            let table = gkr::eq_weights(chunk);
            assert_eq!(table.len(), 1usize << chunk.len());
            assert!(table.capacity() <= 512);
            add(&mut work.cache_muls, 2 * (table.len() - 1));
            tables.push(table.into_boxed_slice());
        }
        Self { tables, bits: point.len() }
    }
    pub(super) fn at(&self, index: usize) -> Fr {
        let Some(first) = self.tables.first() else { return Fr::one(); };
        let mut out = first[index & (first.len() - 1)];
        for (j, table) in self.tables.iter().enumerate().skip(1) { out *= table[(index >> (9 * j)) & (table.len() - 1)]; }
        out
    }
    pub(super) fn bytes(&self) -> usize {
        self.tables.iter().map(|x| x.len() * std::mem::size_of::<Fr>()).sum::<usize>()
            + self.tables.capacity() * std::mem::size_of::<Box<[Fr]>>() + std::mem::size_of::<Self>()
    }
}
fn cache_peak(work: &mut Work, caches: &[&EqCache]) {
    // Include the maximum old/new eq_weights growth during construction (256 Fr).
    let bytes = caches.iter().map(|c| c.bytes()).sum::<usize>() + 256 * std::mem::size_of::<Fr>();
    assert!(bytes <= 131072);
    work.cache_peak_bytes = work.cache_peak_bytes.max(bytes as u64);
}

pub(super) fn folded(bits: &Bits, start: usize, point: &[Fr], work: &mut Work) -> Fr {
    if point.is_empty() { add(&mut work.fold_leaves, 1); return bits.bit(start); }
    let j = point.len() - 1;
    let lo = folded(bits, start, &point[..j], work);
    let hi = folded(bits, start + (1usize << j), &point[..j], work);
    add(&mut work.fold_muls, 1);
    lo + (hi - lo) * point[j]
}

pub(super) fn quadratic(a: &[Fr], b: &[Fr], x: &[Fr]) -> [Fr; 3] {
    assert_eq!(a.len(), b.len()); assert_eq!(a.len(), x.len()); assert_eq!(a.len() & 1, 0);
    let mut out = [Fr::zero(); 3];
    for i in (0..a.len()).step_by(2) {
        let da = a[i + 1] - a[i]; let db = b[i + 1] - b[i]; let dx = x[i + 1] - x[i];
        out[0] += a[i] * x[i] + b[i];
        out[1] += a[i] * dx + da * x[i] + db;
        out[2] += da * dx;
    }
    out
}

/// Fill one whole coefficient window before taking its quadratic. Phase one
/// keeps the right source bit unmodified; phase two uses the left terminal value.
#[allow(clippy::too_many_arguments)]
pub(super) fn fill(
    c: &Circuit, bits: &Bits, row: &EqCache, left: Option<(&EqCache, Fr)>,
    prefix: &EqCache, j: usize, start: usize, a: &mut [Fr], b: &mut [Fr], work: &mut Work,
) {
    assert_eq!(prefix.bits, j); assert_eq!(a.len(), b.len());
    a.fill(Fr::zero()); b.fill(Fr::zero());
    for t in &c.terms {
        add(&mut work.source_visits, 1);
        let g = &t.gate;
        let axis = if left.is_some() { g.right } else { g.left };
        let key = axis >> j;
        if key < start || key >= start + a.len() { continue; }
        add(&mut work.weighted_terms, 1);
        let weight = row.at(t.row) * prefix.at(axis);
        let k = key - start;
        if let Some((u, value)) = left {
            let weight = weight * u.at(g.left);
            a[k] += weight * (g.c2 + g.c3 * value);
            b[k] += weight * (g.c0 + g.c1 * value);
        } else {
            let right = bits.bit(g.right);
            a[k] += weight * (g.c1 + g.c3 * right);
            b[k] += weight * (g.c0 + g.c2 * right);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn phase(
    c: &Circuit, bits: &Bits, d: usize, row: &EqCache, left: Option<(&EqCache, Fr)>,
    a: &mut [Fr], b: &mut [Fr], x: &mut [Fr], claim: &mut Fr,
    rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript, work: &mut Work,
) -> Result<(Vec<Fr>, Fr), Error> {
    let mut point = Vec::with_capacity(d);
    let mut final_value = Fr::zero();
    for j in 0..d {
        let prefix = EqCache::new(&point, work);
        if let Some((u, _)) = left { cache_peak(work, &[row, u, &prefix]); }
        else { cache_peak(work, &[row, &prefix]); }
        let len = c.input_len >> j;
        let mut message = [Fr::zero(); 3];
        let mut endpoints = [Fr::zero(); 2];
        for start in (0..len).step_by(a.len()) {
            let count = a.len().min(len - start);
            fill(c, bits, row, left, &prefix, j, start, &mut a[..count], &mut b[..count], work);
            for (k, out) in x[..count].iter_mut().enumerate() { *out = folded(bits, (start + k) << j, &point, work); }
            let m = quadratic(&a[..count], &b[..count], &x[..count]);
            for k in 0..3 { message[k] += m[k]; }
            if j + 1 == d { endpoints.copy_from_slice(&x[..2]); }
        }
        if message[0] + gkr::eval_polynomial(&message, Fr::one()) != *claim { return Err(Error::Identity); }
        gkr::append_polynomial(transcript, b"gkr-sumcheck-polynomial", &message);
        let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        *claim = gkr::eval_polynomial(&message, challenge);
        point.push(challenge); rounds.push(message.to_vec());
        if j + 1 == d { final_value = endpoints[0] + (endpoints[1] - endpoints[0]) * challenge; }
        // Prefix tables die here before the next prefix is allocated.
    }
    Ok((point, final_value))
}

pub(super) fn terminal(c: &Circuit, row: &EqCache, u: &EqCache, v: &EqCache, work: &mut Work) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for t in &c.terms {
        add(&mut work.terminal_terms, 1);
        let g = &t.gate; let w = row.at(t.row) * u.at(g.left) * v.at(g.right);
        for (out, coefficient) in out.iter_mut().zip([g.c0, g.c1, g.c2, g.c3]) { *out += w * coefficient; }
    }
    out
}

pub(super) fn line(bits: &Bits, u: &[Fr], v: &[Fr], work: &mut Work) -> Vec<Fr> {
    assert_eq!(u.len(), v.len()); assert_eq!(1usize << u.len(), bits.width);
    let d = u.len(); assert!(d <= 18);
    let mut sum = [Fr::zero(); 19];
    let mut product = [Fr::zero(); 19];
    for i in 0..bits.width {
        add(&mut work.line_bits, 1);
        if bits.bit(i).is_zero() { continue; }
        add(&mut work.line_ones, 1);
        product.fill(Fr::zero()); product[0] = Fr::one();
        for j in 0..d {
            let (constant, slope) = if (i >> j) & 1 == 0 { (Fr::one() - u[j], u[j] - v[j]) } else { (u[j], v[j] - u[j]) };
            for k in (0..=j + 1).rev() {
                product[k] = product[k] * constant + if k == 0 { Fr::zero() } else { product[k - 1] * slope };
                add(&mut work.line_updates, 1);
            }
        }
        for k in 0..=d { sum[k] += product[k]; }
    }
    sum[..=d].to_vec()
}

pub(super) fn prove(c: &Circuit, bits: &Bits, log_copies: usize, transcript: &mut Transcript)
    -> Result<(GkrProof, InputClaim, Work), Error> {
    prove_with_binding(c, bits, log_copies, transcript, |t| sparse::bind(c, log_copies, t))
}
pub(super) fn prove_with_binding(c: &Circuit, bits: &Bits, log_copies: usize, transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript)) -> Result<(GkrProof, InputClaim, Work), Error> {
    let (d, _) = admit(c, log_copies)?;
    let mut work = Work::default();
    check(c, bits, &mut work)?;
    bind(transcript);
    let r = gkr::output_point(c.row_count, transcript);
    gkr::append_usize(transcript, b"gkr-layer-index", 0);
    let row = EqCache::new(&r, &mut work);
    let count = WINDOW.min(c.input_len);
    let mut a = vec![Fr::zero(); count].into_boxed_slice();
    let mut b = vec![Fr::zero(); count].into_boxed_slice();
    let mut x = vec![Fr::zero(); count].into_boxed_slice();
    work.window_bytes = (3 * count * std::mem::size_of::<Fr>()) as u64;
    let mut claim = Fr::zero(); let mut rounds = Vec::with_capacity(2 * d);
    let (u, left_value) = phase(c, bits, d, &row, None, &mut a, &mut b, &mut x, &mut claim, &mut rounds, transcript, &mut work)?;
    let u_cache = EqCache::new(&u, &mut work);
    // Full immutable X is reused, with a new empty prefix in phase two.
    let (v, right_value) = phase(c, bits, d, &row, Some((&u_cache, left_value)), &mut a, &mut b, &mut x, &mut claim, &mut rounds, transcript, &mut work)?;
    drop(a); drop(b); drop(x);
    let v_cache = EqCache::new(&v, &mut work); cache_peak(&mut work, &[&row, &u_cache, &v_cache]);
    let w = terminal(c, &row, &u_cache, &v_cache, &mut work);
    if w[0] + w[1] * left_value + w[2] * right_value + w[3] * left_value * right_value != claim { return Err(Error::Terminal); }
    drop(row); drop(u_cache); drop(v_cache);
    let line_coefficients = line(bits, &u, &v, &mut work);
    if gkr::eval_polynomial(&line_coefficients, Fr::zero()) != left_value || gkr::eval_polynomial(&line_coefficients, Fr::one()) != right_value { return Err(Error::Endpoints); }
    transcript.append_scalar(b"gkr-left-value", &left_value);
    transcript.append_scalar(b"gkr-right-value", &right_value);
    gkr::append_polynomial(transcript, b"gkr-line-polynomial", &line_coefficients);
    let challenge = transcript.challenge_scalar(b"gkr-line-challenge");
    let input = InputClaim { point: gkr::line_point(&u, &v, challenge), value: gkr::eval_polynomial(&line_coefficients, challenge) };
    Ok((GkrProof { layers: vec![LayerProof { rounds, left_value, right_value, line_coefficients }] }, input, work))
}

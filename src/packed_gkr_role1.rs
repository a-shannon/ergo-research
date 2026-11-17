//! Private N3 MAX role1 producer. The source and old role binding are borrowed;
//! only bounded Boolean bytes, equality chunks and coefficient windows are owned.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self, GkrProof, InputClaim, LayerProof}, max_header_adapter::MaxHeaderAdapter,
    sparse::Term, transcript::Transcript, work_tree_history_plan::WorkTreeHistoryPlan};

pub(crate) const INPUT_BITS: usize = 22;
pub(crate) const ROW_BITS: usize = 21;
pub(crate) const INPUTS: usize = 1 << INPUT_BITS;
pub(crate) const ROWS: usize = 1 << ROW_BITS;
pub(crate) const BYTES: usize = INPUTS / 8;
pub(crate) const WINDOW: usize = 1 << 18;
pub(crate) const CENSUS: [usize; 4] = [395888, 395888, 396561, 396561];
pub(crate) const TERMS: usize = 1584898;
const OWNER_INPUTS: usize = 1 << 20;
const OWNER_ROWS: usize = 1 << 19;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Error { Scope, Parent, Binding, Framing, Coordinate(usize), Order(usize),
    Count(usize), Adapter(String), Residual(usize), Point, Identity, Terminal, Endpoints,
    Resource, Overflow }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Frame {
    pub headers: u64, pub owners: usize, pub owner_bits: usize,
    pub input_bits: usize, pub row_bits: usize, pub counts: [usize; 4],
    pub binding: [u8; 32],
}

pub(crate) struct Bits { bytes: Box<[u8]> }
impl Bits {
    pub(crate) fn new(bytes: Box<[u8]>) -> Result<Self, Error> {
        if bytes.len() != BYTES { return Err(Error::Framing); }
        Ok(Self { bytes })
    }
    pub(crate) fn bytes(&self) -> &[u8] { &self.bytes }
    pub(crate) fn bit(&self, index: usize) -> Fr {
        assert!(index < INPUTS);
        Fr::from(((self.bytes[index >> 3] >> (index & 7)) & 1) as u64)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Work {
    pub validation_terms: u64, pub residual_terms: u64, pub fill_term_visits: u64,
    pub weighted_terms: u64, pub terminal_terms: u64, pub fold_leaves: u64,
    pub fold_muls: u64, pub line_bits: u64, pub line_ones: u64,
    pub line_updates: u64, pub cache_muls: u64, pub cache_modeled_peak_bytes: u64,
    pub window_bytes: u64,
}
fn add(value: &mut u64, count: usize) -> Result<(), Error> {
    *value = value.checked_add(u64::try_from(count).map_err(|_| Error::Overflow)?)
        .ok_or(Error::Overflow)?; Ok(())
}

/// No source closure supplied by an external caller: every pass uses the same
/// immutable, code-owned MAX/DAA/retirement adapter and exact four-owner shape.
pub(crate) struct Source<'a, 'p> { adapter: &'a MaxHeaderAdapter<'p>, frame: Frame }
impl<'a, 'p> Source<'a, 'p> {
    pub(crate) fn new(adapter: &'a MaxHeaderAdapter<'p>, parent: &'p WorkTreeHistoryPlan)
        -> Result<Self, Error> {
        adapter.check_parent(parent).map_err(|_| Error::Parent)?;
        let frame = Frame { headers: parent.headers(), owners: parent.slots(),
            owner_bits: parent.slot_log(), input_bits: adapter.roster().input_log(),
            row_bits: 19 + parent.slot_log(), counts: CENSUS, binding: adapter.binding() };
        let source = Self { adapter, frame };
        source.admit_frame(frame)?;
        Ok(source)
    }
    pub(crate) fn frame(&self) -> Frame { self.frame }
    pub(crate) fn admit_frame(&self, frame: Frame) -> Result<(), Error> {
        if (frame.headers, frame.owners, frame.owner_bits, frame.input_bits, frame.row_bits)
            != (3, 4, 2, INPUT_BITS, ROW_BITS) || frame.counts != CENSUS
            || self.adapter.max().n() != 3 || self.adapter.max().c() != 4
            || self.adapter.max().input_log() != INPUT_BITS
            || self.adapter.roster().slot_log() != 2 { return Err(Error::Scope); }
        if frame.binding != self.adapter.binding() { return Err(Error::Binding); }
        Ok(())
    }
    pub(crate) fn visit(&self, mut sink: impl FnMut(&Term) -> Result<(), Error>)
        -> Result<(), Error> {
        self.admit_frame(self.frame)?;
        for owner in 0..4 {
            let mut previous = None; let mut emitted = 0usize; let mut failure = None;
            let counts = self.adapter.visit_header_terms(owner, |term| {
                if failure.is_some() { return Ok(()); }
                let result = term_shape(&term, owner, previous).and_then(|()| sink(&term));
                match result { Ok(()) => { previous = Some(term.row); emitted += 1; }
                    Err(error) => { failure = Some(error); } }
                Ok(())
            }).map_err(Error::Adapter)?;
            if let Some(error) = failure { return Err(error); }
            let omitted = if owner < 2 { 673 } else { 0 };
            if emitted != CENSUS[owner] || counts.emitted != emitted
                || counts.omitted_max != omitted || counts.parent.omitted_worktree != 78194
                || counts.parent.omitted_mature_a4 != 0 || counts.parent.omitted_short_a4 != 0 {
                return Err(Error::Count(owner));
            }
        }
        Ok(())
    }
    pub(crate) fn validate(&self, work: &mut Work) -> Result<(), Error> {
        self.visit(|_| add(&mut work.validation_terms, 1))
    }
    pub(crate) fn check(&self, bits: &Bits, work: &mut Work) -> Result<(), Error> {
        let mut rows = RowCheck::default();
        self.visit(|term| {
            let g = &term.gate;
            rows.push(term.row, g.c0 + g.c1 * bits.bit(g.left) + g.c2 * bits.bit(g.right)
                + g.c3 * bits.bit(g.left) * bits.bit(g.right))?;
            add(&mut work.residual_terms, 1)
        })?;
        rows.finish()
    }
}

pub(crate) fn term_shape(term: &Term, owner: usize, previous: Option<usize>) -> Result<(), Error> {
    if owner >= 4 { return Err(Error::Coordinate(owner)); }
    let ib = owner * OWNER_INPUTS; let rb = owner * OWNER_ROWS;
    if !(ib..ib + OWNER_INPUTS).contains(&term.gate.left)
        || !(ib..ib + OWNER_INPUTS).contains(&term.gate.right)
        || !(rb..rb + OWNER_ROWS).contains(&term.row) { return Err(Error::Coordinate(owner)); }
    if previous.is_some_and(|row| row > term.row) { return Err(Error::Order(term.row)); }
    Ok(())
}

#[derive(Default)]
pub(crate) struct RowCheck { row: Option<usize>, residual: Fr }
impl RowCheck {
    pub(crate) fn push(&mut self, row: usize, value: Fr) -> Result<(), Error> {
        if self.row.is_some_and(|old| old > row) { return Err(Error::Order(row)); }
        if self.row != Some(row) { self.finish()?; self.row = Some(row); self.residual = Fr::zero(); }
        self.residual += value; Ok(())
    }
    pub(crate) fn finish(&self) -> Result<(), Error> {
        if self.residual.is_zero() { Ok(()) }
        else { Err(Error::Residual(self.row.expect("nonempty residual"))) }
    }
}

pub(crate) struct Cache { tables: Vec<Box<[Fr]>>, bits: usize }
impl Cache {
    pub(crate) fn new(point: &[Fr], work: &mut Work) -> Result<Self, Error> {
        if point.len() > INPUT_BITS { return Err(Error::Point); }
        let mut tables = Vec::with_capacity(point.len().div_ceil(9));
        for chunk in point.chunks(9) {
            let table = gkr::eq_weights(chunk);
            if table.len() != 1usize << chunk.len() || table.capacity() > 512 { return Err(Error::Resource); }
            add(&mut work.cache_muls, 2 * (table.len() - 1))?;
            tables.push(table.into_boxed_slice());
        }
        Ok(Self { tables, bits: point.len() })
    }
    pub(crate) fn checked_at(&self, index: usize) -> Result<Fr, Error> {
        if index >= 1usize << self.bits { return Err(Error::Point); }
        Ok(self.at(index))
    }
    fn at(&self, index: usize) -> Fr {
        let Some(first) = self.tables.first() else { return Fr::one(); };
        let mut result = first[index & (first.len() - 1)];
        for (j, table) in self.tables.iter().enumerate().skip(1) {
            result *= table[(index >> (9 * j)) & (table.len() - 1)];
        }
        result
    }
    pub(crate) fn bytes(&self) -> usize {
        self.tables.iter().map(|t| t.len() * std::mem::size_of::<Fr>()).sum::<usize>()
            + self.tables.capacity() * std::mem::size_of::<Box<[Fr]>>() + std::mem::size_of::<Self>()
    }
}
fn peak(work: &mut Work, caches: &[&Cache]) -> Result<(), Error> {
    let bytes = caches.iter().map(|c| c.bytes()).sum::<usize>() + 256 * std::mem::size_of::<Fr>();
    if bytes > 131072 { return Err(Error::Resource); }
    work.cache_modeled_peak_bytes = work.cache_modeled_peak_bytes.max(bytes as u64); Ok(())
}

pub(crate) fn folded(bits: &Bits, start: usize, point: &[Fr], work: &mut Work) -> Result<Fr, Error> {
    if point.len() > INPUT_BITS || start.checked_add(1usize << point.len()).is_none_or(|end| end > INPUTS) {
        return Err(Error::Point);
    }
    fn recurse(bits: &Bits, start: usize, point: &[Fr], work: &mut Work) -> Result<Fr, Error> {
        if point.is_empty() { add(&mut work.fold_leaves, 1)?; return Ok(bits.bit(start)); }
        let j = point.len() - 1;
        let lo = recurse(bits, start, &point[..j], work)?;
        let hi = recurse(bits, start + (1usize << j), &point[..j], work)?;
        add(&mut work.fold_muls, 1)?; Ok(lo + (hi - lo) * point[j])
    }
    recurse(bits, start, point, work)
}

fn fill(source: &Source<'_, '_>, bits: &Bits, row: &Cache, left: Option<(&Cache, Fr)>,
    prefix: &Cache, j: usize, start: usize, a: &mut [Fr], b: &mut [Fr], work: &mut Work)
    -> Result<(), Error> {
    if prefix.bits != j || a.len() != b.len() { return Err(Error::Point); }
    a.fill(Fr::zero()); b.fill(Fr::zero());
    source.visit(|term| {
        add(&mut work.fill_term_visits, 1)?;
        let g = &term.gate; let axis = if left.is_some() { g.right } else { g.left };
        let key = axis >> j;
        if key < start || key >= start + a.len() { return Ok(()); }
        add(&mut work.weighted_terms, 1)?;
        let weight = row.at(term.row) * prefix.at(axis); let k = key - start;
        if let Some((u, value)) = left {
            let weight = weight * u.at(g.left);
            a[k] += weight * (g.c2 + g.c3 * value);
            b[k] += weight * (g.c0 + g.c1 * value);
        } else {
            let right = bits.bit(g.right);
            a[k] += weight * (g.c1 + g.c3 * right);
            b[k] += weight * (g.c0 + g.c2 * right);
        }
        Ok(())
    })
}

#[allow(clippy::too_many_arguments)]
fn phase(source: &Source<'_, '_>, bits: &Bits, row: &Cache, left: Option<(&Cache, Fr)>,
    a: &mut [Fr], b: &mut [Fr], x: &mut [Fr], claim: &mut Fr,
    rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript, work: &mut Work)
    -> Result<(Vec<Fr>, Fr), Error> {
    let mut point = Vec::with_capacity(INPUT_BITS); let mut value = Fr::zero();
    for j in 0..INPUT_BITS {
        let prefix = Cache::new(&point, work)?;
        if let Some((u, _)) = left { peak(work, &[row, u, &prefix])?; } else { peak(work, &[row, &prefix])?; }
        let len = INPUTS >> j; let mut message = [Fr::zero(); 3]; let mut ends = [Fr::zero(); 2];
        for start in (0..len).step_by(WINDOW) {
            let count = WINDOW.min(len - start);
            fill(source, bits, row, left, &prefix, j, start, &mut a[..count], &mut b[..count], work)?;
            for (k, out) in x[..count].iter_mut().enumerate() { *out = folded(bits, (start + k) << j, &point, work)?; }
            let m = crate::packed_gkr_window::quadratic(&a[..count], &b[..count], &x[..count]);
            for k in 0..3 { message[k] += m[k]; }
            if j + 1 == INPUT_BITS { ends.copy_from_slice(&x[..2]); }
        }
        if message[0] + gkr::eval_polynomial(&message, Fr::one()) != *claim { return Err(Error::Identity); }
        gkr::append_polynomial(transcript, b"gkr-sumcheck-polynomial", &message);
        let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        *claim = gkr::eval_polynomial(&message, challenge);
        point.push(challenge); rounds.push(message.to_vec());
        if j + 1 == INPUT_BITS { value = ends[0] + (ends[1] - ends[0]) * challenge; }
    }
    Ok((point, value))
}

pub(crate) fn terminal(source: &Source<'_, '_>, row: &Cache, u: &Cache, v: &Cache, work: &mut Work)
    -> Result<[Fr; 4], Error> {
    if row.bits != ROW_BITS || u.bits != INPUT_BITS || v.bits != INPUT_BITS { return Err(Error::Point); }
    let mut result = [Fr::zero(); 4];
    source.visit(|term| {
        add(&mut work.terminal_terms, 1)?;
        let g = &term.gate; let weight = row.at(term.row) * u.at(g.left) * v.at(g.right);
        for (out, coefficient) in result.iter_mut().zip([g.c0, g.c1, g.c2, g.c3]) { *out += weight * coefficient; }
        Ok(())
    })?; Ok(result)
}

pub(crate) fn line(bits: &Bits, u: &[Fr], v: &[Fr], work: &mut Work) -> Result<Vec<Fr>, Error> {
    if u.len() != INPUT_BITS || v.len() != INPUT_BITS { return Err(Error::Point); }
    let mut sum = [Fr::zero(); 23]; let mut product = [Fr::zero(); 23];
    for i in 0..INPUTS {
        add(&mut work.line_bits, 1)?;
        if bits.bit(i).is_zero() { continue; }
        add(&mut work.line_ones, 1)?; product.fill(Fr::zero()); product[0] = Fr::one();
        for j in 0..INPUT_BITS {
            let (constant, slope) = if (i >> j) & 1 == 0 { (Fr::one() - u[j], u[j] - v[j]) } else { (u[j], v[j] - u[j]) };
            for k in (0..=j + 1).rev() {
                product[k] = product[k] * constant + if k == 0 { Fr::zero() } else { product[k - 1] * slope };
                add(&mut work.line_updates, 1)?;
            }
        }
        for k in 0..=INPUT_BITS { sum[k] += product[k]; }
    }
    Ok(sum.to_vec())
}

pub(crate) fn prove(source: &Source<'_, '_>, bits: &Bits, transcript: &mut Transcript,
    bind: impl FnOnce(&mut Transcript)) -> Result<(GkrProof, InputClaim, Work), Error> {
    source.admit_frame(source.frame)?;
    let mut work = Work::default(); source.validate(&mut work)?; source.check(bits, &mut work)?;
    bind(transcript);
    let r = gkr::output_point(ROWS, transcript); gkr::append_usize(transcript, b"gkr-layer-index", 0);
    let row = Cache::new(&r, &mut work)?;
    let mut a = vec![Fr::zero(); WINDOW].into_boxed_slice();
    let mut b = vec![Fr::zero(); WINDOW].into_boxed_slice();
    let mut x = vec![Fr::zero(); WINDOW].into_boxed_slice();
    work.window_bytes = (3 * WINDOW * std::mem::size_of::<Fr>()) as u64;
    let mut claim = Fr::zero(); let mut rounds = Vec::with_capacity(2 * INPUT_BITS);
    let (u, l) = phase(source, bits, &row, None, &mut a, &mut b, &mut x, &mut claim, &mut rounds, transcript, &mut work)?;
    let uc = Cache::new(&u, &mut work)?;
    let (v, rr) = phase(source, bits, &row, Some((&uc, l)), &mut a, &mut b, &mut x, &mut claim, &mut rounds, transcript, &mut work)?;
    drop(a); drop(b); drop(x);
    let vc = Cache::new(&v, &mut work)?; peak(&mut work, &[&row, &uc, &vc])?;
    let w = terminal(source, &row, &uc, &vc, &mut work)?;
    if w[0] + w[1] * l + w[2] * rr + w[3] * l * rr != claim { return Err(Error::Terminal); }
    drop(row); drop(uc); drop(vc);
    let line_coefficients = line(bits, &u, &v, &mut work)?;
    if gkr::eval_polynomial(&line_coefficients, Fr::zero()) != l
        || gkr::eval_polynomial(&line_coefficients, Fr::one()) != rr { return Err(Error::Endpoints); }
    transcript.append_scalar(b"gkr-left-value", &l); transcript.append_scalar(b"gkr-right-value", &rr);
    gkr::append_polynomial(transcript, b"gkr-line-polynomial", &line_coefficients);
    let challenge = transcript.challenge_scalar(b"gkr-line-challenge");
    let input = InputClaim { point: gkr::line_point(&u, &v, challenge),
        value: gkr::eval_polynomial(&line_coefficients, challenge) };
    Ok((GkrProof { layers: vec![LayerProof { rounds, left_value: l, right_value: rr, line_coefficients }] }, input, work))
}

//! Fixed prefix difficulty outputs on existing decoded-work cells.
//! Common commitment/decoder verification is a separate required consumer.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::Gate, sparse::Term, transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self as layout, Endpoints, WIDTH}};

const COUNT: usize = 1088;
const BITS: usize = 224;
const ROW_LOG: usize = 19;
const DOMAIN: &[u8] = b"prefix-difficulty-context-modern-k64-row256-v1";

pub(crate) struct PrefixDifficultyContext<'a> {
    parent: &'a WorkTreeHistoryPlan,
    h: u64,
    first_leaf: usize,
    values: Vec<[u8; 28]>,
    work: [usize; BITS],
    map_fingerprint: String,
}

fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |a, (b, x)|
        a * if index & (1usize << b) == 0 { Fr::one() - x } else { *x })
}

impl<'a> PrefixDifficultyContext<'a> {
    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan, h: u64, values: Vec<[u8; 28]>)
        -> Result<Self, String>
    {
        let s = parent.slot_log();
        if WIDTH != 1 << 20 || !(2..=21).contains(&s)
            || parent.headers().checked_next_power_of_two() != Some(parent.slots() as u64)
            || parent.slots() != 1usize << s || parent.headers() > i32::MAX as u64
            || 1usize.checked_shl((20 + s) as u32).is_none()
        { return Err("prefix context parent geometry rejected".into()); }
        if h < 845760 { return Err("prefix context requires modern checkpoint".into()); }
        let required = h.checked_add(64).ok_or("prefix context query overflow")?;
        if parent.headers() < required { return Err("prefix context query is immature".into()); }
        if values.len() != COUNT { return Err("prefix context requires exactly 1088 values".into()); }
        if values.iter().any(|value| value.iter().all(|b| *b == 0)) {
            return Err("prefix context difficulty must be positive".into());
        }
        let first_leaf = usize::try_from(h.checked_sub(1089).ok_or("prefix context start underflow")?)
            .map_err(|_| "prefix context start overflow")?;
        let last_leaf = first_leaf.checked_add(COUNT - 1).ok_or("prefix context final leaf overflow")?;
        if last_leaf as u64 >= parent.headers() - 1 {
            return Err("prefix context source outside genuine work leaves".into());
        }
        let work: [usize; BITS] = Endpoints::new().work.try_into()
            .map_err(|_| "prefix context work map width changed")?;
        let input_len = 1usize << (20 + s);
        let last_base = last_leaf.checked_mul(WIDTH).ok_or("prefix context global base overflow")?;
        for wire in work {
            if wire >= WIDTH || last_base.checked_add(wire).filter(|i| *i < input_len).is_none() {
                return Err("prefix context source map outside input".into());
            }
        }
        let mut descriptor = b"prefix-context-decoded-work-map-row256-v1".to_vec();
        for value in [COUNT, BITS, ROW_LOG, 256, 20, s, first_leaf] {
            descriptor.extend_from_slice(&(value as u64).to_le_bytes());
        }
        for wire in work { descriptor.extend_from_slice(&(wire as u64).to_le_bytes()); }
        Ok(Self { parent, h, first_leaf, values, work,
            map_fingerprint: layout::hash_bytes(&descriptor) })
    }

    pub(crate) fn input_log(&self) -> usize { 20 + self.parent.slot_log() }
    pub(crate) fn row_log(&self) -> usize { ROW_LOG }
    pub(crate) fn first_height(&self) -> u64 { self.h - 1087 }
    pub(crate) fn values(&self) -> &[[u8; 28]] { &self.values }

    fn bit(&self, j: usize, b: usize) -> bool {
        (self.values[j][27 - b / 8] >> (b % 8)) & 1 == 1
    }

    /// One position at a time; never allocates the complete term list.
    pub(crate) fn visit_position_terms(&self, j: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<usize, String>
    {
        if j >= COUNT { return Err("prefix context position outside output".into()); }
        let base = (self.first_leaf + j) * WIDTH;
        for b in 0..BITS {
            sink(Term { row: (j << 8) + b, gate: Gate { left: base + self.work[b],
                right: 0, c0: -Fr::from(self.bit(j, b) as u64), c1: Fr::one(),
                c2: Fr::zero(), c3: Fr::zero() } })?;
        }
        Ok(BITS)
    }

    pub(crate) fn bind(&self, t: &mut Transcript) {
        t.append_bytes(b"prefix-context-profile", DOMAIN);
        for (tag, value) in [
            (b"prefix-context-version".as_slice(), 1),
            (b"prefix-context-h".as_slice(), self.h),
            (b"prefix-context-first-height".as_slice(), self.first_height()),
            (b"prefix-context-count".as_slice(), COUNT as u64),
            (b"prefix-context-work-bits".as_slice(), BITS as u64),
            (b"prefix-context-row-stride".as_slice(), 256),
            (b"prefix-context-row-log".as_slice(), ROW_LOG as u64),
            (b"prefix-context-input-log".as_slice(), self.input_log() as u64),
        ] { t.append_u64(tag, value); }
        for value in &self.values { t.append_bytes(b"prefix-context-difficulty-be28", value); }
        t.append_bytes(b"prefix-context-map-fingerprint", self.map_fingerprint.as_bytes());
        self.parent.bind(t);
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != ROW_LOG || u.len() != self.input_log() || v.len() != self.input_log() {
            return Err("prefix context coefficient dimensions rejected".into());
        }
        let right = eq(v, 0);
        let mut bit_weights = [Fr::zero(); BITS];
        let mut bit_sum = Fr::zero();
        for b in 0..BITS {
            bit_weights[b] = eq(&r[..8], b) * eq(&u[..20], self.work[b]);
            bit_sum += bit_weights[b];
        }
        let mut owner_sum = Fr::zero();
        let mut constant = Fr::zero();
        for j in 0..COUNT {
            let owner = eq(&r[8..], j) * eq(&u[20..], self.first_leaf + j);
            owner_sum += owner;
            if owner.is_zero() { continue; }
            let mut expected = Fr::zero();
            for (b, weight) in bit_weights.iter().enumerate() {
                if self.bit(j, b) { expected += weight; }
            }
            constant -= owner * expected;
        }
        Ok([right * constant, right * owner_sum * bit_sum, Fr::zero(), Fr::zero()])
    }
}

#[cfg(test)]
#[path = "prefix_difficulty_context_tests.rs"]
mod tests;

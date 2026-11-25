//! Selected M2 relations over four physical copies of one committed witness.
//! This profile supplies neither full-history coverage nor ancestry, hash-core
//! validation, curve membership or PoW. GKR claims require a separate PCS check.
use crate::{
    gkr::{self, GkrProof, InputClaim},
    short_daa_layout::Profile,
    short_header_history_boundary::ShortHeaderHistoryBoundary,
    sparse::Term,
    sparse_stream_roster::EdgeTerm,
    transcript::Transcript,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

pub(crate) const LOCAL_BITS: usize = 20;
pub(crate) const COPY_BITS: usize = 2;
pub(crate) const INPUT_BITS: usize = 22;
pub(crate) const ROW_BITS: usize = 23;
pub(crate) const BASE_ROWS: usize = 19;
pub(crate) const FAMILY_BITS: usize = 2;
pub(crate) const MEMBER_ROWS: [usize; 3] = [19, 17, 10];
pub(crate) const LOGICAL_SLOTS: [usize; 4] = [1023, 2047, 3071, 3072];
pub(crate) const DOMAIN: &[u8] = b"selected-m2-four-copy-common-relation-v1";
pub(crate) const TOTAL_TERMS: usize = 2_123_291;
const WIDTH: usize = 1 << LOCAL_BITS;
const CHILD_COPY: usize = 3;
const N: u64 = 3073;
const SLOT_LOG: usize = 12;
const HEADER_TERMS: usize = 474_755;
const ARITHMETIC_TERMS: usize = 232_175;
const ALIASES: usize = 288;
const LEFT_COUNTS: [usize; 4] = [474_819, 474_851, 474_851, 698_770];
const RIGHT_COUNTS: [usize; 4] = [474_755, 474_755, 474_755, 699_026];

pub(crate) struct Plan {
    header: ShortHeaderHistoryBoundary,
}
impl Plan {
    pub(crate) fn new() -> Result<Self, String> {
        let header = ShortHeaderHistoryBoundary::compile(Profile::M2, N, SLOT_LOG)?;
        let arithmetic = header.short_layout().mapped_relation();
        if arithmetic.input_len != WIDTH
            || arithmetic.row_count != 1 << MEMBER_ROWS[1]
            || arithmetic.terms.len() != ARITHMETIC_TERMS
            || LEFT_COUNTS.iter().sum::<usize>() != TOTAL_TERMS
            || RIGHT_COUNTS.iter().sum::<usize>() != TOTAL_TERMS
        {
            return Err("selected M2 canonical inventories changed".into());
        }
        let out = Self { header };
        out.visit_alias_edges(|_| Ok(()))?;
        Ok(out)
    }
    pub(crate) fn header(&self) -> &ShortHeaderHistoryBoundary {
        &self.header
    }
    pub(crate) fn bind(&self, t: &mut Transcript, setup_id: &[u8; 32], commitment: &[u8]) {
        t.append_bytes(b"selected-common-profile", DOMAIN);
        t.append_bytes(
            b"selected-common-row-rule",
            b"member-local-copy-zero-pad-family-v1",
        );
        for (label, value) in [
            (b"logical-history-count".as_slice(), N),
            (b"logical-slot-bits", SLOT_LOG as u64),
            (b"physical-input-bits", INPUT_BITS as u64),
            (b"physical-row-bits", ROW_BITS as u64),
            (b"local-input-bits", LOCAL_BITS as u64),
            (b"physical-copy-bits", COPY_BITS as u64),
            (b"base-row-bits", BASE_ROWS as u64),
            (b"family-bits", FAMILY_BITS as u64),
            (b"child-copy", CHILD_COPY as u64),
            (b"total-terms", TOTAL_TERMS as u64),
            (b"retained-header-terms", (4 * HEADER_TERMS - 8192) as u64),
            (b"arithmetic-terms", ARITHMETIC_TERMS as u64),
            (b"alias-terms", ALIASES as u64),
        ] {
            t.append_u64(label, value);
        }
        for (copy, logical) in LOGICAL_SLOTS.iter().enumerate() {
            t.append_u64(b"physical-copy", copy as u64);
            t.append_u64(b"logical-slot", *logical as u64);
            t.append_u64(b"left-count", LEFT_COUNTS[copy] as u64);
            t.append_u64(b"right-count", RIGHT_COUNTS[copy] as u64);
        }
        for (family, rows) in MEMBER_ROWS.iter().enumerate() {
            t.append_u64(b"family-index", family as u64);
            t.append_u64(b"member-row-bits", *rows as u64);
        }
        self.header.bind(t);
        t.append_bytes(b"setup-id", setup_id);
        t.append_bytes(b"common-commitment", commitment);
    }
    fn translate(&self, wire: usize) -> Result<usize, String> {
        let logical = wire / WIDTH;
        let copy = LOGICAL_SLOTS
            .iter()
            .position(|slot| *slot == logical)
            .ok_or("selected M2 endpoint absent from physical roster")?;
        copy.checked_mul(WIDTH)
            .and_then(|base| base.checked_add(wire % WIDTH))
            .ok_or_else(|| "selected M2 endpoint offset overflow".into())
    }
    fn visit_alias_edges(
        &self,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        let row_base = LOGICAL_SLOTS[CHILD_COPY] << MEMBER_ROWS[2];
        let mut seen = 0;
        let count = self.header.short_layout().visit_alias_terms(|mut term| {
            let index = term
                .row
                .checked_sub(row_base)
                .ok_or("alias row underflow")?;
            if index != seen || index >= ALIASES || term.gate.right / WIDTH != LOGICAL_SLOTS[3] {
                return Err("selected M2 alias inventory or row owner changed".into());
            }
            term.gate.left = self.translate(term.gate.left)?;
            term.gate.right = self.translate(term.gate.right)?;
            let family_row = (2 << BASE_ROWS) + index;
            term.row = family_row;
            sink(EdgeTerm {
                source_slot: CHILD_COPY,
                family_row,
                term,
            })?;
            seen += 1;
            Ok(())
        })?;
        if count != ALIASES || seen != ALIASES {
            return Err("selected M2 alias count changed".into());
        }
        Ok(())
    }
    pub(crate) fn visit_endpoint(
        &self,
        left: bool,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if copy >= LOGICAL_SLOTS.len() {
            return Err("selected M2 physical copy outside domain".into());
        }
        let logical = LOGICAL_SLOTS[copy];
        let row_base = logical
            .checked_mul(1 << MEMBER_ROWS[0])
            .ok_or("header row overflow")?;
        let input_base = logical.checked_mul(WIDTH).ok_or("header input overflow")?;
        let mut emitted = 0usize;
        let mut emit = |edge| {
            sink(edge)?;
            emitted = emitted
                .checked_add(1)
                .ok_or("selected M2 emission overflow")?;
            Ok(())
        };
        let counts = self.header.visit_slot_terms(logical as u64, |mut term| {
            let family_row = term
                .row
                .checked_sub(row_base)
                .ok_or("header row underflow")?;
            if family_row >= 1 << MEMBER_ROWS[0] {
                return Err("selected M2 header row escapes member".into());
            }
            for endpoint in [&mut term.gate.left, &mut term.gate.right] {
                let local = endpoint
                    .checked_sub(input_base)
                    .ok_or("header endpoint underflow")?;
                if local >= WIDTH {
                    return Err("selected M2 header endpoint escapes copy".into());
                }
                *endpoint = copy * WIDTH + local;
            }
            term.row = family_row;
            emit(EdgeTerm {
                source_slot: copy,
                family_row,
                term,
            })
        })?;
        let released = if copy == CHILD_COPY { 8192 } else { 0 };
        if counts.omitted_mature_a4 != 0
            || counts.omitted_short_a4 != released
            || counts.emitted != HEADER_TERMS - released
        {
            return Err("selected M2 header release/count changed".into());
        }
        if copy == CHILD_COPY {
            for source in &self.header.short_layout().mapped_relation().terms {
                if source.row >= 1 << MEMBER_ROWS[1]
                    || source.gate.left >= WIDTH
                    || source.gate.right >= WIDTH
                {
                    return Err("selected M2 arithmetic escapes member".into());
                }
                let mut term: Term = source.clone();
                let family_row = (1 << BASE_ROWS) + source.row;
                term.row = family_row;
                term.gate.left += copy * WIDTH;
                term.gate.right += copy * WIDTH;
                emit(EdgeTerm {
                    source_slot: copy,
                    family_row,
                    term,
                })?;
            }
        }
        self.visit_alias_edges(|edge| {
            let endpoint = if left {
                edge.term.gate.left
            } else {
                edge.term.gate.right
            };
            if endpoint / WIDTH == copy {
                emit(edge)?;
            }
            Ok(())
        })?;
        if emitted
            != if left {
                LEFT_COUNTS[copy]
            } else {
                RIGHT_COUNTS[copy]
            }
        {
            return Err("selected M2 endpoint inventory changed".into());
        }
        Ok(())
    }
    // Factories are consumer-owned. No emitted edge set is accepted here.
    pub(crate) fn parts(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[[Fr; 4]; 3], String> {
        if r.len() != ROW_BITS || u.len() != INPUT_BITS || v.len() != INPUT_BITS {
            return Err("selected M2 coefficient dimensions rejected".into());
        }
        let mut header = [Fr::zero(); 4];
        for (copy, logical) in LOGICAL_SLOTS.iter().enumerate() {
            let weight =
                eq(&r[21..], 0) * eq(&r[19..21], copy) * eq(&u[20..], copy) * eq(&v[20..], copy);
            if weight.is_zero() {
                continue;
            }
            let fixed = boolean(*logical, SLOT_LOG);
            let c = self.header.coefficients(
                &with_suffix(&r[..19], &fixed),
                &with_suffix(&u[..20], &fixed),
                &with_suffix(&v[..20], &fixed),
            )?;
            for i in 0..4 {
                header[i] += weight * c[i];
            }
        }
        let child = boolean(LOGICAL_SLOTS[3], SLOT_LOG);
        let mut arithmetic = [Fr::zero(); 4];
        let weight = eq(&r[21..], 1)
            * eq(&r[17..19], 3)
            * eq(&r[19..21], 0)
            * eq(&u[20..], 3)
            * eq(&v[20..], 3);
        if !weight.is_zero() {
            arithmetic = self.header.short_layout().arithmetic_coefficients(
                &with_suffix(&r[..17], &child),
                &with_suffix(&u[..20], &child),
                &with_suffix(&v[..20], &child),
            )?;
            for c in &mut arithmetic {
                *c *= weight;
            }
        }
        let mut alias = [Fr::zero(); 4];
        for (copy, logical) in LOGICAL_SLOTS.iter().enumerate() {
            let weight = eq(&r[21..], 2)
                * eq(&r[10..12], 3)
                * eq(&r[12..21], 0)
                * eq(&u[20..], copy)
                * eq(&v[20..], 3);
            if weight.is_zero() {
                continue;
            }
            let c = self.header.short_layout().alias_coefficients(
                &with_suffix(&r[..10], &child),
                &with_suffix(&u[..20], &boolean(*logical, SLOT_LOG)),
                &with_suffix(&v[..20], &child),
            )?;
            for i in 0..4 {
                alias[i] += weight * c[i];
            }
        }
        Ok([header, arithmetic, alias])
    }
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let parts = self.parts(r, u, v)?;
        Ok(std::array::from_fn(|i| {
            parts[0][i] + parts[1][i] + parts[2][i]
        }))
    }
    /// Verifies the relation only. Caller must verify the continued PCS opening.
    pub(crate) fn verify_gkr(
        &self,
        proof: &GkrProof,
        setup_id: &[u8; 32],
        commitment: &[u8],
    ) -> Result<(InputClaim, Transcript), String> {
        let mut t = Transcript::new(DOMAIN);
        let claim = gkr::verify_with_wiring(
            &[INPUT_BITS],
            1 << ROW_BITS,
            proof,
            &mut t,
            |t| self.bind(t, setup_id, commitment),
            |_layer, r, u, v| {
                self.coefficients(r, u, v)
                    .map_err(|_| gkr::GkrError::PointDimension)
            },
        )
        .map_err(|e| e.to_string())?;
        Ok((claim, t))
    }
}
pub(crate) fn boolean(index: usize, bits: usize) -> Vec<Fr> {
    (0..bits)
        .map(|bit| Fr::from(((index >> bit) & 1) as u64))
        .collect()
}
fn with_suffix(local: &[Fr], suffix: &[Fr]) -> Vec<Fr> {
    let mut point = local.to_vec();
    point.extend_from_slice(suffix);
    point
}
pub(crate) fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |a, (bit, x)| {
        a * if (index >> bit) & 1 == 1 {
            *x
        } else {
            Fr::one() - x
        }
    })
}

//! Code-owned full-header relation over the complete declared history domain.
//!
//! This is a bounded producer/consumer adapter. It does not authenticate a
//! chain, prove adjacency, or qualify a backend.
use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    daa_history_layout::{self, DaaHistoryLayout},
    daa_integer::Epoch,
    gkr::{self, GkrError},
    sparse::{self, Circuit, Term},
    transcript::Transcript,
    work_tree_layout,
};

const PROFILE: &[u8] = b"full-header-history-boundary-v1";
const VERSION: &[u8] = b"header-history-boundary-v1";
const RELEASE_RULE: &[u8] = b"code-owned-mature-legacy-eip-a4-only-v1";
const INPUT_BITS: usize = 20;
const ROW_BITS: usize = 19;
const SLOT_INPUTS: usize = 1 << INPUT_BITS;
const SLOT_ROWS: usize = 1 << ROW_BITS;
const CANONICAL_TERMS: usize = 474_755;
const A4_RELEASE_COUNT: usize = 8_192;
const CANONICAL_FINGERPRINT: &str =
    "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76";

/// Exact count from one slot's complete relation traversal.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct EmissionCounts {
    pub(crate) emitted: usize,
    pub(crate) omitted_a4: usize,
}

/// Immutable history-wide projection and its two code-owned release layouts.
/// No caller-controlled template, release range, or callback enters this plan.
pub(crate) struct HeaderHistoryBoundary {
    history_slots: u64,
    slot_log: usize,
    fingerprint: String,
    boundary: Circuit,
    boundary_shape: sparse::Shape,
    legacy: DaaHistoryLayout,
    eip: DaaHistoryLayout,
}

impl HeaderHistoryBoundary {
    pub(crate) fn compile(history_slots: u64, slot_log: usize) -> Result<Self, String> {
        if history_slots == 0 || slot_log > 21 || history_slots > i32::MAX as u64 {
            return Err("header history dimensions exceed the fixed profile".into());
        }
        let domain = 1u64
            .checked_shl(slot_log as u32)
            .ok_or("header history domain overflow")?;
        if history_slots > domain {
            return Err("header history exceeds its declared power-of-two domain".into());
        }

        // All external dimensions are rejected before any large template build.
        let canonical = daa_history_layout::full_header_boundary(None)?;
        let source = &canonical.base.base.base.boundary;
        let fingerprint = work_tree_layout::hash_terms(&source.terms);
        if source.input_len != SLOT_INPUTS
            || source.row_count != SLOT_ROWS
            || source.terms.len() != CANONICAL_TERMS
            || fingerprint != CANONICAL_FINGERPRINT
            || source
                .terms
                .windows(2)
                .any(|pair| pair[0].row > pair[1].row)
        {
            return Err("canonical full-header boundary fingerprint or shape changed".into());
        }
        let boundary_shape = sparse::validate(source, 0)
            .map_err(|error| format!("canonical boundary shape rejected: {error:?}"))?;

        let legacy = DaaHistoryLayout::compile(Epoch::Legacy, history_slots, slot_log)?;
        let eip = DaaHistoryLayout::compile(Epoch::Eip, history_slots, slot_log)?;
        if legacy.a4_anchor_rows() != (348_440..356_632)
            || eip.a4_anchor_rows() != (348_440..356_632)
        {
            return Err("canonical A4 anchor range changed".into());
        }
        Ok(Self {
            history_slots,
            slot_log,
            fingerprint,
            boundary: source.clone(),
            boundary_shape,
            legacy,
            eip,
        })
    }

    fn domain_len(&self) -> u64 {
        1u64 << self.slot_log
    }

    pub(crate) fn releases_anchor(&self, slot: u64, row: usize) -> bool {
        self.legacy.releases_anchor(slot, row) || self.eip.releases_anchor(slot, row)
    }

    /// Visit one complete physical slot. Invalid slots fail before `sink` is
    /// called, and all endpoint/row translations use checked arithmetic.
    pub(crate) fn visit_slot_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<EmissionCounts, String> {
        if slot >= self.domain_len() {
            return Err("header slot is outside the declared power-of-two domain".into());
        }
        let row_base = usize::try_from(slot)
            .ok()
            .and_then(|value| value.checked_mul(SLOT_ROWS))
            .ok_or("header row offset overflow")?;
        let input_base = usize::try_from(slot)
            .ok()
            .and_then(|value| value.checked_mul(SLOT_INPUTS))
            .ok_or("header input offset overflow")?;
        let mut counts = EmissionCounts::default();
        for (source_ordinal, term) in self.boundary.terms.iter().enumerate() {
            if self.releases_anchor(slot, term.row) {
                counts.omitted_a4 = counts
                    .omitted_a4
                    .checked_add(1)
                    .ok_or("omitted A4 count overflow")?;
                continue;
            }
            let row = row_base
                .checked_add(term.row)
                .ok_or("global header row overflow")?;
            let left = input_base
                .checked_add(term.gate.left)
                .ok_or("global left endpoint overflow")?;
            let right = input_base
                .checked_add(term.gate.right)
                .ok_or("global right endpoint overflow")?;
            let mut translated = term.clone();
            translated.row = row;
            translated.gate.left = left;
            translated.gate.right = right;
            #[cfg(test)]
            crate::c425_span_census::with_source_ordinal(source_ordinal, || sink(translated))?;
            #[cfg(not(test))]
            sink(translated)?;
            counts.emitted = counts
                .emitted
                .checked_add(1)
                .ok_or("emitted term count overflow")?;
        }
        let expected_omitted = if counts.omitted_a4 == 0 {
            0
        } else {
            A4_RELEASE_COUNT
        };
        if counts.omitted_a4 != expected_omitted
            || counts.emitted + counts.omitted_a4 != CANONICAL_TERMS
        {
            return Err("slot traversal term or A4 release count changed".into());
        }
        Ok(counts)
    }

    /// Analytic full-history coefficient consumer. Slot dimensions are the
    /// high LSB-first coordinates; no history-slot enumeration occurs here.
    fn evaluate_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let expected_rows = ROW_BITS
            .checked_add(self.slot_log)
            .ok_or("header row dimension overflow")?;
        let expected_inputs = INPUT_BITS
            .checked_add(self.slot_log)
            .ok_or("header input dimension overflow")?;
        if r.len() != expected_rows || u.len() != expected_inputs || v.len() != expected_inputs {
            return Err("full-header coefficient point dimensions rejected".into());
        }
        let mut result = sparse::wiring(
            &self.boundary,
            &self.boundary_shape,
            &r[..ROW_BITS],
            &u[..INPUT_BITS],
            &v[..INPUT_BITS],
        )
        .map_err(|error| format!("canonical boundary wiring rejected: {error:?}"))?;
        let extension = same_slot_extension(&r[ROW_BITS..], &u[INPUT_BITS..], &v[INPUT_BITS..]);
        for coefficient in &mut result {
            *coefficient *= extension;
        }
        result[1] -= self.legacy.a4_release_coefficient(r, u, v)?;
        result[1] -= self.eip.a4_release_coefficient(r, u, v)?;
        Ok(result)
    }

    pub(crate) fn fingerprint(&self) -> &str {
        &self.fingerprint
    }

    /// Immutable local template for code-owned downstream adapters.
    pub(crate) fn canonical_circuit(&self) -> &Circuit {
        &self.boundary
    }

    pub(crate) fn history_slots(&self) -> u64 {
        self.history_slots
    }

    pub(crate) fn slot_log(&self) -> usize {
        self.slot_log
    }

    /// Share the already admitted immutable mature template with the roster.
    pub(crate) fn mature_layout(&self, epoch: Epoch) -> &DaaHistoryLayout {
        match epoch {
            Epoch::Legacy => &self.legacy,
            Epoch::Eip => &self.eip,
        }
    }

    #[cfg(test)]
    pub(crate) fn eip_arithmetic_terms(&self) -> &[Term] {
        &self.eip.mapped_relation().terms
    }

    #[cfg(test)]
    pub(crate) fn eip_arithmetic_fingerprint(&self) -> String {
        work_tree_layout::hash_terms(&self.eip.mapped_relation().terms)
    }

    #[cfg(test)]
    pub(crate) fn eip_arithmetic_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        self.eip.arithmetic_coefficients(r, u, v)
    }

    #[cfg(test)]
    pub(crate) fn eip_is_mature_at(&self, slot: u64) -> bool {
        self.eip.releases_anchor(slot, 348_440)
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        self.evaluate_coefficients(r, u, v)
    }

    /// Restrict the family to an aligned pair. The pair's free slot bit is
    /// inserted before the fixed prefix bits in every LSB-first point.
    pub(crate) fn pair_coefficients(
        &self,
        pair_start: u64,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        self.validate_pair(pair_start)?;
        if r.len() != ROW_BITS + 1 || u.len() != INPUT_BITS + 1 || v.len() != INPUT_BITS + 1 {
            return Err("two-slot coefficient point dimensions rejected".into());
        }
        let mut full_r = r[..ROW_BITS].to_vec();
        let mut full_u = u[..INPUT_BITS].to_vec();
        let mut full_v = v[..INPUT_BITS].to_vec();
        full_r.push(r[ROW_BITS]);
        full_u.push(u[INPUT_BITS]);
        full_v.push(v[INPUT_BITS]);
        let fixed = pair_start >> 1;
        for bit in 0..(self.slot_log - 1) {
            let value = Fr::from((fixed >> bit) & 1);
            full_r.push(value);
            full_u.push(value);
            full_v.push(value);
        }
        self.evaluate_coefficients(&full_r, &full_u, &full_v)
    }

    pub(crate) fn validate_pair(&self, pair_start: u64) -> Result<(), String> {
        let end = pair_start
            .checked_add(2)
            .ok_or("pair slot bound overflow")?;
        if self.slot_log == 0
            || pair_start & 1 != 0
            || end > self.history_slots
            || end > self.domain_len()
        {
            return Err("two-slot pair is not aligned or is outside history bounds".into());
        }
        Ok(())
    }

    fn pair_circuit(&self, pair_start: u64) -> Result<Circuit, String> {
        self.validate_pair(pair_start)?;
        let pair_row_base = usize::try_from(pair_start)
            .ok()
            .and_then(|value| value.checked_mul(SLOT_ROWS))
            .ok_or("pair row base overflow")?;
        let pair_input_base = usize::try_from(pair_start)
            .ok()
            .and_then(|value| value.checked_mul(SLOT_INPUTS))
            .ok_or("pair input base overflow")?;
        let capacity = CANONICAL_TERMS
            .checked_mul(2)
            .ok_or("pair term capacity overflow")?;
        let mut terms = Vec::with_capacity(capacity);
        let mut omitted_a4 = 0usize;
        for slot in pair_start..pair_start + 2 {
            let counts = self.visit_slot_terms(slot, |mut term| {
                term.row = term
                    .row
                    .checked_sub(pair_row_base)
                    .ok_or("pair row precedes its local base")?;
                term.gate.left = term
                    .gate
                    .left
                    .checked_sub(pair_input_base)
                    .ok_or("pair left endpoint precedes its local base")?;
                term.gate.right = term
                    .gate
                    .right
                    .checked_sub(pair_input_base)
                    .ok_or("pair right endpoint precedes its local base")?;
                terms.push(term);
                Ok(())
            })?;
            omitted_a4 = omitted_a4
                .checked_add(counts.omitted_a4)
                .ok_or("pair A4 omission count overflow")?;
        }
        let expected_terms = CANONICAL_TERMS
            .checked_mul(2)
            .and_then(|total| total.checked_sub(omitted_a4))
            .ok_or("two-slot emitted term count overflow")?;
        if terms.len() != expected_terms {
            return Err("two-slot sparse term count changed".into());
        }
        let circuit = Circuit {
            input_len: 1usize << (INPUT_BITS + 1),
            row_count: 1usize << (ROW_BITS + 1),
            terms,
        };
        sparse::validate(&circuit, 0)
            .map_err(|error| format!("two-slot sparse circuit rejected: {error:?}"))?;
        Ok(circuit)
    }
}

fn same_slot_extension(r: &[Fr], u: &[Fr], v: &[Fr]) -> Fr {
    r.iter().zip(u).zip(v).fold(Fr::one(), |acc, ((r, u), v)| {
        acc * ((Fr::one() - r) * (Fr::one() - u) * (Fr::one() - v) + *r * u * v)
    })
}

fn bind_pair_statement(
    history_slots: u64,
    slot_log: usize,
    pair_start: u64,
    fingerprint: &str,
    transcript: &mut Transcript,
) {
    transcript.append_bytes(b"header-history-profile", PROFILE);
    transcript.append_bytes(b"header-history-version", VERSION);
    gkr::append_usize(
        transcript,
        b"header-history-pair-input-bits",
        INPUT_BITS + 1,
    );
    gkr::append_usize(transcript, b"header-history-pair-row-bits", ROW_BITS + 1);
    gkr::append_usize(transcript, b"header-history-slot-log", slot_log);
    gkr::append_usize(
        transcript,
        b"header-history-slot-count",
        history_slots as usize,
    );
    gkr::append_usize(
        transcript,
        b"header-history-pair-start",
        pair_start as usize,
    );
    transcript.append_bytes(b"header-history-fingerprint", fingerprint.as_bytes());
    transcript.append_bytes(b"header-history-release-rule", RELEASE_RULE);
}

fn map_gkr_error(_: String) -> GkrError {
    GkrError::PointDimension
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{
        daa_header_window::{self, Action},
        daa_history_layout,
        sparse::Circuit,
    };

    fn scalar(value: u64) -> Fr {
        Fr::from(value)
    }

    fn challenge(bits: usize, seed: u64) -> Vec<Fr> {
        (0..bits)
            .map(|index| scalar(seed + (index as u64 + 1) * 17))
            .collect()
    }

    fn set_boolean_suffix(point: &mut [Fr], local_bits: usize, value: u64) {
        for bit in 0..point.len() - local_bits {
            point[local_bits + bit] = Fr::from((value >> bit) & 1);
        }
    }

    fn expected_mature_release(slot: u64, history_slots: u64, row: usize) -> bool {
        if slot >= history_slots || !(348_440..356_632).contains(&row) {
            return false;
        }
        let Ok(child) = u32::try_from(slot + 1) else {
            return false;
        };
        matches!(daa_header_window::for_child_height(child), Ok(plan)
            if plan.sample_heights().len() == 9
                && matches!(plan.action(), Action::Retarget(Epoch::Legacy | Epoch::Eip)))
    }

    fn local_coefficients(family: &HeaderHistoryBoundary, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        sparse::wiring(&family.boundary, &family.boundary_shape, r, u, v).unwrap()
    }

    #[test]
    fn invalid_slot_rejects_before_visiting_the_sink() {
        assert!(HeaderHistoryBoundary::compile(0, 0).is_err());
        assert!(HeaderHistoryBoundary::compile(1, 22).is_err());
        assert!(HeaderHistoryBoundary::compile(3, 1).is_err());
        let family = HeaderHistoryBoundary::compile(1, 0).unwrap();
        let calls = std::cell::Cell::new(0usize);
        assert!(family
            .visit_slot_terms(1, |_| {
                calls.set(calls.get() + 1);
                Ok(())
            })
            .is_err());
        assert_eq!(calls.get(), 0);
        let mut calls = 0usize;
        let rejected = family.visit_slot_terms(0, |_| {
            calls += 1;
            Err("sink rejected first term".into())
        });
        assert_eq!(rejected.unwrap_err(), "sink rejected first term");
        assert_eq!(calls, 1);
    }

    #[test]
    fn physical_slot_terms_match_the_complete_canonical_relation() {
        let history_slots = 844_674;
        let family = HeaderHistoryBoundary::compile(history_slots, 20).unwrap();
        assert_eq!(family.fingerprint(), CANONICAL_FINGERPRINT);
        let canonical = &daa_history_layout::full_header_boundary(None)
            .unwrap()
            .base
            .base
            .base
            .boundary;
        for slot in [
            0,
            9 * 1024 - 1,
            9 * 1024,
            417_791,
            417_792,
            417_793,
            844_672,
            844_673,
            (1 << 20) - 1,
        ] {
            let mut observed = Vec::new();
            let counts = family
                .visit_slot_terms(slot, |term| {
                    observed.push(term);
                    Ok(())
                })
                .unwrap();
            let mut expected = Vec::new();
            let expected_omitted = canonical
                .terms
                .iter()
                .filter(|term| expected_mature_release(slot, history_slots, term.row))
                .count();
            for source in &canonical.terms {
                if expected_mature_release(slot, history_slots, source.row) {
                    continue;
                }
                let mut term = source.clone();
                term.row += slot as usize * SLOT_ROWS;
                term.gate.left += slot as usize * SLOT_INPUTS;
                term.gate.right += slot as usize * SLOT_INPUTS;
                expected.push(term);
            }
            assert_eq!(counts.omitted_a4, expected_omitted);
            assert_eq!(counts.emitted, CANONICAL_TERMS - expected_omitted);
            assert_eq!(observed, expected, "physical slot {slot}");
            assert_eq!(
                expected_omitted,
                if matches!(slot, 9_216 | 844_672) {
                    A4_RELEASE_COUNT
                } else {
                    0
                },
                "only the code-owned mature child releases A4 in this sample"
            );
        }
    }

    #[test]
    fn history_prefix_threshold_and_symbolic_upper_slot_are_bounded() {
        for mature_slot in [9_216u64, 844_672] {
            let before = HeaderHistoryBoundary::compile(mature_slot, 20).unwrap();
            let after = HeaderHistoryBoundary::compile(mature_slot + 1, 20).unwrap();
            let before_count = before.visit_slot_terms(mature_slot, |_| Ok(())).unwrap();
            let after_count = after.visit_slot_terms(mature_slot, |_| Ok(())).unwrap();
            assert_eq!(before_count.omitted_a4, 0);
            assert_eq!(after_count.omitted_a4, A4_RELEASE_COUNT);

            let mut r = challenge(ROW_BITS + 20, 11);
            let mut u = challenge(INPUT_BITS + 20, 37);
            let mut v = challenge(INPUT_BITS + 20, 83);
            set_boolean_suffix(&mut r, ROW_BITS, mature_slot);
            set_boolean_suffix(&mut u, INPUT_BITS, mature_slot);
            set_boolean_suffix(&mut v, INPUT_BITS, mature_slot);
            let removed = Circuit {
                input_len: SLOT_INPUTS,
                row_count: SLOT_ROWS,
                terms: after
                    .boundary
                    .terms
                    .iter()
                    .filter(|term| (348_440..356_632).contains(&term.row))
                    .cloned()
                    .collect(),
            };
            assert_eq!(removed.terms.len(), A4_RELEASE_COUNT);
            let shape = sparse::validate(&removed, 0).unwrap();
            let reference = sparse::wiring(
                &removed,
                &shape,
                &r[..ROW_BITS],
                &u[..INPUT_BITS],
                &v[..INPUT_BITS],
            )
            .unwrap();
            assert!(!reference[1].is_zero());
            let before_coefficients = before.coefficients(&r, &u, &v).unwrap();
            let after_coefficients = after.coefficients(&r, &u, &v).unwrap();
            for coefficient in 0..4 {
                assert_eq!(
                    before_coefficients[coefficient] - after_coefficients[coefficient],
                    reference[coefficient],
                    "mature cutoff {mature_slot}, coefficient {coefficient}"
                );
            }
        }

        let high = HeaderHistoryBoundary::compile(844_674, 21).unwrap();
        let padding_slot = (1 << 20) + 123_457;
        let high_counts = high.visit_slot_terms(padding_slot, |_| Ok(())).unwrap();
        assert_eq!(high_counts.emitted, CANONICAL_TERMS);
        assert_eq!(high_counts.omitted_a4, 0);
        let local_r = challenge(ROW_BITS, 19);
        let local_u = challenge(INPUT_BITS, 43);
        let local_v = challenge(INPUT_BITS, 89);
        let mut high_r = local_r.clone();
        let mut high_u = local_u.clone();
        let mut high_v = local_v.clone();
        high_r.extend((0..21).map(|bit| Fr::from((padding_slot >> bit) & 1)));
        high_u.extend((0..21).map(|bit| Fr::from((padding_slot >> bit) & 1)));
        high_v.extend((0..21).map(|bit| Fr::from((padding_slot >> bit) & 1)));
        assert_eq!(
            high.coefficients(&high_r, &high_u, &high_v).unwrap(),
            local_coefficients(&high, &local_r, &local_u, &local_v)
        );
    }

    #[test]
    fn asymmetric_non_boolean_coefficients_match_an_explicit_two_slot_slice() {
        let family = HeaderHistoryBoundary::compile(2, 1).unwrap();
        let r = challenge(ROW_BITS + 1, 5);
        let u = challenge(INPUT_BITS + 1, 29);
        let v = challenge(INPUT_BITS + 1, 71);
        let actual = family.coefficients(&r, &u, &v).unwrap();
        let local = local_coefficients(&family, &r[..ROW_BITS], &u[..INPUT_BITS], &v[..INPUT_BITS]);
        let mut expected = [Fr::zero(); 4];
        for slot in 0..2 {
            let weight = if slot == 0 {
                (Fr::one() - r[ROW_BITS])
                    * (Fr::one() - u[INPUT_BITS])
                    * (Fr::one() - v[INPUT_BITS])
            } else {
                r[ROW_BITS] * u[INPUT_BITS] * v[INPUT_BITS]
            };
            for (out, coefficient) in expected.iter_mut().zip(local) {
                *out += coefficient * weight;
            }
        }
        assert_eq!(actual, expected);
        assert!(family.coefficients(&r[..ROW_BITS], &u, &v).is_err());
        assert!(family.coefficients(&r, &u[..INPUT_BITS], &v).is_err());
        assert!(family.pair_coefficients(1, &r, &u, &v).is_err());
    }

    #[test]
    fn pair_projection_preserves_all_terms_except_the_mature_a4_rows() {
        let family = HeaderHistoryBoundary::compile(844_674, 20).unwrap();
        let mature_carry = family.pair_circuit(844_672).unwrap();
        assert_eq!(mature_carry.input_len, 1 << 21);
        assert_eq!(mature_carry.row_count, 1 << 20);
        assert_eq!(mature_carry.terms.len(), 941_318);
        let non_mature = family.pair_circuit(844_544).unwrap();
        assert_eq!(non_mature.input_len, 1 << 21);
        assert_eq!(non_mature.row_count, 1 << 20);
        assert_eq!(non_mature.terms.len(), 2 * CANONICAL_TERMS);
        assert!(family.validate_pair(844_673).is_err());
        assert!(family.validate_pair(844_674).is_err());
    }

    #[test]
    fn legacy_and_eip_pair_consumers_match_the_emitted_sparse_circuits() {
        let family = HeaderHistoryBoundary::compile(844_674, 20).unwrap();
        let r = challenge(ROW_BITS + 1, 7);
        let u = challenge(INPUT_BITS + 1, 41);
        let v = challenge(INPUT_BITS + 1, 97);
        for pair_start in [9_216u64, 844_672] {
            let circuit = family.pair_circuit(pair_start).unwrap();
            let shape = sparse::validate(&circuit, 0).unwrap();
            let explicit = sparse::wiring(&circuit, &shape, &r, &u, &v).unwrap();
            let analytic = family.pair_coefficients(pair_start, &r, &u, &v).unwrap();
            assert_eq!(analytic, explicit, "pair start {pair_start}");
        }
    }

    #[test]
    fn mature_release_and_carry_retention_are_causal_on_a_real_nonzero_a4_cell() {
        let (fixture, headers) = fixture();
        let family = HeaderHistoryBoundary::compile(844_674, 20).unwrap();
        let mature = assignment_for_child(844_673, &fixture, &headers);
        let source = family
            .boundary
            .terms
            .iter()
            .find(|term| {
                (348_440..356_632).contains(&term.row)
                    && term.gate.c0.is_zero()
                    && term.gate.c1.is_one()
                    && term.gate.c2.is_zero()
                    && term.gate.c3.is_zero()
                    && !mature[term.gate.left].is_zero()
            })
            .expect("native mature DAA A4 bank has a nonzero anchored cell");
        let row_terms = family
            .boundary
            .terms
            .iter()
            .filter(|term| term.row == source.row)
            .collect::<Vec<_>>();
        assert_eq!(row_terms.as_slice(), &[source]);
        assert_eq!(source.gate.evaluate(&mature), Fr::one());

        let mut mature_emitted = Vec::new();
        family
            .visit_slot_terms(844_672, |term| {
                mature_emitted.push(term);
                Ok(())
            })
            .unwrap();
        let mature_global_row = 844_672usize * SLOT_ROWS + source.row;
        assert!(!mature_emitted
            .iter()
            .any(|term| term.row == mature_global_row));
        assert_ne!(source.gate.evaluate(&mature), Fr::zero());

        let mut carry_emitted = Vec::new();
        family
            .visit_slot_terms(844_673, |term| {
                carry_emitted.push(term);
                Ok(())
            })
            .unwrap();
        let carry_global_row = 844_673usize * SLOT_ROWS + source.row;
        let carry_term = carry_emitted
            .iter()
            .find(|term| term.row == carry_global_row)
            .expect("carry retains the exact A4 anchor row");
        let carry_row_terms = carry_emitted
            .iter()
            .filter(|term| term.row == carry_global_row)
            .collect::<Vec<_>>();
        assert_eq!(carry_row_terms.len(), 1);
        let mut isolated_carry = vec![Fr::zero(); SLOT_INPUTS];
        isolated_carry[source.gate.left] = Fr::one();
        assert_eq!(
            carry_term.gate.left,
            844_673usize * SLOT_INPUTS + source.gate.left
        );
        assert_eq!(source.gate.evaluate(&isolated_carry), Fr::one());
        let wrongly_released_residual = carry_row_terms
            .iter()
            .filter(|term| !std::ptr::eq(**term, carry_term))
            .fold(Fr::zero(), |sum, term| {
                let mut local_gate = term.gate.clone();
                local_gate.left -= 844_673usize * SLOT_INPUTS;
                local_gate.right -= 844_673usize * SLOT_INPUTS;
                sum + local_gate.evaluate(&isolated_carry)
            });
        assert!(wrongly_released_residual.is_zero());
    }

    #[derive(serde::Deserialize)]
    pub(crate) struct Fixture {
        cases: Vec<FixtureCase>,
        headers: Vec<FixtureHeader>,
    }

    #[derive(serde::Deserialize)]
    struct FixtureCase {
        child: u32,
        parent: u32,
        samples: Vec<u32>,
    }

    #[derive(serde::Deserialize)]
    struct FixtureHeader {
        height: u32,
        raw_hex: String,
    }

    const MAINNET_FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");

    pub(crate) fn fixture() -> (Fixture, std::collections::HashMap<u32, Vec<u8>>) {
        use ergo_header_core::Header;
        let fixture: Fixture = serde_json::from_str(MAINNET_FIXTURE).unwrap();
        let headers = fixture
            .headers
            .iter()
            .map(|header| {
                let raw = header
                    .raw_hex
                    .as_bytes()
                    .chunks_exact(2)
                    .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                    .collect::<Vec<_>>();
                assert_eq!(Header::decode(&raw, None).unwrap().height, header.height);
                (header.height, raw)
            })
            .collect();
        (fixture, headers)
    }

    fn selected_window(
        child: u32,
        fixture: &Fixture,
        headers: &std::collections::HashMap<u32, Vec<u8>>,
    ) -> crate::daa_header_window::SelectedWindow {
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == child)
            .unwrap();
        let samples: [&[u8]; 9] = case
            .samples
            .iter()
            .map(|height| headers.get(height).unwrap().as_slice())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        crate::daa_header_window::select_window(
            headers.get(&case.parent).unwrap(),
            headers.get(&child).unwrap(),
            &samples,
        )
        .unwrap()
    }

    pub(crate) fn assignment_for_child(
        child: u32,
        fixture: &Fixture,
        headers: &std::collections::HashMap<u32, Vec<u8>>,
    ) -> Vec<Fr> {
        use crate::{
            daa_count, daa_finish, daa_header_window, header_compact_links, mapped_daa_plan,
            serializer,
        };
        use ergo_header_core::Header;
        let child_header = Header::decode(headers.get(&child).unwrap(), None).unwrap();
        let parent = Header::decode(headers.get(&(child - 1)).unwrap(), None).unwrap();
        let fields = serializer::Fields::from_header(&child_header).unwrap();
        let mut boundary = daa_history_layout::full_header_boundary(Some(&fields)).unwrap();
        header_compact_links::assign_order(
            &mut boundary,
            &fields,
            child - 1,
            parent.timestamp,
            false,
        )
        .unwrap();

        match daa_header_window::for_child_height(child).unwrap().action() {
            Action::Retarget(epoch) => {
                let selected = selected_window(child, fixture, headers);
                let compiled = daa_finish::compile_finish_with_child(
                    epoch,
                    &daa_count::q(),
                    selected.prediction(),
                    selected.child_nbits(),
                    true,
                )
                .unwrap();
                let mapped = mapped_daa_plan::MappedDaaPlan::compile(&compiled).unwrap();
                let input = boundary.base.base.base.input.as_mut().unwrap();
                for (start, end) in mapped.phase_bank_ranges() {
                    input[start..end].copy_from_slice(&mapped.witness()[start..end]);
                }
                assert!(residuals(mapped.circuit(), input).iter().all(Zero::is_zero));
            }
            Action::Carry => {}
            Action::FixedV2 => panic!("the bounded fixture pair must not include a reset"),
        }
        boundary.base.base.base.input.take().unwrap()
    }

    fn residuals(circuit: &Circuit, input: &[Fr]) -> Vec<Fr> {
        let mut rows = vec![Fr::zero(); circuit.row_count];
        for term in &circuit.terms {
            rows[term.row] += term.gate.evaluate(input);
        }
        rows
    }

    fn unique_artifact_path(kind: &str) -> std::path::PathBuf {
        let root = std::env::var_os("NIPOPOW_HEADER_PAIR_DIR")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(std::env::temp_dir);
        assert!(root.is_dir(), "pair artifact directory must already exist");
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        root.join(format!(
            "header-pair-{kind}-{}-{stamp}.bin",
            std::process::id()
        ))
    }

    fn packed_bytes(input: &[Fr]) -> Vec<u8> {
        let mut bytes = vec![0u8; input.len().div_ceil(8)];
        for (index, value) in input.iter().enumerate() {
            if value.is_zero() {
                continue;
            }
            assert!(
                value.is_one(),
                "pair witness must be Boolean for packed MLE"
            );
            bytes[index / 8] |= 1 << (index % 8);
        }
        bytes
    }

    pub(crate) fn pair_statement(
        family: &HeaderHistoryBoundary,
        pair_start: u64,
        transcript: &mut Transcript,
    ) {
        bind_pair_statement(
            family.history_slots,
            family.slot_log,
            pair_start,
            &family.fingerprint,
            transcript,
        );
    }

    fn verify_pair(
        family: &HeaderHistoryBoundary,
        pair_start: u64,
        proof: &gkr::GkrProof,
        transcript: &mut Transcript,
        verifier_pair_start: u64,
    ) -> Result<gkr::InputClaim, GkrError> {
        family
            .validate_pair(verifier_pair_start)
            .map_err(map_gkr_error)?;
        gkr::verify_with_wiring(
            &[INPUT_BITS + 1],
            1 << (ROW_BITS + 1),
            proof,
            transcript,
            |transcript| pair_statement(family, pair_start, transcript),
            |_index, r, u, v| {
                family
                    .pair_coefficients(verifier_pair_start, r, u, v)
                    .map_err(map_gkr_error)
            },
        )
    }

    #[test]
    fn real_mainnet_mature_carry_pair_gkr_claim_mutants_and_packed_mle() {
        let started = std::time::Instant::now();
        let (fixture, headers) = fixture();
        let family = HeaderHistoryBoundary::compile(844_674, 20).unwrap();
        let pair_start = 844_672;
        let circuit = family.pair_circuit(pair_start).unwrap();
        assert_eq!(circuit.input_len, 1 << 21);
        assert_eq!(circuit.row_count, 1 << 20);
        assert_eq!(circuit.terms.len(), 941_318);

        let mut witness = assignment_for_child(844_673, &fixture, &headers);
        witness.extend(assignment_for_child(844_674, &fixture, &headers));
        assert_eq!(witness.len(), 1 << 21);
        for slot in 0..2 {
            let input = &witness[slot * SLOT_INPUTS..(slot + 1) * SLOT_INPUTS];
            let mut slot_terms = Vec::with_capacity(CANONICAL_TERMS);
            let counts = family
                .visit_slot_terms(pair_start + slot as u64, |term| {
                    let mut local = term;
                    local.row -= (pair_start as usize + slot) * SLOT_ROWS;
                    local.gate.left -= (pair_start as usize + slot) * SLOT_INPUTS;
                    local.gate.right -= (pair_start as usize + slot) * SLOT_INPUTS;
                    slot_terms.push(local);
                    Ok(())
                })
                .unwrap();
            assert_eq!(
                counts.omitted_a4,
                if slot == 0 { A4_RELEASE_COUNT } else { 0 }
            );
            let slot_relation = Circuit {
                input_len: SLOT_INPUTS,
                row_count: SLOT_ROWS,
                terms: slot_terms,
            };
            assert!(residuals(&slot_relation, input).iter().all(Zero::is_zero));
        }

        let packed_path = unique_artifact_path("packed");
        let mut packed_writer = crate::packed::PackedFileWriter::create_new(&packed_path, 21)
            .expect("create unique packed pair witness");
        packed_writer
            .write_bytes(&packed_bytes(&witness))
            .expect("write packed pair witness");
        let packed = packed_writer.finish().expect("finish packed pair witness");
        assert_eq!(std::fs::metadata(&packed_path).unwrap().len(), 262_144);

        let mut producer = Transcript::new(b"header-history-pair-gkr-v1");
        let (proof, producer_claim) =
            sparse::prove_with_binding(&circuit, &witness, 0, &mut producer, |transcript| {
                pair_statement(&family, pair_start, transcript)
            })
            .unwrap();
        let mut verifier = Transcript::new(b"header-history-pair-gkr-v1");
        let verifier_claim =
            verify_pair(&family, pair_start, &proof, &mut verifier, pair_start).unwrap();
        assert_eq!(producer_claim, verifier_claim);
        assert_eq!(
            packed.evaluate(&producer_claim.point).unwrap(),
            producer_claim.value
        );

        // Each mutant reuses the exact same proof and context binding. Only its
        // historical release coefficient changes.
        for mutant in ["release-omitted", "release-sign", "global-zero-endpoint"] {
            let mut transcript = Transcript::new(b"header-history-pair-gkr-v1");
            let result = gkr::verify_with_wiring(
                &[INPUT_BITS + 1],
                1 << (ROW_BITS + 1),
                &proof,
                &mut transcript,
                |transcript| pair_statement(&family, pair_start, transcript),
                |_index, r, u, v| {
                    let mut coefficients = family
                        .pair_coefficients(pair_start, r, u, v)
                        .map_err(map_gkr_error)?;
                    let full_r = embed_pair_point(&family, pair_start, r, ROW_BITS)?;
                    let full_u = embed_pair_point(&family, pair_start, u, INPUT_BITS)?;
                    let full_v = embed_pair_point(&family, pair_start, v, INPUT_BITS)?;
                    let release = family
                        .legacy
                        .a4_release_coefficient(&full_r, &full_u, &full_v)
                        .map_err(map_gkr_error)?
                        + family
                            .eip
                            .a4_release_coefficient(&full_r, &full_u, &full_v)
                            .map_err(map_gkr_error)?;
                    let wrong_release = match mutant {
                        "release-omitted" => Fr::zero(),
                        "release-sign" => -release,
                        "global-zero-endpoint" => global_zero_release_in_pair(pair_start, release),
                        _ => unreachable!(),
                    };
                    // Undo the correct c1 subtraction and install one isolated
                    // wrong release result; c0/c2/c3 and proof are unchanged.
                    coefficients[1] += release - wrong_release;
                    Ok(coefficients)
                },
            );
            assert_eq!(
                result.unwrap_err(),
                GkrError::TerminalExpression,
                "{mutant}"
            );
        }

        let mut prefix_transcript = Transcript::new(b"header-history-pair-gkr-v1");
        let prefix_mutant = gkr::verify_with_wiring(
            &[INPUT_BITS + 1],
            1 << (ROW_BITS + 1),
            &proof,
            &mut prefix_transcript,
            |transcript| pair_statement(&family, pair_start, transcript),
            |_index, r, u, v| {
                let wrong_r = embed_pair_point_with_prefix_flip(&family, pair_start, r, ROW_BITS)?;
                let wrong_u =
                    embed_pair_point_with_prefix_flip(&family, pair_start, u, INPUT_BITS)?;
                let wrong_v =
                    embed_pair_point_with_prefix_flip(&family, pair_start, v, INPUT_BITS)?;
                family
                    .coefficients(&wrong_r, &wrong_u, &wrong_v)
                    .map_err(map_gkr_error)
            },
        );
        assert_eq!(((pair_start >> 1) ^ 1) << 1, 844_674);
        assert_eq!(prefix_mutant.unwrap_err(), GkrError::TerminalExpression);

        let mut changed_context = Transcript::new(b"header-history-pair-gkr-v1");
        let changed = gkr::verify_with_wiring(
            &[INPUT_BITS + 1],
            1 << (ROW_BITS + 1),
            &proof,
            &mut changed_context,
            |transcript| pair_statement(&family, pair_start - 2, transcript),
            |_index, r, u, v| {
                family
                    .pair_coefficients(pair_start, r, u, v)
                    .map_err(map_gkr_error)
            },
        );
        assert_eq!(
            changed.unwrap_err(),
            GkrError::SumcheckIdentity,
            "changed context changes transcript challenges before the coefficient gate"
        );

        if std::env::var_os("NIPOPOW_HEADER_PAIR_DIR").is_some() {
            let proof_path = unique_artifact_path("proof");
            let receipt_path = unique_artifact_path("receipt");
            write_create_new(&proof_path, &gkr::encode_proof(&proof).unwrap());
            let receipt = serde_json::json!({
                "profile": String::from_utf8_lossy(PROFILE),
                "version": String::from_utf8_lossy(VERSION),
                "history_slots": family.history_slots,
                "slot_log": family.slot_log,
                "pair_start": pair_start,
                "full_boundary_fingerprint": family.fingerprint,
                "release_rule": String::from_utf8_lossy(RELEASE_RULE),
                "input_bits": 21,
                "row_bits": 20,
                "terms": 941318,
                "packed_bytes": 262144,
                "claim_value": producer_claim.value.to_string(),
                "elapsed_ms": started.elapsed().as_millis(),
                "authority_ceiling": "bounded GKR producer/consumer discriminator; no PCS, setup, chain, or complete-history proof"
            });
            write_create_new(&receipt_path, receipt.to_string().as_bytes());
        }
    }

    fn embed_pair_point(
        family: &HeaderHistoryBoundary,
        pair_start: u64,
        point: &[Fr],
        local_bits: usize,
    ) -> Result<Vec<Fr>, GkrError> {
        if point.len() != local_bits + 1 {
            return Err(GkrError::PointDimension);
        }
        let mut full = point[..local_bits].to_vec();
        full.push(point[local_bits]);
        let fixed = pair_start >> 1;
        for bit in 0..(family.slot_log - 1) {
            full.push(Fr::from((fixed >> bit) & 1));
        }
        Ok(full)
    }

    fn embed_pair_point_with_prefix_flip(
        family: &HeaderHistoryBoundary,
        pair_start: u64,
        point: &[Fr],
        local_bits: usize,
    ) -> Result<Vec<Fr>, GkrError> {
        let mut full = embed_pair_point(family, pair_start, point, local_bits)?;
        let fixed_prefix_start = local_bits + 1;
        full[fixed_prefix_start] = Fr::one() - full[fixed_prefix_start];
        Ok(full)
    }

    fn global_zero_release_in_pair(pair_start: u64, local_zero_release: Fr) -> Fr {
        let pair_input_base = usize::try_from(pair_start)
            .ok()
            .and_then(|slot| slot.checked_mul(SLOT_INPUTS));
        let Some(pair_input_base) = pair_input_base else {
            return Fr::zero();
        };
        match 0usize.checked_sub(pair_input_base) {
            Some(local_endpoint) if local_endpoint == 0 => local_zero_release,
            _ => Fr::zero(),
        }
    }

    fn write_create_new(path: &std::path::Path, bytes: &[u8]) {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .unwrap();
        file.write_all(bytes).unwrap();
        file.sync_all().unwrap();
    }
}

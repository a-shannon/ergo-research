//! Tagged role joining serialized height and native numeric DAA.
//!
//! The generic entry streams one owner and uses analytic selectors. The legacy
//! N3/N4 entry retains its 22-bit input and fixed materializer. Other DAA roles
//! enforce retarget arithmetic; this relation alone is not a history proof.

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    daa_work_actions::DaaWorkActions,
    gkr::Gate,
    header_height_layout::HeaderHeightLayout,
    sparse::{Circuit, Term},
    transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH,
};

const PROFILE_N3: &[u8] = b"historical-prefix-height-work-tagged-v1";
const PROFILE_N4: &[u8] = b"historical-prefix-height-work-tagged-n4-v1";
const PROFILE_HISTORY: &[u8] = b"historical-prefix-height-work-owner-stream-v1";
const VERSION: u64 = 1;
const SLOT_LOG: usize = 2;
const SLOTS: usize = 1 << SLOT_LOG;
const INPUT_LOG: usize = 22;
const INPUT_LEN: usize = 1 << INPUT_LOG;
const ROW_LOG: usize = 8;
const ROW_COUNT: usize = 1 << ROW_LOG;
const HEIGHT_LOCAL_ROW_LOG: usize = 5;
const HEIGHT_TAG: usize = 0;
const NUMERIC_TAG: usize = 1;
const HEIGHT_ROWS: usize = 1 << (HEIGHT_LOCAL_ROW_LOG + SLOT_LOG);
const NUMERIC_ROW_BASE: usize = HEIGHT_ROWS;
const N3_HEIGHT_TERMS: usize = 96;
const N3_NUMERIC_TERMS: usize = 673;
const N3_TOTAL_TERMS: usize = N3_HEIGHT_TERMS + N3_NUMERIC_TERMS;
const N4_HEIGHT_TERMS: usize = 128;
const N4_NUMERIC_TERMS: usize = 1121;
const N4_TOTAL_TERMS: usize = N4_HEIGHT_TERMS + N4_NUMERIC_TERMS;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct OwnerCounts {
    pub(crate) height: usize,
    pub(crate) numeric: usize,
}

/// Compiler-owned composite borrowing the same immutable history plan.
pub(crate) struct HeightWork<'a> {
    headers: u64,
    slot_log: usize,
    generic: bool,
    height: HeaderHeightLayout,
    numeric: DaaWorkActions<'a>,
}

impl<'a> HeightWork<'a> {
    pub(crate) fn check_history_endpoint_scope(&self) -> Result<(), String> {
        let parent = self.numeric.endpoint_parent();
        if !self.generic || self.headers < 3 || !(2..=21).contains(&self.slot_log)
            || self.headers > self.slots() as u64 || self.headers != parent.headers()
            || self.slot_log != parent.slot_log() || self.slots() != parent.slots() {
            return Err("history height endpoint mode or geometry".into());
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn history_endpoint_scope_controls_for_test(parent: &'a WorkTreeHistoryPlan) -> Result<usize, String> {
        let mut role = Self::compile_history(parent)?;
        for fault in 0..3 {
            let (headers,h,generic) = (role.headers,role.slot_log,role.generic);
            match fault { 0 => role.headers = if headers == 3 { 4 } else { headers - 1 },
                1 => role.slot_log += 1, _ => role.generic = false }
            if role.check_history_endpoint_scope().err().as_deref() != Some("history height endpoint mode or geometry") {
                return Err("history height isolated scope control".into());
            }
            role.headers=headers;role.slot_log=h;role.generic=generic;
        }
        role.check_history_endpoint_scope()?; Ok(3)
    }

    pub(crate) fn visit_history_endpoint_terms(&self, left: bool, slot: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<usize, String> {
        self.check_history_endpoint_scope()?;
        if slot >= self.slots() { return Err("history height endpoint owner".into()); }
        let mut count = 0usize;
        let mut send = |term: Term| {
            sink(term)?;
            count = count.checked_add(1).ok_or("history height endpoint count")?;
            Ok(())
        };
        if slot < self.headers as usize { self.height.visit_slot_terms(slot as u64, &mut send)?; }
        self.numeric.visit_endpoint_terms(left, slot, |mut term| {
            term.row = self.numeric_base().checked_add(term.row).ok_or("history height numeric row")?;
            send(term)
        })?;
        Ok(count)
    }

    pub(crate) fn endpoint_parent(&self) -> &WorkTreeHistoryPlan {self.numeric.endpoint_parent()}

    #[cfg(test)]
    pub(crate) fn visit_complete_s2_endpoint_terms(&self,left:bool,slot:usize,
        mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String> {
        if !self.generic || self.headers!=3 || self.slot_log!=2 || slot>=4 {
            return Err("height endpoint complete S2 scope rejected".into());
        }
        let mut count=0usize;
        if slot<self.headers as usize {
            count+=self.height.visit_slot_terms(slot as u64,&mut sink)?;
        }
        count+=self.numeric.visit_endpoint_terms(left,slot,|mut term| {
            term.row=self.numeric_base().checked_add(term.row).ok_or("height endpoint numeric row overflow")?;
            sink(term)
        })?;
        Ok(count)
    }

    #[cfg(test)]
    pub(crate) fn check_s12_endpoint_scope(&self)->Result<(),String> {
        if !self.generic || self.headers!=3073 || self.slot_log!=12 {
            return Err("height endpoint whole S12 scope rejected".into());
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn visit_s12_endpoint_terms(&self,left:bool,slot:usize,
        mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String> {
        self.check_s12_endpoint_scope()?;
        if slot>=4096 {return Err("height S12 endpoint owner rejected".into());}
        let mut count=0;
        if slot<3073 {count+=self.height.visit_slot_terms(slot as u64,&mut sink)?;}
        count+=self.numeric.visit_endpoint_terms(left,slot,|mut term| {
            term.row=self.numeric_base().checked_add(term.row).ok_or("height S12 numeric row overflow")?;
            sink(term)
        })?;
        Ok(count)
    }

    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan) -> Result<Self, String> {
        let headers = parent.headers();
        if !matches!(headers, 3 | 4) || parent.slot_log() != SLOT_LOG || parent.slots() != SLOTS {
            return Err("height/work role requires a fixed N3/N4/S4 profile".into());
        }
        let mut role = Self::compile_history(parent)?;
        role.generic = false;
        Ok(role)
    }

    /// No owner masks, decoded values or endpoint maps are caller supplied.
    pub(crate) fn compile_history(parent: &'a WorkTreeHistoryPlan) -> Result<Self, String> {
        let headers = parent.headers();
        let slot_log = parent.slot_log();
        if headers < 3 || !(2..=21).contains(&slot_log)
            || parent.slots() != 1usize << slot_log
            || headers > parent.slots() as u64
            || 1usize.checked_shl((20 + slot_log) as u32).is_none()
            || 1usize.checked_shl((6 + slot_log) as u32).is_none()
        {
            return Err("height/work generic parent geometry rejected".into());
        }
        if WIDTH != 1 << 20 {
            return Err("height/work global input geometry changed".into());
        }
        let height = HeaderHeightLayout::compile(headers, slot_log)?;
        let numeric = DaaWorkActions::new(parent)?;
        if height.fingerprint().is_empty()
            || numeric.row_log() != slot_log
            || numeric.input_log() != 20 + slot_log
        {
            return Err("height/work producer dimensions or fingerprint changed".into());
        }
        Ok(Self {
            headers,
            slot_log,
            generic: true,
            height,
            numeric,
        })
    }

    pub(crate) fn input_log(&self) -> usize { 20 + self.slot_log }
    pub(crate) fn row_log(&self) -> usize { 6 + self.slot_log }
    pub(crate) fn slots(&self) -> usize { 1usize << self.slot_log }
    fn numeric_base(&self) -> usize { 32 * self.slots() }

    /// Bounded emission: at most 32 height plus 448 numeric terms per owner.
    /// Padding emits nothing; an out-of-domain owner rejects before the sink.
    pub(crate) fn visit_owner_terms(
        &self,
        owner: u64,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<OwnerCounts, String> {
        if owner >= self.slots() as u64 {
            return Err("height/work owner outside slot domain".into());
        }
        let owner_index = usize::try_from(owner).map_err(|_| "height/work owner overflow")?;
        let mut counts = OwnerCounts::default();
        if owner < self.headers {
            counts.height = self.height.visit_slot_terms(owner, &mut sink)?;
        }
        counts.numeric = self.numeric.visit_owner(owner_index, |mut term| {
            if term.row != owner_index || term.gate.right != 0
                || term.gate.left >= 1usize << self.input_log()
            {
                return Err("height/work numeric producer coordinate mismatch".into());
            }
            term.row = self.numeric_base().checked_add(owner_index)
                .ok_or("height/work numeric row overflow")?;
            sink(term)
        })?;
        Ok(counts)
    }

    /// Bind the public history plan, source templates, role tags, and exact
    /// dimensions before this role samples any GKR challenges.
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        if self.generic {
            transcript.append_bytes(b"historical-prefix-height-work-profile", PROFILE_HISTORY);
            transcript.append_u64(b"historical-prefix-height-work-version", VERSION);
            transcript.append_u64(b"historical-prefix-height-work-n", self.headers);
            transcript.append_u64(b"historical-prefix-height-work-slot-log", self.slot_log as u64);
            transcript.append_u64(b"historical-prefix-height-work-slots", self.slots() as u64);
            transcript.append_u64(b"historical-prefix-height-work-input-log", self.input_log() as u64);
            transcript.append_u64(b"historical-prefix-height-work-row-log", self.row_log() as u64);
            transcript.append_u64(b"historical-prefix-height-work-height-rows", self.numeric_base() as u64);
            transcript.append_u64(b"historical-prefix-height-work-height-terms", self.headers * 32);
            transcript.append_u64(b"historical-prefix-height-work-numeric-base", self.numeric_base() as u64);
            transcript.append_bytes(b"historical-prefix-height-work-row-convention",
                b"LSB-first;height=32*owner+bit;numeric=32*slots+owner;tag-bit=slot-log+5;numeric-unused-low-bits=zero");
            transcript.append_bytes(b"historical-prefix-height-work-height-template", self.height.fingerprint().as_bytes());
            self.numeric.bind(transcript);
            return;
        }
        let profile = if self.headers == 3 {
            PROFILE_N3
        } else {
            PROFILE_N4
        };
        let height_terms = self.headers as usize * 32;
        let numeric_terms = if self.headers == 3 {
            N3_NUMERIC_TERMS
        } else {
            N4_NUMERIC_TERMS
        };
        transcript.append_bytes(b"historical-prefix-height-work-profile", profile);
        transcript.append_u64(b"historical-prefix-height-work-version", VERSION);
        transcript.append_u64(b"historical-prefix-height-work-n", self.headers);
        transcript.append_u64(b"historical-prefix-height-work-slot-log", SLOT_LOG as u64);
        transcript.append_u64(b"historical-prefix-height-work-slots", SLOTS as u64);
        transcript.append_u64(b"historical-prefix-height-work-input-log", INPUT_LOG as u64);
        transcript.append_u64(b"historical-prefix-height-work-input-len", INPUT_LEN as u64);
        transcript.append_u64(b"historical-prefix-height-work-row-log", ROW_LOG as u64);
        transcript.append_u64(b"historical-prefix-height-work-row-count", ROW_COUNT as u64);
        transcript.append_u64(
            b"historical-prefix-height-work-height-tag",
            HEIGHT_TAG as u64,
        );
        transcript.append_u64(
            b"historical-prefix-height-work-numeric-tag",
            NUMERIC_TAG as u64,
        );
        transcript.append_u64(
            b"historical-prefix-height-work-height-rows",
            HEIGHT_ROWS as u64,
        );
        transcript.append_u64(
            b"historical-prefix-height-work-height-terms",
            height_terms as u64,
        );
        transcript.append_u64(
            b"historical-prefix-height-work-numeric-base",
            NUMERIC_ROW_BASE as u64,
        );
        transcript.append_u64(
            b"historical-prefix-height-work-numeric-terms",
            numeric_terms as u64,
        );
        transcript.append_u64(
            b"historical-prefix-height-work-total-terms",
            (height_terms + numeric_terms) as u64,
        );
        transcript.append_bytes(
            b"historical-prefix-height-work-height-template",
            self.height.fingerprint().as_bytes(),
        );
        self.numeric.bind(transcript);
    }

    /// Materialize the N-specific canonical terms in the global input and
    /// tagged row domain. The fixed roles cannot be supplied by the caller.
    pub(crate) fn circuit(&self) -> Result<Circuit, String> {
        if self.generic {
            return Err("generic height/work requires owner streaming, not materialization".into());
        }
        let height_terms = self.headers as usize * 32;
        let (expected_numeric, numeric_terms) = match self.headers {
            3 => ([0usize, 225, 448, 0], N3_NUMERIC_TERMS),
            4 => ([0usize, 225, 448, 448], N4_NUMERIC_TERMS),
            _ => return Err("height/work header count changed after construction".into()),
        };
        let total_terms = height_terms + numeric_terms;
        let mut terms = Vec::with_capacity(total_terms);
        for owner in 0..self.headers as usize {
            let count = self.height.visit_slot_terms(owner as u64, |term| {
                // The height emitter already uses the global owner input base.
                if term.row < owner * 32
                    || term.row >= (owner + 1) * 32
                    || term.gate.left >= INPUT_LEN
                    || term.gate.right >= INPUT_LEN
                {
                    return Err("height wire outside global N3 input".into());
                }
                terms.push(term);
                Ok(())
            })?;
            if count != 32 {
                return Err(format!(
                    "height owner {owner}: emitted {count}, expected 32"
                ));
            }
        }
        if terms.len() != height_terms {
            return Err("height producer total changed".into());
        }

        let mut numeric_total = 0usize;
        for (owner, expected_count) in expected_numeric.into_iter().enumerate() {
            let count = self.numeric.visit_owner(owner, |mut term| {
                if term.row != owner {
                    return Err("numeric producer row differs from child owner".into());
                }
                term.row = NUMERIC_ROW_BASE
                    .checked_add(owner)
                    .ok_or("numeric tagged row overflow")?;
                if term.gate.left >= INPUT_LEN || term.gate.right >= INPUT_LEN {
                    return Err("numeric wire outside global N3 input".into());
                }
                // Numeric terms deliberately keep right=GLOBAL0 (wire zero).
                if term.gate.right != 0 {
                    return Err("numeric DAA right endpoint is not GLOBAL0".into());
                }
                terms.push(term);
                Ok(())
            })?;
            if count != expected_count {
                return Err(format!(
                    "numeric owner {owner}: emitted {count}, expected {expected_count}"
                ));
            }
            numeric_total += count;
        }
        if numeric_total != numeric_terms || terms.len() != total_terms {
            return Err("height/work term roster changed".into());
        }
        if terms.iter().any(|term| term.row >= ROW_COUNT) {
            return Err("height/work term escaped the padded row domain".into());
        }
        Ok(Circuit {
            input_len: INPUT_LEN,
            row_count: ROW_COUNT,
            terms,
        })
    }

    /// Evaluate all four channels using the existing analytic producers and
    /// fixed tag selectors; row/input points use LSB-first coordinates.
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let h = self.slot_log;
        if r.len() != self.row_log() || u.len() != self.input_log() || v.len() != self.input_log() {
            return Err("height/work coefficient point dimensions rejected".into());
        }
        let height = self
            .height
            .coefficients(&r[..HEIGHT_LOCAL_ROW_LOG + h], u, v)?;
        let numeric = self.numeric.coefficients(&r[..h], u, v)?;
        let height_tag = Fr::one() - r[HEIGHT_LOCAL_ROW_LOG + h];
        let mut numeric_tag = r[HEIGHT_LOCAL_ROW_LOG + h];
        for coordinate in &r[h..HEIGHT_LOCAL_ROW_LOG + h] {
            numeric_tag *= Fr::one() - coordinate;
        }
        let mut result = [Fr::zero(); 4];
        for channel in 0..4 {
            result[channel] = height[channel] * height_tag + numeric[channel] * numeric_tag;
        }
        Ok(result)
    }
}

#[cfg(test)]
mod history_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{daa_work_actions::DaaWorkActions, work_tree_history_plan::WorkTreeHistoryPlan};

    fn eq(point: &[Fr], index: usize) -> Fr {
        point
            .iter()
            .enumerate()
            .fold(Fr::one(), |acc, (bit, coordinate)| {
                acc * if (index >> bit) & 1 == 1 {
                    *coordinate
                } else {
                    Fr::one() - coordinate
                }
            })
    }

    fn dense(bits: usize, seed: u64) -> Vec<Fr> {
        (0..bits)
            .map(|bit| Fr::from(seed + 13 * bit as u64))
            .collect()
    }

    fn enumerate(circuit: &Circuit, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let mut result = [Fr::zero(); 4];
        for term in &circuit.terms {
            let weight = eq(r, term.row) * eq(u, term.gate.left) * eq(v, term.gate.right);
            for (out, coefficient) in
                result
                    .iter_mut()
                    .zip([term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3])
            {
                *out += weight * coefficient;
            }
        }
        result
    }

    fn boolean_point(bits: usize, index: usize) -> Vec<Fr> {
        (0..bits)
            .map(|bit| Fr::from(((index >> bit) & 1) as u64))
            .collect()
    }

    fn assert_mutation_detected(
        composite: &HeightWork<'_>,
        circuit: &Circuit,
        mutated: &Circuit,
        row: usize,
        left: usize,
        right: usize,
    ) {
        let r = boolean_point(ROW_LOG, row);
        let u = boolean_point(INPUT_LOG, left);
        let v = boolean_point(INPUT_LOG, right);
        let expected = composite.coefficients(&r, &u, &v).unwrap();
        assert_eq!(expected, enumerate(circuit, &r, &u, &v));
        assert_ne!(expected, enumerate(mutated, &r, &u, &v));
    }

    fn rejected_profile(headers: u64, slot_log: usize) -> bool {
        match WorkTreeHistoryPlan::compile(headers, slot_log, [3; 32], [5; 28]) {
            Err(_) => true,
            Ok(plan) => HeightWork::new(&plan).is_err(),
        }
    }

    #[test]
    fn n3_height_work_emitter_matches_analytic_coefficients_in_all_channels() {
        let plan = WorkTreeHistoryPlan::compile(3, 2, [7; 32], [0; 28]).unwrap();
        let composite = HeightWork::new(&plan).unwrap();
        let circuit = composite.circuit().unwrap();
        assert_eq!(
            (circuit.input_len, circuit.row_count, circuit.terms.len()),
            (INPUT_LEN, ROW_COUNT, N3_TOTAL_TERMS)
        );
        let height_count = circuit
            .terms
            .iter()
            .filter(|term| term.row < HEIGHT_ROWS)
            .count();
        let numeric_count = circuit
            .terms
            .iter()
            .filter(|term| term.row >= NUMERIC_ROW_BASE)
            .count();
        assert_eq!((height_count, numeric_count), (96, 673));
        assert!(circuit.terms.iter().all(|term| term.row < ROW_COUNT));
        for seed in [3, 19, 87] {
            let r = dense(ROW_LOG, seed);
            let u = dense(INPUT_LOG, seed + 1);
            let v = dense(INPUT_LOG, seed + 2);
            assert_eq!(
                composite.coefficients(&r, &u, &v).unwrap(),
                enumerate(&circuit, &r, &u, &v)
            );
        }
    }

    #[test]
    fn n3_height_work_tag_padding_owner_and_global_zero_are_separate() {
        let plan = WorkTreeHistoryPlan::compile(3, 2, [9; 32], [0; 28]).unwrap();
        let composite = HeightWork::new(&plan).unwrap();
        let circuit = composite.circuit().unwrap();

        // Height rows are selected only under tag zero; numeric row 129 is
        // active only under tag one, and all remaining padded rows are zero.
        let u = dense(INPUT_LOG, 41);
        let v = dense(INPUT_LOG, 43);
        let height_row = boolean_point(ROW_LOG, 7);
        let numeric_row = boolean_point(ROW_LOG, NUMERIC_ROW_BASE + 1);
        let padding_row = boolean_point(ROW_LOG, NUMERIC_ROW_BASE + 4);
        assert_eq!(
            composite.coefficients(&height_row, &u, &v).unwrap(),
            enumerate(&circuit, &height_row, &u, &v)
        );
        assert_eq!(
            composite.coefficients(&numeric_row, &u, &v).unwrap(),
            enumerate(&circuit, &numeric_row, &u, &v)
        );
        assert_eq!(
            composite.coefficients(&padding_row, &u, &v).unwrap(),
            [Fr::zero(); 4]
        );

        // The selected row is keyed by child owner; 129 and 130 remain
        // distinct despite sharing one tagged numeric subdomain.
        let owner1_terms = circuit
            .terms
            .iter()
            .filter(|term| term.row == NUMERIC_ROW_BASE + 1)
            .count();
        let owner2_terms = circuit
            .terms
            .iter()
            .filter(|term| term.row == NUMERIC_ROW_BASE + 2)
            .count();
        assert_eq!((owner1_terms, owner2_terms), (225, 448));
        assert_ne!(
            enumerate(&circuit, &numeric_row, &u, &v),
            enumerate(
                &circuit,
                &boolean_point(ROW_LOG, NUMERIC_ROW_BASE + 2),
                &u,
                &v
            )
        );

        // A numeric linear term is anchored at wire zero globally. Moving the
        // v evaluation to owner-local zero must remove its coefficient.
        let action = DaaWorkActions::new(&plan).unwrap();
        let mut selected = None;
        action
            .visit_owner(1, |term| {
                if !term.gate.c1.is_zero() {
                    selected = Some(term);
                }
                Ok(())
            })
            .unwrap();
        let term = selected.expect("H2 has a linear work term");
        assert_eq!(term.gate.right, 0);
        let row = boolean_point(ROW_LOG, NUMERIC_ROW_BASE + 1);
        let left = boolean_point(INPUT_LOG, term.gate.left);
        let global_zero = boolean_point(INPUT_LOG, 0);
        let owner_local_zero = boolean_point(INPUT_LOG, WIDTH);
        let global = composite.coefficients(&row, &left, &global_zero).unwrap();
        let local = composite
            .coefficients(&row, &left, &owner_local_zero)
            .unwrap();
        assert!(!global[1].is_zero());
        assert!(local[1].is_zero());

        // Isolated tag mutant: move H2's terms into the height tag. The
        // canonical row-129 selector must distinguish it from the real list.
        let mut wrong_tag = circuit.clone();
        for item in &mut wrong_tag.terms {
            if item.row == NUMERIC_ROW_BASE + 1 {
                item.row = 1;
            }
        }
        assert_ne!(enumerate(&wrong_tag, &row, &left, &global_zero), global);

        // Isolated owner mutant: move one H2 term to H3 while retaining its
        // gate and channel coefficients.
        let mut wrong_owner = circuit.clone();
        let moved = wrong_owner
            .terms
            .iter_mut()
            .find(|item| {
                item.row == NUMERIC_ROW_BASE + 1
                    && item.gate.left == term.gate.left
                    && item.gate.c1 == term.gate.c1
            })
            .expect("selected H2 term present");
        moved.row = NUMERIC_ROW_BASE + 2;
        assert_ne!(enumerate(&wrong_owner, &row, &left, &global_zero), global);

        // Isolated padding mutant: introduce a nonzero row outside 0..131.
        let mut wrong_padding = circuit.clone();
        wrong_padding.terms.push(Term {
            row: NUMERIC_ROW_BASE + SLOTS,
            gate: Gate {
                left: 0,
                right: 0,
                c0: Fr::one(),
                c1: Fr::zero(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        });
        let padding_u = boolean_point(INPUT_LOG, 0);
        let padding_v = boolean_point(INPUT_LOG, 0);
        assert_ne!(
            enumerate(&wrong_padding, &padding_row, &padding_u, &padding_v),
            [Fr::zero(); 4]
        );

        // Isolated global-zero mutant: redirect a single numeric term's right
        // endpoint from GLOBAL0 to the H2-local zero coordinate.
        let mut wrong_zero = circuit.clone();
        let redirected = wrong_zero
            .terms
            .iter_mut()
            .find(|item| {
                item.row == NUMERIC_ROW_BASE + 1
                    && item.gate.left == term.gate.left
                    && item.gate.right == 0
            })
            .expect("selected numeric term present");
        redirected.gate.right = WIDTH;
        assert_ne!(enumerate(&wrong_zero, &row, &left, &global_zero), global);
    }

    #[test]
    fn n4_height_work_emitter_matches_analytic_coefficients_in_all_channels() {
        let plan = WorkTreeHistoryPlan::compile(4, 2, [7; 32], [0; 28]).unwrap();
        let composite = HeightWork::new(&plan).unwrap();
        let circuit = composite.circuit().unwrap();
        assert_eq!(
            (circuit.input_len, circuit.row_count, circuit.terms.len()),
            (INPUT_LEN, ROW_COUNT, 1249)
        );

        let height_counts: Vec<_> = (0..4)
            .map(|owner| {
                circuit
                    .terms
                    .iter()
                    .filter(|term| term.row >= owner * 32 && term.row < (owner + 1) * 32)
                    .count()
            })
            .collect();
        assert_eq!(height_counts, [32, 32, 32, 32]);
        let numeric_counts: Vec<_> = (0..4)
            .map(|owner| {
                circuit
                    .terms
                    .iter()
                    .filter(|term| term.row == NUMERIC_ROW_BASE + owner)
                    .count()
            })
            .collect();
        assert_eq!(numeric_counts, [0, 225, 448, 448]);
        assert!(circuit.terms.iter().all(|term| term.row < ROW_COUNT));
        assert!(circuit
            .terms
            .iter()
            .filter(|term| term.row >= NUMERIC_ROW_BASE)
            .all(|term| term.gate.right == 0));
        for seed in [3, 19, 87] {
            let r = dense(ROW_LOG, seed);
            let u = dense(INPUT_LOG, seed + 1);
            let v = dense(INPUT_LOG, seed + 2);
            assert_eq!(
                composite.coefficients(&r, &u, &v).unwrap(),
                enumerate(&circuit, &r, &u, &v)
            );
        }
    }

    #[test]
    fn n4_height_work_is_sensitive_to_owner3_height_numeric_tag_padding_and_global_zero() {
        let plan = WorkTreeHistoryPlan::compile(4, 2, [9; 32], [0; 28]).unwrap();
        let composite = HeightWork::new(&plan).unwrap();
        let circuit = composite.circuit().unwrap();

        // Move one owner-3 height term to owner 2 while preserving its gate.
        let mut wrong_height_owner = circuit.clone();
        let height = circuit
            .terms
            .iter()
            .find(|term| {
                (96..128).contains(&term.row)
                    && [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
                        .iter()
                        .any(|coefficient| !coefficient.is_zero())
            })
            .expect("owner-3 height term present");
        let row = height.row;
        let left = height.gate.left;
        let right = height.gate.right;
        let moved = wrong_height_owner
            .terms
            .iter_mut()
            .find(|term| {
                term.row == row
                    && term.gate.left == left
                    && term.gate.right == right
                    && term.gate.c0 == height.gate.c0
                    && term.gate.c1 == height.gate.c1
                    && term.gate.c2 == height.gate.c2
                    && term.gate.c3 == height.gate.c3
            })
            .expect("selected owner-3 height term retained");
        moved.row -= 32;
        assert_mutation_detected(&composite, &circuit, &wrong_height_owner, row, left, right);

        // Move one owner-3 numeric term to owner 2 without changing its gates.
        let numeric = circuit
            .terms
            .iter()
            .find(|term| {
                term.row == NUMERIC_ROW_BASE + 3
                    && [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
                        .iter()
                        .any(|coefficient| !coefficient.is_zero())
            })
            .expect("owner-3 numeric term present");
        let numeric_row = numeric.row;
        let numeric_left = numeric.gate.left;
        let numeric_right = numeric.gate.right;
        let mut wrong_numeric_owner = circuit.clone();
        let moved = wrong_numeric_owner
            .terms
            .iter_mut()
            .find(|term| {
                term.row == numeric_row
                    && term.gate.left == numeric_left
                    && term.gate.right == numeric_right
                    && term.gate.c0 == numeric.gate.c0
                    && term.gate.c1 == numeric.gate.c1
                    && term.gate.c2 == numeric.gate.c2
                    && term.gate.c3 == numeric.gate.c3
            })
            .expect("selected owner-3 numeric term retained");
        moved.row -= 1;
        assert_mutation_detected(
            &composite,
            &circuit,
            &wrong_numeric_owner,
            numeric_row,
            numeric_left,
            numeric_right,
        );

        // Move one owner-3 numeric term into the height tag domain.
        let mut wrong_tag = circuit.clone();
        let tagged = wrong_tag
            .terms
            .iter_mut()
            .find(|term| {
                term.row == NUMERIC_ROW_BASE + 3
                    && [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
                        .iter()
                        .any(|coefficient| !coefficient.is_zero())
            })
            .expect("owner-3 tagged numeric term present");
        let tag_left = tagged.gate.left;
        let tag_right = tagged.gate.right;
        tagged.row = 3;
        assert_mutation_detected(
            &composite,
            &circuit,
            &wrong_tag,
            NUMERIC_ROW_BASE + 3,
            tag_left,
            tag_right,
        );

        // A term in padded row 132 must remain zero in the accepted relation.
        let mut wrong_padding = circuit.clone();
        wrong_padding.terms.push(Term {
            row: NUMERIC_ROW_BASE + SLOTS,
            gate: Gate {
                left: 0,
                right: 0,
                c0: Fr::one(),
                c1: Fr::zero(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        });
        let padding_r = boolean_point(ROW_LOG, NUMERIC_ROW_BASE + SLOTS);
        let zero = boolean_point(INPUT_LOG, 0);
        assert_eq!(
            composite.coefficients(&padding_r, &zero, &zero).unwrap(),
            [Fr::zero(); 4]
        );
        assert_ne!(
            enumerate(&wrong_padding, &padding_r, &zero, &zero),
            [Fr::zero(); 4]
        );

        // Redirect an owner-3 numeric endpoint from GLOBAL0 to owner-3 local zero.
        let mut wrong_global_zero = circuit.clone();
        let zero_term = wrong_global_zero
            .terms
            .iter_mut()
            .find(|term| {
                term.row == NUMERIC_ROW_BASE + 3
                    && term.gate.right == 0
                    && [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
                        .iter()
                        .any(|coefficient| !coefficient.is_zero())
            })
            .expect("owner-3 numeric GLOBAL0 term present");
        let zero_row = zero_term.row;
        let zero_left = zero_term.gate.left;
        zero_term.gate.right = 3 * WIDTH;
        assert_mutation_detected(
            &composite,
            &circuit,
            &wrong_global_zero,
            zero_row,
            zero_left,
            0,
        );
    }

    #[test]
    fn n3_height_work_binding_and_dimensions_are_fixed() {
        let plan = WorkTreeHistoryPlan::compile(3, 2, [3; 32], [5; 28]).unwrap();
        let composite = HeightWork::new(&plan).unwrap();
        let mut first = Transcript::new(b"height-work-binding-test");
        composite.bind(&mut first);
        assert_eq!(first.challenges(), 0);
        assert!(composite
            .coefficients(&[Fr::zero(); 7], &[Fr::zero(); 22], &[Fr::zero(); 22])
            .is_err());
        let n4 = WorkTreeHistoryPlan::compile(4, 2, [3; 32], [5; 28]).unwrap();
        let n4_composite = HeightWork::new(&n4).unwrap();
        let n4_circuit = n4_composite.circuit().unwrap();
        assert_eq!(
            (
                n4_circuit.input_len,
                n4_circuit.row_count,
                n4_circuit.terms.len()
            ),
            (INPUT_LEN, ROW_COUNT, N4_TOTAL_TERMS)
        );
        assert!(n4_composite
            .coefficients(&[Fr::zero(); 7], &[Fr::zero(); 22], &[Fr::zero(); 22])
            .is_err());

        for (headers, slot_log) in [(2, 2), (5, 2), (4, 1), (4, 3)] {
            assert!(rejected_profile(headers, slot_log));
        }
    }
}

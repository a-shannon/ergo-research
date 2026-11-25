//! Fixed n=4 retained header-pair construction over the ordinary history plan.
//!
//! The visitor has already translated every slot term into global coordinates.
//! This adapter subtracts the selected pair base exactly once; it does not
//! rebuild retired rows or introduce endpoint anchors.

use ark_bn254::Fr;
use ark_ff::Zero;

use crate::{
    gkr,
    sparse::Term,
    work_tree_history_plan::{RetirementCounts, WorkTreeHistoryPlan},
};

pub(crate) const HEADERS: u64 = 4;
pub(crate) const SLOT_LOG: usize = 2;
pub(crate) const PAIR_STARTS: [u64; 2] = [0, 2];
pub(crate) const SLOT_ROW_WIDTH: usize = 1 << 19;
pub(crate) const SLOT_INPUT_WIDTH: usize = 1 << 20;
pub(crate) const PAIR_ROW_COUNT: usize = 1 << 20;
pub(crate) const PAIR_INPUT_LEN: usize = 1 << 21;
pub(crate) const PAIR_ROW_LOG: usize = 20;
pub(crate) const PAIR_INPUT_LOG: usize = 21;
pub(crate) const OWNER_RETAINED_TERMS: usize = 396_561;
pub(crate) const OWNER_RETIRED_TERMS: usize = 78_194;
pub(crate) const PAIR_RETAINED_TERMS: usize = 793_122;
pub(crate) const PAIR_TERM_CAP: usize = 1_048_576;

pub(crate) const EXPECTED_RETIREMENT: RetirementCounts = RetirementCounts {
    terms: 78_194,
    rows: 78_002,
    dummy_terms: 4_806,
    dummy_rows: 4_614,
    node_terms: 65_268,
    endpoint_terms: 8_120,
    protected_endpoint_terms: 72,
};

#[derive(Clone)]
pub(crate) struct RetainedHeaderPair {
    start: u64,
    terms: Vec<Term>,
    owner_terms: [usize; 2],
    omitted_worktree: [usize; 2],
    omitted_a4: [usize; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RetainedPairSummary {
    pub(crate) start: u64,
    pub(crate) term_count: usize,
    pub(crate) owner_terms: [usize; 2],
    pub(crate) omitted_worktree: [usize; 2],
    pub(crate) omitted_a4: [usize; 2],
}

impl RetainedHeaderPair {
    pub(crate) fn start(&self) -> u64 {
        self.start
    }

    pub(crate) fn terms(&self) -> &[Term] {
        &self.terms
    }

    pub(crate) fn owner_term_counts(&self) -> [usize; 2] {
        self.owner_terms
    }

    pub(crate) fn omitted_worktree_counts(&self) -> [usize; 2] {
        self.omitted_worktree
    }

    pub(crate) fn omitted_a4_counts(&self) -> [usize; 2] {
        self.omitted_a4
    }

    pub(crate) fn checked_summary(&self) -> Result<RetainedPairSummary, String> {
        validate_pair_coverage(self)?;
        Ok(RetainedPairSummary {
            start: self.start,
            term_count: self.terms.len(),
            owner_terms: self.owner_terms,
            omitted_worktree: self.omitted_worktree,
            omitted_a4: self.omitted_a4,
        })
    }

    pub(crate) fn into_terms(self) -> Vec<Term> {
        self.terms
    }

    pub(crate) fn coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        if r.len() != PAIR_ROW_LOG
            || u.len() != PAIR_INPUT_LOG
            || v.len() != PAIR_INPUT_LOG
        {
            return Err("retained pair coefficient point dimensions rejected".into());
        }

        let row_weights = gkr::eq_weights(r);
        let left_weights = gkr::eq_weights(u);
        let right_weights = gkr::eq_weights(v);
        let mut result = [Fr::zero(); 4];
        for term in &self.terms {
            let weight = row_weights[term.row]
                * left_weights[term.gate.left]
                * right_weights[term.gate.right];
            result[0] += weight * term.gate.c0;
            result[1] += weight * term.gate.c1;
            result[2] += weight * term.gate.c2;
            result[3] += weight * term.gate.c3;
        }
        Ok(result)
    }
}

pub(crate) struct RetainedHeaderPairs {
    pairs: [RetainedHeaderPair; 2],
}

impl RetainedHeaderPairs {
    pub(crate) fn new_for_history(parent: &WorkTreeHistoryPlan) -> Result<Self, String> {
        validate_history_parent(parent)?;

        let pair0 = build_pair(parent, PAIR_STARTS[0])?;
        let pair2 = build_pair(parent, PAIR_STARTS[1])?;
        let result = Self {
            pairs: [pair0, pair2],
        };
        if result.starts() != PAIR_STARTS {
            return Err("retained pair coverage differs from [0,2]".into());
        }
        Ok(result)
    }

    pub(crate) fn starts(&self) -> [u64; 2] {
        [self.pairs[0].start, self.pairs[1].start]
    }

    pub(crate) fn pair(&self, start: u64) -> Result<&RetainedHeaderPair, String> {
        self.pairs
            .iter()
            .find(|pair| pair.start == start)
            .ok_or_else(|| "retained pair start is not in the fixed [0,2] set".into())
    }

    pub(crate) fn embed_row_point(&self, start: u64, point: &[Fr]) -> Result<Vec<Fr>, String> {
        self.pair(start)?;
        append_pair_bit(start, point, PAIR_ROW_LOG)
    }

    pub(crate) fn embed_input_point(
        &self,
        start: u64,
        point: &[Fr],
    ) -> Result<Vec<Fr>, String> {
        self.pair(start)?;
        append_pair_bit(start, point, PAIR_INPUT_LOG)
    }
}

pub(crate) fn validate_history_parent(parent: &WorkTreeHistoryPlan) -> Result<(), String> {
    let descriptor = parent.descriptor();
    if parent.headers() != HEADERS
        || parent.slot_log() != SLOT_LOG
        || parent.slots() != 4
        || descriptor.headers != 4
        || descriptor.genuine != 3
        || descriptor.slots != 4
        || descriptor.leaves != 4
    {
        return Err("retained pair adapter requires the fixed n=4/h=2 history".into());
    }
    if parent.retirement_counts() != EXPECTED_RETIREMENT {
        return Err("retained pair retirement census differs".into());
    }
    Ok(())
}

pub(crate) fn build_one_for_history(
    parent: &WorkTreeHistoryPlan,
    start: u64,
) -> Result<RetainedHeaderPair, String> {
    validate_history_parent(parent)?;
    // `build_pair` checks exact coverage, census and bounds before returning.
    build_pair(parent, start)
}

fn append_pair_bit(start: u64, point: &[Fr], expected_len: usize) -> Result<Vec<Fr>, String> {
    if point.len() != expected_len {
        return Err("retained pair embedding point dimensions rejected".into());
    }
    let pair_bit: u64 = match start {
        0 => 0u64,
        2 => 1u64,
        _ => return Err("retained pair embedding start is not 0 or 2".into()),
    };
    let mut embedded = Vec::with_capacity(expected_len + 1);
    embedded.extend_from_slice(point);
    embedded.push(Fr::from(pair_bit));
    Ok(embedded)
}

fn build_pair(
    parent: &WorkTreeHistoryPlan,
    start: u64,
) -> Result<RetainedHeaderPair, String> {
    if !PAIR_STARTS.contains(&start) {
        return Err("retained pair start is not in the fixed [0,2] set".into());
    }
    let start_usize = usize::try_from(start).map_err(|_| "retained pair start overflow")?;
    let row_base = start_usize
        .checked_mul(SLOT_ROW_WIDTH)
        .ok_or("retained pair row base overflow")?;
    let input_base = start_usize
        .checked_mul(SLOT_INPUT_WIDTH)
        .ok_or("retained pair input base overflow")?;

    let mut terms = Vec::new();
    terms
        .try_reserve_exact(PAIR_RETAINED_TERMS)
        .map_err(|_| "retained pair term allocation failed")?;
    let mut owner_terms = [0usize; 2];
    let mut omitted_worktree = [0usize; 2];
    let mut omitted_a4 = [0usize; 2];

    for slot in start..start + 2 {
        let owner_index = usize::try_from(slot - start)
            .map_err(|_| "retained pair owner index overflow")?;
        let counts = parent.visit_slot_terms(slot, |mut term| {
            if terms.len() >= PAIR_RETAINED_TERMS {
                return Err("retained pair term count exceeded its fixed capacity".into());
            }
            term.row = term
                .row
                .checked_sub(row_base)
                .ok_or("retained pair row precedes its base")?;
            term.gate.left = term
                .gate
                .left
                .checked_sub(input_base)
                .ok_or("retained pair left endpoint precedes its base")?;
            term.gate.right = term
                .gate
                .right
                .checked_sub(input_base)
                .ok_or("retained pair right endpoint precedes its base")?;
            if term.row >= PAIR_ROW_COUNT
                || term.gate.left >= PAIR_INPUT_LEN
                || term.gate.right >= PAIR_INPUT_LEN
            {
                return Err("retained pair term is outside its fixed dimensions".into());
            }
            owner_terms[owner_index] = owner_terms[owner_index]
                .checked_add(1)
                .ok_or("retained pair owner term census overflow")?;
            terms.push(term);
            Ok(())
        })?;
        if counts.emitted != OWNER_RETAINED_TERMS
            || counts.omitted_worktree != OWNER_RETIRED_TERMS
            || counts.omitted_a4 != 0
        {
            return Err(format!(
                "retained pair owner {slot} census differs: emitted={} retired={} a4={}",
                counts.emitted, counts.omitted_worktree, counts.omitted_a4
            ));
        }
        omitted_worktree[owner_index] = counts.omitted_worktree;
        omitted_a4[owner_index] = counts.omitted_a4;
    }

    let pair = RetainedHeaderPair {
        start,
        terms,
        owner_terms,
        omitted_worktree,
        omitted_a4,
    };
    validate_pair_coverage(&pair)?;
    Ok(pair)
}

fn validate_pair_coverage(pair: &RetainedHeaderPair) -> Result<(), String> {
    if !PAIR_STARTS.contains(&pair.start)
        || pair.terms.len() != PAIR_RETAINED_TERMS
        || pair.owner_terms != [OWNER_RETAINED_TERMS; 2]
        || pair.omitted_worktree != [OWNER_RETIRED_TERMS; 2]
        || pair.omitted_a4 != [0; 2]
        || pair.terms.len() > PAIR_TERM_CAP
    {
        return Err("retained pair exact coverage census differs".into());
    }

    let mut observed_owner_terms = [0usize; 2];
    let mut previous_row = None;
    for term in &pair.terms {
        if term.row >= PAIR_ROW_COUNT
            || term.gate.left >= PAIR_INPUT_LEN
            || term.gate.right >= PAIR_INPUT_LEN
        {
            return Err("retained pair term is outside its fixed dimensions".into());
        }
        if let Some(previous) = previous_row {
            if previous > term.row {
                return Err("retained pair terms are not in canonical row order".into());
            }
        }
        previous_row = Some(term.row);
        let owner = term.row / SLOT_ROW_WIDTH;
        if owner >= observed_owner_terms.len() {
            return Err("retained pair row is outside its two owner slices".into());
        }
        observed_owner_terms[owner] = observed_owner_terms[owner]
            .checked_add(1)
            .ok_or("retained pair coverage count overflow")?;
    }
    if observed_owner_terms != pair.owner_terms {
        return Err("retained pair per-owner term coverage differs".into());
    }
    Ok(())
}

#[cfg(test)]
#[path = "retained_header_pairs_tests.rs"]
mod tests;

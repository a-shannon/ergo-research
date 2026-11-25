//! Production-available source relation and physical translation for Bank53 Map terms.
use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    legacy_envelope_map::{Map, BASE as MAP_BASE},
    sparse::Term,
};
#[path = "h21_cut_descriptor.rs"]
mod cut_descriptor;
pub(crate) use cut_descriptor::CutDescriptor;
#[cfg(test)]
pub(crate) use cut_descriptor::{CutProfile, MaturityMode};

pub(crate) const INPUT_STRIDE: usize = 1 << 20;
pub(crate) const ROW_STRIDE: usize = 1 << 19;
pub(crate) const MAP_ROW_STRIDE: usize = 1 << 14;
pub(crate) const CONTEXTS: usize = 2;
pub(crate) const CONTEXT_INPUT_BASE: usize = 671_744;
pub(crate) const CONTEXT_ROW_BASE: usize = 409_600;
pub(crate) const MAP_LIVE: usize = 5_757;
pub(crate) const MAP_TAIL_START: usize = 5_757;
pub(crate) const MAP_TAIL_END: usize = 7_898;
pub(crate) const MAP_TAIL_COUNT: usize = MAP_TAIL_END - MAP_TAIL_START;
const MAP_OWNER_TERM_CAP: usize = 200_000;

pub(crate) const BANK53_N: u64 = 1_827_840;
pub(crate) const BANK53_H: u64 = 1_827_775;
pub(crate) const BANK53_F: u64 = BANK53_H + 63;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HistoryBounds {
    pub n: u64,
    pub h: u64,
    pub f: u64,
}

/// Validate the pinned H21 endpoints before constructing either context plan.
pub(crate) fn bank53_history_bounds(n: u64, h: u64) -> Result<HistoryBounds, String> {
    let after_cut = h.checked_add(64).ok_or("bank53 cut overflow")?;
    if after_cut > n {
        return Err("bank53 requires h+64<=N".into());
    }
    let f = h.checked_add(63).ok_or("bank53 sampled endpoint overflow")?;
    if (n, h, f) != (BANK53_N, BANK53_H, BANK53_F) {
        return Err("bank53 pinned endpoint descriptor".into());
    }
    Ok(HistoryBounds { n, h, f })
}

pub(crate) fn context_ok(context: usize) -> Result<(), String> {
    if context < CONTEXTS { Ok(()) } else { Err("bank53 context index".into()) }
}

fn map_geometry_for_context(
    map: &Map, owner: u64, context: usize, expected_endpoint: u64,
) -> Result<(), String> {
    context_ok(context)?;
    if map.h() > 21 || map.slots() != (1u64 << map.h()) {
        return Err("bank53 Map owner geometry".into());
    }
    if map.h() == 21 {
        if map.n() != expected_endpoint {
            return Err("bank53 Map context endpoint must be N or h".into());
        }
    }
    if owner >= map.slots() { return Err("bank53 Map owner index".into()); }
    let local_row_base = CONTEXT_ROW_BASE + context * 32_768;
    if local_row_base + MAP_ROW_STRIDE > ROW_STRIDE
        || CONTEXT_INPUT_BASE + context * 8_192 + MAP_LIVE > INPUT_STRIDE {
        return Err("bank53 Map lane bounds".into());
    }
    Ok(())
}

fn map_geometry(map: &Map, owner: u64, context: usize) -> Result<(), String> {
    context_ok(context)?;
    let bounds=bank53_history_bounds(BANK53_N,BANK53_H)?;
    map_geometry_for_context(map, owner, context, [bounds.n,bounds.h][context])
}

fn map_geometry_for_descriptor(map: &Map, owner: u64, context: usize,
    descriptor: CutDescriptor) -> Result<(), String> {
    context_ok(context)?;
    if map.h()!=21 || map.slots()!=(1u64<<21) {
        return Err("bank53 descriptor requires H21 Map geometry".into());
    }
    map_geometry_for_context(map,owner,context,descriptor.terminals()[context] as u64)
}

pub(crate) fn owner_input_base(owner: u64) -> Result<usize, String> {
    usize::try_from(owner).ok()
        .and_then(|o| o.checked_mul(INPUT_STRIDE))
        .ok_or_else(|| "bank53 input owner offset overflow".into())
}

fn owner_row_base(owner: u64) -> Result<usize, String> {
    usize::try_from(owner).ok()
        .and_then(|o| o.checked_mul(ROW_STRIDE))
        .ok_or_else(|| "bank53 row owner offset overflow".into())
}

fn map_source_row_base(owner: u64) -> Result<usize, String> {
    usize::try_from(owner).ok()
        .and_then(|o| o.checked_mul(MAP_ROW_STRIDE))
        .ok_or_else(|| "bank53 Map source row offset overflow".into())
}

fn map_input(index: usize, owner: u64, context: usize) -> Result<usize, String> {
    let base = owner_input_base(owner)?;
    let Some(local) = index.checked_sub(base) else { return Ok(index); };
    if local < INPUT_STRIDE && (MAP_BASE..MAP_BASE + MAP_LIVE).contains(&local) {
        base.checked_add(CONTEXT_INPUT_BASE + context * 8_192 + local - MAP_BASE)
            .ok_or_else(|| "bank53 Map helper coordinate overflow".into())
    } else if local < INPUT_STRIDE
        && (MAP_BASE + MAP_TAIL_START..MAP_BASE + MAP_TAIL_END).contains(&local) {
        Err("bank53 retained Map term reads retired tail helper".into())
    } else {
        Ok(index)
    }
}

pub(crate) fn exact_zero_tail(term: &Term, owner: u64, local_row: usize) -> Result<(), String> {
    let row = map_source_row_base(owner)?
        .checked_add(local_row)
        .ok_or("bank53 Map tail row overflow")?;
    let input = owner_input_base(owner)?
        .checked_add(MAP_BASE + local_row)
        .ok_or("bank53 Map tail input overflow")?;
    let placeholder = owner_input_base(owner)?;
    if term.row != row
        || term.gate.left != input
        || term.gate.right != placeholder
        || term.gate.c0 != Fr::zero()
        || term.gate.c1 != Fr::one()
        || term.gate.c2 != Fr::zero()
        || term.gate.c3 != Fr::zero() {
        return Err(format!("bank53 Map tail row {row} is not its exact zero gate"));
    }
    Ok(())
}

/// Remove only the 2,141 verified zero-tail gates, then translate Map rows and
/// its live destination helpers into this context's physical lanes.
pub(crate) fn translate_map_terms(
    map: &Map,
    owner: u64,
    context: usize,
    source: &[Term],
) -> Result<Vec<Term>, String> {
    context_ok(context)?;
    let bounds=bank53_history_bounds(BANK53_N,BANK53_H)?;
    translate_map_terms_for_context(map,owner,context,source,[bounds.n,bounds.h][context])
}

fn translate_map_terms_for_context(
    map: &Map,
    owner: u64,
    context: usize,
    source: &[Term],
    expected_endpoint: u64,
) -> Result<Vec<Term>, String> {
    map_geometry_for_context(map, owner, context, expected_endpoint)?;
    if source.len() > MAP_OWNER_TERM_CAP {
        return Err("bank53 Map owner materialization cap".into());
    }
    let old_row_base = map_source_row_base(owner)?;
    let row_end = old_row_base.checked_add(MAP_ROW_STRIDE)
        .ok_or("bank53 Map source row range overflow")?;
    let mut tail_seen = vec![false; MAP_TAIL_COUNT];
    let mut kept = Vec::with_capacity(source.len().saturating_sub(MAP_TAIL_COUNT));
    for term in source {
        if (old_row_base + MAP_TAIL_START..old_row_base + MAP_TAIL_END).contains(&term.row) {
            let local = term.row - old_row_base;
            exact_zero_tail(term, owner, local)?;
            let seen = &mut tail_seen[local - MAP_TAIL_START];
            if *seen { return Err("duplicate bank53 Map tail row".into()); }
            *seen = true;
            continue;
        }
        if !(old_row_base..row_end).contains(&term.row) {
            return Err("bank53 Map term escapes its owner row bank".into());
        }
        kept.push(term.clone());
    }
    if tail_seen.iter().any(|seen| !seen) {
        return Err("bank53 Map zero-tail census is incomplete".into());
    }
    if source.len() != kept.len() + MAP_TAIL_COUNT {
        return Err("bank53 Map zero-tail retirement count".into());
    }
    let physical_row_base = owner_row_base(owner)?
        .checked_add(CONTEXT_ROW_BASE + context * 32_768)
        .ok_or("bank53 Map physical row base overflow")?;
    for term in &mut kept {
        let local_row = term.row - old_row_base;
        term.row = physical_row_base.checked_add(local_row)
            .ok_or("bank53 Map physical row overflow")?;
        term.gate.left = map_input(term.gate.left, owner, context)?;
        term.gate.right = map_input(term.gate.right, owner, context)?;
    }
    Ok(kept)
}

/// The same physical Map lane, with its source endpoint bound to an exact
/// fixed draft-0.8 cut. This diagnostic path is not a global X writer.
pub(crate) fn translate_map_terms_for_descriptor(
    map: &Map, owner: u64, context: usize, source: &[Term], descriptor: CutDescriptor,
) -> Result<Vec<Term>, String> {
    map_geometry_for_descriptor(map,owner,context,descriptor)?;
    translate_map_terms_for_context(map,owner,context,source,descriptor.terminals()[context] as u64)
}

pub(crate) fn map_owner_terms(map: &Map, owner: u64, context: usize) -> Result<Vec<Term>, String> {
    map_geometry(map, owner, context)?;
    let terms = map.terms(owner)?;
    if terms.len() > MAP_OWNER_TERM_CAP {
        return Err("bank53 Map owner materialization cap".into());
    }
    translate_map_terms(map, owner, context, &terms)
}

pub(crate) fn map_owner_terms_for_descriptor(
    map: &Map, owner: u64, context: usize, descriptor: CutDescriptor,
) -> Result<Vec<Term>, String> {
    map_geometry_for_descriptor(map, owner, context, descriptor)?;
    let terms = map.terms(owner)?;
    if terms.len() > MAP_OWNER_TERM_CAP {
        return Err("bank53 Map owner materialization cap".into());
    }
    translate_map_terms_for_descriptor(map, owner, context, &terms, descriptor)
}

//! HEADER permission gate only: no suffix, cap arithmetic, Score or proof admission.
use std::ops::Range;

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{sparse::{Circuit, Term}, transcript::Transcript,
    work_tree_history_plan::{EmissionCounts, WorkTreeHistoryPlan}, work_tree_layout};

const WIDTH: usize = 1 << 20;
const ROWS: usize = 1 << 19;
const BASE: usize = 999_424;
const ANCHOR: usize = 356_632;
const END: usize = 1_004_866;
const ACTIVATION: usize = 844_672;
const EPOCH: usize = 128;
const MATURITY: usize = 1088;

/// Height-space partition only. No D/W value or MAX recurrence is evaluated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScheduledEpoch { pub(crate) start: usize, pub(crate) end: usize }

fn epoch_at(terminal: usize, height: usize) -> Option<ScheduledEpoch> {
    if !(ACTIVATION..=terminal).contains(&height) { return None; }
    let start = if height == ACTIVATION { ACTIVATION } else {
        ACTIVATION + 1 + (height - ACTIVATION - 1) / EPOCH * EPOCH
    };
    let end = if start == ACTIVATION { start } else { (start + EPOCH - 1).min(terminal) };
    Some(ScheduledEpoch { start, end })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Relation { Max, Cap }

#[derive(Clone, Copy, Debug)]
enum Policy { H21, #[cfg(test)] FixtureN3 }

impl Policy {
    fn endpoints(self, context: usize) -> Result<(usize,usize),String> {
        match (self,context) {
            (Self::H21,0) => Ok((1_827_840,1_827_838)),
            (Self::H21,1) => Ok((1_827_775,1_827_775)),
            #[cfg(test)] (Self::FixtureN3,0) => Ok((3,2)),
            #[cfg(test)] (Self::FixtureN3,1) => Ok((2,2)),
            _ => Err("schedule context outside declared pair".into()),
        }
    }
    /// Source-owner and shifted/clipped guard-owner geometry only. It does
    /// not authenticate the D/W values or implement their recurrence.
    fn active(self, owner: usize, context: usize, relation: Relation) -> Result<bool,String> {
        let (terminal,guard) = self.endpoints(context)?;
        Ok(match self {
            Self::H21 => match relation {
                Relation::Max => owner.checked_add(2).and_then(|height| epoch_at(terminal,height))
                    .is_some_and(|epoch| epoch.end - 2 == owner),
                Relation::Cap => {
                    let origin = owner.checked_add(1).ok_or("schedule origin overflow")?;
                    origin == 845_760 || (origin >= 845_761 && origin <= guard &&
                        (origin == guard || (origin >= 845_888 && (origin-845_888)%128 == 0)))
                }
            },
            #[cfg(test)] Self::FixtureN3 => match (context,relation) {
                (0,Relation::Max) => owner < 2,
                (1,Relation::Max) | (0,Relation::Cap) => owner == 0,
                (1,Relation::Cap) => owner == 1,
                _ => false,
            }
        })
    }

    /// MAX is stored at b-2 for epoch [a,b]. These are only the neighboring
    /// epoch owners for a future recurrence; there is no MAX arithmetic or
    /// same-X authentication here. An inactive owner is rejected.
    fn max_neighbors(self, owner: usize, context: usize) -> Result<(Option<usize>,Option<usize>),String> {
        let (terminal,_) = self.endpoints(context)?;
        if !matches!(self,Self::H21) || !self.active(owner,context,Relation::Max)? {
            return Err("schedule MAX geometry owner rejected".into());
        }
        let epoch = epoch_at(terminal,owner+2).ok_or("schedule MAX epoch absent")?;
        let previous = epoch.start.checked_sub(1).and_then(|h| epoch_at(terminal,h)).map(|e|e.end-2);
        let next = epoch_at(terminal,epoch.end+1).map(|e|e.end-2);
        Ok((previous,next))
    }

    /// Cap at i-1 imports the MAX of the epoch containing i-1088. For an
    /// ordinary candidate i=b+1088 this is i-1090. At a clipped guard, use
    /// that epoch's end rather than pretending the guard is an epoch end.
    fn cap_max_source_owner(self, owner: usize, context: usize) -> Result<usize,String> {
        let (terminal,guard) = self.endpoints(context)?;
        if !matches!(self,Self::H21) || !self.active(owner,context,Relation::Cap)? {
            return Err("schedule Cap geometry owner rejected".into());
        }
        let origin = owner.checked_add(1).ok_or("schedule origin overflow")?;
        if origin == guard {
            let height = origin.checked_sub(MATURITY).ok_or("schedule maturity underflow")?;
            Ok(epoch_at(terminal,height).ok_or("schedule Cap source epoch absent")?.end-2)
        } else {
            origin.checked_sub(MATURITY+2).ok_or_else(||"schedule Cap source underflow".into())
        }
    }
}

fn wires(context: usize, relation: Relation) -> Result<Range<usize>, String> {
    match (context, relation) {
        (0, Relation::Max) => Ok(999_424..1_000_097),
        (1, Relation::Max) => Ok(1_000_097..1_000_770),
        (0, Relation::Cap) => Ok(1_000_770..1_002_818),
        (1, Relation::Cap) => Ok(1_002_818..1_004_866),
        _ => Err("schedule context outside declared pair".into()),
    }
}

fn identity(term: &Term, row_base: usize, input_base: usize) -> Result<usize, String> {
    let local = term.row.checked_sub(row_base).ok_or("schedule row precedes owner")?;
    let offset = local.checked_sub(ANCHOR).filter(|i| *i < END-BASE)
        .ok_or("schedule row outside declared anchors")?;
    let g = &term.gate;
    if g.left != input_base + BASE + offset || g.right != input_base ||
        [g.c0,g.c1,g.c2,g.c3] != [Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()] {
        return Err("schedule zero-anchor identity changed".into());
    }
    Ok(offset)
}

/// Census checks every term on every declared row; duplicates cannot hide behind
/// an otherwise canonical anchor. No numerical gap is inferred writable.
fn certify(source: &Circuit) -> Result<String, String> {
    if source.input_len != WIDTH || source.row_count != ROWS {
        return Err("schedule canonical HEADER geometry changed".into());
    }
    let mut seen = vec![false; END-BASE];
    let mut anchors = Vec::with_capacity(END-BASE);
    for term in &source.terms {
        if (ANCHOR..ANCHOR+END-BASE).contains(&term.row) {
            let offset = identity(term,0,0)?;
            if seen[offset] { return Err("schedule duplicate zero anchor".into()); }
            seen[offset] = true;
            anchors.push(term.clone());
        } else if (BASE..END).contains(&term.gate.left) || (BASE..END).contains(&term.gate.right) {
            return Err("schedule helper has an additional HEADER consumer".into());
        }
    }
    if seen.iter().any(|b| !b) {return Err("schedule missing zero anchor".into());}
    anchors.sort_unstable_by_key(|t| t.row);
    Ok(work_tree_layout::hash_terms(&anchors))
}

pub(crate) struct ScheduleAnchorAllocator<'a> {
    parent: &'a WorkTreeHistoryPlan,
    policy: Policy,
    anchor_hash: String,
}

#[derive(Debug)]
pub(crate) struct Counts {
    pub(crate) parent: EmissionCounts,
    pub(crate) omitted: [usize;4], // c0 MAX, c1 MAX, c0 Cap, c1 Cap
    pub(crate) emitted: usize,
}

impl<'a> ScheduleAnchorAllocator<'a> {
    pub(crate) fn compile_h21(parent: &'a WorkTreeHistoryPlan) -> Result<Self,String> {
        Self::compile(parent,Policy::H21)
    }
    fn compile(parent: &'a WorkTreeHistoryPlan, policy: Policy) -> Result<Self,String> {
        let admitted = match policy {
            Policy::H21 => parent.headers() == 1_827_840 && parent.slots() == 1<<21 && parent.slot_log() == 21,
            #[cfg(test)] Policy::FixtureN3 => parent.headers() == 3 && parent.slots() == 4 && parent.slot_log() == 2,
        };
        if !admitted {return Err("schedule policy/parent geometry rejected".into());}
        let anchor_hash = certify(parent.header_boundary().canonical_circuit())?;
        let result = Self { parent, policy, anchor_hash };
        // The parent currently has an owner-invariant mask. Verify it for a
        // concrete admitted owner; every mask request checks it again.
        result.replacement_mask(0)?;
        Ok(result)
    }

    pub(crate) fn check_parent(&self, parent: &WorkTreeHistoryPlan) -> Result<(),String> {
        if !std::ptr::eq(self.parent,parent) { return Err("schedule parent identity mismatch".into()); }
        Ok(())
    }

    fn active(&self, owner: usize, context: usize, relation: Relation) -> Result<bool,String> {
        if owner >= self.parent.slots() {return Err("schedule owner outside physical domain".into());}
        self.policy.active(owner,context,relation)
    }

    /// Writer requests carry their semantic identity and exact local endpoints.
    /// This is permission evidence only; it does not authenticate witness values.
    fn claim_writer(&self, owner: usize, context: usize, relation: Relation,
        requested: Range<usize>, mask: &mut [bool]) -> Result<(),String> {
        let range = wires(context,relation)?;
        if requested != range || !self.active(owner,context,relation)? || mask.len() != WIDTH {
            return Err("schedule writer relation/context/endpoints rejected".into());
        }
        if mask[range.clone()].iter().any(|b| *b) {
            return Err("schedule writer overlaps an existing writer".into());
        }
        mask[range].fill(true);
        Ok(())
    }

    pub(crate) fn replacement_mask(&self, owner: usize) -> Result<Vec<bool>,String> {
        if owner >= self.parent.slots() {return Err("schedule owner outside physical domain".into());}
        let mut mask = self.parent.physical_assignment_replacement_mask(owner as u64)?;
        // Reject parent ownership even on inactive cells, rather than treating
        // absence of a local claim as evidence that their anchors are free.
        if mask[BASE..END].iter().any(|b| *b) {return Err("schedule helpers overlap parent writer".into());}
        for relation in [Relation::Max,Relation::Cap] {
            for context in 0..2 {
                if self.active(owner,context,relation)? {
                    self.claim_writer(owner,context,relation,wires(context,relation)?,&mut mask)?;
                }
            }
        }
        Ok(mask)
    }

    pub(crate) fn visit_header_terms(&self, owner: usize,
        mut sink: impl FnMut(Term)->Result<(),String>) -> Result<Counts,String> {
        self.replacement_mask(owner)?;
        let row_base = owner.checked_mul(ROWS).ok_or("schedule row translation overflow")?;
        let input_base = owner.checked_mul(WIDTH).ok_or("schedule input translation overflow")?;
        let mut seen = vec![false;END-BASE];
        let mut omitted = [0;4];
        let parent = self.parent.visit_slot_terms(owner as u64, |term| {
            let local = term.row.checked_sub(row_base).ok_or("schedule row precedes owner")?;
            if (ANCHOR..ANCHOR+END-BASE).contains(&local) {
                let offset = identity(&term,row_base,input_base)?;
                if seen[offset] {return Err("schedule duplicate translated anchor".into());}
                seen[offset] = true;
                for (index,(context,relation)) in [(0,Relation::Max),(1,Relation::Max),
                    (0,Relation::Cap),(1,Relation::Cap)].into_iter().enumerate() {
                    if wires(context,relation)?.contains(&(BASE+offset)) && self.active(owner,context,relation)? {
                        omitted[index] += 1;
                        return Ok(());
                    }
                }
            }
            sink(term)
        })?;
        if seen.iter().any(|b| !b) {return Err("schedule translated anchor census mismatch".into());}
        for (index,(context,relation)) in [(0,Relation::Max),(1,Relation::Max),
            (0,Relation::Cap),(1,Relation::Cap)].into_iter().enumerate() {
            let expected = if self.active(owner,context,relation)? {wires(context,relation)?.len()} else {0};
            if omitted[index] != expected {return Err("schedule retirement count mismatch".into());}
        }
        let emitted = parent.emitted.checked_sub(omitted.iter().sum()).ok_or("schedule count underflow")?;
        Ok(Counts{parent,omitted,emitted})
    }

    pub(crate) fn bind(&self, t: &mut Transcript) {
        self.parent.bind(t);
        t.append_bytes(b"schedule-anchor-rule",b"two-context-epoch-end-max-cap-header-anchor-permission-v2");
        t.append_bytes(b"schedule-anchor-census",self.anchor_hash.as_bytes());
        t.append_bytes(b"schedule-owner-policy",match self.policy {
            Policy::H21=>b"fixed-h21-epoch-end-max-clipped-cap-source-v2",
            #[cfg(test)] Policy::FixtureN3=>b"synthetic-n3-fixture-only-v1",
        });
        t.append_bytes(b"schedule-max-owner",b"epoch-end-minus-two");
        t.append_bytes(b"schedule-max-neighbors",b"previous-next-scheduled-epoch-ends-geometry-only");
        t.append_bytes(b"schedule-cap-source",b"ordinary-origin-minus-1090-clipped-containing-epoch-end-minus-two");
        for context in 0..2 {
            let (terminal,guard) = self.policy.endpoints(context).expect("compiled context");
            for value in [context,terminal,guard] {t.append_u64(b"schedule-context",value as u64);}
            for relation in [Relation::Max,Relation::Cap] {
                t.append_bytes(b"schedule-relation",match relation {Relation::Max=>b"MAX",Relation::Cap=>b"CAP"});
                let range = wires(context,relation).expect("compiled context");
                for value in [844_672,128,1088,range.start,range.end,
                    ANCHOR+range.start-BASE,ANCHOR+range.end-BASE,WIDTH,ROWS] {
                    t.append_u64(b"schedule-allocation",value as u64);
                }
            }
        }
    }
}

#[cfg(test)]
#[path="schedule_anchor_allocator_tests.rs"]
mod tests;

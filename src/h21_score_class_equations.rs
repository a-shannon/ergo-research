//! Fixed Eligible08 modern Score equations in original X coordinates.
//! A plan is arithmetic context and unresolved predicate requirements. It has
//! no witness, commitment, producing-role proof, or structural acceptance.
use super::{modern_spec, ScoreReplayAuthor, ScoreRelationReadAuthor,
    SCORE_X, SCORE_ROW, V_ALIAS_ROW, W_ALIAS_ROW, UPPER_LOCAL, ROW_WIDTH};
use super::super::Eligible08RegularScoreOwner;
use crate::{bank53_map::CutDescriptor, bank53_required_writer::{self, RequiredWriter,
    ScoreEndpointKind}, gkr::Gate, origin_score as score, sparse::Term};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

const WIDTH: usize = 1 << 20;
const STRIDE: usize = 128;
const CAP_BASE: [usize; 2] = [1_000_770, 1_002_818];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MemberKind { Regular, Clipped { context: usize } }

/// Each named predicate still needs its actual producing-role proof and the
/// common original-X commitment. Equality of these descriptions is not proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RequiredPredicate {
    Map { context: usize, owner: usize },
    Difficulty { owner: usize, height: usize },
    PreviousScore { context: usize, owner: usize },
    PremodernAnchor { context: usize, owner: usize },
    FirstModernScore { context: usize, owner: usize },
    Cap { context: usize, owner: usize, max_owner: usize },
    MaxRecurrence { context: usize, owner: usize, next: Option<usize> },
    WorkUpper { owner: usize, height: usize },
    HeaderDaa { owner: usize },
}

/// Requests identify the existing source mechanism. They neither perform
/// retirement nor authorize writes. Old Map-tail removal and HEADER helper
/// retirement are different operations; inactive Score and Slack stay separate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RetirementRequest {
    ExistingMapTail { context: usize, first: usize, end: usize },
    ScheduledCapHeader { context: usize, owner: usize, origin: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClassEquationPlan {
    descriptor: CutDescriptor,
    owner: usize,
    kind: MemberKind,
    authors: [Option<ScoreReplayAuthor>; 2],
}

impl Eligible08RegularScoreOwner {
    /// Includes clipped endpoints as well as the regular class. No source or
    /// NativePrefix is required; callers receive a plan, never an admission.
    pub(crate) fn equation_plan(owner: usize) -> Result<ClassEquationPlan, String> {
        ClassEquationPlan::for_member(CutDescriptor::eligible08(), owner)
    }
}

impl ClassEquationPlan {
    pub(crate) fn for_member(descriptor: CutDescriptor, owner: usize) -> Result<Self, String> {
        if descriptor != CutDescriptor::eligible08() || owner >= 1 << 21 {
            return Err("Score class fixed Eligible08 descriptor/owner".into());
        }
        let clipped = descriptor.guards().iter().position(|guard| owner == guard - 1);
        let (kind, active, previous, maximum) = if let Some(context) = clipped {
            let first = descriptor.modern_start() + STRIDE - 1;
            let previous = first + ((owner - first) / STRIDE) * STRIDE;
            let maximum = previous + STRIDE - descriptor.offset() - 1;
            (MemberKind::Clipped { context },
                std::array::from_fn(|c| c == context), previous, maximum)
        } else {
            let member = Eligible08RegularScoreOwner::classify(owner)?;
            (MemberKind::Regular, member.active(), member.previous_r_owner(), member.max_owner())
        };
        let authors = std::array::from_fn(|context| active[context].then_some(ScoreReplayAuthor {
            context, origin: owner + 1, previous_owner: previous,
            max_owner: maximum, cap_owner: owner,
        }));
        let plan = Self { descriptor, owner, kind, authors };
        plan.require_writer_specialization()?;
        Ok(plan)
    }

    pub(crate) fn owner(&self) -> usize { self.owner }
    pub(crate) fn kind(&self) -> MemberKind { self.kind }
    pub(crate) fn authors(&self) -> &[Option<ScoreReplayAuthor>; 2] { &self.authors }
    pub(crate) fn active(&self) -> [bool; 2] { self.authors.map(|a| a.is_some()) }

    /// Compact class traversal: one small plan at a time, no global witness.
    pub(crate) fn members() -> impl Iterator<Item = Result<Self, String>> {
        let d = CutDescriptor::eligible08();
        let first = d.modern_start() + STRIDE - 1;
        (first..d.guards()[0] - 1).step_by(STRIDE)
            .chain(d.guards().map(|guard| guard - 1))
            .map(move |owner| Self::for_member(d, owner))
    }

    /// Policy specialization only. Serializer, POINT and CorePool have no
    /// writer grant here. Slack's 387 cells are never part of Score's 2048.
    pub(crate) fn require_writer_specialization(&self) -> Result<(), String> {
        for context in 0..2 {
            let endpoint = match self.kind {
                MemberKind::Regular => ScoreEndpointKind::Regular,
                MemberKind::Clipped { .. } => ScoreEndpointKind::Clipped,
            };
            let required = if self.authors[context].is_some() {
                RequiredWriter::ScoreReplay { context, endpoint }
            } else { RequiredWriter::HeaderZero };
            for offset in crate::bank53_map::MAP_LIVE..crate::bank53_map::MAP_LIVE + score::INPUT {
                if bank53_required_writer::required_bank53_writer(self.owner, context, offset)
                    != Ok(required) {
                    return Err(format!("Score class writer owner {} context {context} offset {offset}", self.owner));
                }
            }
        }
        Ok(())
    }

    /// Selected imports of this modern Map class. Timestamp is not selected.
    /// The retained HEADER/DAA producing predicates are still required.
    pub(crate) fn map_difficulty_reads(&self, context: usize) -> Result<Vec<usize>, String> {
        if context >= 2 { return Err("Score class Map context".into()); }
        Ok((0..if self.owner < self.descriptor.terminals()[context] - 1 { 224 } else { 0 })
            .map(|bit| self.owner * WIDTH + crate::legacy_envelope_map::D_LOCAL + bit).collect())
    }

    pub(crate) fn required_predicates(&self) -> Vec<RequiredPredicate> {
        let mut out = vec![RequiredPredicate::HeaderDaa { owner: self.owner }];
        for context in 0..2 {
            // Map also produces its zero relation at/after its endpoint.
            out.push(RequiredPredicate::Map { context, owner: self.owner });
            if self.owner < self.descriptor.terminals()[context] - 1 {
                out.push(RequiredPredicate::Difficulty { owner: self.owner, height: self.owner + 2 });
            }
            if let Some(a) = self.authors[context] {
                out.push(RequiredPredicate::PreviousScore { context, owner: a.previous_owner });
                // PreviousScore recursively requires its own predecessor. These
                // are the irreducible premodern roots of that recurrence.
                for owner in super::ANCHOR_OWNERS {
                    out.push(RequiredPredicate::PremodernAnchor { context, owner });
                }
                out.push(RequiredPredicate::FirstModernScore { context,
                    owner: self.descriptor.modern_start() - 1 });
                out.push(RequiredPredicate::Cap { context, owner: self.owner, max_owner: a.max_owner });
                let end = self.descriptor.terminals()[context];
                let next = (a.max_owner + 2 < end)
                    .then_some((a.max_owner + 2 + STRIDE).min(end) - 2);
                out.push(RequiredPredicate::MaxRecurrence { context, owner: a.max_owner, next });
                out.push(RequiredPredicate::Difficulty { owner: a.max_owner, height: a.max_owner + 2 });
                out.push(RequiredPredicate::WorkUpper { owner: self.owner - 1, height: self.owner + 1 });
                out.push(RequiredPredicate::HeaderDaa { owner: self.owner - 1 });
            }
        }
        out
    }

    /// Checks exact ordered metadata only. Even a successful check leaves
    /// every required producing predicate unresolved.
    pub(crate) fn require_dependency_metadata(&self, provided: &[RequiredPredicate]) -> Result<(), String> {
        if provided != self.required_predicates().as_slice() {
            return Err(format!("Score class unresolved dependency metadata owner {}", self.owner));
        }
        Ok(())
    }

    pub(crate) fn retirement_requests(&self) -> Vec<RetirementRequest> {
        let mut out = Vec::new();
        for context in 0..2 {
            out.push(RetirementRequest::ExistingMapTail { context,
                first: crate::bank53_map::MAP_TAIL_START, end: crate::bank53_map::MAP_TAIL_END });
            if self.authors[context].is_some() {
                out.push(RetirementRequest::ScheduledCapHeader {
                    context, owner: self.owner, origin: self.owner + 1 });
            }
        }
        out
    }

    /// Validate the exact pre-existing Map-tail gate, never merely its range.
    /// The Map translator owns removal; replacements/HEADER retirement still
    /// need the existing merger and the named Score/Slack/Cap producing roles.
    pub(crate) fn require_map_tail_source(&self, context: usize, local: usize, old: &Term) -> Result<(), String> {
        if context >= 2 || !(crate::bank53_map::MAP_TAIL_START..crate::bank53_map::MAP_TAIL_END).contains(&local) {
            return Err("Score class Map retirement coordinate".into());
        }
        crate::bank53_map::exact_zero_tail(old, self.owner as u64, local)
    }

    /// Name the replacement author required by the existing policy for one
    /// old tail gate. This is still an unresolved producing predicate: the
    /// request is not discharged by finding that its addresses are disjoint.
    pub(crate) fn map_tail_replacement(&self, context: usize, local: usize) -> Result<RequiredWriter, String> {
        if !(crate::bank53_map::MAP_TAIL_START..crate::bank53_map::MAP_TAIL_END).contains(&local) {
            return Err("Score class Map replacement coordinate".into());
        }
        bank53_required_writer::required_bank53_writer(self.owner, context, local)
            .map_err(str::to_string)
    }

    /// Specialize the old HEADER Cap zero gate named by a request. The
    /// existing header_scheduled_retirement::Merge remains the only remover;
    /// checking this source tuple does not supply the scheduled Cap proof.
    pub(crate) fn require_cap_header_source(&self, context: usize, bit: usize, old: &Term) -> Result<(), String> {
        if context >= 2 || bit >= 2048 || self.authors[context].is_none() {
            return Err("Score class Cap HEADER request inactive/coordinate".into());
        }
        let expected = Term { row: self.owner * ROW_WIDTH + [357_978, 360_026][context] + bit,
            gate: Gate { left: self.owner * WIDTH + CAP_BASE[context] + bit,
                right: self.owner * WIDTH, c0: Fr::zero(), c1: Fr::one(),
                c2: Fr::zero(), c3: Fr::zero() } };
        if old != &expected { return Err("Score class Cap HEADER exact old gate".into()); }
        Ok(())
    }

    /// Emit only this member's active Score rows, in native producer order.
    /// Inactive Score equations remain the existing HEADER zero anchors.
    pub(crate) fn emit(&self, context: usize, sink: impl FnMut(Term)) -> Result<usize, String> {
        let author = self.authors.get(context).ok_or("Score class context")?;
        match author {
            Some(author) => emit_context(*author, &modern_spec(self.descriptor, context)?, sink),
            None => Ok(0),
        }
    }

    pub(crate) fn reads(&self) -> Vec<(usize, ScoreRelationReadAuthor)> {
        let layout = score::Layout::new();
        let mut out = Vec::new();
        for a in self.authors.iter().flatten() {
            for bit in 0..layout.r.len() {
                out.push((a.previous_owner * WIDTH + SCORE_X[a.context] + layout.r.start + bit,
                    ScoreRelationReadAuthor::PreviousR { context: a.context, owner: a.previous_owner }));
            }
            for bit in 0..layout.sv.len() {
                out.push((self.owner * WIDTH + CAP_BASE[a.context] + 740 + bit,
                    ScoreRelationReadAuthor::Cap { context: a.context, origin: a.origin,
                        max_owner: a.max_owner, cap_owner: self.owner }));
            }
            for bit in 0..layout.sw.len() {
                out.push(((self.owner - 1) * WIDTH + UPPER_LOCAL + bit,
                    ScoreRelationReadAuthor::WorkUpper { owner: self.owner - 1, height: self.owner + 1 }));
            }
        }
        out
    }

    /// Agreement of a source with this deterministic recipe, not proof of its
    /// imported values or a common commitment. Values remain with old producers.
    pub(crate) fn require_source_recipe(&self, terms: [&[Term]; 2],
        reads: &[(usize, ScoreRelationReadAuthor, Fr)],
        authors: &[Option<ScoreReplayAuthor>; 2]) -> Result<(), String> {
        if authors != &self.authors { return Err("Score class source authors/activity".into()); }
        for context in 0..2 {
            let mut cursor = 0;
            let mut mismatch = None;
            self.emit(context, |term| {
                if mismatch.is_none() && terms[context].get(cursor) != Some(&term) {
                    mismatch = Some(format!("Score class source equation owner {} context {context} ordinal {cursor} row {} left {} right {}",
                        self.owner, term.row, term.gate.left, term.gate.right));
                }
                cursor += 1;
            })?;
            if let Some(error) = mismatch { return Err(error); }
            if cursor != terms[context].len() {
                return Err(format!("Score class source trailing equations owner {} context {context} expected {cursor} found {}",
                    self.owner, terms[context].len()));
            }
        }
        if !reads.iter().map(|&(wire, author, _)| (wire, author)).eq(self.reads()) {
            return Err("Score class source read order/operand/multiplicity".into());
        }
        Ok(())
    }

    /// Coefficients of ONE member and ONE active context, for arbitrary Fr
    /// points. No full-class cost or global verifier claim follows. This folds
    /// the local symbolic relation and explicit alias formulas without a
    /// physical term vector; both operands retain their equality weights.
    pub(crate) fn coefficients(&self, context: usize, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if (r.len(), u.len(), v.len()) != (40, 41, 41) { return Err("Score class coefficient dimensions".into()); }
        let author = self.authors.get(context).ok_or("Score class coefficient context")?;
        let mut out = [Fr::zero(); 4];
        let Some(a) = author else { return Ok(out); };
        let owner = self.owner;
        let layout = score::Layout::new();
        let mut add = |row, left, right, cs: [Fr; 4]| {
            let weight = eq(r, row) * eq(u, left) * eq(v, right);
            for (sum, coefficient) in out.iter_mut().zip(cs) { *sum += weight * coefficient; }
        };
        score::emit_local(&modern_spec(self.descriptor, context)?, |local| {
            let g = local.term.gate;
            let left_owner = if local.previous { a.previous_owner } else { owner };
            add(owner * ROW_WIDTH + SCORE_ROW[context] + local.term.row,
                left_owner * WIDTH + SCORE_X[context] + g.left,
                owner * WIDTH + SCORE_X[context] + g.right, [g.c0, g.c1, g.c2, g.c3]);
        })?;
        for bit in 0..layout.sv.len() {
            add(owner * ROW_WIDTH + V_ALIAS_ROW[context] + bit,
                owner * WIDTH + SCORE_X[context] + layout.sv.start + bit,
                owner * WIDTH + CAP_BASE[context] + 740 + bit,
                [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]);
        }
        for bit in 0..layout.sw.len() {
            let row = owner * ROW_WIDTH + W_ALIAS_ROW[context] + bit;
            add(row, owner * WIDTH + SCORE_X[context] + layout.sw.start + bit, 0,
                [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]);
            add(row, (owner - 1) * WIDTH + UPPER_LOCAL + bit, 0,
                [Fr::zero(), -Fr::one(), Fr::zero(), Fr::zero()]);
        }
        Ok(out)
    }
}

fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |product, (bit, z)|
        product * if index >> bit & 1 == 1 { *z } else { Fr::one() - z })
}

/// Shared pure placement of the production native Score relation. This helper
/// also preserves the existing first-modern source caller's compatibility.
pub(super) fn emit_context(a: ScoreReplayAuthor, spec: &score::Spec,
    mut sink: impl FnMut(Term)) -> Result<usize, String> {
    let c = a.context;
    if c >= 2 || a.origin == 0 || a.origin != a.cap_owner + 1 || a.cap_owner >= 1 << 21
        || a.previous_owner >= a.cap_owner || !spec.active || !spec.reducing || spec.first {
        return Err("Score equation placement author/spec".into());
    }
    let owner = a.cap_owner;
    let layout = score::Layout::new();
    let mut error = None;
    let count = score::emit_local(spec, |local| {
        let mut term = local.term;
        if local.previous && !layout.r.contains(&term.gate.left) {
            error = Some("Score relation predecessor outside R".to_string()); return;
        }
        term.row += owner * ROW_WIDTH + SCORE_ROW[c];
        let left_owner = if local.previous { a.previous_owner } else { owner };
        term.gate.left += left_owner * WIDTH + SCORE_X[c];
        term.gate.right += owner * WIDTH + SCORE_X[c];
        sink(term);
    })?;
    if let Some(error) = error { return Err(error); }
    let zero = Fr::zero(); let one = Fr::one();
    for bit in 0..layout.sv.len() {
        sink(Term { row: owner * ROW_WIDTH + V_ALIAS_ROW[c] + bit,
            gate: Gate { left: owner * WIDTH + SCORE_X[c] + layout.sv.start + bit,
                right: owner * WIDTH + CAP_BASE[c] + 740 + bit,
                c0: zero, c1: one, c2: -one, c3: zero } });
    }
    for bit in 0..layout.sw.len() {
        let row = owner * ROW_WIDTH + W_ALIAS_ROW[c] + bit;
        sink(Term { row, gate: Gate { left: owner * WIDTH + SCORE_X[c] + layout.sw.start + bit,
            right: 0, c0: zero, c1: one, c2: zero, c3: zero } });
        sink(Term { row, gate: Gate { left: (owner - 1) * WIDTH + UPPER_LOCAL + bit,
            right: 0, c0: zero, c1: -one, c2: zero, c3: zero } });
    }
    Ok(count + layout.sv.len() + 2 * layout.sw.len())
}

#[cfg(test)]
#[path = "h21_score_class_equations_tests.rs"]
mod tests;

//! Source-owned Score anchors and first modern Score/Cap join for Eligible08.
//! Stages remain opaque until HEADER retirement and complete ROW/X admission.
use super::*;
use ark_ff::{One, Zero};
use crate::{gkr::Gate, origin_score as score,
    h21_scheduled_max_cap::{Eligible08NativeSnapshot, FirstModernCapLease,
        MaxStream, ScoreEndpointLease}};

#[path = "h21_score_terminal_public.rs"]
mod h21_score_terminal_public;
#[path = "h21_score_import_seam.rs"]
mod h21_score_import_seam;
#[path = "h21_score_class_equations.rs"]
pub(super) mod h21_score_class_equations;

const ANCHOR_OWNERS: [usize; 2] = [417_790, 845_758];
const FIRST_MODERN_OWNER: usize = 845_759;
const SCORE_X: [usize; 2] = [677_501, 685_693];
const SCORE_ROW: [usize; 2] = [487_421, 502_652];
const V_ALIAS_ROW: [usize; 2] = [491_629, 506_860];
const W_ALIAS_ROW: [usize; 2] = [491_694, 506_925];
const UPPER_LOCAL: usize = 987_450;
const ROW_WIDTH: usize = 1 << 19;

#[cfg(test)]
#[path = "h21_structural_roster.rs"]
pub(crate) mod structural_roster;

#[cfg(test)]
#[path = "h21_native_owner_values.rs"]
pub(crate) mod native_owner_values;

#[derive(Clone, Debug, PartialEq, Eq)]
struct RLease {
    parent_root: [u8; 32],
    parent_total: [u8; 28],
    parent_profile: [u8; 32],
    cut_identity: Vec<u8>,
    binding: crate::legacy_envelope_map::Binding,
    context: usize,
    writer_owner: usize,
    value: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AnchorRecord {
    parent_root: [u8; 32],
    parent_total: [u8; 28],
    parent_profile: [u8; 32],
    cut_identity: Vec<u8>,
    binding: crate::legacy_envelope_map::Binding,
    context: usize,
    owner: usize,
    bits: Vec<bool>,
    r: BigUint,
    terms: Vec<Term>,
}

/// One first-anchor physical Score bit. This is an anchor author, rather than
/// the modern Score replay author with previous-R/MAX/Cap premises.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Eligible08ScoreAnchorCell {
    wire: usize,
    context: usize,
    value: bool,
}

impl Eligible08ScoreAnchorCell {
    pub(crate) fn physical_wire(&self) -> usize { self.wire }
    pub(crate) fn context(&self) -> usize { self.context }
    pub(crate) fn value(&self) -> bool { self.value }
}

/// Both first-anchor records retain their one generated Map template and the
/// native Work LOCAL publication at owner417789. No second anchor is staged.
#[derive(Clone)]
pub(super) struct FirstScoreAnchorSource {
    template: H21EligibleMapStage,
    claimed: H21EligibleMapStage,
    maps: [Map; 2],
    upper: crate::packed_owner_assembly::WorkUpperPublication,
    source_word: BigUint,
    records: [AnchorRecord; 2],
}

impl FirstScoreAnchorSource {
    fn new(template: H21EligibleMapStage, maps: [Map; 2],
        upper: crate::packed_owner_assembly::WorkUpperPublication,
        source_word: BigUint) -> Result<Self, String> {
        let cells = upper.checked_upper(template.parent_root, template.parent_total,
            template.parent_profile, &template.cut_identity, ANCHOR_OWNERS[0] - 1)?;
        if upper_word(ANCHOR_OWNERS[0] - 1, cells)? != source_word {
            return Err("C441 source_upper differs from typed Work Upper".into());
        }
        let mut records = Vec::with_capacity(2);
        let mut claimed = template.clone();
        for context in 0..2 {
            let u = maps[context].cap().to_biguint().ok_or("C441 negative Map cap")?;
            let record = score_material(&template, H21EligibleMapStage::descriptor(),
                context, source_word.clone(), u, None)?;
            claimed.claim_score_anchor(record.clone(), None)?;
            records.push(record);
        }
        Ok(Self { template, claimed, maps, upper, source_word,
            records: records.try_into().map_err(|_| "C441 anchor record census")? })
    }

    pub(super) fn checked_cells(&self,
        expected: &crate::packed_owner_assembly::HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass,
        map_slack: &Eligible08MapSlackBundle,
    ) -> Result<Vec<Eligible08ScoreAnchorCell>, String> {
        use crate::daa_history_roster::OwnerClass;
        let template = &self.template;
        let descriptor = H21EligibleMapStage::descriptor();
        if owner != ANCHOR_OWNERS[0] || class != OwnerClass::Carry
            || template.owner != owner || template.class != class
            || template.cut_identity != descriptor.canonical_identity()
            || !expected.matches_sink(template.parent_root, template.parent_total,
                template.parent_profile, &template.cut_identity, owner)
            || template.claims.len() != 2 * BANK53_MAP_LIVE_BITS
            || template.score_terms.iter().any(|terms| !terms.is_empty())
            || template.cap_terms.iter().any(|terms| !terms.is_empty()) {
            return Err("C441 exact first-anchor parent/cut/owner/Carry Map template".into());
        }
        let map = map_slack.map_lease();
        let map_cells = map.checked_cells(expected, owner, class)?;
        for cell in map_cells {
            let local = cell.physical_wire().checked_sub(owner * WIDTH)
                .ok_or("C441 Map cell outside owner")?;
            if template.claims.get(&local)
                != Some(&(H21StageAuthor::Map(cell.context()), cell.value())) {
                return Err("C441 retained Map template differs from paired source".into());
            }
        }
        let upper = self.upper.checked_upper(template.parent_root, template.parent_total,
            template.parent_profile, &template.cut_identity, owner - 1)?;
        let w = upper_word(owner - 1, upper)?;
        if w != self.source_word {
            return Err("C441 retained typed Upper/source_upper mismatch".into());
        }
        let mut replay = template.clone();
        let mut cells = Vec::with_capacity(4096);
        let mut row_authors = std::collections::BTreeMap::new();
        for context in 0..2 {
            let exact_map = Map::new_modern_global_u_selected_lower(
                descriptor.terminals()[context] as u64, 21, 55,
                LowerSelector { source: LowerSource::HeaderDifficulty { height: 841_729 },
                    branch: LowerBranch::Pivot(54) })?;
            if self.maps[context].binding() != template.map_bindings[context]
                || self.maps[context].binding() != exact_map.binding()
                || map.map_binding(context)? != &template.map_bindings[context]
                || self.maps[context].n() != descriptor.terminals()[context] as u64
                || self.maps[context].h() != 21
                || self.maps[context].binding().parent_root.is_some()
                || map.terms(context)? != template.map_terms[context].as_slice() {
                return Err("C441 retained Map context/cap/binding/terms".into());
            }
            let u = self.maps[context].cap().to_biguint().ok_or("C441 negative replay Map cap")?;
            let record = score_material(template, descriptor, context, w.clone(), u, None)?;
            if record != self.records[context] {
                return Err("C441 complete independent Score record/ordered term replay".into());
            }
            replay.claim_score_anchor(record, None)?;
            let domain = H21EligibleMapStage::score_live(context)?;
            if domain.len() != 2048 { return Err("C441 Score exact context width".into()); }
            for local in domain {
                let &(author, value) = self.claimed.claims.get(&local)
                    .ok_or("C441 absent Score anchor bit")?;
                if author != H21StageAuthor::ScoreAnchor(context) {
                    return Err("C441 exact ScoreAnchor author".into());
                }
                cells.push(Eligible08ScoreAnchorCell { wire: owner * WIDTH + local,
                    context, value });
            }
            // Terms can repeat a ROW within one source polynomial. Distinct
            // source families and contexts must never share a ROW.
            let slack = map_slack.checked_slack_terms(expected, owner, class, context)?;
            for (role, terms) in [(context * 3, map.terms(context)?),
                (context * 3 + 1, self.records[context].terms.as_slice()),
                (context * 3 + 2, slack)] {
                for term in terms {
                    let local = term.row.checked_sub(owner * ROW_WIDTH)
                        .ok_or("C441 source ROW before owner")?;
                    let (source, destination, width) = match role % 3 {
                        0 => (409_600 + context * 32_768, [477_074, 492_305][context], 10_347),
                        1 => (SCORE_ROW[context], SCORE_ROW[context], 4_497),
                        _ => (409_600 + context * 32_768 + crate::bank53_slack::SLACK_ROW_OFFSET,
                            [491_918, 507_149][context], 387),
                    };
                    if !(source..source + width).contains(&local) {
                        return Err("C441 source ROW outside exact family envelope".into());
                    }
                    let destination_row = owner * ROW_WIDTH + destination + local - source;
                    if term.row / ROW_WIDTH != owner
                        || row_authors.insert(destination_row, role).is_some_and(|old| old != role) {
                        return Err("C441 Map/Score/Slack source ROW collision or owner".into());
                    }
                }
            }
        }
        if replay != self.claimed || cells.len() != 4096
            || self.claimed.claims.len() != 2 * BANK53_MAP_LIVE_BITS + 4096 {
            return Err("C441 exact replayed Score/Map author and bit census".into());
        }
        Ok(cells)
    }

    pub(super) fn terms(&self, context: usize) -> Result<&[Term], String> {
        self.records.get(context).map(|record| record.terms.as_slice())
            .ok_or_else(|| "C441 Score context outside ordered pair".into())
    }

    pub(super) fn checked_packed(&self, map_slack: &Eligible08MapSlackBundle,
        row: &crate::packed_owner_assembly::NativePackedRow) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        let expected = map_slack.map_lease().binding();
        row.require_header_source_binding(expected, ANCHOR_OWNERS[0], OwnerClass::Carry)?;
        let cells = self.checked_cells(expected, ANCHOR_OWNERS[0], OwnerClass::Carry, map_slack)?;
        let bytes = row.packed_bytes();
        for cell in cells {
            let local = cell.physical_wire() % WIDTH;
            let packed = bytes.get(local / 8).ok_or("C443 predecessor packed row width")?;
            if ((packed >> (local % 8)) & 1 != 0) != cell.value() {
                return Err(format!("C443 predecessor packed Score mismatch wire{local}"));
            }
        }
        Ok(())
    }

    /// Conditional mechanical fixture only. The retained Upper has the checked
    /// projection shape, but these synthetic operands are not a native LOCAL
    /// publication and do not establish source authentication.
    #[cfg(test)]
    pub(super) fn synthetic_for_test(map_slack: &Eligible08MapSlackBundle)
        -> Result<Self, String> {
        Self::synthetic_with_plan_for_test(map_slack, None)
    }

    /// Geometry-only fixture under either the historical diagnostic identity
    /// or an actual plan binding. Production parent/source checks still run.
    #[cfg(test)]
    pub(super) fn synthetic_with_plan_for_test(map_slack: &Eligible08MapSlackBundle,
        plan: Option<&WorkTreeHistoryPlan>,
    ) -> Result<Self, String> {
        let owner = ANCHOR_OWNERS[0];
        let mut template = H21EligibleMapStage::test_identity_only(owner)?;
        template.class = crate::daa_history_roster::OwnerClass::Carry;
        if let Some(plan) = plan {
            let binding = crate::packed_owner_assembly::HeaderSourceBinding::for_plan(plan, owner)?;
            template.parent_root = plan.descriptor().root;
            template.parent_total = plan.work_profile().total_be28;
            template.parent_profile = binding.profile();
            template.cut_identity = H21EligibleMapStage::descriptor().canonical_identity();
            if map_slack.map_lease().binding() != &binding {
                return Err("C448 synthetic Score exact plan binding".into());
            }
        }
        let expected = map_slack.map_lease().binding();
        for cell in map_slack.map_lease().checked_cells(expected, owner, template.class)? {
            template.claim_cell(H21StageAuthor::Map(cell.context()),
                cell.physical_wire() - owner * WIDTH, cell.value())?;
        }
        for context in 0..2 {
            template.map_terms[context] = map_slack.map_lease().terms(context)?.to_vec();
        }
        let plan = WorkTreeHistoryPlan::compile(1_827_840, 21,
            template.parent_root, template.parent_total)?;
        let upper_owner = owner - 1;
        let source_word = BigUint::from(owner);
        let upper: Vec<_> = (0..224).map(|bit| (upper_owner * WIDTH + UPPER_LOCAL + bit,
            Fr::from(source_word.bit(bit as u64) as u64))).collect();
        let operands = crate::h21_work_local_source::operand_domain(upper_owner)?
            .into_iter().map(|wire| {
                let value = upper.iter().find(|&&(found, _)| found == wire)
                    .map(|&(_, value)| value).unwrap_or_else(Fr::zero);
                (wire, value)
            }).collect();
        let publication = crate::packed_owner_assembly::WorkUpperPublication {
            parent: crate::h21_work_local_source::Parent {
                root: template.parent_root, total: template.parent_total,
                profile: template.parent_profile, headers: 1_827_840,
                slots: 1 << 21, cut: template.cut_identity.clone(),
            }, owner: upper_owner, height: upper_owner + 2,
            terms: crate::h21_work_local_source::canonical_terms(&plan, upper_owner)?,
            operands, upper,
        };
        Self::new(template, H21EligibleMapStage::source_maps()?, publication, source_word)
    }

    #[cfg(test)]
    pub(super) fn remove_bit_for_test(&mut self, context: usize, index: usize)
        -> Result<(), String> {
        if context >= 2 || index >= 2048 { return Err("C441 test Score bit outside domain".into()); }
        self.claimed.claims.remove(&(SCORE_X[context] + index));
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn flip_bit_for_test(&mut self, context: usize, index: usize)
        -> Result<(), String> {
        if context >= 2 || index >= 2048 { return Err("C441 test Score bit outside domain".into()); }
        self.claimed.claims.get_mut(&(SCORE_X[context] + index))
            .ok_or("C441 test Score bit missing")?.1 ^= true;
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn alter_term_for_test(&mut self, context: usize, index: usize)
        -> Result<(), String> {
        let term = self.records.get_mut(context).and_then(|record| record.terms.get_mut(index))
            .ok_or("C441 test Score term outside source")?;
        term.gate.c0 += Fr::one();
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn swap_contexts_for_test(&mut self) { self.records.swap(0, 1); }

    #[cfg(test)]
    pub(super) fn swap_maps_for_test(&mut self) { self.maps.swap(0, 1); }

    #[cfg(test)]
    pub(super) fn replace_map_for_test(&mut self, context: usize, map: Map)
        -> Result<(), String> {
        *self.maps.get_mut(context).ok_or("C441 test Map context outside pair")? = map;
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn mutate_upper_for_test(&mut self, kind: usize) -> Result<(), String> {
        match kind {
            0 => { self.upper.upper.pop().ok_or("C441 test Upper already missing")?; },
            1 => {
                self.upper.upper[0].1 = Fr::one() - self.upper.upper[0].1;
                let (wire, value) = self.upper.upper[0];
                self.upper.operands.iter_mut().find(|(found, _)| *found == wire)
                    .ok_or("C441 test Upper operand absent")?.1 = value;
            },
            2 => { self.upper.owner += 1; },
            3 => { self.upper.parent.root[0] ^= 1; },
            4 => {
                // Reverse values while preserving physical little-endian wires.
                let values: Vec<_> = self.upper.upper.iter().map(|&(_, value)| value).rev().collect();
                for ((_, value), reversed) in self.upper.upper.iter_mut().zip(values) { *value = reversed; }
                for &(wire, value) in &self.upper.upper {
                    self.upper.operands.iter_mut().find(|(found, _)| *found == wire)
                        .ok_or("C441 test Upper endian operand absent")?.1 = value;
                }
            },
            _ => return Err("C441 test Upper mutation unknown".into()),
        }
        Ok(())
    }
}

impl H21EligibleContext<'_> {
    pub(super) fn first_score_anchor_from_stage(&self, stage: H21EligibleMapStage)
        -> Result<FirstScoreAnchorSource, String> {
        if stage.owner != ANCHOR_OWNERS[0] { return Err("C441 first anchor owner only".into()); }
        let parent = self.producer.work_local_native_parent()?;
        let owner = ANCHOR_OWNERS[0] - 1;
        let lease = self.producer.native_work_local_lease_for_owner(owner)?;
        self.producer.require_native_work_local_lease_for_owner(&parent, owner, &lease)?;
        let upper = self.producer.work_upper_publication(owner, lease.local())?;
        let w = source_upper(ANCHOR_OWNERS[0] + 1, self.producer.input,
            &self.producer.exports)?;
        for context in 0..2 {
            if self.maps[context].cap().to_biguint() != Some(self.envelopes[context].u.clone())
                || self.maps[context].binding() != stage.map_bindings[context] {
                return Err("C441 first Score envelope U/Map cap binding".into());
            }
        }
        FirstScoreAnchorSource::new(stage, self.maps.clone(), upper, w)
    }
}

/// Four source-owned Score leases, with no serialized row or finish operation.
#[derive(Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) struct H21PremodernAnchors {
    first: H21EligibleMapStage,
    second: H21EligibleMapStage,
    first_r: [RLease; 2],
    second_r: [RLease; 2],
}

/// A checked source projection, not native publication authority. The native
/// wrapper below additionally retains both physical Upper publications.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct R450Projection {
    pub(super) cells: [Vec<(usize, usize, bool)>; 2],
}

#[derive(Clone, PartialEq, Eq)]
struct R450Candidate {
    anchors: H21PremodernAnchors,
    projection: R450Projection,
}

/// Opaque local custody only: no public X/ROW transfer, serialization or proof.
/// Both source stages, all four R leases, ordered Score terms and the two
/// complete physical Work LOCAL/Upper sources remain alive together.
#[derive(Clone)]
pub(crate) struct PremodernRPublication {
    candidate: R450Candidate,
    templates: [H21EligibleMapStage; 2],
    maps: [Map; 2],
    upper: [crate::packed_owner_assembly::WorkUpperPublication; 2],
}

/// Second-anchor source retained with the checked two-anchor replay and the
/// typed first-anchor author it causally consumes. It owns no packed mutation.
#[cfg_attr(test, derive(Clone))]
pub(super) struct SecondScoreAnchorSource {
    template: H21EligibleMapStage,
    publication: PremodernRPublication,
    first: FirstScoreAnchorSource,
    first_map_slack: Eligible08MapSlackBundle,
}

fn project_r450(anchors: &H21PremodernAnchors) -> Result<R450Projection, String> {
    let mut cells = [Vec::with_capacity(450), Vec::with_capacity(450)];
    for (anchor, stage) in [&anchors.first, &anchors.second].into_iter().enumerate() {
        if stage.owner != ANCHOR_OWNERS[anchor] { return Err("R450 anchor owner/order".into()); }
        for context in 0..2 {
            for bit in 0..225 {
                let local = SCORE_X[context] + score::Layout::new().r.start + bit;
                let &(author, value) = stage.claims.get(&local).ok_or("R450 missing R author")?;
                if author != H21StageAuthor::ScoreAnchor(context) {
                    return Err("R450 exact R author".into());
                }
                cells[anchor].push((stage.owner * WIDTH + local, context, value));
            }
        }
    }
    Ok(R450Projection { cells })
}

fn upper_word(owner: usize, cells: &[(usize, Fr)]) -> Result<BigUint, String> {
    if cells.len() != 224 { return Err("R450 Upper census".into()); }
    let mut value = BigUint::from(0u8);
    for (bit, &(wire, digit)) in cells.iter().enumerate() {
        if wire != owner * WIDTH + UPPER_LOCAL + bit || !(digit.is_zero() || digit.is_one()) {
            return Err("R450 Upper wire/boolean/order".into());
        }
        if digit.is_one() { value |= BigUint::from(1u8) << bit; }
    }
    Ok(value)
}

/// Rebuild from independent W and Map premises. No supplied first_r value is
/// used as a seed: only the newly computed first stage/leases feed stage two.
fn replay_full_r450(candidate: &R450Candidate, templates: &[H21EligibleMapStage; 2],
    maps: &[Map; 2], upper: [&[(usize, Fr)]; 2]) -> Result<H21PremodernAnchors, String> {
    let descriptor = H21EligibleMapStage::descriptor();
    let bindings = [maps[0].binding(), maps[1].binding()];
    for (anchor, stage) in templates.iter().enumerate() {
        if stage.owner != ANCHOR_OWNERS[anchor]
            || stage.cut_identity != descriptor.canonical_identity()
            || stage.map_bindings != bindings
            || stage.parent_root != templates[0].parent_root
            || stage.parent_total != templates[0].parent_total
            || stage.parent_profile != templates[0].parent_profile
            || stage.claims.values().any(|(author, _)| !matches!(author, H21StageAuthor::Map(_)))
            || stage.score_terms.iter().any(|terms| !terms.is_empty())
            || stage.cap_terms.iter().any(|terms| !terms.is_empty()) {
            return Err("R450 expected source identity/empty Score stage".into());
        }
    }
    for context in 0..2 {
        if bindings[context].n != descriptor.terminals()[context] as u64
            || bindings[context].h != 21 || bindings[context].parent_root.is_some()
            || bindings[context].e > 64 {
            return Err("R450 exact Map context/cut".into());
        }
    }
    let w0 = upper_word(ANCHOR_OWNERS[0] - 1, upper[0])?;
    let w1 = upper_word(ANCHOR_OWNERS[1] - 1, upper[1])?;
    let mut first = templates[0].clone();
    let mut first_r = Vec::with_capacity(2);
    for context in 0..2 {
        let u = maps[context].cap().to_biguint().ok_or("R450 negative U")?;
        let record = score_material(&first, descriptor, context, w0.clone(), u, None)?;
        first_r.push(first.claim_score_anchor(record, None)?);
    }
    let first_r: [RLease; 2] = first_r.try_into().map_err(|_| "R450 first lease census")?;
    let mut second = templates[1].clone();
    let mut second_r = Vec::with_capacity(2);
    for context in 0..2 {
        let prior = Some((&first_r[context], &first));
        let u = maps[context].cap().to_biguint().ok_or("R450 negative U")?;
        let record = score_material(&second, descriptor, context, w1.clone(), u, prior)?;
        second_r.push(second.claim_score_anchor(record, prior)?);
    }
    let second_r: [RLease; 2] = second_r.try_into().map_err(|_| "R450 second lease census")?;
    let expected = H21PremodernAnchors { first, second, first_r, second_r };
    if candidate.anchors.first != expected.first || candidate.anchors.second != expected.second
        || candidate.anchors.first_r != expected.first_r || candidate.anchors.second_r != expected.second_r {
        return Err("R450 independent canonical anchor/lease replay".into());
    }
    let projection = project_r450(&expected)?;
    if candidate.projection != projection { return Err("R450 exact ordered projection".into()); }
    Ok(expected)
}

fn replay_r450(candidate: &R450Candidate, templates: &[H21EligibleMapStage; 2],
    maps: &[Map; 2], upper: [&[(usize, Fr)]; 2]) -> Result<R450Projection, String> {
    let replay = replay_full_r450(candidate, templates, maps, upper)?;
    project_r450(&replay)
}

/// Conditional arithmetic/coordinates fixture only; it cannot construct a
/// PremodernRPublication or claim a physical/native Upper source.
#[cfg(test)]
pub(super) fn conditional_r450_projection_for_test() -> (R450Projection, H21EligibleMapStage) {
    let (candidate, templates, maps, upper) = tests::r450_fixture();
    let projection = replay_r450(&candidate, &templates, &maps, [&upper[0], &upper[1]]).unwrap();
    (projection, templates[1].clone())
}

impl PremodernRPublication {
    pub(super) fn checked_full_replay(&self, root: [u8; 32], total: [u8; 28], profile: [u8; 32],
        cut: &[u8], maps: &[crate::legacy_envelope_map::Binding; 2])
        -> Result<H21PremodernAnchors, String> {
        for stage in &self.templates {
            if stage.parent_root != root || stage.parent_total != total || stage.parent_profile != profile
                || stage.cut_identity != cut || &stage.map_bindings != maps {
                return Err("R450 exact destination parent/root/total/profile/cut/Maps".into());
            }
        }
        let first = self.upper[0].checked_upper(root, total, profile, cut, ANCHOR_OWNERS[0] - 1)?;
        let second = self.upper[1].checked_upper(root, total, profile, cut, ANCHOR_OWNERS[1] - 1)?;
        replay_full_r450(&self.candidate, &self.templates, &self.maps, [first, second])
    }

    pub(super) fn checked_projection(&self, root: [u8; 32], total: [u8; 28], profile: [u8; 32],
        cut: &[u8], maps: &[crate::legacy_envelope_map::Binding; 2]) -> Result<R450Projection, String> {
        project_r450(&self.checked_full_replay(root, total, profile, cut, maps)?)
    }
}

impl SecondScoreAnchorSource {
    pub(super) fn new(template: H21EligibleMapStage, publication: &PremodernRPublication,
        first: &FirstScoreAnchorSource, first_map_slack: &Eligible08MapSlackBundle)
        -> Result<Self, String> {
        let first_binding = first_map_slack.map_lease().binding();
        let first_cells = first.checked_cells(first_binding, ANCHOR_OWNERS[0],
            crate::daa_history_roster::OwnerClass::Carry, first_map_slack)?;
        let replay = publication.checked_full_replay(template.parent_root,
            template.parent_total, template.parent_profile, &template.cut_identity,
            &template.map_bindings)?;
        if replay.first != first.claimed
            || replay.second.owner != ANCHOR_OWNERS[1]
            || template.owner != ANCHOR_OWNERS[1]
            || template.class != crate::daa_history_roster::OwnerClass::Carry
            || replay.second.class != crate::daa_history_roster::OwnerClass::Carry
            || template.parent_root != replay.second.parent_root
            || template.parent_total != replay.second.parent_total
            || template.parent_profile != replay.second.parent_profile
            || template.cut_identity != replay.second.cut_identity
            || template.map_bindings != replay.second.map_bindings
            || first_cells.len() != 4096 {
            return Err("C443 second source requires matching typed first source and full replay".into());
        }
        Ok(Self { template, publication: publication.clone(), first: first.clone(),
            first_map_slack: first_map_slack.clone() })
    }

    pub(super) fn checked_cells(&self,
        expected: &crate::packed_owner_assembly::HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass,
        map_slack: &Eligible08MapSlackBundle,
    ) -> Result<Vec<Eligible08ScoreAnchorCell>, String> {
        use crate::daa_history_roster::OwnerClass;
        let descriptor = H21EligibleMapStage::descriptor();
        if owner != ANCHOR_OWNERS[1] || class != OwnerClass::Carry
            || self.template.owner != owner || self.template.class != class
            || self.template.cut_identity != descriptor.canonical_identity()
            || !expected.matches_sink(self.template.parent_root, self.template.parent_total,
                self.template.parent_profile, &self.template.cut_identity, owner)
            || self.template.claims.len() != 2 * BANK53_MAP_LIVE_BITS
            || self.template.score_terms.iter().any(|terms| !terms.is_empty())
            || self.template.cap_terms.iter().any(|terms| !terms.is_empty()) {
            return Err("C443 exact second-anchor parent/cut/owner/Carry Map template".into());
        }
        map_slack.checked_slack_cells(expected, owner, class)?;
        let map = map_slack.map_lease();
        let map_cells = map.checked_cells(expected, owner, class)?;
        for cell in map_cells {
            let local = cell.physical_wire().checked_sub(owner * WIDTH)
                .ok_or("C443 Map cell outside owner")?;
            if self.template.claims.get(&local)
                != Some(&(H21StageAuthor::Map(cell.context()), cell.value())) {
                return Err("C443 retained Map template differs from paired source".into());
            }
        }

        let first_binding = self.first_map_slack.map_lease().binding();
        let first_cells = self.first.checked_cells(first_binding, ANCHOR_OWNERS[0],
            OwnerClass::Carry, &self.first_map_slack)?;
        let maps = [map.map_binding(0)?.clone(), map.map_binding(1)?.clone()];
        let replay = self.publication.checked_full_replay(self.template.parent_root,
            self.template.parent_total, self.template.parent_profile,
            &self.template.cut_identity, &maps)?;
        if replay.first != self.first.claimed || replay.second.owner != owner
            || first_cells.len() != 4096 {
            return Err("C443 retained first source differs from full two-anchor replay".into());
        }
        if replay.second.claims.len() != self.template.claims.len() + 4096
            || self.template.claims.iter().any(|(local, claim)|
                replay.second.claims.get(local) != Some(claim)) {
            return Err("C443 generated Map stage differs from full second-anchor replay".into());
        }
        let mut cells = Vec::with_capacity(4096);
        let mut row_authors = std::collections::BTreeMap::new();
        for context in 0..2 {
            if replay.second.map_bindings[context] != *map.map_binding(context)?
                || self.template.map_terms[context] != map.terms(context)?
                || replay.second.map_terms[context] != map.terms(context)?
                || replay.second.score_terms[context].is_empty() {
                return Err("C443 replayed second Score context/ordered terms".into());
            }
            let layout = score::Layout::new();
            let base = H21EligibleMapStage::score_live(context)?.start;
            let prior_bits = layout.p.clone().map(|offset| {
                replay.second.claims.get(&(base + offset))
                    .map(|(_, value)| *value).ok_or("C443 replayed second prior R bit missing")
            }).collect::<Result<Vec<_>, _>>()?;
            if bits_to_word(&prior_bits) != replay.first_r[context].value {
                return Err("C443 second replay does not consume first anchor R".into());
            }
            let domain = H21EligibleMapStage::score_live(context)?;
            if domain.len() != 2048 { return Err("C443 Score exact context width".into()); }
            for local in domain {
                let &(author, value) = replay.second.claims.get(&local)
                    .ok_or("C443 absent replayed second Score cell")?;
                if author != H21StageAuthor::ScoreAnchor(context) {
                    return Err("C443 exact second ScoreAnchor author".into());
                }
                cells.push(Eligible08ScoreAnchorCell { wire: owner * WIDTH + local,
                    context, value });
            }
            let slack_terms = map_slack.checked_slack_terms(expected, owner, class, context)?;
            for (role, terms) in [(context * 3, map.terms(context)?),
                (context * 3 + 1, replay.second.score_terms[context].as_slice()),
                (context * 3 + 2, slack_terms)] {
                for term in terms {
                    let local = term.row.checked_sub(owner * ROW_WIDTH)
                        .ok_or("C443 source ROW before owner")?;
                    let (source, destination, width) = match role % 3 {
                        0 => (409_600 + context * 32_768, [477_074, 492_305][context], 10_347),
                        1 => (SCORE_ROW[context], SCORE_ROW[context], 4_497),
                        _ => (409_600 + context * 32_768 + crate::bank53_slack::SLACK_ROW_OFFSET,
                            [491_918, 507_149][context], 387),
                    };
                    if !(source..source + width).contains(&local) {
                        return Err("C443 source ROW outside exact family envelope".into());
                    }
                    let destination_row = owner * ROW_WIDTH + destination + local - source;
                    if term.row / ROW_WIDTH != owner
                        || row_authors.insert(destination_row, role).is_some_and(|old| old != role) {
                        return Err("C443 Map/Score/Slack source ROW collision or owner".into());
                    }
                }
            }
        }
        if cells.len() != 4096 {
            return Err("C443 exact replayed second Score census".into());
        }
        Ok(cells)
    }

    pub(super) fn terms(&self, expected: &crate::packed_owner_assembly::HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass,
        map_slack: &Eligible08MapSlackBundle, context: usize) -> Result<&[Term], String> {
        self.checked_cells(expected, owner, class, map_slack)?;
        self.publication.candidate.anchors.second.score_terms.get(context)
            .map(Vec::as_slice).ok_or_else(|| "C443 Score context outside pair".into())
    }

    pub(super) fn checked_predecessor_packed(
        &self, first: &crate::packed_owner_assembly::NativePackedRow,
    ) -> Result<(), String> {
        self.first.checked_packed(&self.first_map_slack, first)
    }

    #[cfg(test)]
    pub(super) fn flip_first_r_lease_for_test(&mut self, context: usize) -> Result<(), String> {
        let lease = self.publication.candidate.anchors.first_r.get_mut(context)
            .ok_or("C443 test first R context outside pair")?;
        lease.value ^= BigUint::from(1u8);
        Ok(())
    }

    /// kind 0 flips one physical Upper845757 bit and its operand mirror;
    /// kind 1 changes only the published owner identity.
    #[cfg(test)]
    pub(super) fn mutate_second_upper_for_test(&mut self, kind: usize) -> Result<(), String> {
        let upper = self.publication.upper.get_mut(1).ok_or("C443 test second Upper missing")?;
        match kind {
            0 => {
                let (wire, value) = upper.upper.get_mut(0)
                    .ok_or("C443 test second Upper bit missing")?;
                let source_wire = *wire;
                *value = Fr::one() - *value;
                let flipped = *value;
                upper.operands.iter_mut().find(|(found, _)| *found == source_wire)
                    .ok_or("C443 test second Upper operand missing")?.1 = flipped;
            }
            1 => upper.owner += 1,
            _ => return Err("C443 test second Upper mutation kind".into()),
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn remove_zero_second_score_for_test(&mut self, context: usize)
        -> Result<usize, String> {
        let domain = H21EligibleMapStage::score_live(context)?;
        let local = domain.filter(|local| self.publication.candidate.anchors.second.claims
            .get(local).is_some_and(|(author, value)|
                *author == H21StageAuthor::ScoreAnchor(context) && !*value))
            .next().ok_or("C443 test second Score has no zero claim")?;
        self.publication.candidate.anchors.second.claims.remove(&local);
        Ok(local)
    }

    #[cfg(test)]
    pub(super) fn swap_second_score_terms_for_test(&mut self, context: usize)
        -> Result<(), String> {
        let terms = self.publication.candidate.anchors.second.score_terms.get_mut(context)
            .ok_or("C443 test second Score context outside pair")?;
        if terms.len() < 2 { return Err("C443 test second Score term census too small".into()); }
        terms.swap(0, 1);
        Ok(())
    }

    /// kind 0 changes only the first R lease profile; kind 1 changes its
    /// context; kind 2 binds it to the other Map context.
    #[cfg(test)]
    pub(super) fn mutate_second_binding_for_test(&mut self, kind: usize) -> Result<(), String> {
        let lease = self.publication.candidate.anchors.second_r.get_mut(0)
            .ok_or("C443 test second R context missing")?;
        match kind {
            0 => lease.parent_profile[0] ^= 1,
            1 => lease.context ^= 1,
            2 => lease.binding = self.publication.maps[1].binding(),
            _ => return Err("C443 test binding mutation kind".into()),
        }
        Ok(())
    }
}

impl H21EligibleContext<'_> {
    /// Requires the actual packed owners417789/845757. This path performs no
    /// global finish and must not be replaced by relocated fixture authority.
    pub(crate) fn premodern_r_publication(&self, anchors: H21PremodernAnchors)
        -> Result<PremodernRPublication, String> {
        let parent = self.producer.work_local_native_parent()?;
        let mut upper = Vec::with_capacity(2);
        for owner in ANCHOR_OWNERS.map(|owner| owner - 1) {
            let lease = self.producer.native_work_local_lease_for_owner(owner)?;
            self.producer.require_native_work_local_lease_for_owner(&parent, owner, &lease)?;
            upper.push(self.producer.work_upper_publication(owner, lease.local())?);
        }
        let projection = project_r450(&anchors)?;
        let out = PremodernRPublication { candidate: R450Candidate { anchors, projection },
            templates: [self.stage(ANCHOR_OWNERS[0])?, self.stage(ANCHOR_OWNERS[1])?],
            maps: self.maps.clone(), upper: upper.try_into().map_err(|_| "R450 physical Upper census")? };
        out.checked_projection(self.producer.plan.descriptor().root,
            self.producer.plan.work_profile().total_be28, self.producer.input.profile(),
            &self.descriptor.canonical_identity(), &[self.maps[0].binding(), self.maps[1].binding()])?;
        Ok(out)
    }
}

/// Keeps both authenticated predecessor R authors and the MAX/Cap import
/// author alive beside the incomplete owner-845759 Score/Cap stage.
#[allow(dead_code)]
pub(crate) struct H21FirstModernScore {
    current: H21EligibleMapStage,
    anchors: H21PremodernAnchors,
    cap: FirstModernCapLease,
}

/// Retains all B2 source leases beside the admitted owner-local ROW/X ledger.
/// It is not a NativePackedRow and exposes no bytes or completion operation.
#[allow(dead_code)]
pub(crate) struct H21FirstModernLedger {
    source: H21FirstModernScore,
    joined: super::super::h21_first_modern_ledger::Joined,
}

/// One sparse Score owner may author one or both cut contexts. The fixed
/// 2,048-bit payload is lossless, including the required zero padding.
#[derive(Clone)]
struct ScoreEndpointRole {
    lease_index: usize,
    previous_owner: usize,
    bits: [u8; score::INPUT / 8],
}
#[derive(Clone)]
struct ScoreEndpointRecord {
    owner: usize,
    roles: [Option<ScoreEndpointRole>; 2],
}
#[derive(Clone)]
struct ScoreFrontier {
    owner: usize,
    last_origin: usize,
    w: BigUint,
    r: BigUint,
}

/// Source closure only. The later X/ROW merger must import these exact bits,
/// physical Cap/WORK aliases and the final R output into its proof relation.
#[allow(dead_code)]
pub(crate) struct H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot> {
    context: &'ctx H21EligibleContext<'src>,
    closed_max: &'max MaxStream<'snapshot>,
    first_modern: H21FirstModernScore,
    leases: [Vec<ScoreEndpointLease>; 2],
    next: [usize; 2],
    frontier: [ScoreFrontier; 2],
    records: Vec<ScoreEndpointRecord>,
}

/// Opaque owner-local Map/Slack/Score source borrowed from one closed stream.
/// The stage is owned here; each term observation rechecks terminal closure
/// and reconstructs it from this same stream and its private context.
pub(crate) struct H21ClosedOwnerSource<'stream, 'ctx, 'src, 'max, 'snapshot> {
    stream: &'stream H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot>,
    owner: usize,
    stage: super::super::h21_eligible_slack::H21EligibleSlackStage,
}

// Private transport of an already fully revalidated WHOLE owner source.
// No stage clone or acceptance state survives its higher-ranked callback.
struct C575CheckedStage<'stage, 'stream, 'ctx, 'src, 'max, 'snapshot> {
    source: &'stage H21ClosedOwnerSource<'stream, 'ctx, 'src, 'max, 'snapshot>,
    active: [bool; 2],
}
impl C575CheckedStage<'_, '_, '_, '_, '_, '_> {
    fn map_terms(&self, context: usize) -> Result<&[Term], String> {
        self.source.stage.map_stage.map_terms.get(context).map(Vec::as_slice)
            .ok_or_else(|| "checked stage Map context outside pair".into())
    }
    fn score_terms(&self, context: usize) -> Result<&[Term], String> {
        self.source.stage.score_rows().get(context).map(Vec::as_slice)
            .ok_or_else(|| "checked stage Score context outside pair".into())
    }
    fn slack_terms(&self, context: usize) -> Result<&[Term], String> {
        self.source.stage.slack_rows().get(context).map(Vec::as_slice)
            .ok_or_else(|| "checked stage Slack context outside pair".into())
    }
}

#[cfg(test)]
std::thread_local! {
    static C575_CARRIER_COUNTS: std::cell::Cell<Option<[usize; 2]>> = const { std::cell::Cell::new(None) };
    static C575_NATIVE_CARRIERS: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

#[cfg(test)]
struct C575CarrierCounter;
#[cfg(test)]
impl C575CarrierCounter {
    fn start() -> Result<Self, String> {
        C575_CARRIER_COUNTS.with(|counter| {
            if counter.get().is_some() { return Err("C575 nested carrier counter".into()); }
            counter.set(Some([0, 0]));
            Ok(Self)
        })
    }
    fn finish(self) -> Result<(), String> {
        C575_CARRIER_COUNTS.with(|counter| {
            if counter.get() != Some([2, 1]) {
                return Err("C575 actual carrier needs two named builds/one qualification".into());
            }
            Ok(())
        })
    }
}
#[cfg(test)]
impl Drop for C575CarrierCounter {
    fn drop(&mut self) { C575_CARRIER_COUNTS.with(|counter| counter.set(None)); }
}
#[cfg(test)]
fn c575_note_operation(index: usize) {
    C575_CARRIER_COUNTS.with(|counter| {
        if let Some(mut counts) = counter.get() {
            counts[index] = counts[index].checked_add(1).expect("C575 scoped test counter overflow");
            counter.set(Some(counts));
        }
    });
}

#[cfg(test)]
fn c575_native_carrier_checks(carrier: &mut ClosedRegularCarrier<'_, '_, '_, '_, '_>)
    -> Result<(), String> {
    let selected = C575_NATIVE_CARRIERS.with(|count| {
        let previous = count.get();
        if let Some(n) = previous { count.set(Some(n.checked_add(1).expect("C575 carrier counter overflow"))); }
        previous
    });
    if selected != Some(0) { return Ok(()); } // One fault campaign; both actual carriers are counted.
    {
        let source = &carrier.owner_source;
        let old_active = source.active_contexts()?;
        let old_map = [source.map_terms(0)?, source.map_terms(1)?];
        let old_score = [source.score_terms(0)?, source.score_terms(1)?];
        let old_slack = [source.slack_terms(0)?, source.slack_terms(1)?];
        source.with_checked_stage(|view| {
            if view.active != old_active || view.active != [true, true] {
                return Err("C575 native old/new active mask differential".into());
            }
            for context in 0..2 {
                if view.map_terms(context)? != old_map[context]
                    || view.score_terms(context)? != old_score[context]
                    || view.slack_terms(context)? != old_slack[context] {
                    return Err("C575 native six original ordered slice differential".into());
                }
            }
            if view.map_terms(2).is_ok() || view.score_terms(2).is_ok()
                || view.slack_terms(2).is_ok() { return Err("C575 context bound".into()); }
            Ok(())
        })?;
    } // End the valid whole-source borrow BEFORE every mutable fault.
    for fault in 0..5 {
        let mut original_reads = Vec::new();
        if fault == 1 {
            let reads = carrier.owner_source.stage.score_imports();
            original_reads.try_reserve_exact(reads.len()).map_err(|_| "C575 read snapshot allocation")?;
            original_reads.extend_from_slice(reads);
        }
        c575_toggle_stored_fault(&mut carrier.owner_source, fault)?;
        if fault == 1 {
            let reads = carrier.owner_source.stage.score_imports();
            if reads.len() != original_reads.len() || reads.is_empty()
                || reads[0].0 != (original_reads[0].0 ^ 1)
                || reads[0].1 != original_reads[0].1 || reads[0].2 != original_reads[0].2
                || reads[1..] != original_reads[1..] {
                return Err("C575 read seam must change ONLY first stored wire bit".into());
            }
        }
        let consumed = std::cell::Cell::new(false);
        let rejected = carrier.owner_source.with_checked_stage(|_| {
            consumed.set(true); Ok(())
        });
        if consumed.get() || rejected.err().as_deref() != Some("closed owner source stage replay mismatch") {
            return Err("C575 full stage fault must reject before scoped consumption".into());
        }
        if fault == 1 {
            if carrier.owner_source.map_terms(0).err().as_deref()
                != Some("closed owner source stage replay mismatch") {
                return Err("C575 fresh old getter accepted post-drop stored read fault".into());
            }
            let rejected = carrier.with_c514(|_, _| { consumed.set(true); });
            if consumed.get() || rejected.err().as_deref() != Some("closed owner source stage replay mismatch") {
                return Err("C575 fresh with_c514 accepted post-drop stored read fault".into());
            }
        }
        c575_toggle_stored_fault(&mut carrier.owner_source, fault)?;
        if fault == 1 && carrier.owner_source.stage.score_imports() != original_reads.as_slice() {
            return Err("C575 stored reads not exactly restored".into());
        }
        carrier.owner_source.with_checked_stage(|view| {
            if view.active != [true, true] { return Err("C575 native recovery active mask".into()); }
            Ok(())
        })?;
    }
    Ok(())
}

#[cfg(test)]
fn c575_toggle_stored_fault(source: &mut H21ClosedOwnerSource<'_, '_, '_, '_, '_>,
    fault: usize) -> Result<(), String> {
    match fault {
        0 => {
            let (_, cell) = source.stage.map_stage.claims.iter_mut().next()
                .ok_or("C575 genuine Map claim absent")?;
            cell.1 = !cell.1; // Not a term-slice change: exercises FULL replay Eq.
        }
        1 => source.stage.c575_toggle_first_stored_score_read_wire()?,
        2 => source.stage.map_stage.parent_root[0] ^= 1,
        3 => {
            if source.stage.map_stage.map_bindings[0] == source.stage.map_stage.map_bindings[1] {
                return Err("C575 nonvacuous full Map binding fault unavailable".into());
            }
            source.stage.map_stage.map_bindings.swap(0, 1);
        }
        4 => source.stage.map_stage.map_terms[0].first_mut()
            .ok_or("C575 genuine Map term absent")?.gate.left ^= 1,
        _ => return Err("C575 unknown stored-stage fault".into()),
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn c575_structural_guard_controls() { tests::c575_structural_guard_controls(); }

/// One closed Score source and the physical regular-owner census produced
/// from that same source and context. This carrier is intentionally not
/// cloneable: it is the sole scoped route into the C509/C514 consumer.
pub(crate) struct ClosedRegularCarrier<'stream, 'ctx, 'src, 'max, 'snapshot> {
    owner_source: H21ClosedOwnerSource<'stream, 'ctx, 'src, 'max, 'snapshot>,
    census: crate::packed_owner_assembly::NativeRegularOwnerAuthorCensus<'ctx, 'src>,
}

impl ClosedRegularCarrier<'_, '_, '_, '_, '_> {
    /// Construct C509 ROW terms and C514 edges only for the retained source
    /// census. The closure receives borrowed edge values and identity metadata;
    /// neither can escape this call through its return value.
    pub(crate) fn with_c514<R>(
        &self,
        consume: impl for<'edges> FnOnce(
            &'edges [crate::sparse_stream_roster::EdgeTerm],
            &'edges [crate::header_daa_row_placement::C514Role1EdgeIdentity],
        ) -> R,
    ) -> Result<R, String> {
        use crate::header_daa_row_placement::{C509RegularBatch, C514Role1EdgeBatch};

        if self.owner_source.owner() != 845_887
            || self.owner_source.active_contexts()? != [true, true] {
            return Err("C517 retained closed source owner/active contexts".into());
        }
        let source = self.census.c509_regular_row_source()?;
        let binding = self.census.binding()?;
        let batch = C509RegularBatch::checked_from_source(&source, binding)?;
        let edges = C514Role1EdgeBatch::checked_from_batch(&batch)?;
        Ok(consume(edges.edges(), edges.sidecar()))
    }
}

impl<'stream, 'ctx, 'src, 'max, 'snapshot>
    H21ClosedOwnerSource<'stream, 'ctx, 'src, 'max, 'snapshot> {
    fn with_checked_stage<R>(&self,
        consume: impl for<'stage> FnOnce(
            C575CheckedStage<'stage, 'stream, 'ctx, 'src, 'max, 'snapshot>,
        ) -> Result<R, String>,
    ) -> Result<R, String> {
        let active = self.revalidate()?;
        #[cfg(test)]
        c575_note_operation(1);
        consume(C575CheckedStage { source: self, active })
    }
    pub(crate) fn owner(&self) -> usize { self.owner }

    pub(crate) fn active_contexts(&self) -> Result<[bool; 2], String> {
        self.revalidate()
    }

    pub(crate) fn map_terms(&self, context: usize) -> Result<&[Term], String> {
        self.revalidate()?;
        self.stage.map_stage.map_terms.get(context).map(Vec::as_slice)
            .ok_or_else(|| "closed owner Map context outside pair".into())
    }

    pub(crate) fn slack_terms(&self, context: usize) -> Result<&[Term], String> {
        self.revalidate()?;
        self.stage.slack_rows().get(context).map(Vec::as_slice)
            .ok_or_else(|| "closed owner Slack context outside pair".into())
    }

    pub(crate) fn score_terms(&self, context: usize) -> Result<&[Term], String> {
        self.revalidate()?;
        self.stage.score_rows().get(context).map(Vec::as_slice)
            .ok_or_else(|| "closed owner Score context outside pair".into())
    }

    fn revalidate(&self) -> Result<[bool; 2], String> {
        let status = self.stream.closed_owner_relation_status(self.owner)?;
        let active = checked_owner_status_contexts(status.as_ref(), self.owner,
            self.stream.context.producer.input.root(),
            self.stream.context.producer.input.total_be28(),
            self.stream.context.producer.input.profile(),
            &self.stream.context.descriptor.canonical_identity(),
            [&self.stream.context.maps[0].binding(),
                &self.stream.context.maps[1].binding()])?;
        let replay = build_closed_owner_stage(
            self.stream.context, self.owner, status,
        )?;
        if replay != self.stage {
            return Err("closed owner source stage replay mismatch".into());
        }
        Ok(active)
    }
}

fn checked_relation_contexts(
    relation: &H21ClosedScoreOwnerRelation<'_>,
    owner: usize,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: &[u8],
    bindings: [&crate::legacy_envelope_map::Binding; 2],
) -> Result<[bool; 2], String> {
    if relation.owner() != owner
        || relation.parent_root() != root
        || relation.parent_total() != total
        || relation.parent_profile() != profile
        || relation.cut_identity() != cut
    {
        return Err("closed owner relation parent/cut/owner identity".into());
    }
    relation.require_original_map_bindings(bindings)?;

    let mut active = [false; 2];
    let mut cell_counts = [0usize; 2];
    for (c, author) in relation.authors().iter().enumerate() {
        let terms = relation.terms(c)?;
        match author {
            Some(author) if author.context == c && author.cap_owner == owner
                && author.origin == owner + 1 && !terms.is_empty() => active[c] = true,
            None if terms.is_empty() => (),
            _ => return Err("closed owner relation active context census".into()),
        }
    }
    if !active.iter().any(|is_active| *is_active) {
        return Err("closed owner relation has no active context".into());
    }
    for &(address, author, _) in relation.cells() {
        let c = author.context;
        if c >= 2 || !active[c] || relation.authors()[c] != Some(author) {
            return Err("closed owner relation source tuple context/author".into());
        }
        let start = owner * WIDTH + SCORE_X[c];
        if !(start..start + crate::origin_score::INPUT).contains(&address) {
            return Err("closed owner relation source tuple address".into());
        }
        cell_counts[c] += 1;
    }
    for c in 0..2 {
        let expected = if active[c] { crate::origin_score::INPUT } else { 0 };
        if cell_counts[c] != expected {
            return Err("closed owner relation source tuple census".into());
        }
    }
    Ok(active)
}

fn checked_owner_status_contexts(
    status: Option<&H21ClosedScoreOwnerRelation<'_>>,
    owner: usize,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: &[u8],
    bindings: [&crate::legacy_envelope_map::Binding; 2],
) -> Result<[bool; 2], String> {
    match status {
        Some(relation) => checked_relation_contexts(
            relation, owner, root, total, profile, cut, bindings,
        ),
        None => Ok([false, false]),
    }
}

/// The production and structural-fixture admission boundary. It consumes an
/// already generated Map+Slack stage and returns it only after any closed
/// Score source is admitted and compared against its exact source tuples.
fn admit_closed_owner_score_stage(
    mut stage: super::super::h21_eligible_slack::H21EligibleSlackStage,
    relation: Option<H21ClosedScoreOwnerRelation<'_>>,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: &[u8],
    bindings: [&crate::legacy_envelope_map::Binding; 2],
) -> Result<(super::super::h21_eligible_slack::H21EligibleSlackStage, [bool; 2]), String> {
    let map_stage = &stage.map_stage;
    if map_stage.owner != owner || map_stage.class != class
        || map_stage.parent_root != root || map_stage.parent_total != total
        || map_stage.parent_profile != profile || map_stage.cut_identity != cut
        || map_stage.map_bindings.iter().enumerate().any(|(c, binding)|
            binding != bindings[c])
        || !stage.score_cells().is_empty()
        || stage.score_rows().iter().any(|terms| !terms.is_empty())
        || !stage.score_imports().is_empty()
    {
        return Err("closed owner Map/Slack stage identity or empty Score destination".into());
    }

    let original_map_stage = stage.map_stage.clone();
    let original_slack_cells = stage.slack_cells().clone();
    let original_slack_rows = stage.slack_rows().clone();
    let active = match relation {
        None => [false, false],
        Some(relation) => {
            let active = checked_relation_contexts(&relation, owner, root, total,
                profile, cut, bindings)?;
            let mut expected_cells = std::collections::BTreeMap::new();
            for &(address, author, value) in relation.cells() {
                let local = address.checked_sub(owner * WIDTH)
                    .ok_or("closed owner Score source tuple before owner")?;
                if expected_cells.insert(local, (author, value)).is_some() {
                    return Err("closed owner duplicate Score source tuple".into());
                }
            }
            let expected_terms = [relation.terms(0)?.to_vec(), relation.terms(1)?.to_vec()];
            let expected_reads = relation.reads().to_vec();
            stage.admit_score_relation(relation)?;
            if stage.score_cells() != &expected_cells
                || stage.score_rows() != &expected_terms
                || stage.score_imports() != expected_reads.as_slice()
            {
                return Err("closed owner admitted Score differs from source tuples".into());
            }
            active
        }
    };
    if stage.map_stage != original_map_stage
        || stage.slack_cells() != &original_slack_cells
        || stage.slack_rows() != &original_slack_rows
    {
        return Err("closed owner Score admission changed Map/Slack sources".into());
    }
    Ok((stage, active))
}

fn build_closed_owner_stage(
    context: &H21EligibleContext<'_>,
    owner: usize,
    relation: Option<H21ClosedScoreOwnerRelation<'_>>,
) -> Result<super::super::h21_eligible_slack::H21EligibleSlackStage, String> {
    #[cfg(test)]
    c575_note_operation(0);
    if owner >= context.producer.plan.slots() {
        return Err("closed owner source outside H21".into());
    }
    let root = context.producer.input.root();
    let total = context.producer.input.total_be28();
    let profile = context.producer.input.profile();
    let cut = context.descriptor.canonical_identity();
    let class = context.producer.roster.owner_class(owner as u64)?;
    let bindings = [context.maps[0].binding(), context.maps[1].binding()];

    let map_slack = context.stage_with_slack(owner)?;
    let (stage, _) = admit_closed_owner_score_stage(map_slack, relation, owner, class,
        root, total, profile, &cut, [&bindings[0], &bindings[1]])?;
    stage.map_stage.validate_identity(
        context.producer.plan, profile, context.descriptor, &context.maps,
    )?;
    if stage.map_stage.owner != owner
        || stage.map_stage.class != class
        || stage.map_stage.parent_root != root
        || stage.map_stage.parent_total != total
        || stage.map_stage.parent_profile != profile
        || stage.map_stage.cut_identity != cut
        || stage.map_stage.map_bindings != bindings
    {
        return Err("closed owner generated stage identity".into());
    }
    Ok(stage)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScoreReplayAuthor {
    pub context: usize,
    pub origin: usize,
    pub previous_owner: usize,
    pub max_owner: usize,
    pub cap_owner: usize,
}

/// Typed physical inputs of the Score relation. These are source reads, not
/// claims that the global X merger has installed their authors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScoreRelationReadAuthor {
    PreviousR { context: usize, owner: usize },
    WorkUpper { owner: usize, height: usize },
    Cap { context: usize, origin: usize, max_owner: usize, cap_owner: usize },
}

/// A closed stream's owner-local source relation. Private borrowed source
/// fields prevent construction, retargeting, or mutation by the consumer.
/// This is not a finished row, a proof, or a byte-export interface.
pub(crate) struct H21ClosedScoreOwnerRelation<'a> {
    record: &'a ScoreEndpointRecord,
    identity: &'a H21EligibleMapStage,
    material: ScoreRelationMaterial,
}
impl H21ClosedScoreOwnerRelation<'_> {
    pub(crate) fn owner(&self)->usize {self.record.owner}
    pub(crate) fn parent_root(&self)->[u8;32] {self.identity.parent_root}
    pub(crate) fn parent_total(&self)->[u8;28] {self.identity.parent_total}
    pub(crate) fn parent_profile(&self)->[u8;32] {self.identity.parent_profile}
    pub(crate) fn cut_identity(&self)->&[u8] {&self.identity.cut_identity}
    pub(crate) fn require_original_map_bindings(&self,
        maps: [&crate::legacy_envelope_map::Binding; 2])->Result<(),String> {
        if maps.iter().enumerate().any(|(context,binding)|
            **binding!=self.identity.map_bindings[context]) {
            return Err("Score relation original Map bindings".into());
        }
        Ok(())
    }
    pub(crate) fn cells(&self)->&[(usize,ScoreReplayAuthor,Fr)] {&self.material.cells}
    pub(crate) fn authors(&self)->&[Option<ScoreReplayAuthor>;2] {&self.material.authors}
    pub(crate) fn terms(&self,context:usize)->Result<&[Term],String> {
        self.material.terms.get(context).map(Vec::as_slice)
            .ok_or_else(||"Score relation context outside two cuts".into())
    }
    pub(crate) fn reads(&self)->&[(usize,ScoreRelationReadAuthor,Fr)] {&self.material.reads}

    /// Shared ordinary/clipped recipe seam. The returned arithmetic plan
    /// compares source equations and metadata; it verifies no producing-role
    /// proof or common commitment. Consumer custody/value checks remain due.
    pub(crate) fn source_equation_plan(&self,owner:usize)
        ->Result<h21_score_class_equations::ClassEquationPlan,String> {
        let equations=super::Eligible08RegularScoreOwner::equation_plan(owner)?;
        equations.require_source_recipe([self.terms(0)?,self.terms(1)?],
            self.reads(),self.authors())?;
        Ok(equations)
    }
}

struct ScoreRelationMaterial {
    cells: Vec<(usize,ScoreReplayAuthor,Fr)>,
    authors: [Option<ScoreReplayAuthor>;2],
    terms: [Vec<Term>;2],
    reads: Vec<(usize,ScoreRelationReadAuthor,Fr)>,
}
#[derive(Clone)]
struct ScorePreviousInput {context:usize,owner:usize,r:BigUint}
#[derive(Clone)]
struct ScoreWorkInput {owner:usize,height:usize,w:BigUint}

fn closed_relation_record<'a>(terminal:Result<[BigUint;2],String>,
    records:&'a [ScoreEndpointRecord],owner:usize)->Result<&'a ScoreEndpointRecord,String> {
    terminal?;
    score_endpoint_record(records,owner)
        .ok_or_else(||"Score relation inactive owner".into())
}

/// The stream seeds its first modern record once, then `push_native` appends
/// only `next_owner()`. Thus records are strictly ascending and unique.
fn score_endpoint_record(records:&[ScoreEndpointRecord],owner:usize)
    ->Option<&ScoreEndpointRecord> {
    let index=records.partition_point(|record|record.owner<owner);
    records.get(index).filter(|record|record.owner==owner)
}

/// All physical terms are emitted from the descriptor and the original local
/// relation, preserving its order and repeated terms within the same row.
fn score_relation_material(descriptor:crate::bank53_map::CutDescriptor,
    record:&ScoreEndpointRecord,leases:[Option<&ScoreEndpointLease>;2],
    previous:[Option<ScorePreviousInput>;2],work:ScoreWorkInput,
)->Result<ScoreRelationMaterial,String> {
    let owner=record.owner;
    if descriptor!=H21EligibleMapStage::descriptor() || owner<FIRST_MODERN_OWNER
        || owner>=1<<21 || work.owner!=owner-1 || work.height!=owner+1
        || work.w.bits()>224 {
        return Err("Score relation descriptor/owner/WORK source".into());
    }
    if record.roles.iter().all(Option::is_none) {
        return Err("Score relation owner without active context".into());
    }
    let mut out=ScoreRelationMaterial {cells:Vec::new(),authors:[None;2],
        terms:std::array::from_fn(|_|Vec::new()),reads:Vec::new()};
    let layout=score::Layout::new();
    for c in 0..2 {
        let Some(role)=&record.roles[c] else {
            if leases[c].is_some() || previous[c].is_some() {
                return Err("Score relation inactive context source".into());
            }
            continue;
        };
        let lease=leases[c].ok_or("Score relation missing Cap endpoint")?;
        if lease.context()!=c || lease.cap_owner()!=owner || lease.last_origin()!=owner+1
            || lease.last_origin()>descriptor.guards()[c]
            || lease.first_origin()<descriptor.modern_start()
            || lease.first_origin()>lease.last_origin() || lease.value().bits()>65 {
            return Err("Score relation Cap endpoint/context".into());
        }
        let prior=previous[c].as_ref().ok_or("Score relation missing previous R")?;
        if prior.context!=c || prior.owner!=role.previous_owner || prior.owner>=owner
            || prior.owner+2!=lease.first_origin() || prior.r.bits()>225 {
            return Err("Score relation previous R author".into());
        }
        if packed_word(&role.bits,layout.p.clone())!=prior.r {
            return Err("Score relation previous R bit".into());
        }
        if packed_word(&role.bits,layout.sw.clone())!=work.w {
            return Err("Score relation WORK upper bit".into());
        }
        if packed_word(&role.bits,layout.sv.clone())!=*lease.value() {
            return Err("Score relation Cap q bit".into());
        }
        if (score::LIVE..score::INPUT).any(|bit|packed_bit(&role.bits,bit)) {
            return Err("Score relation nonzero input tail".into());
        }
        let spec=modern_spec(descriptor,c)?;
        if spec.maturity!=descriptor.maturity_value(c,lease.last_origin())? {
            return Err("Score relation changed maturity".into());
        }
        // Replaying the exact producer checks every retained helper and R bit,
        // rather than trusting a self-consistent alias or repeated metadata.
        let expected=pack_score(&score::produce(&spec,Some(&score::ConditionalInputs {
            w:work.w.clone(),v:lease.value().clone()}),&prior.r)?)?;
        if role.bits!=expected {return Err("Score relation exact source replay".into());}
        let author=ScoreReplayAuthor {context:c,origin:lease.last_origin(),
            previous_owner:prior.owner,max_owner:lease.max_owner(),cap_owner:owner};
        out.authors[c]=Some(author);
        for bit in 0..score::INPUT {
            out.cells.push((owner*WIDTH+SCORE_X[c]+bit,author,
                Fr::from(packed_bit(&role.bits,bit) as u64)));
        }
        for bit in 0..225 {
            out.reads.push((prior.owner*WIDTH+SCORE_X[c]+layout.r.start+bit,
                ScoreRelationReadAuthor::PreviousR {context:c,owner:prior.owner},
                Fr::from(prior.r.bit(bit as u64) as u64)));
        }
        h21_score_class_equations::emit_context(author, &spec,
            |term| out.terms[c].push(term))?;
        for bit in 0..65 {
            let address=owner*WIDTH+[1_000_770,1_002_818][c]+740+bit;
            out.reads.push((address,ScoreRelationReadAuthor::Cap {context:c,
                origin:author.origin,max_owner:author.max_owner,cap_owner:owner},
                Fr::from(lease.value().bit(bit as u64) as u64)));
        }
        for bit in 0..224 {
            let address=work.owner*WIDTH+UPPER_LOCAL+bit;
            out.reads.push((address,ScoreRelationReadAuthor::WorkUpper {
                owner:work.owner,height:work.height},Fr::from(work.w.bit(bit as u64) as u64)));
        }
    }
    Ok(out)
}

fn packed_bit(bits: &[u8; score::INPUT / 8], bit: usize) -> bool {
    bits[bit / 8] & (1 << (bit % 8)) != 0
}
fn packed_word(bits: &[u8; score::INPUT / 8], range: std::ops::Range<usize>) -> BigUint {
    let mut word=BigUint::from(0u8);
    for (bit,local) in range.enumerate() {
        if packed_bit(bits,local) {word|=BigUint::from(1u8)<<bit;}
    }
    word
}
fn pack_score(values: &[ark_bn254::Fr]) -> Result<[u8; score::INPUT / 8], String> {
    if values.len()!=score::INPUT {return Err("Score endpoint exact input width".into());}
    let mut bits=[0u8; score::INPUT / 8];
    for (local,value) in values.iter().enumerate() {
        if value.is_one() {bits[local/8]|=1<<(local%8);}
        else if !value.is_zero() {return Err("Score endpoint nonboolean bit".into());}
    }
    if (score::LIVE..score::INPUT).any(|local|packed_bit(&bits,local)) {
        return Err("Score endpoint nonzero input tail".into());
    }
    Ok(bits)
}
fn first_modern_bits(stage:&H21EligibleMapStage,context:usize)
    ->Result<[u8; score::INPUT / 8],String> {
    let domain=H21EligibleMapStage::score_live(context)?;
    let mut bits=[0u8; score::INPUT / 8];
    for (local,cell) in domain.enumerate() {
        let &(author,value)=stage.claims.get(&cell)
            .ok_or("first modern Score source cell missing")?;
        if author!=H21StageAuthor::ScoreModern(context) {
            return Err("first modern Score source author".into());
        }
        if value {bits[local/8]|=1<<(local%8);}
    }
    if (score::LIVE..score::INPUT).any(|local|packed_bit(&bits,local)) {
        return Err("first modern Score input tail".into());
    }
    Ok(bits)
}

fn endpoint_role(context:usize,lease:&ScoreEndpointLease,
    previous:&ScoreFrontier,w:BigUint,lease_index:usize)
    ->Result<(ScoreEndpointRole,ScoreFrontier),String> {
    let origin=lease.last_origin();
    let owner=lease.cap_owner();
    if lease.context()!=context || origin!=owner+1
        || lease.first_origin()!=previous.last_origin+1
        || previous.owner>=owner || w<=previous.w {
        return Err("Score endpoint interval/previous R/W order".into());
    }
    let descriptor=H21EligibleMapStage::descriptor();
    if origin<descriptor.modern_start() || origin>descriptor.guards()[context] {
        return Err("Score endpoint outside modern guard".into());
    }
    let maturity=descriptor.maturity_value(context,origin)?;
    if maturity!=[4_995,2_090][context] {
        return Err("Score endpoint modern maturity changed within span".into());
    }
    let spec=score::Spec {active:true,origin_one:false,reducing:true,
        first:false,terminal:false,empty_terminal:false,maturity,
        guard_total:None,expected:BigUint::from(0u8)};
    let values=score::produce(&spec,Some(&score::ConditionalInputs {
        w:w.clone(),v:lease.value().clone()}),&previous.r)?;
    let bits=pack_score(&values)?;
    let layout=score::Layout::new();
    let p=packed_word(&bits,layout.p.clone());
    let r=packed_word(&bits,layout.r);
    let candidate=&w+lease.value()*maturity;
    if p!=previous.r || r!=std::cmp::max(previous.r.clone(),candidate) {
        return Err("Score endpoint exact successor R".into());
    }
    Ok((ScoreEndpointRole {lease_index,previous_owner:previous.owner,bits},
        ScoreFrontier {owner,last_origin:origin,w,r}))
}

#[allow(dead_code)]
impl<'ctx, 'src, 'max, 'snapshot> H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot> {
    #[cfg(test)]
    pub(super) fn c575_check_incomplete_source_gate(&self) -> Result<(), String> {
        if self.terminal_r().is_ok() { return Err("C575 incomplete check requires actual partial stream".into()); }
        if self.closed_owner_source(845_887).err().as_deref()
            != Some("Score endpoint incomplete R closure") {
            return Err("C575 actual incomplete factory did not reject before qualification".into());
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn c575_with_native_carrier_checks<R>(&self,
        perform: impl FnOnce() -> Result<R, String>) -> Result<R, String> {
        self.terminal_r()?;
        C575_NATIVE_CARRIERS.with(|count| -> Result<(), String> {
            if count.get().is_some() { return Err("C575 nested native counter".into()); }
            count.set(Some(0)); Ok(())
        })?;
        let result = perform();
        let actual = C575_NATIVE_CARRIERS.with(|count| { let n = count.get(); count.set(None); n });
        let out = result?;
        if actual != Some(2) { return Err("C575 requires the TWO existing real carrier constructions".into()); }
        Ok(out)
    }
    /// Consume two real checked physical rows. No global finish/export or
    /// cryptographic authority is returned. Replay uses this same borrowed
    /// terminal-closed context and performs fresh actual assembly.
    pub(crate) fn c574_second_regular_rows(&self,
        budget: &mut super::scored_owner_source::C574Budget,
        max_budget: &mut super::scored_owner_source::C576MaxBudget,
        work_budget: &mut super::scored_owner_source::C578WorkBudget,
        mut sink: impl FnMut(usize, usize, &[u8],
            &[Option<crate::packed_owner_assembly::NativeRegularPhysicalAuthor>]) -> Result<(), String>)
        -> Result<[usize; 4], String> {
        use super::scored_owner_source::{c574_check_read, c574_replay_chunk,
            c574_require_census, C574RowCursor};
        use crate::packed_owner_assembly::{HeaderSourceBinding, ScoredOwnerPackingView};
        self.terminal_r()?;
        // The fixed factories/classification are checked before new row work.
        for owner in [845_887, 846_015] {
            if Eligible08RegularScoreOwner::classify(owner)?.active() != [true, true] {
                return Err("C574 fixed regular writer preflight".into());
            }
        }
        let work_bound=crate::packed_owner_assembly::c578_work_retained_bound()?;
        work_budget.charge(1,0,work_bound)?;
        #[allow(unused_mut)]
        let mut physical_upper=self.context.producer.ordinary_work_upper_author_lease(846_014)?;
        if physical_upper.retained_capacity_bytes()?>work_bound {
            return Err("C578 actual Work retained budget".into());
        }
        physical_upper.require_live_source(&self.context.producer)?;
        #[cfg(test)]
        physical_upper.c578_native_source_controls(&self.context.producer)?;
        // ONE additional physical MAX row, retained across the two existing
        // destination joins. Its work is separate from C574's original budget.
        let max_bound=crate::packed_owner_assembly::c576_max_retained_bound(844_926)?;
        max_budget.charge(1,0,max_bound)?;
        #[allow(unused_mut)]
        let mut physical_max=self.context.producer.produce_scheduled_max_owner(844_926,self.closed_max)?;
        if physical_max.retained_capacity_bytes()?>max_bound {return Err("C576 actual MAX retained budget".into());}
        #[cfg(test)]
        {
            // A real distinct partial stream must fail identity BEFORE any
            // completion/value test; no fake closed stream is constructed.
            let snapshot=self.closed_max.closed_native_snapshot(self.context.producer.plan,self.context.producer.input)?;
            let different=MaxStream::new(self.context.producer.plan,self.context.producer.input,snapshot)?;
            if physical_max.require_live_source(&self.context.producer,&different).err().as_deref()
                !=Some("C576 physical MAX closed-stream identity") {
                return Err("C576 live distinct-stream gate attribution".into());
            }
            physical_max.require_live_source(&self.context.producer,self.closed_max)?;
            physical_max.c576_native_fr_read_controls()?;
        }
        let retained_limit = 4usize.checked_mul(2 * (WIDTH / 8)
            + WIDTH * std::mem::size_of::<Option<crate::packed_owner_assembly::NativeRegularPhysicalAuthor>>())
            .ok_or("C574 fixed retained buffer bound overflow")?;
        budget.charge(0, 0, 0, retained_limit)?;
        budget.charge(1, 0, 0, 0)?;
        let donor = self.closed_regular_carrier()?;
        let mut build_destination = || {
            let relation = self.closed_owner_relation(846_015)?;
            let join = self.context.join_scored_owner_source_with_physical_max_and_upper(
                846_015, relation, self.closed_max,&physical_max,max_budget,
                &physical_upper,work_budget)?;
            self.context.producer.produce_regular_owner846015_author_census(
                ScoredOwnerPackingView::from_checked_join(join)?)
        };
        budget.charge(1, 0, 0, 0)?;
        let destination = build_destination()?;
        let relation = self.closed_owner_relation(846_015)?;
        let recipe = relation.source_equation_plan(846_015)?;
        let mut expected = recipe.reads().into_iter().filter(|(_, author)|
            *author == (ScoreRelationReadAuthor::PreviousR { context: 0, owner: 845_887 }));
        // No copy or bool conversion of Fr reads; preserve the original order.
        let mut index = 0;
        for &read in relation.reads().iter().filter(|(_, author, _)|
            matches!(author, ScoreRelationReadAuthor::PreviousR { context: 0, .. })) {
            let (wire, author) = expected.next().ok_or("C574 extra PreviousR occurrence")?;
            if read.0 != wire || read.1 != author { return Err("C574 recipe/read order".into()); }
            budget.charge(0, 0, 1, 0)?;
            let dst_wire = 846_015 * WIDTH + SCORE_X[0] + score::Layout::new().p.start + index;
            let (src_author, src_value) = donor.census.c574_score_cell(wire)?;
            let (dst_author, dst_value) = destination.c574_score_cell(dst_wire)?;
            c574_check_read(index, read, (wire, src_author, src_value),
                (dst_wire, dst_author, dst_value))?;
            index += 1;
        }
        c574_require_census(index, expected.next().is_some())?;
        budget.charge(1, 0, 0, 0)?;
        let replay_donor = self.closed_regular_carrier()?;
        budget.charge(1, 0, 0, 0)?;
        let replay_destination = build_destination()?;
        drop(build_destination);
        if max_budget.usage()!=[1,896,max_bound] {return Err("C576 actual physical MAX work census".into());}
        if work_budget.usage()!=[1,896,work_bound] {return Err("C578 actual physical Upper work census".into());}
        let sources = [&donor.census, &destination, &replay_donor.census, &replay_destination];
        let mut retained = 0usize;
        for source in sources {
            let (bytes, authors, _) = source.c574_source()?;
            retained = bytes.len().checked_mul(2).and_then(|size| retained.checked_add(size)).and_then(|n|
                n.checked_add(std::mem::size_of_val(authors)))
                .ok_or("C574 retained source accounting overflow")?;
        }
        budget.charge(0, 0, 0, retained)?;
        let mut cursor = C574RowCursor::new();
        for (owner, source, replay) in [(845_887, &donor.census, &replay_donor.census),
            (846_015, &destination, &replay_destination)] {
            let binding = HeaderSourceBinding::for_plan(self.context.producer.plan, owner)?;
            crate::packed_owner_assembly::c574_require_binding(source.binding()?, &binding)?;
            crate::packed_owner_assembly::c574_require_binding(replay.binding()?, &binding)?;
            let (bytes, authors, _) = source.c574_source()?;
            let (again, again_authors, _) = replay.c574_source()?;
            if bytes.len() != WIDTH / 8 || authors.len() != WIDTH
                || again.len() != bytes.len() || again_authors.len() != authors.len() {
                return Err("C574 early EOF/source extent".into());
            }
            for offset in (0..bytes.len()).step_by(8192) {
                let end = offset + 8192;
                c574_replay_chunk(owner, offset, &bytes[offset..end], &authors[offset*8..end*8],
                    &again[offset..end], &again_authors[offset*8..end*8])?;
                budget.charge(0, end-offset, 0, retained)?;
                cursor.accept(owner, offset, end-offset)?;
                sink(owner, offset, &bytes[offset..end], &authors[offset*8..end*8])?;
            }
        }
        cursor.complete()?;
        Ok(budget.usage())
    }
    /// The first modern endpoint is produced by the existing native anchor,
    /// MAX and Cap join. No caller can supply a first R or a Score value.
    pub(crate) fn new(context:&'ctx H21EligibleContext<'src>,
        closed_max:&'max MaxStream<'snapshot>)->Result<Self,String> {
        let snapshot=closed_max.closed_native_snapshot(
            context.producer.plan,context.producer.input)?;
        let leases=[closed_max.closed_score_endpoint_leases(0)?,
            closed_max.closed_score_endpoint_leases(1)?];
        let first_origin=H21EligibleMapStage::descriptor().modern_start();
        if first_origin!=845_760 || leases.iter().enumerate().any(|(c,spans)| {
            spans.first().is_none_or(|span|span.context()!=c
                || span.first_origin()!=first_origin
                || span.last_origin()!=first_origin
                || span.cap_owner()!=FIRST_MODERN_OWNER
                || span.max_owner()!=844_670
                || span.parent()!=&snapshot.parent())
        }) {return Err("Score first modern source lease census".into());}
        let anchors=context.premodern_score_anchors()?;
        let first_modern=context.first_modern_score_cap(anchors,snapshot)?;
        first_modern.current.validate_identity(context.producer.plan,
            context.producer.input.profile(),context.descriptor,&context.maps)?;
        let w=source_upper(first_origin,context.producer.input,&context.producer.exports)?;
        first_modern.require_source_replay(context.stage(FIRST_MODERN_OWNER)?,
            w.clone(),context.descriptor)?;
        let mut first=ScoreEndpointRecord {owner:FIRST_MODERN_OWNER,roles:[None,None]};
        let mut frontiers=Vec::with_capacity(2);
        let layout=score::Layout::new();
        for c in 0..2 {
            let bits=first_modern_bits(&first_modern.current,c)?;
            if packed_word(&bits,layout.sv.clone())!=*leases[c][0].value()
                || packed_word(&bits,layout.p.clone())!=first_modern.anchors.second_r[c].value {
                return Err("Score first modern Cap/previous R source".into());
            }
            let r=packed_word(&bits,layout.r.clone());
            frontiers.push(ScoreFrontier {owner:FIRST_MODERN_OWNER,
                last_origin:first_origin,w:w.clone(),r});
            first.roles[c]=Some(ScoreEndpointRole {lease_index:0,
                previous_owner:ANCHOR_OWNERS[1],bits});
        }
        let frontier:[ScoreFrontier;2]=frontiers.try_into()
            .map_err(|_|"Score first modern frontier census")?;
        let mut records=Vec::new();
        records.try_reserve_exact(crate::h21_snapshot::SCORE_OWNERS)
            .map_err(|_|"Score endpoint compact record allocation")?;
        records.push(first);
        let out=Self {context,closed_max,first_modern,leases,next:[1,1],
            frontier,records};
        if out.retained_capacity_bytes()>16*1024*1024 {
            return Err("Score endpoint record/lease capacity cap".into());
        }
        Ok(out)
    }

    pub(crate) fn next_owner(&self)->Option<usize> {
        (0..2).filter_map(|c|self.leases[c].get(self.next[c])
            .map(ScoreEndpointLease::cap_owner)).min()
    }

    pub(crate) fn remaining_owners(&self)->usize {
        crate::h21_snapshot::SCORE_OWNERS-self.records.len()
    }

    /// Failure in either active context leaves both R frontiers unchanged.
    pub(crate) fn push_native(&mut self,owner:usize)->Result<(),String> {
        if self.next_owner()!=Some(owner) {
            return Err("Score endpoint exact ascending owner".into());
        }
        let snapshot=self.closed_max.closed_native_snapshot(
            self.context.producer.plan,self.context.producer.input)?;
        let mut staged_next=self.next;
        let mut staged_frontier=self.frontier.clone();
        let mut record=ScoreEndpointRecord {owner,roles:[None,None]};
        for c in 0..2 {
            let Some(lease)=self.leases[c].get(self.next[c]) else {continue};
            if lease.cap_owner()!=owner {continue;}
            if lease.parent()!=&snapshot.parent() || lease.context()!=c {
                return Err("Score endpoint parent/cut/context lease".into());
            }
            let w=source_upper(lease.last_origin(),self.context.producer.input,
                &self.context.producer.exports)?;
            let (role,frontier)=endpoint_role(c,lease,&self.frontier[c],w,self.next[c])?;
            staged_next[c]+=1;
            staged_frontier[c]=frontier;
            record.roles[c]=Some(role);
        }
        if record.roles.iter().all(Option::is_none) {
            return Err("Score endpoint owner without context".into());
        }
        // The sole state transition follows both source and arithmetic checks.
        self.records.push(record);
        self.next=staged_next;
        self.frontier=staged_frontier;
        Ok(())
    }

    pub(crate) fn is_closed(&self)->bool {
        self.next.iter().enumerate().all(|(c,index)|*index==self.leases[c].len())
            && self.records.len()==crate::h21_snapshot::SCORE_OWNERS && self.next_owner().is_none()
    }

    pub(crate) fn terminal_r(&self)->Result<[BigUint;2],String> {
        if !self.is_closed() {return Err("Score endpoint incomplete R closure".into());}
        let guards=H21EligibleMapStage::descriptor().guards();
        for c in 0..2 {
            if self.frontier[c].last_origin!=guards[c]
                || self.frontier[c].owner!=guards[c]-1 {
                return Err("Score endpoint terminal owner/guard".into());
            }
        }
        Ok([self.frontier[0].r.clone(),self.frontier[1].r.clone()])
    }

    /// Closed-stream membership. `None` means the owner has no source record;
    /// source or material errors for an admitted record remain errors.
    pub(crate) fn closed_owner_relation_status(&self,owner:usize)
        ->Result<Option<H21ClosedScoreOwnerRelation<'_>>,String> {
        if owner>=1<<21 {return Err("Score relation owner outside H21".into());}
        self.terminal_r()?;
        if score_endpoint_record(&self.records,owner).is_none() {return Ok(None);}
        self.closed_owner_relation(owner).map(Some)
    }

    /// Bind one generated Map/Slack/Score stage to this already closed stream.
    /// Callers supply only an owner; the parent context is always `self.context`.
    pub(crate) fn closed_owner_source(&self, owner: usize)
        -> Result<H21ClosedOwnerSource<'_, 'ctx, 'src, 'max, 'snapshot>, String> {
        if owner >= self.context.producer.plan.slots() {
            return Err("closed owner source outside H21".into());
        }
        let status = self.closed_owner_relation_status(owner)?;
        let stage = build_closed_owner_stage(self.context, owner, status)?;
        Ok(H21ClosedOwnerSource { stream: self, owner, stage })
    }

    /// Bind terminal-closed owner845887 Score terms to the regular physical
    /// author census produced from this stream's exact relation and context.
    pub(crate) fn closed_regular_carrier(
        &self,
    ) -> Result<ClosedRegularCarrier<'_, 'ctx, 'src, 'max, 'snapshot>, String> {
        use crate::packed_owner_assembly::{HeaderSourceBinding, ScoredOwnerPackingView};

        #[cfg(test)]
        let c575_counter = C575CarrierCounter::start()?;

        const OWNER: usize = 845_887;
        let owner_source = self.closed_owner_source(OWNER)?;
        let census = owner_source.with_checked_stage(|checked| {
            if checked.source.owner() != OWNER || checked.active != [true, true] {
                return Err("C517 closed regular Score exact owner/active contexts".into());
            }
            let relation = self.closed_owner_relation(OWNER)?;
            let join = self.context.join_scored_owner_source(OWNER, relation, self.closed_max)?;
            let view = ScoredOwnerPackingView::from_checked_join(join)?;
            let census = self.context.producer.produce_regular_owner845887_author_census(view)?;
            let expected = HeaderSourceBinding::for_plan(self.context.producer.plan, OWNER)?;
            if census.binding()? != &expected {
                return Err("C517 regular census exact HeaderSourceBinding".into());
            }
            let row_source = census.c509_regular_row_source()?;
            for context in 0..2 {
                if checked.map_terms(context)? != row_source.map_terms(context)?
                    || checked.score_terms(context)? != row_source.score_terms(context)?
                    || checked.slack_terms(context)? != row_source.slack_terms(context)? {
                    return Err("C517 closed token/census ordered Map/Score/Slack terms".into());
                }
            }
            Ok(census)
        })?;
        let carrier = ClosedRegularCarrier { owner_source, census };
        #[cfg(test)]
        let carrier = {
            c575_counter.finish()?; // Differential/fault work is OUTSIDE this counter.
            let mut carrier = carrier;
            c575_native_carrier_checks(&mut carrier)?;
            carrier
        };
        Ok(carrier)
    }

    /// Run one selected C514 U0 contribution from this stream's closed
    /// owner845887 carrier and the five physical source owners derived from
    /// this same context and MAX stream. The caller supplies only diagnostic r.
    pub(crate) fn c518_selected_u0(
        &self,
        r: &[Fr],
    ) -> Result<(
        [Fr; 3],
        crate::sparse_stream_roster::C514Metrics,
        [usize; 5],
        [usize; 5],
    ), String> {
        use crate::packed_owner_assembly::{
            HeaderSourceBinding, NativePhysicalAuthor, NativeRegularPhysicalAuthor,
            NativeWorkEndpointAuthor, ScoredOwnerPackingView,
        };
        use crate::h21_scheduled_max_cap::{MaxReplayAuthor, Writer};

        const OWNER: usize = 845_887;
        const PREVIOUS: usize = 845_759;
        const MAX_OWNER: usize = 844_798;
        const WORK0: usize = 845_885;
        const WORK1: usize = 845_886;

        // Construct the only 845887 candidate first. Every C514 edge below is
        // borrowed from this carrier's source-owned C509/C514 path.
        let carrier = self.closed_regular_carrier()?;

        // Build PreviousR845759 from this exact closed Score stream, then
        // complete the same sink's Work, PreviousR, Upper, Cap and MAX joins.
        let previous_relation = self.closed_owner_relation(PREVIOUS)?;
        let previous_stage = self.context.stage_with_score_slack(PREVIOUS, previous_relation)?;
        let previous_lease = self.context.owner_score_slack_lease(previous_stage)?;
        let mut previous_sink = self.context.owner_sink_845759()?;
        previous_sink.admit(previous_lease)?;
        self.context.join_owner_work_local_845759(&mut previous_sink)?;
        self.context.join_owner_previous_r_845759(&mut previous_sink)?;
        self.context.join_owner_work_upper_845759(&mut previous_sink)?;

        let snapshot = self.closed_max.closed_native_snapshot(
            self.context.producer.plan, self.context.producer.input,
        )?;
        let admission = crate::h21_scheduled_family_ledger::Admission::new(
            self.context.producer.plan, self.context.producer.input, &snapshot,
        )?;
        let cap_publication = admission.first_modern_cap_publication(
            self.context.producer.input,
        )?;
        previous_sink.admit_first_modern_cap(cap_publication)?;
        self.context.join_owner_cap_max_845759(&mut previous_sink, self.closed_max)?;

        let cap_lease = snapshot.first_modern_cap_lease(
            self.context.producer.plan, self.context.producer.input,
        )?;
        let overlay = previous_sink.packed_overlay_845759(self.context)?;
        let (previous_row, _previous_daa, previous_census) = self.context.producer
            .produce_with_carry_zero_daa_cap01_overlay_census_source_lease(
                PREVIOUS, &snapshot, &cap_lease, &overlay,
            )?;
        let bindings = [
            HeaderSourceBinding::for_plan(self.context.producer.plan, OWNER)?,
            HeaderSourceBinding::for_plan(self.context.producer.plan, PREVIOUS)?,
            HeaderSourceBinding::for_plan(self.context.producer.plan, MAX_OWNER)?,
            HeaderSourceBinding::for_plan(self.context.producer.plan, WORK0)?,
            HeaderSourceBinding::for_plan(self.context.producer.plan, WORK1)?,
        ];
        let previous_view = previous_sink.complete_row_source_view_845759(self.context)?;
        previous_census.check_complete(&bindings[1], &previous_row)?;
        previous_census.require_complete_row_view(&bindings[1], &previous_row, &previous_view)?;

        let max = self.context.producer.produce_scheduled_max_844798(self.closed_max)?;
        max.check_complete()?;
        let work0 = self.context.producer.work_endpoint_author_lease(WORK0)?;
        work0.check_complete()?;
        let work1 = self.context.producer.work_endpoint_author_lease(WORK1)?;
        work1.check_complete()?;

        let root = self.context.producer.plan.descriptor().root;
        let total = self.context.producer.plan.work_profile().total_be28;
        let profile = self.context.producer.input.profile();
        let cut = self.context.descriptor.canonical_identity();
        for (binding, owner) in bindings.iter().zip([OWNER, PREVIOUS, MAX_OWNER, WORK0, WORK1]) {
            if !binding.matches_sink(root, total, profile, &cut, owner) {
                return Err("C518 five physical sources do not share exact H21 parent/cut/layout".into());
            }
        }
        if carrier.census.binding()? != &bindings[0]
            || previous_view.binding() != &bindings[1]
            || max.binding() != &bindings[2]
            || work0.binding() != &bindings[3]
            || work1.binding() != &bindings[4] {
            return Err("C518 exact carrier/PreviousR/MAX/Work source bindings".into());
        }

        carrier.with_c514(|edges, _identity_sidecar| {
            if carrier.census.binding()? != &bindings[0] {
                return Err("C518 C514 edges differ from retained carrier census binding".into());
            }

            let family_for_wire = |wire: usize| -> Result<usize, String> {
                let owner = wire / WIDTH;
                let local = wire % WIDTH;
                match owner {
                    OWNER => Ok(0),
                    PREVIOUS => Ok(1),
                    MAX_OWNER if (999_424..1_000_097).contains(&local)
                        || (1_000_097..1_000_770).contains(&local) => Ok(2),
                    WORK0 if (987_450..987_898).contains(&local) => Ok(3),
                    WORK1 if (987_450..987_898).contains(&local) => Ok(4),
                    _ => Err(format!("C518 no physical source for owner{owner} local{local}")),
                }
            };

            let mut qualified = [0usize; 5];
            let mut reads = [0usize; 5];
            let (polynomial, metrics) = crate::sparse_stream_roster::c514_selected_u0_contribution(
                edges, r, 20, 21, 19, 0, &[19],
                |demands| {
                    for binding in &bindings {
                        let owner = binding.owner();
                        if !binding.matches_sink(root, total, profile, &cut, owner) {
                            return Err("C518 C514 demand source binding changed".into());
                        }
                    }
                    for demand in demands {
                        qualified[family_for_wire(demand.coordinate)?] += 1;
                    }
                    Ok(())
                },
                |wire| {
                    let family = family_for_wire(wire)?;
                    let value = match family {
                        0 => {
                            let (author, value) = carrier.census.checked_cell(wire)?;
                            match author {
                                NativeRegularPhysicalAuthor::Header
                                | NativeRegularPhysicalAuthor::Tree
                                | NativeRegularPhysicalAuthor::Daa
                                | NativeRegularPhysicalAuthor::Scored => value,
                            }
                        }
                        1 => {
                            previous_census.require_complete_row_view(
                                &bindings[1], &previous_row, &previous_view,
                            )?;
                            let (author, value) = previous_census.checked_cell(
                                &bindings[1], &previous_row, wire,
                            )?;
                            if author != NativePhysicalAuthor::Bank53 {
                                return Err("C518 PreviousR physical author is not Bank53".into());
                            }
                            value
                        }
                        2 => {
                            let (author, value) = max.checked_max_cell(wire)?;
                            let local = wire % WIDTH;
                            let context = if (999_424..1_000_097).contains(&local) { 0 } else { 1 };
                            if author != MaxReplayAuthor::Scheduled(Writer::Max {
                                context, end: MAX_OWNER + 2,
                            }) {
                                return Err("C518 scheduled MAX author/owner mismatch".into());
                            }
                            value
                        }
                        3 | 4 => {
                            let (author, value) = if family == 3 {
                                work0.checked_endpoint(wire)?
                            } else {
                                work1.checked_endpoint(wire)?
                            };
                            if author != NativeWorkEndpointAuthor::Tree {
                                return Err("C518 Work endpoint physical author is not Tree".into());
                            }
                            value
                        }
                        _ => return Err("C518 unsupported physical source family".into()),
                    };
                    reads[family] += 1;
                    Ok(value)
                },
            )?;
            if qualified.iter().sum::<usize>() != metrics.demands
                || reads.iter().sum::<usize>() != metrics.loads
                || qualified != reads {
                return Err("C518 per-family C514 demand/read census mismatch".into());
            }
            Ok((polynomial, metrics, qualified, reads))
        })?
    }

    pub(crate) fn c487_terminal_public_binding(&self,observed_frame_sha:&str,
        max_owners:usize,score_owners:usize,score_roles:usize)->Result<String,String> {
        h21_score_terminal_public::run_native(self,observed_frame_sha,
            max_owners,score_owners,score_roles)
    }

    pub(crate) fn c488_native_score_import(&self,frame_sha:&str,max_owners:usize,
        score_owners:usize,score_roles:usize)->Result<String,String>{
        self.terminal_r()?;let relation=self.closed_owner_relation(845_887)?;
        h21_score_import_seam::run_native(relation,frame_sha,max_owners,score_owners,score_roles)
    }

    /// The selected Score/Slack source remains borrowed from this closed stream
    /// and its held Eligible08 context until the local offer is published.
    #[allow(dead_code)]
    pub(crate) fn c489_native_score_slack_join(&self,frame_sha:&str,max_owners:usize,
        score_owners:usize,score_roles:usize)->Result<String,String>{
        self.terminal_r()?;
        h21_score_import_seam::run_c489_native(self,frame_sha,max_owners,
            score_owners,score_roles)
    }

    /// Lossless source values for a later authenticated X/ROW merger. A partial
    /// run has no replay interface; this grants no proof or statement output.
    pub(crate) fn closed_owner_cells(&self,owner:usize)
        ->Result<Vec<(usize,ScoreReplayAuthor,ark_bn254::Fr)>,String> {
        self.terminal_r()?;
        let index=self.records.partition_point(|record|record.owner<owner);
        let record=self.records.get(index).filter(|record|record.owner==owner)
            .ok_or("Score endpoint replay inactive owner")?;
        let mut cells=Vec::with_capacity(score::INPUT
            *record.roles.iter().filter(|role|role.is_some()).count());
        for c in 0..2 {
            let Some(role)=&record.roles[c] else {continue};
            let lease=self.leases[c].get(role.lease_index)
                .ok_or("Score endpoint replay lease index")?;
            if lease.cap_owner()!=owner || lease.context()!=c
                || lease.parent()!=&self.closed_max.closed_native_snapshot(
                    self.context.producer.plan,self.context.producer.input)?.parent() {
                return Err("Score endpoint replay source identity".into());
            }
            let author=ScoreReplayAuthor {context:c,origin:lease.last_origin(),
                previous_owner:role.previous_owner,max_owner:lease.max_owner(),
                cap_owner:lease.cap_owner()};
            for bit in 0..score::INPUT {
                cells.push((owner*WIDTH+SCORE_X[c]+bit,author,
                    ark_bn254::Fr::from(packed_bit(&role.bits,bit) as u64)));
            }
        }
        Ok(cells)
    }

    /// Reconstructs one exact owner relation only after both terminal R
    /// closures. The borrow keeps its immutable source stream alive. Physical
    /// input obligations remain visible to the later global author merger.
    pub(crate) fn closed_owner_relation(&self,owner:usize)
        ->Result<H21ClosedScoreOwnerRelation<'_>,String> {
        let record=closed_relation_record(self.terminal_r(),&self.records,owner)?;
        let snapshot=self.closed_max.closed_native_snapshot(
            self.context.producer.plan,self.context.producer.input)?;
        let identity=&self.first_modern.current;
        // The private immutable first-modern source was identity-validated at construction.
        let mut leases=[None,None];
        let mut previous:[Option<ScorePreviousInput>;2]=[None,None];
        for c in 0..2 {
            let Some(role)=&record.roles[c] else {continue};
            let lease=self.leases[c].get(role.lease_index)
                .ok_or("Score relation lease index")?;
            if lease.parent()!=&snapshot.parent() {
                return Err("Score relation source parent/cut".into());
            }
            leases[c]=Some(lease);
            let r=if role.lease_index==0 {
                if owner!=FIRST_MODERN_OWNER || role.previous_owner!=ANCHOR_OWNERS[1] {
                    return Err("Score relation first previous R author".into());
                }
                modern_previous(identity,c,&self.first_modern.anchors)?
            } else {
                let index=self.records.partition_point(|prior|prior.owner<role.previous_owner);
                let prior=self.records.get(index).filter(|prior|
                    prior.owner==role.previous_owner && prior.owner<owner)
                    .ok_or("Score relation missing source previous record")?;
                let prior_role=prior.roles[c].as_ref()
                    .ok_or("Score relation previous context absent")?;
                if prior_role.lease_index+1!=role.lease_index {
                    return Err("Score relation previous context sequence".into());
                }
                packed_word(&prior_role.bits,score::Layout::new().r)
            };
            previous[c]=Some(ScorePreviousInput {context:c,owner:role.previous_owner,r});
        }
        let work=ScoreWorkInput {owner:owner-1,height:owner+1,
            w:source_upper(owner+1,self.context.producer.input,&self.context.producer.exports)?};
        let material=score_relation_material(self.context.descriptor,record,leases,previous,work)?;
        Ok(H21ClosedScoreOwnerRelation {record,identity,material})
    }

    /// Capacity of owned compact records and endpoint leases only. The
    /// retained first-modern stages, source snapshot and native prefix are
    /// deliberately outside this local accounting and require runner limits.
    pub(crate) fn retained_capacity_bytes(&self)->usize {
        self.records.capacity()*std::mem::size_of::<ScoreEndpointRecord>()
            +self.leases.iter().map(|leases|leases.capacity()
                *std::mem::size_of::<ScoreEndpointLease>()
                +leases.iter().map(|lease|lease.value().to_bytes_le().len()).sum::<usize>())
                .sum::<usize>()
    }

    pub(crate) fn record_payload_bytes(&self)->usize {
        self.records.iter().map(|record|record.roles.iter()
            .filter(|role|role.is_some()).count()*(score::INPUT/8)).sum()
    }
}

impl H21FirstModernScore {
    pub(crate) fn publish_into(self, context: &H21EligibleContext<'_>,
        destination: &mut FirstModernDestination) -> Result<H21FirstModernLedger,String> {
        self.cap.require_native_parent(context.producer.plan,context.producer.input)?;
        self.current.validate_identity(context.producer.plan,context.producer.input.profile(),
            context.descriptor,&context.maps)?;
        // Replay the one owner against the same immutable context, retained R
        // authors and exact source MAX/Cap lease before assigning ROW ownership.
        let expected=context.stage(FIRST_MODERN_OWNER)?;
        let w=source_upper(FIRST_MODERN_OWNER+1,context.producer.input,&context.producer.exports)?;
        self.require_source_replay(expected,w,context.descriptor)?;
        let joined=super::super::h21_first_modern_ledger::publish(context.producer.plan,
            context.producer.input.profile(),&self.current,destination)?;
        Ok(H21FirstModernLedger {source:self,joined})
    }

    fn require_source_replay(&self,mut expected:H21EligibleMapStage,w:BigUint,
        descriptor:crate::bank53_map::CutDescriptor)->Result<(),String> {
        let records=std::array::from_fn(|c|modern_score_material(&expected,
            descriptor,c,w.clone(),&self.cap,&self.anchors));
        let [record0,record1]=records;
        expected.claim_first_modern_score_cap(&self.cap,&self.anchors,[record0?,record1?])?;
        if self.current != expected {return Err("first modern B2 source replay mismatch".into());}
        Ok(())
    }
}

fn anchor_index(owner: usize) -> Result<usize, String> {
    ANCHOR_OWNERS.iter().position(|candidate| *candidate == owner).ok_or_else(|| {
        if owner == FIRST_MODERN_OWNER {
            "Eligible08 modern Score requires authenticated Cap/ROW lease".into()
        } else {
            "Eligible08 owner is not a premodern Score anchor".into()
        }
    })
}

fn bits_to_word(bits: &[bool]) -> BigUint {
    let mut value = BigUint::from(0u8);
    for (k, bit) in bits.iter().enumerate() {
        if *bit { value |= BigUint::from(1u8) << k; }
    }
    value
}

fn checked_upper_bits(
    upper: [u8; 28], mut exported: impl FnMut(usize) -> Result<bool, String>,
) -> Result<BigUint, String> {
    let value = BigUint::from_bytes_be(&upper);
    for k in 0..224 {
        if exported(k)? != value.bit(k as u64) {
            return Err(format!("Eligible08 Upper export mismatch at bit {k}"));
        }
    }
    Ok(value)
}

fn source_upper(
    origin: usize, prefix: &NativePrefix,
    exports: &crate::native_owner_exports::NativeExports<'_>,
) -> Result<BigUint, String> {
    let source_owner = origin.checked_sub(2).ok_or("Eligible08 Upper owner underflow")?;
    let (_, upper) = prefix.interval(origin)?;
    checked_upper_bits(upper, |k| exports.bit(source_owner * WIDTH + UPPER_LOCAL + k))
}

fn anchor_spec(
    descriptor: crate::bank53_map::CutDescriptor, context: usize, owner: usize,
) -> Result<score::Spec, String> {
    let which = anchor_index(owner)?;
    let origin = owner.checked_add(1).ok_or("Eligible08 Score origin overflow")?;
    let maturity = descriptor.maturity_value(context, origin)?;
    Ok(score::Spec {
        active: true, origin_one: false, reducing: true, first: which == 0,
        terminal: false, empty_terminal: false, maturity,
        guard_total: None, expected: BigUint::from(0u8),
    })
}

fn check_previous(stage: &H21EligibleMapStage, context: usize, owner: usize,
    previous: Option<(&RLease, &H21EligibleMapStage)>) -> Result<BigUint, String> {
    match anchor_index(owner)? {
        0 if previous.is_none() => Ok(BigUint::from(0u8)),
        1 => {
            let (lease, source) = previous.ok_or("Eligible08 second anchor missing first R lease")?;
            if lease.parent_root != stage.parent_root
                || lease.parent_total != stage.parent_total
                || lease.parent_profile != stage.parent_profile
                || lease.cut_identity != stage.cut_identity
                || lease.binding != stage.map_bindings[context]
                || lease.context != context || lease.writer_owner != ANCHOR_OWNERS[0]
                || source.owner != lease.writer_owner
                || source.parent_root != lease.parent_root
                || source.parent_total != lease.parent_total
                || source.parent_profile != lease.parent_profile
                || source.cut_identity != lease.cut_identity
                || source.map_bindings[context] != lease.binding
                || lease.value.bits() > 225
            {
                return Err("Eligible08 previous R parent/cut/context/source lease".into());
            }
            let start = H21EligibleMapStage::score_live(context)?.start
                + score::Layout::new().r.start;
            for k in 0..225 {
                if source.claims.get(&(start + k))
                    != Some(&(H21StageAuthor::ScoreAnchor(context), lease.value.bit(k as u64))) {
                    return Err("Eligible08 previous R not authored at first anchor".into());
                }
            }
            Ok(lease.value.clone())
        }
        _ => Err("Eligible08 unexpected previous R lease".into()),
    }
}

fn score_material(
    stage: &H21EligibleMapStage, descriptor: crate::bank53_map::CutDescriptor,
    context: usize, w: BigUint, u: BigUint,
    previous: Option<(&RLease, &H21EligibleMapStage)>,
) -> Result<AnchorRecord, String> {
    if descriptor != H21EligibleMapStage::descriptor()
        || stage.cut_identity != descriptor.canonical_identity()
        || context >= 2 || stage.owner >= 1 << 21
    {
        return Err("Eligible08 Score parent/cut/context identity".into());
    }
    let spec = anchor_spec(descriptor, context, stage.owner)?;
    let p = check_previous(stage, context, stage.owner, previous)?;
    if w.bits() > 224 || u.is_zero() || u.bits() > 65 {
        return Err("Eligible08 Score W/U source range".into());
    }
    let input = score::ConditionalInputs { w, v: u.clone() };
    let values = score::produce(&spec, Some(&input), &p)?;
    let bits = values.iter().map(|value| {
        if value.is_zero() { Ok(false) }
        else if value.is_one() { Ok(true) }
        else { Err("Eligible08 Score non-Boolean producer bit".to_string()) }
    }).collect::<Result<Vec<_>, _>>()?;
    if bits.len() != score::INPUT { return Err("Eligible08 Score source width".into()); }
    let layout = score::Layout::new();
    let r = bits_to_word(&bits[layout.r.clone()]);
    if r.bits() > 225 || bits_to_word(&bits[layout.p.clone()]) != p {
        return Err("Eligible08 Score prior R/range".into());
    }

    let base = SCORE_X[context];
    let owner = stage.owner;
    let prior_owner = previous.map(|(lease, _)| lease.writer_owner);
    let mut terms = Vec::new();
    let mut emit_error = None;
    score::emit_local(&spec, |local| {
        if emit_error.is_some() { return; }
        let mut term = local.term;
        term.row = owner * ROW_WIDTH + SCORE_ROW[context] + term.row;
        let left_owner = if local.previous {
            match prior_owner {
                Some(previous) if layout.r.contains(&term.gate.left) => previous,
                _ => {
                    emit_error = Some("Eligible08 predecessor term without R lease".to_string());
                    return;
                }
            }
        } else { owner };
        term.gate.left = left_owner * WIDTH + base + term.gate.left;
        term.gate.right = owner * WIDTH + base + term.gate.right;
        terms.push(term);
    })?;
    if let Some(error) = emit_error { return Err(error); }
    let zero = Fr::zero();
    let one = Fr::one();
    for k in 0..65 {
        terms.push(Term { row: owner * ROW_WIDTH + V_ALIAS_ROW[context] + k,
            gate: Gate { left: owner * WIDTH + base + layout.sv.start + k,
                right: 0, c0: -Fr::from(u64::from(u.bit(k as u64))),
                c1: one, c2: zero, c3: zero } });
    }
    let upper_owner = owner - 1;
    for k in 0..224 {
        let row = owner * ROW_WIDTH + W_ALIAS_ROW[context] + k;
        terms.push(Term { row, gate: Gate {
            left: owner * WIDTH + base + layout.sw.start + k, right: 0,
            c0: zero, c1: one, c2: zero, c3: zero,
        }});
        terms.push(Term { row, gate: Gate {
            left: upper_owner * WIDTH + UPPER_LOCAL + k, right: 0,
            c0: zero, c1: -one, c2: zero, c3: zero,
        }});
    }
    Ok(AnchorRecord { parent_root: stage.parent_root,
        parent_total: stage.parent_total, parent_profile: stage.parent_profile,
        cut_identity: stage.cut_identity.clone(), binding: stage.map_bindings[context].clone(),
        context, owner, bits, r, terms })
}

fn modern_spec(descriptor:crate::bank53_map::CutDescriptor,
    context:usize)->Result<score::Spec,String> {
    if descriptor!=H21EligibleMapStage::descriptor()
        || descriptor.modern_start()!=845_760 || context>=2 {
        return Err("Eligible08 modern Score cut/context".into());
    }
    let maturity=descriptor.maturity_value(context,845_760)?;
    if maturity!=[4_995,2_090][context] {
        return Err("Eligible08 modern Score maturity".into());
    }
    Ok(score::Spec {active:true,origin_one:false,reducing:true,first:false,
        terminal:false,empty_terminal:false,maturity,guard_total:None,
        expected:BigUint::from(0u8)})
}

fn modern_previous(stage:&H21EligibleMapStage,context:usize,
    anchors:&H21PremodernAnchors)->Result<BigUint,String> {
    let lease=anchors.second_r.get(context).ok_or("Eligible08 modern R context")?;
    let source=&anchors.second;
    if stage.owner!=FIRST_MODERN_OWNER || source.owner!=ANCHOR_OWNERS[1]
        || lease.writer_owner!=ANCHOR_OWNERS[1] || lease.context!=context
        || lease.parent_root!=stage.parent_root || lease.parent_total!=stage.parent_total
        || lease.parent_profile!=stage.parent_profile || lease.cut_identity!=stage.cut_identity
        || lease.binding!=stage.map_bindings[context]
        || source.parent_root!=lease.parent_root || source.parent_total!=lease.parent_total
        || source.parent_profile!=lease.parent_profile || source.cut_identity!=lease.cut_identity
        || source.map_bindings[context]!=lease.binding || lease.value.bits()>225 {
        return Err("Eligible08 modern previous R parent/cut/context/source lease".into());
    }
    let start=H21EligibleMapStage::score_live(context)?.start+score::Layout::new().r.start;
    for k in 0..225 {
        if source.claims.get(&(start+k))
            !=Some(&(H21StageAuthor::ScoreAnchor(context),lease.value.bit(k as u64))) {
            return Err("Eligible08 modern previous R not authored at 845758".into());
        }
    }
    Ok(lease.value.clone())
}

fn modern_score_material(stage:&H21EligibleMapStage,
    descriptor:crate::bank53_map::CutDescriptor,context:usize,w:BigUint,
    cap:&FirstModernCapLease,anchors:&H21PremodernAnchors,
)->Result<AnchorRecord,String> {
    if descriptor!=H21EligibleMapStage::descriptor()
        || stage.cut_identity!=descriptor.canonical_identity()
        || stage.owner!=FIRST_MODERN_OWNER || context>=2 || w.bits()>224 {
        return Err("Eligible08 modern Score parent/cut/context/W".into());
    }
    cap.require_stage_identity(stage.parent_root,stage.parent_total,
        stage.parent_profile,&stage.cut_identity)?;
    let previous=modern_previous(stage,context,anchors)?;
    let spec=modern_spec(descriptor,context)?;
    let mut v=BigUint::from(0u8);
    for k in 0..65 {
        let (address,bit)=cap.cap_cell(context,k)?;
        if address!=stage.owner*WIDTH+[1_000_770,1_002_818][context]+740+k {
            return Err("Eligible08 modern V physical Cap address".into());
        }
        if bit {v|=BigUint::from(1u8)<<k;}
    }
    let values=score::produce(&spec,Some(&score::ConditionalInputs {w,v}),&previous)?;
    let bits=values.iter().map(|value| {
        if value.is_zero(){Ok(false)} else if value.is_one(){Ok(true)}
        else {Err("Eligible08 modern Score nonboolean bit".to_string())}
    }).collect::<Result<Vec<_>,_>>()?;
    if bits.len()!=score::INPUT {return Err("Eligible08 modern Score source width".into());}
    let layout=score::Layout::new();
    let r=bits_to_word(&bits[layout.r.clone()]);
    if r.bits()>225 || bits_to_word(&bits[layout.p.clone()])!=previous {
        return Err("Eligible08 modern Score previous R/range".into());
    }
    let owner=stage.owner;let base=SCORE_X[context];
    let mut terms=Vec::new();let mut emit_error=None;
    score::emit_local(&spec,|local| {
        if emit_error.is_some(){return;}
        let mut term=local.term;
        term.row=owner*ROW_WIDTH+SCORE_ROW[context]+term.row;
        let left_owner=if local.previous {
            if !layout.r.contains(&term.gate.left) {
                emit_error=Some("Eligible08 modern predecessor outside R".to_string());
                return;
            }
            ANCHOR_OWNERS[1]
        } else {owner};
        term.gate.left=left_owner*WIDTH+base+term.gate.left;
        term.gate.right=owner*WIDTH+base+term.gate.right;
        terms.push(term);
    })?;
    if let Some(error)=emit_error{return Err(error);}
    let zero=Fr::zero();let one=Fr::one();
    for k in 0..65 {
        let (cap_address,cap_bit)=cap.cap_cell(context,k)?;
        if bits[layout.sv.start+k]!=cap_bit {
            return Err("Eligible08 modern Score V differs from authored Cap q".into());
        }
        terms.push(Term {row:owner*ROW_WIDTH+V_ALIAS_ROW[context]+k,
            gate:Gate {left:owner*WIDTH+base+layout.sv.start+k,right:cap_address,
                c0:zero,c1:one,c2:-one,c3:zero}});
    }
    for k in 0..224 {
        let row=owner*ROW_WIDTH+W_ALIAS_ROW[context]+k;
        terms.push(Term {row,gate:Gate {left:owner*WIDTH+base+layout.sw.start+k,
            right:0,c0:zero,c1:one,c2:zero,c3:zero}});
        terms.push(Term {row,gate:Gate {left:(owner-1)*WIDTH+UPPER_LOCAL+k,
            right:0,c0:zero,c1:-one,c2:zero,c3:zero}});
    }
    Ok(AnchorRecord {parent_root:stage.parent_root,parent_total:stage.parent_total,
        parent_profile:stage.parent_profile,cut_identity:stage.cut_identity.clone(),
        binding:stage.map_bindings[context].clone(),context,owner,bits,r,terms})
}

impl H21EligibleMapStage {
    fn claim_score_anchor(&mut self, record: AnchorRecord,
        previous: Option<(&RLease, &H21EligibleMapStage)>) -> Result<RLease, String> {
        let context = record.context;
        if context >= 2 || record.owner != self.owner
            || record.parent_root != self.parent_root
            || record.parent_total != self.parent_total
            || record.parent_profile != self.parent_profile
            || record.cut_identity != self.cut_identity
            || record.binding != self.map_bindings[context]
        {
            return Err("Eligible08 Score stage parent/cut/context/binding".into());
        }
        let p = check_previous(self, context, self.owner, previous)?;
        let domain = Self::score_live(context)?;
        let layout = score::Layout::new();
        if record.bits.len() != score::INPUT || domain.len() != score::INPUT
            || bits_to_word(&record.bits[layout.r]) != record.r
            || bits_to_word(&record.bits[layout.p]) != p
            || domain.clone().any(|cell| self.claims.contains_key(&cell))
        {
            return Err("Eligible08 Score source/duplicate cell lease".into());
        }
        // All identity, source and collision checks precede every insertion.
        for (cell, bit) in domain.zip(record.bits) {
            self.claim_cell(H21StageAuthor::ScoreAnchor(context), cell, bit)?;
        }
        self.score_terms[context] = record.terms;
        Ok(RLease { parent_root: self.parent_root, parent_total: self.parent_total,
            parent_profile: self.parent_profile, cut_identity: self.cut_identity.clone(),
            binding: self.map_bindings[context].clone(), context, writer_owner: self.owner,
            value: record.r })
    }

    fn claim_first_modern_score_cap(&mut self,cap:&FirstModernCapLease,
        anchors:&H21PremodernAnchors,records:[AnchorRecord;2])->Result<(),String> {
        if self.owner!=FIRST_MODERN_OWNER {
            return Err("Eligible08 first modern owner only".into());
        }
        cap.require_stage_identity(self.parent_root,self.parent_total,
            self.parent_profile,&self.cut_identity)?;
        let mut staged=self.clone();
        let layout=score::Layout::new();
        for (context,record) in records.iter().enumerate() {
            if record.context!=context || record.owner!=self.owner
                || record.parent_root!=self.parent_root
                || record.parent_total!=self.parent_total
                || record.parent_profile!=self.parent_profile
                || record.cut_identity!=self.cut_identity
                || record.binding!=self.map_bindings[context]
                || record.bits.len()!=score::INPUT
                || bits_to_word(&record.bits[layout.r.clone()])!=record.r
                || bits_to_word(&record.bits[layout.p.clone()])
                    !=modern_previous(self,context,anchors)? {
                return Err("Eligible08 first modern Score source/identity/R".into());
            }
            let cap_domain=Self::cap_live(context)?;
            let cap_cells=cap.cap_cells(context)?;
            let cap_rows=cap.cap_rows(context)?;
            if cap_cells.len()!=cap_domain.len() {
                return Err("Eligible08 first modern Cap cell census".into());
            }
            for (expected,(local,bit)) in cap_domain.clone().zip(cap_cells.iter()) {
                if *local!=expected {return Err("Eligible08 first modern Cap physical X".into());}
                staged.claim_cell(H21StageAuthor::Cap(context),*local,*bit)?;
            }
            let score_domain=Self::score_live(context)?;
            for (cell,bit) in score_domain.zip(record.bits.iter().copied()) {
                staged.claim_cell(H21StageAuthor::ScoreModern(context),cell,bit)?;
            }
            for k in 0..65 {
                let (cap_address,cap_bit)=cap.cap_cell(context,k)?;
                if record.bits[layout.sv.start+k]!=cap_bit
                    || cap_cells[740+k]!=(cap_address%WIDTH,cap_bit) {
                    return Err("Eligible08 modern V/Cap authored X alias".into());
                }
                let alias=Term {row:self.owner*ROW_WIDTH+V_ALIAS_ROW[context]+k,
                    gate:Gate {left:self.owner*WIDTH+SCORE_X[context]+layout.sv.start+k,
                        right:cap_address,c0:Fr::zero(),c1:Fr::one(),
                        c2:-Fr::one(),c3:Fr::zero()}};
                if record.terms.iter().filter(|term|term.row==alias.row).count()!=1
                    || !record.terms.contains(&alias) {
                    return Err("Eligible08 modern V/Cap physical ROW alias".into());
                }
            }
            for k in 0..224 {
                let row=self.owner*ROW_WIDTH+W_ALIAS_ROW[context]+k;
                let score_term=Term {row,gate:Gate {
                    left:self.owner*WIDTH+SCORE_X[context]+layout.sw.start+k,
                    right:0,c0:Fr::zero(),c1:Fr::one(),
                    c2:Fr::zero(),c3:Fr::zero()}};
                let work_term=Term {row,gate:Gate {
                    left:(self.owner-1)*WIDTH+UPPER_LOCAL+k,
                    right:0,c0:Fr::zero(),c1:-Fr::one(),
                    c2:Fr::zero(),c3:Fr::zero()}};
                if record.terms.iter().filter(|term|term.row==row).count()!=2
                    || !record.terms.contains(&score_term)
                    || !record.terms.contains(&work_term) {
                    return Err("Eligible08 modern W/WORK physical ROW alias".into());
                }
            }
            staged.score_terms[context]=record.terms.clone();
            staged.cap_terms[context]=cap_rows;
        }
        // Only this incomplete stage's four active producers are considered;
        // global HEADER retirement and all other ROW families remain pending.
        let mut row_authors=BTreeMap::new();
        for (author,terms) in [(&staged.map_terms[0],0usize),(&staged.map_terms[1],1),
            (&staged.score_terms[0],2),(&staged.score_terms[1],3),
            (&staged.cap_terms[0],4),(&staged.cap_terms[1],5)]
            .into_iter().map(|(terms,author)|(author,terms)) {
            for term in terms {
                if term.row/ROW_WIDTH!=self.owner
                    || row_authors.insert(term.row,author).is_some_and(|prior|prior!=author) {
                    return Err("Eligible08 first modern local ROW author collision".into());
                }
            }
        }
        *self=staged;
        Ok(())
    }
}

impl<'a> H21EligibleContext<'a> {
    /// The type stays opaque to callers; future X/ROW admission may consume
    /// only its complete replay and must verify physical aliases separately.
    pub(crate) fn score_endpoint_stream<'ctx, 'max, 'snapshot>(
        &'ctx self,closed_max:&'max MaxStream<'snapshot>,
    )->Result<H21ScoreEndpointStream<'ctx, 'a, 'max, 'snapshot>,String> {
        H21ScoreEndpointStream::new(self,closed_max)
    }

    /// Produce only the two premodern anchors of each cut from this exact parent.
    /// The first modern owner has no admission until Cap/MAX and ROW source
    /// leases are available.
    pub(crate) fn premodern_score_anchors(&self) -> Result<H21PremodernAnchors, String> {
        let mut first = self.stage(ANCHOR_OWNERS[0])?;
        let mut second = self.stage(ANCHOR_OWNERS[1])?;
        let mut first_r = Vec::with_capacity(2);
        for context in 0..2 {
            let u = self.envelopes[context].u.clone();
            if self.maps[context].cap().to_biguint() != Some(u.clone())
                || self.maps[context].binding() != first.map_bindings[context]
                || self.maps[context].binding() != second.map_bindings[context]
            {
                return Err("Eligible08 Score U/Map cut source".into());
            }
            let w0 = source_upper(ANCHOR_OWNERS[0] + 1, self.producer.input,
                &self.producer.exports)?;
            let record0 = score_material(&first, self.descriptor, context,
                w0, u.clone(), None)?;
            let lease0 = first.claim_score_anchor(record0, None)?;
            first_r.push(lease0);
        }
        let first_r: [RLease; 2] = first_r.try_into()
            .map_err(|_| "Eligible08 first R census")?;
        let mut second_r = Vec::with_capacity(2);
        for context in 0..2 {
            let w1 = source_upper(ANCHOR_OWNERS[1] + 1, self.producer.input,
                &self.producer.exports)?;
            let record1 = score_material(&second, self.descriptor, context,
                w1, self.envelopes[context].u.clone(), Some((&first_r[context], &first)))?;
            let lease1 = second.claim_score_anchor(record1,
                Some((&first_r[context], &first)))?;
            second_r.push(lease1);
        }
        Ok(H21PremodernAnchors { first, second,
            first_r,
            second_r: second_r.try_into().map_err(|_| "Eligible08 second R census")? })
    }

    /// Owner 845759 is admitted only from the same NativePrefix, its two
    /// retained R anchors and the source-owned first Cap lease.
    pub(crate) fn first_modern_score_cap(&self,anchors:H21PremodernAnchors,
        snapshot:&Eligible08NativeSnapshot)->Result<H21FirstModernScore,String> {
        H21EligibleMapStage::require_header_owned_first_modern_scheduled(&self.parent_mask)?;
        let cap=snapshot.first_modern_cap_lease(self.producer.plan,self.producer.input)?;
        let mut current=self.stage(FIRST_MODERN_OWNER)?;
        let w=source_upper(FIRST_MODERN_OWNER+1,self.producer.input,
            &self.producer.exports)?;
        let records=[0,1].into_iter().map(|context|
            modern_score_material(&current,self.descriptor,context,w.clone(),&cap,&anchors))
            .collect::<Result<Vec<_>,_>>()?.try_into()
            .map_err(|_|"Eligible08 modern Score context census")?;
        current.claim_first_modern_score_cap(&cap,&anchors,records)?;
        Ok(H21FirstModernScore {current,anchors,cap})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map};

    pub(super) fn c575_structural_guard_controls() {
        // Existing actual admission checks; no closed-native source is minted.
        c515c_structural_only_relation_owner_and_status_join();
        let maps = synthetic_maps();
        let fixture = RelationFixture::new(845_761, 845_888, [true, true]);
        let identity = synthetic_stage(fixture.record.owner, &maps);
        let relation = fixture_relation(&fixture, &identity);
        let bindings = [maps[0].binding(), maps[1].binding()];
        assert!(checked_relation_contexts(&relation, fixture.record.owner,
            identity.parent_root, identity.parent_total, identity.parent_profile,
            &identity.cut_identity, [&bindings[0], &bindings[1]]).unwrap() == [true, true]);
        for fault in 0..6 {
            let mut owner = fixture.record.owner;
            let mut root = identity.parent_root;
            let mut total = identity.parent_total;
            let mut profile = identity.parent_profile;
            let mut cut = identity.cut_identity.clone();
            let mut bindings = [maps[0].binding(), maps[1].binding()];
            match fault {
                0 => owner += 1, 1 => root[0] ^= 1, 2 => total[0] ^= 1,
                3 => profile[0] ^= 1, 4 => cut.push(0),
                _ => { assert!(bindings[0] != bindings[1]); bindings.swap(0, 1); }
            }
            let error = checked_relation_contexts(&relation, owner, root, total,
                profile, &cut, [&bindings[0], &bindings[1]]).err()
                .expect("C575 isolated structural identity must reject");
            if fault < 5 { assert!(error == "closed owner relation parent/cut/owner identity"); }
        }
        assert!(checked_owner_status_contexts(None, fixture.record.owner,
            identity.parent_root, identity.parent_total, identity.parent_profile,
            &identity.cut_identity, [&bindings[0], &bindings[1]]).unwrap() == [false, false]);
    }

    fn synthetic_maps() -> [Map; 2] {
        let cuts = H21EligibleMapStage::descriptor().terminals();
        [55usize, 48].into_iter().enumerate().map(|(context, e)| {
            Map::new_modern_global_u_selected_lower(cuts[context] as u64, 21, e,
                LowerSelector { source: LowerSource::HeaderDifficulty { height: 841_729 },
                    branch: LowerBranch::Pivot(e - 1) }).unwrap()
        }).collect::<Vec<_>>().try_into().unwrap()
    }

    // A structural no-frame stage: it cannot stand in for NativePrefix, Map
    // generation, or a verified H21 parent. It isolates the lease boundary.
    fn synthetic_stage(owner: usize, maps: &[Map; 2]) -> H21EligibleMapStage {
        H21EligibleMapStage {
            owner, class: crate::daa_history_roster::OwnerClass::Carry,
            parent_root: [0x72; 32], parent_total: [0x73; 28],
            parent_profile: [0x74; 32],
            cut_identity: H21EligibleMapStage::descriptor().canonical_identity(),
            map_bindings: [maps[0].binding(), maps[1].binding()],
            map_reservations: [H21EligibleMapStage::map_live(0).unwrap(),
                H21EligibleMapStage::map_live(1).unwrap()],
            claims: BTreeMap::new(), map_terms: [Vec::new(), Vec::new()],
            score_terms: [Vec::new(), Vec::new()],
            cap_terms: [Vec::new(), Vec::new()],
        }
    }

    fn synthetic_anchors(maps:&[Map;2])->H21PremodernAnchors {
        let descriptor=H21EligibleMapStage::descriptor();
        let mut first=synthetic_stage(ANCHOR_OWNERS[0],maps);
        let mut second=synthetic_stage(ANCHOR_OWNERS[1],maps);
        let mut first_r=Vec::new();
        for context in 0..2 {
            let u=maps[context].cap().to_biguint().unwrap();
            let record=score_material(&first,descriptor,context,
                BigUint::from(417_790u64),u,None).unwrap();
            first_r.push(first.claim_score_anchor(record,None).unwrap());
        }
        let first_r:[RLease;2]=first_r.try_into().unwrap();
        let mut second_r=Vec::new();
        for context in 0..2 {
            let u=maps[context].cap().to_biguint().unwrap();
            let record=score_material(&second,descriptor,context,
                BigUint::from(845_758u64),u,Some((&first_r[context],&first))).unwrap();
            second_r.push(second.claim_score_anchor(record,
                Some((&first_r[context],&first))).unwrap());
        }
        H21PremodernAnchors {first,second,first_r,
            second_r:second_r.try_into().unwrap()}
    }

    /// Conditional W arrays carry arithmetic premises only. No native Upper
    /// publication is fabricated or relocated for this fixture.
    pub(super) fn r450_fixture() -> (R450Candidate, [H21EligibleMapStage; 2], [Map; 2], [Vec<(usize, Fr)>; 2]) {
        let maps = synthetic_maps();
        let anchors = synthetic_anchors(&maps);
        let templates = ANCHOR_OWNERS.map(|owner| synthetic_stage(owner, &maps));
        let upper = std::array::from_fn(|anchor| (0..224).map(|bit| (
            (ANCHOR_OWNERS[anchor] - 1) * WIDTH + UPPER_LOCAL + bit,
            Fr::from(((ANCHOR_OWNERS[anchor] as u64 >> bit.min(63)) & u64::from(bit < 64)) as u64)
        )).collect());
        let projection = project_r450(&anchors).unwrap();
        (R450Candidate { anchors, projection }, templates, maps, upper)
    }

    fn reject_r450(candidate: &R450Candidate, templates: &[H21EligibleMapStage; 2],
        maps: &[Map; 2], upper: &[Vec<(usize, Fr)>; 2], expected: &str) {
        let before = candidate.clone();
        assert_eq!(replay_r450(candidate, templates, maps, [&upper[0], &upper[1]]).unwrap_err(), expected);
        assert!(*candidate == before);
    }

    #[test]
    fn c205_r450_independent_replay_rejects_coordinated_r_lease_claim_projection_for_each_anchor_context() {
        let (golden, templates, maps, upper) = r450_fixture();
        let good = replay_r450(&golden, &templates, &maps, [&upper[0], &upper[1]]).unwrap();
        assert_eq!(good.cells.iter().map(Vec::len).collect::<Vec<_>>(), vec![450, 450]);
        for anchor in 0..2 { for context in 0..2 {
            let mut bad = golden.clone();
            let (stage, lease) = if anchor == 0 {
                (&mut bad.anchors.first, &mut bad.anchors.first_r[context])
            } else { (&mut bad.anchors.second, &mut bad.anchors.second_r[context]) };
            lease.value ^= BigUint::from(1u8);
            stage.claims.get_mut(&(SCORE_X[context] + score::Layout::new().r.start)).unwrap().1 ^= true;
            bad.projection.cells[anchor][context * 225].2 ^= true;
            reject_r450(&bad, &templates, &maps, &upper, "R450 independent canonical anchor/lease replay");
        }}
    }

    #[test]
    fn c205_r450_parent_map_context_owner_padding_and_ordered_term_faults_are_isolated() {
        let (golden, templates, maps, upper) = r450_fixture();
        for anchor in 0..2 { for context in 0..2 { for kind in 0..17 {
            let mut bad = golden.clone();
            let (stage, lease) = if anchor == 0 {
                (&mut bad.anchors.first, &mut bad.anchors.first_r[context])
            } else { (&mut bad.anchors.second, &mut bad.anchors.second_r[context]) };
            match kind {
                0 => stage.parent_root[0] ^= 1,
                1 => stage.parent_total[0] ^= 1,
                2 => stage.parent_profile[0] ^= 1,
                3 => stage.cut_identity.push(0),
                4 => stage.map_bindings.swap(0, 1),
                5 => stage.owner += 1,
                6 => lease.writer_owner += 1,
                7 => lease.context ^= 1,
                8 => lease.binding = maps[context ^ 1].binding(),
                9 => stage.claims.get_mut(&(SCORE_X[context] + score::INPUT - 1)).unwrap().1 = true,
                10 => { stage.score_terms[context].remove(0); },
                11 => { let duplicate = stage.score_terms[context][0].clone(); stage.score_terms[context].push(duplicate); },
                12 => stage.score_terms[context].swap(0, 1),
                13 => lease.parent_root[0] ^= 1,
                14 => lease.parent_total[0] ^= 1,
                15 => lease.parent_profile[0] ^= 1,
                _ => lease.cut_identity.push(0),
            }
            reject_r450(&bad, &templates, &maps, &upper, "R450 independent canonical anchor/lease replay");
        }}}
        for anchor in 0..2 {
            let mut bad = upper.clone(); bad[anchor][0].1 = Fr::one() - bad[anchor][0].1;
            reject_r450(&golden, &templates, &maps, &bad, "R450 independent canonical anchor/lease replay");
            let mut bad = upper.clone(); bad[anchor].pop();
            reject_r450(&golden, &templates, &maps, &bad, "R450 Upper census");
            let mut bad = upper.clone(); bad[anchor].swap(0, 1);
            reject_r450(&golden, &templates, &maps, &bad, "R450 Upper wire/boolean/order");
        }
        for kind in 0..3 {
            let mut bad = golden.clone();
            match kind { 0 => { bad.projection.cells[1].pop(); },
                1 => { let duplicate = bad.projection.cells[1][0]; bad.projection.cells[1].push(duplicate); },
                _ => bad.projection.cells[1].swap(0, 1) }
            reject_r450(&bad, &templates, &maps, &upper, "R450 exact ordered projection");
        }
        let mut swapped = maps.clone(); swapped.swap(0, 1);
        reject_r450(&golden, &templates, &swapped, &upper, "R450 expected source identity/empty Score stage");
        let mut reversed = templates.clone(); reversed.swap(0, 1);
        reject_r450(&golden, &reversed, &maps, &upper, "R450 expected source identity/empty Score stage");
    }

    #[test]
    fn c205_first_r_source_claim_mutants_reject_for_both_contexts() {
        let (golden, templates, maps, upper) = r450_fixture();
        let layout = score::Layout::new();
        for context in 0..2 {
            let first_r = SCORE_X[context] + layout.r.start;
            let mut flipped = golden.clone();
            let (author, value) = flipped.anchors.first.claims.get_mut(&first_r)
                .expect("first R fixture bit exists");
            assert_eq!(*author, H21StageAuthor::ScoreAnchor(context));
            *value ^= true;
            assert_eq!(flipped.anchors.first_r, golden.anchors.first_r,
                "first R lease remains unchanged for context{context}");
            assert_eq!(flipped.projection, golden.projection,
                "R450 projection remains unchanged for context{context}");
            reject_r450(&flipped, &templates, &maps, &upper,
                "R450 independent canonical anchor/lease replay");

            for wanted in [false, true] {
                let local = layout.r.clone().map(|offset| SCORE_X[context] + offset)
                    .find(|local| golden.anchors.first.claims.get(local)
                        .is_some_and(|(author, value)|
                            *author == H21StageAuthor::ScoreAnchor(context) && *value == wanted))
                    .expect("first R fixture has an identified zero and one bit per context");
                let mut removed = golden.clone();
                let (author, value) = removed.anchors.first.claims.get(&local)
                    .expect("identified first R bit exists");
                assert_eq!(*author, H21StageAuthor::ScoreAnchor(context));
                assert_eq!(*value, wanted);
                removed.anchors.first.claims.remove(&local);
                assert_eq!(removed.anchors.first_r, golden.anchors.first_r,
                    "first R lease remains unchanged for context{context}");
                assert_eq!(removed.projection, golden.projection,
                    "R450 projection remains unchanged for context{context}");
                reject_r450(&removed, &templates, &maps, &upper,
                    "R450 independent canonical anchor/lease replay");
            }
        }
    }

    #[test]
    fn maturity_calendar_matches_existing_local_reference() {
        let d = H21EligibleMapStage::descriptor();
        for context in 0..2 {
            let mode = d.maturity_mode(context).unwrap();
            for origin in [1, 417_791, 417_792, 845_759, 845_760,
                d.guards()[context]] {
                assert_eq!(d.maturity_value(context, origin).unwrap(),
                    crate::origin_score_map::maturity(mode, origin as u64));
            }
            assert!(d.maturity_value(context, d.guards()[context] + 1).is_err());
        }
        assert!(d.maturity_value(2, 417_791).is_err());
    }

    #[test]
    fn source_upper_export_mutant_is_isolated() {
        let mut bytes = [0u8; 28];
        bytes[27] = 0b0001_0101;
        let expected = BigUint::from_bytes_be(&bytes);
        assert_eq!(checked_upper_bits(bytes, |k| Ok(expected.bit(k as u64))).unwrap(),
            expected);
        let error = checked_upper_bits(bytes, |k| {
            Ok(expected.bit(k as u64) ^ (k == 2))
        }).unwrap_err();
        assert!(error.contains("bit 2"));
    }

    #[test]
    fn score_live_requires_unreplaced_parent_cells() {
        let mask = vec![false; WIDTH];
        H21EligibleMapStage::require_header_owned_score_live(&mask).unwrap();
        for context in 0..2 {
            let mut mutant = mask.clone();
            mutant[H21EligibleMapStage::score_live(context).unwrap().start] = true;
            assert_eq!(H21EligibleMapStage::require_header_owned_score_live(&mutant)
                .unwrap_err(),
                "Eligible08 Score LIVE must be HEADER-owned in parent mask");
        }
        assert_eq!(H21EligibleMapStage::require_header_owned_score_live(&mask[..WIDTH - 1])
            .unwrap_err(), "Eligible08 parent replacement mask width");
    }

    #[test]
    fn second_anchor_must_use_r_from_first_and_can_also_win() {
        let d = H21EligibleMapStage::descriptor();
        let u = BigUint::from(1u8) << 55usize;
        let w0 = BigUint::from(417_790u64);
        let w1 = &w0 + BigUint::from(427_968u64);
        let first = score::produce(&anchor_spec(d, 0, ANCHOR_OWNERS[0]).unwrap(),
            Some(&score::ConditionalInputs { w: w0, v: u.clone() }),
            &BigUint::from(0u8)).unwrap();
        let layout = score::Layout::new();
        let first_r = bits_to_word(&first[layout.r.clone()].iter()
            .map(|x| x.is_one()).collect::<Vec<_>>());
        let correct = score::produce(&anchor_spec(d, 0, ANCHOR_OWNERS[1]).unwrap(),
            Some(&score::ConditionalInputs { w: w1.clone(), v: u.clone() }),
            &first_r).unwrap();
        let wrong_zero = score::produce(&anchor_spec(d, 0, ANCHOR_OWNERS[1]).unwrap(),
            Some(&score::ConditionalInputs { w: w1, v: u }),
            &BigUint::from(0u8)).unwrap();
        assert_eq!(bits_to_word(&correct[layout.r.clone()].iter()
            .map(|x| x.is_one()).collect::<Vec<_>>()), first_r);
        assert_ne!(correct[layout.r.clone()], wrong_zero[layout.r]);

        // This large delta is an algebraic branch test, not a NativePrefix
        // fixture. W=[1,2,3] or this isolated pair proves no H21 provenance.
        let u = BigUint::from(1u8) << 48usize;
        let w0 = BigUint::from(417_790u64);
        let w1 = &w0 + BigUint::from(10u8).pow(21);
        let a0 = &w0 + &u * d.maturity_value(1, 417_791).unwrap();
        let a1 = &w1 + &u * d.maturity_value(1, 845_759).unwrap();
        assert!(a1 > a0);
        let second = score::produce(&anchor_spec(d, 1, ANCHOR_OWNERS[1]).unwrap(),
            Some(&score::ConditionalInputs { w: w1, v: u }), &a0).unwrap();
        let r = bits_to_word(&second[score::Layout::new().r].iter()
            .map(|x| x.is_one()).collect::<Vec<_>>());
        assert_eq!(r, a1);
    }

    #[test]
    fn synthetic_anchor_leases_bind_r_parent_cut_context_and_author() {
        let d = H21EligibleMapStage::descriptor();
        let maps = synthetic_maps();
        let mut first = synthetic_stage(ANCHOR_OWNERS[0], &maps);
        let mut second = synthetic_stage(ANCHOR_OWNERS[1], &maps);
        let w0 = BigUint::from(417_790u64);
        let w1 = &w0 + BigUint::from(427_968u64);
        let mut first_leases = Vec::new();
        for context in 0..2 {
            let u = maps[context].cap().to_biguint().unwrap();
            let record = score_material(&first, d, context, w0.clone(), u.clone(), None).unwrap();
            let duplicate = record.clone();
            let lease = first.claim_score_anchor(record, None).unwrap();
            assert_eq!(first.claim_score_anchor(duplicate, None).unwrap_err(),
                "Eligible08 Score source/duplicate cell lease");
            assert_eq!(first.claims.len(), (context + 1) * score::INPUT);
            first_leases.push(lease);
        }
        let mut wrong_zero = first_leases[0].clone(); wrong_zero.value = BigUint::from(0u8);
        assert!(score_material(&second, d, 0, w1.clone(),
            maps[0].cap().to_biguint().unwrap(), Some((&wrong_zero, &first)))
            .unwrap_err().contains("not authored"));
        let mut wrong_cut = first_leases[0].clone(); wrong_cut.cut_identity.push(1);
        assert!(score_material(&second, d, 0, w1.clone(),
            maps[0].cap().to_biguint().unwrap(), Some((&wrong_cut, &first))).is_err());
        let mut wrong_parent = first_leases[0].clone(); wrong_parent.parent_root[0] ^= 1;
        assert!(score_material(&second, d, 0, w1.clone(),
            maps[0].cap().to_biguint().unwrap(), Some((&wrong_parent, &first))).is_err());
        assert!(score_material(&second, d, 1, w1.clone(),
            maps[1].cap().to_biguint().unwrap(), Some((&first_leases[0], &first))).is_err());
        assert_eq!(second.claims.len(), 0);
        for context in 0..2 {
            let u = maps[context].cap().to_biguint().unwrap();
            let record = score_material(&second, d, context, w1.clone(), u,
                Some((&first_leases[context], &first))).unwrap();
            assert_eq!(record.owner, ANCHOR_OWNERS[1]);
            let prior_x = ANCHOR_OWNERS[0] * WIDTH + SCORE_X[context]
                + score::Layout::new().r.start;
            assert!(record.terms.iter().any(|term| term.gate.left == prior_x));
            let lease = second.claim_score_anchor(record,
                Some((&first_leases[context], &first))).unwrap();
            assert_eq!(lease.value, first_leases[context].value);
        }
        assert_eq!(second.claims.len(), 2 * score::INPUT);
        assert_eq!(anchor_spec(d, 0, FIRST_MODERN_OWNER).unwrap_err(),
            "Eligible08 modern Score requires authenticated Cap/ROW lease");
    }

    #[test]
    fn first_modern_score_reads_physical_cap_and_retained_r() {
        // This exercises the production join with no frame. The test-only
        // inputs do not authenticate NativePrefix or the full H21 history.
        let maps=synthetic_maps();
        let anchors=synthetic_anchors(&maps);
        let cap=Eligible08NativeSnapshot::first_modern_constant_d_for_test(
            [0x72;32],[0x73;28],[0x74;32],16).unwrap();
        let descriptor=H21EligibleMapStage::descriptor();
        let w=BigUint::from(845_759u64);
        let mut stage=synthetic_stage(FIRST_MODERN_OWNER,&maps);
        for context in 0..2 {
            stage.claim_map_live(context,&vec![false;BANK53_MAP_LIVE_BITS]).unwrap();
        }
        let pristine=stage.clone();
        let records:[AnchorRecord;2]=std::array::from_fn(|context|
            modern_score_material(&stage,descriptor,context,w.clone(),&cap,&anchors).unwrap());
        let layout=score::Layout::new();
        for context in 0..2 {
            let u=maps[context].cap().to_biguint().unwrap();
            assert_ne!(u,BigUint::from(32u8));
            assert!(cap.cap_cell(context,5).unwrap().1);
            assert!(records[context].bits[layout.sv.start+5]);
        }
        stage.claim_first_modern_score_cap(&cap,&anchors,records.clone()).unwrap();
        assert_eq!(stage.claims.len(),2*(BANK53_MAP_LIVE_BITS+score::INPUT+2048));
        for context in 0..2 {
            let cap_local=[1_000_770,1_002_818][context]+745;
            let score_local=SCORE_X[context]+layout.sv.start+5;
            assert_eq!(stage.claims.get(&cap_local),
                Some(&(H21StageAuthor::Cap(context),true)));
            assert_eq!(stage.claims.get(&score_local),
                Some(&(H21StageAuthor::ScoreModern(context),true)));
            assert_eq!(stage.cap_terms[context].len(),6419);
            let alias=stage.score_terms[context].iter().find(|term|
                term.row==FIRST_MODERN_OWNER*ROW_WIDTH+V_ALIAS_ROW[context]+5).unwrap();
            assert_eq!(alias.gate.left,FIRST_MODERN_OWNER*WIDTH+score_local);
            assert_eq!(alias.gate.right,FIRST_MODERN_OWNER*WIDTH+cap_local);
            assert_eq!((alias.gate.c1,alias.gate.c2),(Fr::one(),-Fr::one()));
            let predecessor=ANCHOR_OWNERS[1]*WIDTH+SCORE_X[context]+layout.r.start;
            assert!(stage.score_terms[context].iter().any(|term|term.gate.left==predecessor));
        }
        let claims_before=stage.claims.clone();
        assert!(stage.claim_first_modern_score_cap(&cap,&anchors,records.clone()).is_err());
        assert_eq!(stage.claims,claims_before,"duplicate writes are transactional");
        assert!(stage.claim_cell(H21StageAuthor::Cap(0),1_000_770+745,true).is_err());
        assert!(stage.claim_cell(H21StageAuthor::ScoreModern(0),SCORE_X[0]+224+5,true).is_err());

        let mut wrong_cap=Eligible08NativeSnapshot::first_modern_constant_d_for_test(
            [0x72;32],[0x73;28],[0x74;32],16).unwrap();
        wrong_cap.flip_cap_q_bit_for_test(1,5).unwrap();
        assert_eq!(wrong_cap.cap_cell(0,5).unwrap(),cap.cap_cell(0,5).unwrap());
        assert_ne!(wrong_cap.cap_cell(1,5).unwrap(),cap.cap_cell(1,5).unwrap());
        let mut candidate=pristine.clone();
        assert_eq!(candidate.claim_first_modern_score_cap(&wrong_cap,&anchors,records.clone())
            .unwrap_err(),"Eligible08 modern V/Cap authored X alias");
        assert_eq!(candidate.claims,pristine.claims);

        // A standalone local Score can be produced with V=U, yet its physical
        // V→Cap alias must reject that substitution even when algebraic Score
        // relations remain locally satisfiable.
        let u=maps[0].cap().to_biguint().unwrap();
        let previous=modern_previous(&pristine,0,&anchors).unwrap();
        let wrong_values=score::produce(&modern_spec(descriptor,0).unwrap(),
            Some(&score::ConditionalInputs {w:w.clone(),v:u.clone()}),&previous).unwrap();
        let wrong_bits=wrong_values.iter().map(|value|value.is_one()).collect::<Vec<_>>();
        let differing=(0..65).find(|k|wrong_bits[layout.sv.start+k]
            !=cap.cap_cell(0,*k).unwrap().1).unwrap();
        assert!(u.bit(differing as u64)!=cap.cap_cell(0,differing).unwrap().1);
        let mut wrong=records.clone();
        wrong[0].bits=wrong_bits;
        wrong[0].r=bits_to_word(&wrong[0].bits[layout.r.clone()]);
        let mut candidate=pristine.clone();
        assert_eq!(candidate.claim_first_modern_score_cap(&cap,&anchors,wrong).unwrap_err(),
            "Eligible08 modern V/Cap authored X alias");
        assert_eq!(candidate.claims,pristine.claims);

        let mut wrong_r=anchors.clone();wrong_r.second_r[0].value=BigUint::from(0u8);
        assert!(modern_score_material(&pristine,descriptor,0,w.clone(),&cap,&wrong_r)
            .unwrap_err().contains("not authored"));
        let mut missing_r=anchors.clone();
        missing_r.second.claims.remove(&(SCORE_X[0]+layout.r.start));
        assert!(modern_score_material(&pristine,descriptor,0,w.clone(),&cap,&missing_r)
            .unwrap_err().contains("not authored"));
        let mut wrong_parent=pristine.clone();wrong_parent.parent_root[0]^=1;
        assert!(modern_score_material(&wrong_parent,descriptor,0,w.clone(),&cap,&anchors)
            .is_err());
        let mut wrong_cut=pristine.clone();wrong_cut.cut_identity.push(1);
        assert!(modern_score_material(&wrong_cut,descriptor,0,w.clone(),&cap,&anchors)
            .is_err());
        let mut switched=pristine.clone();
        assert!(switched.claim_first_modern_score_cap(&cap,&anchors,
            [records[1].clone(),records[0].clone()]).is_err());
        assert_eq!(switched.claims,pristine.claims);
        let mut wrong_alias=records.clone();
        let alias_row=FIRST_MODERN_OWNER*ROW_WIDTH+V_ALIAS_ROW[0];
        wrong_alias[0].terms.iter_mut().find(|term|term.row==alias_row)
            .unwrap().gate.right^=1;
        let mut candidate=pristine.clone();
        assert_eq!(candidate.claim_first_modern_score_cap(&cap,&anchors,wrong_alias)
            .unwrap_err(),"Eligible08 modern V/Cap physical ROW alias");
        assert_eq!(candidate.claims,pristine.claims);
        let mut wrong_work_alias=records.clone();
        let work_row=FIRST_MODERN_OWNER*ROW_WIDTH+W_ALIAS_ROW[0];
        wrong_work_alias[0].terms.iter_mut().find(|term|
            term.row==work_row && term.gate.left==(FIRST_MODERN_OWNER-1)*WIDTH+UPPER_LOCAL)
            .unwrap().gate.left^=1;
        let mut candidate=pristine.clone();
        assert_eq!(candidate.claim_first_modern_score_cap(&cap,&anchors,wrong_work_alias)
            .unwrap_err(),"Eligible08 modern W/WORK physical ROW alias");
        assert_eq!(candidate.claims,pristine.claims);
        let mut off_schedule=synthetic_stage(FIRST_MODERN_OWNER-1,&maps);
        assert_eq!(off_schedule.claim_first_modern_score_cap(&cap,&anchors,records)
            .unwrap_err(),"Eligible08 first modern owner only");
    }

    #[test]
    fn first_modern_mask_and_work_export_mutants_fail() {
        // Compiling the full H21 plan exceeds the test harness's default 2 MiB stack.
        // Keep the production-plan check, but give this isolated no-frame test its own stack.
        std::thread::Builder::new().stack_size(32 * 1024 * 1024).spawn(|| {
            let plan=WorkTreeHistoryPlan::compile(1_827_840,21,[0x72;32],[0x73;28]).unwrap();
            let mask=plan.physical_assignment_replacement_mask(0).unwrap();
            H21EligibleMapStage::require_header_owned_first_modern_scheduled(&mask).unwrap();
            for local in [999_424,1_000_097,1_000_770,1_002_818] {
                let mut wrong=mask.clone();wrong[local]=true;
                assert_eq!(H21EligibleMapStage::require_header_owned_first_modern_scheduled(&wrong)
                    .unwrap_err(),"Eligible08 MAX/Cap LIVE must be HEADER-owned in parent mask");
            }
        }).unwrap().join().unwrap();
        let mut upper=[0u8;28];upper[27]=0b10101;
        let expected=BigUint::from_bytes_be(&upper);
        assert!(checked_upper_bits(upper,|k|Ok(expected.bit(k as u64)^(k==0)))
            .unwrap_err().contains("bit 0"));
    }

    #[test]
    fn first_modern_header_retirement_precode() {
        std::thread::Builder::new().stack_size(32 * 1024 * 1024).spawn(|| {
            let plan=WorkTreeHistoryPlan::compile(1_827_840,21,[0x72;32],[0x73;28]).unwrap();
            let maps=synthetic_maps();
            let anchors=synthetic_anchors(&maps);
            let cap=Eligible08NativeSnapshot::first_modern_constant_d_for_test(
                [0x72;32],[0x73;28],[0x74;32],16).unwrap();
            let mut stage=synthetic_stage(FIRST_MODERN_OWNER,&maps);
            for context in 0..2 {
                stage.claim_map_live(context,&vec![false;BANK53_MAP_LIVE_BITS]).unwrap();
                stage.map_terms[context]=crate::bank53_map::map_owner_terms_for_descriptor(
                    &maps[context],FIRST_MODERN_OWNER as u64,context,H21EligibleMapStage::descriptor()).unwrap();
            }
            let records=std::array::from_fn(|context|modern_score_material(&stage,
                H21EligibleMapStage::descriptor(),context,845_759u64.into(),&cap,&anchors).unwrap());
            stage.claim_first_modern_score_cap(&cap,&anchors,records).unwrap();
            let rows=stage.map_terms.iter().chain(stage.score_terms.iter()).chain(stage.cap_terms.iter())
                .flat_map(|terms|terms.iter()).map(|term|term.row).collect::<std::collections::BTreeSet<_>>();
            let mut retired=0;
            let mut conflicts=Vec::new();
            plan.visit_slot_terms(FIRST_MODERN_OWNER as u64,|term| {
                let local=term.gate.left.checked_sub(FIRST_MODERN_OWNER*WIDTH);
                let transferred=local.is_some_and(|local|stage.claims.contains_key(&local));
                if transferred {
                    assert_eq!((term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3),
                        (Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()));
                    assert_eq!(term.gate.right,FIRST_MODERN_OWNER*WIDTH);
                    retired+=1;
                } else if rows.contains(&term.row) {conflicts.push(term.row%ROW_WIDTH);}
                Ok(())
            }).unwrap();
            // Bank53 Map/Score zeros have HEADER assignment ownership but
            // no physical HEADER anchor here. Only Cap has anchor rows.
            assert_eq!(retired,4096);
            assert!(conflicts.is_empty(),"unretired shared HEADER rows {conflicts:?}");
        }).unwrap().join().unwrap();
    }

    #[test]
    fn production_first_modern_ledger_positive_and_isolated_faults() {
        std::thread::Builder::new().stack_size(32 * 1024 * 1024).spawn(|| {
            let plan=WorkTreeHistoryPlan::compile(1_827_840,21,[0x72;32],[0x73;28]).unwrap();
            let maps=synthetic_maps();
            let anchors=synthetic_anchors(&maps);
            let cap=Eligible08NativeSnapshot::first_modern_constant_d_for_test(
                [0x72;32],[0x73;28],[0x74;32],16).unwrap();
            let mut pristine=synthetic_stage(FIRST_MODERN_OWNER,&maps);
            for context in 0..2 {
                pristine.claim_map_live(context,&vec![false;BANK53_MAP_LIVE_BITS]).unwrap();
                pristine.map_terms[context]=crate::bank53_map::map_owner_terms_for_descriptor(
                    &maps[context],FIRST_MODERN_OWNER as u64,context,H21EligibleMapStage::descriptor()).unwrap();
            }
            let records=std::array::from_fn(|context|modern_score_material(&pristine,
                H21EligibleMapStage::descriptor(),context,845_759u64.into(),&cap,&anchors).unwrap());
            let mut current=pristine.clone();
            current.claim_first_modern_score_cap(&cap,&anchors,records).unwrap();
            let mut source=H21FirstModernScore {current,anchors,cap};
            source.require_source_replay(pristine.clone(),845_759u64.into(),
                H21EligibleMapStage::descriptor()).unwrap();

            // Corrupt the source-owned context1 q bit itself, leaving the
            // destination stage untouched: physical Cap-to-V admission fails.
            source.cap.flip_cap_q_bit_for_test(1,0).unwrap();
            assert_eq!(source.require_source_replay(pristine.clone(),845_759u64.into(),
                H21EligibleMapStage::descriptor()).unwrap_err(),"first modern B2 source replay mismatch");
            source.cap.flip_cap_q_bit_for_test(1,0).unwrap();

            // Keep identity and every other row unchanged while changing the
            // predecessor MAX source of one Cap D import in the retained B2 stage.
            let rows_before=source.current.cap_terms[0].clone();
            source.current.cap_terms[0].iter_mut().find(|term|
                term.gate.left/WIDTH==844_670 && term.gate.c1==-Fr::one())
                .unwrap().gate.left+=1;
            assert_eq!(source.require_source_replay(pristine,845_759u64.into(),
                H21EligibleMapStage::descriptor()).unwrap_err(),"first modern B2 source replay mismatch");
            source.current.cap_terms[0]=rows_before;
            super::super::super::h21_first_modern_ledger::exercise_structural_negatives(
                &plan,[0x74;32],&source.current);
        }).unwrap().join().unwrap();
    }

    #[test]
    fn modern_score_endpoint_matches_dense_recurrence_at_boundary_and_clipped_tails() {
        let descriptor=H21EligibleMapStage::descriptor();
        let cases=[(0,845_760,845_760,55usize),(0,845_761,845_888,55),
            (0,1_810_881,1_810_905,55),(1,1_810_753,1_810_842,48)];
        for (context,first,last,exponent) in cases {
            let v=BigUint::from(1u8)<<exponent;
            let maturity=descriptor.maturity_value(context,last).unwrap();
            assert!((first..=last).all(|origin|
                descriptor.maturity_value(context,origin).unwrap()==maturity));
            for previous_r in [BigUint::from(1u8)<<50usize,
                BigUint::from(1u8)<<130usize] {
                let prior_w=BigUint::from(1u8)<<120usize;
                let mut w=prior_w.clone();
                let mut dense=previous_r.clone();
                for origin in first..=last {
                    w+=BigUint::from(1+(origin%7) as u64);
                    let candidate=&w+&v*maturity;
                    if candidate>dense {dense=candidate;}
                }
                let lease=ScoreEndpointLease::synthetic_for_test(
                    context,first,last,v.clone());
                let prior=ScoreFrontier {owner:first-2,last_origin:first-1,
                    w:prior_w.clone(),r:previous_r.clone()};
                let (role,next)=endpoint_role(context,&lease,&prior,w.clone(),0).unwrap();
                assert_eq!(next.r,dense,"context {context} [{first},{last}]");
                assert_eq!(packed_word(&role.bits,score::Layout::new().p),previous_r);
                assert_eq!(next.last_origin,last);
                assert_eq!(next.owner,last-1);
                assert_eq!(role.previous_owner,first-2);

                // A missing positive-work step, a gap and a switched context
                // each fail before a successor R could be published.
                assert!(endpoint_role(context,&lease,&prior,prior_w.clone(),0).is_err());
                assert!(endpoint_role(1-context,&lease,&prior,w.clone(),0).is_err());
                let wrong=ScoreEndpointLease::synthetic_for_test(
                    context,first+1,last,v.clone());
                assert!(endpoint_role(context,&wrong,&prior,w.clone(),0).is_err());
            }
        }
        assert_eq!(descriptor.guards(),[1_810_905,1_810_842]);
        // The maturity reset before 845760 forbids compressing a span across
        // this boundary: larger W can still yield a smaller score there.
        let v=BigUint::from(100u8);
        let before=BigUint::from(100u8)+&v*23_155u64;
        let after=BigUint::from(101u8)+&v*4_995u64;
        assert!(before>after);
    }

    #[derive(Clone)]
    struct RelationFixture {
        record:ScoreEndpointRecord,
        leases:[Option<ScoreEndpointLease>;2],
        previous:[Option<ScorePreviousInput>;2],
        work:ScoreWorkInput,
    }
    impl RelationFixture {
        fn new(first:usize,last:usize,active:[bool;2])->Self {
            let owner=last-1;
            let w=(BigUint::from(1u8)<<120usize)+100u8;
            let mut out=Self {record:ScoreEndpointRecord {owner,roles:[None,None]},
                leases:[None,None],previous:[None,None],
                work:ScoreWorkInput {owner:owner-1,height:last,w:w.clone()}};
            for c in 0..2 {
                if !active[c] {continue;}
                let lease=ScoreEndpointLease::synthetic_for_test(c,first,last,
                    BigUint::from(1u8)<<[55usize,48][c]);
                let prior=ScoreFrontier {owner:first-2,last_origin:first-1,
                    w:&w-1u8,r:BigUint::from(1u8)<<125usize};
                out.record.roles[c]=Some(endpoint_role(c,&lease,&prior,w.clone(),1).unwrap().0);
                out.previous[c]=Some(ScorePreviousInput {context:c,owner:prior.owner,r:prior.r});
                out.leases[c]=Some(lease);
            }
            out
        }
        fn material(&self)->Result<ScoreRelationMaterial,String> {
            score_relation_material(H21EligibleMapStage::descriptor(),&self.record,
                [self.leases[0].as_ref(),self.leases[1].as_ref()],
                self.previous.clone(),self.work.clone())
        }
        fn c488()->Self {
            let owner=845_887;let w=(BigUint::from(1u8)<<120usize)+100u8;
            let pair=crate::h21_scheduled_max_cap::c488_first_regular_score_leases().unwrap();
            let mut out=Self{record:ScoreEndpointRecord{owner,roles:[None,None]},leases:[None,None],previous:[None,None],work:ScoreWorkInput{owner:845_886,height:845_888,w:w.clone()}};
            for (c,lease) in pair.into_iter().enumerate(){let prior=ScoreFrontier{owner:845_759,last_origin:845_760,w:&w-1u8,r:BigUint::from(1u8)<<125usize};out.record.roles[c]=Some(endpoint_role(c,&lease,&prior,w.clone(),1).unwrap().0);out.previous[c]=Some(ScorePreviousInput{context:c,owner:prior.owner,r:prior.r});out.leases[c]=Some(lease);}out
        }
        fn error(&self)->String {self.material().err().expect("isolated fault must reject")}
    }

    fn assert_relation_residuals(material:&ScoreRelationMaterial) {
        let mut values:BTreeMap<usize,Fr>=material.cells.iter()
            .map(|&(address,_,value)|(address,value)).collect();
        for &(address,_,value) in &material.reads {
            if let Some(prior)=values.insert(address,value) {assert_eq!(prior,value);}
        }
        let mut rows:BTreeMap<usize,Fr>=BTreeMap::new();
        for term in material.terms.iter().flatten() {
            let gate=&term.gate;
            if !gate.c1.is_zero() || !gate.c3.is_zero() {assert!(values.contains_key(&gate.left));}
            if !gate.c2.is_zero() || !gate.c3.is_zero() {assert!(values.contains_key(&gate.right));}
            let left=values.get(&gate.left).copied().unwrap_or_else(Fr::zero);
            let right=values.get(&gate.right).copied().unwrap_or_else(Fr::zero);
            *rows.entry(term.row).or_insert_with(Fr::zero)+=
                gate.c0+gate.c1*left+gate.c2*right+gate.c3*left*right;
        }
        assert!(!rows.is_empty());
        assert!(rows.values().all(Zero::is_zero));
    }

    #[test]
    fn c188_relation_matches_first_modern_ordered_terms_and_lossless_cells() {
        let maps=synthetic_maps();
        let anchors=synthetic_anchors(&maps);
        let identity=synthetic_stage(FIRST_MODERN_OWNER,&maps);
        let cap=Eligible08NativeSnapshot::first_modern_constant_d_for_test(
            [0x72;32],[0x73;28],[0x74;32],16).unwrap();
        let descriptor=H21EligibleMapStage::descriptor();
        let w=BigUint::from(845_759u64);
        let original:[AnchorRecord;2]=std::array::from_fn(|c|
            modern_score_material(&identity,descriptor,c,w.clone(),&cap,&anchors).unwrap());
        let leases:[ScoreEndpointLease;2]=std::array::from_fn(|c|
            ScoreEndpointLease::synthetic_for_test(c,845_760,845_760,32u8.into()));
        let record=ScoreEndpointRecord {owner:FIRST_MODERN_OWNER,
            roles:std::array::from_fn(|c|Some(ScoreEndpointRole {lease_index:0,
                previous_owner:ANCHOR_OWNERS[1],bits:pack_score(&original[c].bits.iter()
                    .map(|&bit|Fr::from(bit as u64)).collect::<Vec<_>>()).unwrap()}))};
        let previous=std::array::from_fn(|c|Some(ScorePreviousInput {
            context:c,owner:ANCHOR_OWNERS[1],r:anchors.second_r[c].value.clone()}));
        let material=score_relation_material(descriptor,&record,
            [Some(&leases[0]),Some(&leases[1])],previous,
            ScoreWorkInput {owner:FIRST_MODERN_OWNER-1,height:845_760,w}).unwrap();
        for c in 0..2 {
            assert_eq!(material.terms[c],original[c].terms,"ordered terms and multiplicity");
            assert_eq!(material.cells.iter().filter(|(_,a,_)|a.context==c).count(),score::INPUT);
            for bit in 0..score::INPUT {
                assert_eq!(material.cells[c*score::INPUT+bit],
                    (FIRST_MODERN_OWNER*WIDTH+SCORE_X[c]+bit,material.authors[c].unwrap(),
                        Fr::from(original[c].bits[bit] as u64)));
            }
        }
        assert_eq!(material.reads.len(),2*(225+65+224));
        assert_relation_residuals(&material);
        let relation=H21ClosedScoreOwnerRelation {record:&record,identity:&identity,material};
        assert_eq!(relation.owner(),FIRST_MODERN_OWNER);
        assert_eq!(relation.parent_root(),[0x72;32]);
        assert_eq!(relation.parent_total(),[0x73;28]);
        assert_eq!(relation.parent_profile(),[0x74;32]);
        assert_eq!(relation.cut_identity(),descriptor.canonical_identity());
        assert_eq!(relation.cells().len(),4096);
        assert!(relation.authors().iter().all(Option::is_some));
        assert_eq!(relation.reads().len(),1028);
        assert_eq!(relation.terms(0).unwrap(),original[0].terms);
        assert!(relation.terms(2).is_err());
    }

    #[test]
    fn c188_relation_previous_work_and_cap_single_faults_reject() {
        let good=RelationFixture::new(845_761,845_888,[true,true]);
        assert_relation_residuals(&good.material().unwrap());
        for c in 0..2 {
            let mut bad=good.clone();bad.previous[c]=None;
            assert_eq!(bad.error(),"Score relation missing previous R");
            let mut bad=good.clone();bad.previous[c].as_mut().unwrap().owner-=1;
            assert_eq!(bad.error(),"Score relation previous R author");
            let mut bad=good.clone();bad.previous[c].as_mut().unwrap().context=1-c;
            assert_eq!(bad.error(),"Score relation previous R author");
            let mut bad=good.clone();bad.previous[c].as_mut().unwrap().r+=1u8;
            assert_eq!(bad.error(),"Score relation previous R bit");
            let mut bad=good.clone();bad.leases[c]=None;
            assert_eq!(bad.error(),"Score relation missing Cap endpoint");
            let mut bad=good.clone();bad.leases[c]=Some(ScoreEndpointLease::synthetic_for_test(
                c,845_761,845_889,good.leases[c].as_ref().unwrap().value().clone()));
            assert_eq!(bad.error(),"Score relation Cap endpoint/context");
            let mut bad=good.clone();bad.leases[c]=Some(ScoreEndpointLease::synthetic_for_test(
                1-c,845_761,845_888,good.leases[c].as_ref().unwrap().value().clone()));
            assert_eq!(bad.error(),"Score relation Cap endpoint/context");
            let mut bad=good.clone();bad.leases[c]=Some(ScoreEndpointLease::synthetic_for_test(
                c,845_761,845_888,good.leases[c].as_ref().unwrap().value()+1u8));
            assert_eq!(bad.error(),"Score relation Cap q bit");
            let mut bad=good.clone();bad.record.roles[c].as_mut().unwrap().bits[250]|=1;
            assert_eq!(bad.error(),"Score relation nonzero input tail");
            let mut bad=good.clone();bad.record.roles[c].as_mut().unwrap().bits[100]^=1;
            assert_eq!(bad.error(),"Score relation exact source replay");
        }
        let mut bad=good.clone();bad.work.owner-=1;
        assert_eq!(bad.error(),"Score relation descriptor/owner/WORK source");
        let mut bad=good.clone();bad.work.height-=1;
        assert_eq!(bad.error(),"Score relation descriptor/owner/WORK source");
        let mut bad=good.clone();bad.work.w+=1u8;
        assert_eq!(bad.error(),"Score relation WORK upper bit");
        let mut bad=good.clone();bad.record.roles=[None,None];
        assert_eq!(bad.error(),"Score relation owner without active context");
    }

    #[test]
    fn c188_relation_one_context_clipped_tails_and_closed_selection() {
        for (c,first,last) in [(0,1_810_881,1_810_905),(1,1_810_753,1_810_842)] {
            let fixture=RelationFixture::new(first,last,[c==0,c==1]);
            let material=fixture.material().unwrap();
            assert_eq!(material.cells.len(),score::INPUT);
            assert_eq!(material.reads.len(),225+65+224);
            assert!(material.authors[1-c].is_none());
            assert!(material.terms[1-c].is_empty());
            assert!(material.cells.iter().all(|(_,a,_)|a.context==c && a.origin==last));
            assert_relation_residuals(&material);
            let mut bad=fixture.clone();
            bad.previous[1-c]=Some(ScorePreviousInput {context:1-c,owner:first-2,r:1u8.into()});
            assert_eq!(bad.error(),"Score relation inactive context source");
            let records=[fixture.record];
            assert_eq!(closed_relation_record(Err("Score endpoint incomplete R closure".into()),
                &records,last-1).err().unwrap(),"Score endpoint incomplete R closure");
            assert_eq!(closed_relation_record(Ok([0u8.into(),0u8.into()]),
                &records,last-2).err().unwrap(),"Score relation inactive owner");
            assert_eq!(closed_relation_record(Ok([0u8.into(),0u8.into()]),
                &records,last-1).unwrap().owner,last-1);
        }
    }

    #[test]
    fn c515b_sorted_score_record_membership_covers_first_regular_tail_and_absent_owner() {
        let records=vec![
            ScoreEndpointRecord {owner:845_759,roles:[Some(ScoreEndpointRole {
                lease_index:0,previous_owner:ANCHOR_OWNERS[1],bits:[0;score::INPUT/8]
            }),Some(ScoreEndpointRole {
                lease_index:0,previous_owner:ANCHOR_OWNERS[1],bits:[0;score::INPUT/8]
            })]},
            ScoreEndpointRecord {owner:845_887,roles:[Some(ScoreEndpointRole {
                lease_index:1,previous_owner:845_759,bits:[0;score::INPUT/8]
            }),Some(ScoreEndpointRole {
                lease_index:1,previous_owner:845_759,bits:[0;score::INPUT/8]
            })]},
            // Synthetic membership keys; the tail's active mask matches the
            // scheduled one-context endpoint, without claiming stream closure.
            ScoreEndpointRecord {owner:1_810_879,roles:[Some(ScoreEndpointRole {
                lease_index:7_540,previous_owner:1_810_751,bits:[0;score::INPUT/8]
            }),None]},
        ];
        assert_eq!(score_endpoint_record(&records,845_759).map(|record|record.owner),
            Some(845_759));
        assert_eq!(score_endpoint_record(&records,845_887).map(|record|record.owner),
            Some(845_887));
        let tail=score_endpoint_record(&records,1_810_879).unwrap();
        assert!(tail.roles[0].is_some());
        assert!(tail.roles[1].is_none());
        assert!(score_endpoint_record(&records,845_888).is_none());
    }

    // Conditional schedule-derived no-frame fixtures. These retain source
    // identities but grant no native authentication or global X/ROW authority.
    fn c498_clipped_fixture(lease:ScoreEndpointLease)->RelationFixture {
        let context=lease.context();
        let owner=lease.cap_owner();
        let w=(BigUint::from(1u8)<<120usize)+100u8;
        let prior=ScoreFrontier {owner:lease.first_origin()-2,
            last_origin:lease.first_origin()-1,w:&w-1u8,
            r:BigUint::from(1u8)<<125usize};
        let lease_index=[7_542,7_541][context]-1;
        let role=endpoint_role(context,&lease,&prior,w.clone(),lease_index).unwrap().0;
        let mut fixture=RelationFixture {record:ScoreEndpointRecord {owner,roles:[None,None]},
            leases:[None,None],previous:[None,None],
            work:ScoreWorkInput {owner:owner-1,height:owner+1,w}};
        fixture.record.roles[context]=Some(role);
        fixture.previous[context]=Some(ScorePreviousInput {
            context,owner:prior.owner,r:prior.r});
        fixture.leases[context]=Some(lease);
        fixture
    }

    fn c498_check_clipped_relation(relation:&H21ClosedScoreOwnerRelation<'_>,
        lease:&ScoreEndpointLease)->Result<(),String> {
        let context=lease.context();
        let (owner,previous,max_owner)=match context {
            0=>(1_810_904,1_810_879,1_809_918),
            1=>(1_810_841,1_810_751,1_809_790),
            _=>return Err("c498 clipped relation context".into()),
        };
        if relation.owner()!=owner || lease.cap_owner()!=owner
            || lease.last_origin()!=owner+1 || lease.first_origin()!=previous+2
            || lease.max_owner()!=max_owner
            || relation.parent_root()!=[0x72;32] || relation.parent_total()!=[0x73;28]
            || relation.parent_profile()!=[0x74;32]
            || relation.cut_identity()!=H21EligibleMapStage::descriptor().canonical_identity().as_slice()
            || relation.record.roles[context].as_ref().map(|role|role.lease_index)
                !=Some([7_542,7_541][context]-1) {
            return Err("c498 clipped relation source identity".into());
        }
        let author=ScoreReplayAuthor {context,origin:owner+1,
            previous_owner:previous,max_owner,cap_owner:owner};
        if relation.authors()[context]!=Some(author)
            || relation.authors()[1-context].is_some()
            || !relation.terms(1-context)?.is_empty() || relation.cells().len()!=2_048 {
            return Err("c498 clipped relation active census".into());
        }
        for (bit,&(wire,found,value)) in relation.cells().iter().enumerate() {
            if wire!=owner*WIDTH+SCORE_X[context]+bit || found!=author
                || (value!=Fr::zero() && value!=Fr::one())
                || (bit>=score::LIVE && value!=Fr::zero()) {
                return Err("c498 clipped relation ordered cell/author".into());
            }
        }
        let terms=relation.terms(context)?;
        if terms.len()!=8_545
            || terms.iter().map(|term|term.row).collect::<std::collections::BTreeSet<_>>().len()!=3_371
            || relation.reads().len()!=514 {
            return Err("c498 clipped relation term/ROW/read census".into());
        }
        let layout=score::Layout::new();
        for (index,&(wire,found,value)) in relation.reads().iter().enumerate() {
            let (expected_wire,expected_author,source_bit)=if index<225 {
                (previous*WIDTH+SCORE_X[context]+layout.r.start+index,
                    ScoreRelationReadAuthor::PreviousR {context,owner:previous},
                    layout.p.start+index)
            } else if index<290 {
                let bit=index-225;
                (owner*WIDTH+[1_000_770,1_002_818][context]+740+bit,
                    ScoreRelationReadAuthor::Cap {context,origin:owner+1,max_owner,cap_owner:owner},
                    layout.sv.start+bit)
            } else {
                let bit=index-290;
                ((owner-1)*WIDTH+UPPER_LOCAL+bit,
                    ScoreRelationReadAuthor::WorkUpper {owner:owner-1,height:owner+1},
                    layout.sw.start+bit)
            };
            if wire!=expected_wire || found!=expected_author
                || value!=relation.cells()[source_bit].2 {
                return Err("c498 clipped relation ordered typed read".into());
            }
        }
        Ok(())
    }

    #[test]
    fn c498_clipped_relations_retain_scheduled_source_cells_terms_and_reads() {
        let leases=crate::h21_scheduled_max_cap::c498_clipped_score_leases().unwrap();
        assert_eq!(leases[0].parent(),leases[1].parent());
        let maps=synthetic_maps();
        for lease in leases {
            let context=lease.context();
            let fixture=c498_clipped_fixture(lease);
            let retained=fixture.leases[context].as_ref().unwrap();
            let identity=synthetic_stage(fixture.record.owner,&maps);
            let relation=fixture_relation(&fixture,&identity);
            c498_check_clipped_relation(&relation,retained).unwrap();
            assert_relation_residuals(&relation.material);
            assert_eq!(relation.reads().iter().filter(|(_,author,_)|
                matches!(author,ScoreRelationReadAuthor::PreviousR {..})).count(),225);
            assert_eq!(relation.reads().iter().filter(|(_,author,_)|
                matches!(author,ScoreRelationReadAuthor::Cap {..})).count(),65);
            assert_eq!(relation.reads().iter().filter(|(_,author,_)|
                matches!(author,ScoreRelationReadAuthor::WorkUpper {..})).count(),224);
            assert_eq!(relation.authors()[context].unwrap().max_owner,retained.max_owner());
            assert_eq!(relation.authors()[context].unwrap().cap_owner,retained.cap_owner());
        }
    }

    #[test]
    fn c498_clipped_relation_missing_reordered_and_foreign_sources_reject() {
        let maps=synthetic_maps();
        for lease in crate::h21_scheduled_max_cap::c498_clipped_score_leases().unwrap() {
            let context=lease.context();
            let fixture=c498_clipped_fixture(lease);
            let retained=fixture.leases[context].as_ref().unwrap();
            let identity=synthetic_stage(fixture.record.owner,&maps);
            for fault in 0..5 {
                let mut relation=fixture_relation(&fixture,&identity);
                match fault {
                    0=>{relation.material.cells.pop();}, // Required zero padding still needs a source.
                    1=>relation.material.cells.swap(0,1),
                    2=>relation.material.cells[0].1.max_owner-=1,
                    3=>relation.material.reads.swap(0,1),
                    4=>relation.material.reads[225].1=ScoreRelationReadAuthor::Cap {
                        context,origin:fixture.record.owner+1,
                        max_owner:retained.max_owner()-1,cap_owner:fixture.record.owner},
                    _=>unreachable!(),
                }
                assert!(c498_check_clipped_relation(&relation,retained).is_err(),
                    "isolated conditional source fault {fault}");
                c498_check_clipped_relation(&fixture_relation(&fixture,&identity),retained).unwrap();
            }
        }
    }

    fn c498_h21_profile()->[u8;32] {
        use blake2::{Blake2b, Digest, digest::consts::U32};
        let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        Blake2b::<U32>::digest(bytes).into()
    }

    // The parent is selected before either fixture material or Map Pair issue.
    // This owner and its callback exist only in this unit-test module.
    struct C498H21FixtureOwner {
        fixture:RelationFixture,
        identity:H21EligibleMapStage,
        binding:crate::packed_owner_assembly::HeaderSourceBinding,
        map_pair:crate::packed_owner_assembly::Eligible08MapPairLease,
    }
    impl C498H21FixtureOwner {
        fn new(lease:ScoreEndpointLease,root:[u8;32],total:[u8;28],profile:[u8;32],
            maps:[Map;2])->Result<Self,String> {
            use crate::packed_owner_assembly::{HeaderSourceBinding,Eligible08MapPairLease};
            let owner=lease.cap_owner();
            let cut=H21EligibleMapStage::descriptor().canonical_identity();
            if profile!=c498_h21_profile()
                || !lease.c498_matches_parent(root,total,profile,&cut) {
                return Err("c498b fixture scheduled parent".into());
            }
            let identity=H21EligibleMapStage {
                owner,class:crate::daa_history_roster::OwnerClass::Carry,
                parent_root:root,parent_total:total,parent_profile:profile,
                cut_identity:cut.clone(),map_bindings:maps.each_ref().map(Map::binding),
                map_reservations:[H21EligibleMapStage::map_live(0)?,
                    H21EligibleMapStage::map_live(1)?],
                claims:BTreeMap::new(),map_terms:[Vec::new(),Vec::new()],
                score_terms:[Vec::new(),Vec::new()],cap_terms:[Vec::new(),Vec::new()],
            };
            let binding=HeaderSourceBinding::from_sink_for_test(root,total,profile,cut,owner);
            let map_pair=Eligible08MapPairLease::synthetic_valid_for_test(
                binding.clone(),owner,crate::daa_history_roster::OwnerClass::Carry,maps)?;
            Ok(Self {fixture:c498_clipped_fixture(lease),identity,binding,map_pair})
        }

        fn with_relation(&self,consume:impl FnOnce(
            &H21ClosedScoreOwnerRelation<'_>,
            &crate::packed_owner_assembly::HeaderSourceBinding,
            &crate::packed_owner_assembly::Eligible08MapPairLease)->Result<(),String>)
            ->Result<(),String> {
            let relation=fixture_relation(&self.fixture,&self.identity);
            consume(&relation,&self.binding,&self.map_pair)
        }
    }

    // Signature-only custody probe: private fields retain the three original
    // borrows. It cannot author a row or leave the unit-result callback.
    mod c498_borrow_probe {
        use super::*;
        use crate::packed_owner_assembly::{HeaderSourceBinding,Eligible08MapPairLease};

        pub(super) struct Probe<'borrow,'source> {
            relation:&'borrow H21ClosedScoreOwnerRelation<'source>,
            binding:&'borrow HeaderSourceBinding,
            map_pair:&'borrow Eligible08MapPairLease,
        }
        impl<'borrow,'source> Probe<'borrow,'source> {
            pub(super) fn new(relation:&'borrow H21ClosedScoreOwnerRelation<'source>,
                binding:&'borrow HeaderSourceBinding,map_pair:&'borrow Eligible08MapPairLease,
                context:usize)->Result<Self,String> {
                if context>=2 || relation.owner()!=[1_810_904,1_810_841][context]
                    || relation.parent_profile()!=c498_h21_profile()
                    || !binding.matches_sink(relation.parent_root(),relation.parent_total(),
                        relation.parent_profile(),relation.cut_identity(),relation.owner())
                    || map_pair.binding()!=binding {
                    return Err("c498b borrowed parent/context".into());
                }
                map_pair.checked_cells(binding,relation.owner(),
                    crate::daa_history_roster::OwnerClass::Carry)?;
                for c in 0..2 {
                    if map_pair.map_binding(c)?!=&relation.identity.map_bindings[c] {
                        return Err("c498b borrowed Map binding".into());
                    }
                }
                Ok(Self {relation,binding,map_pair})
            }

            pub(super) fn check(&self,fixture:&RelationFixture,context:usize,
                original_pair:&Eligible08MapPairLease)->Result<(),String> {
                if !std::ptr::eq(self.map_pair,original_pair)
                    || !self.binding.matches_sink(self.relation.parent_root(),
                        self.relation.parent_total(),self.relation.parent_profile(),
                        self.relation.cut_identity(),self.relation.owner()) {
                    return Err("c498b original borrow identity".into());
                }
                c498_check_h21_relation(self.relation,fixture,context)
            }
        }
    }

    fn c498_check_h21_relation(relation:&H21ClosedScoreOwnerRelation<'_>,
        fixture:&RelationFixture,context:usize)->Result<(),String> {
        let (owner,first,last,previous,max_owner,index)=match context {
            0=>(1_810_904,1_810_881,1_810_905,1_810_879,1_809_918,7_541),
            1=>(1_810_841,1_810_753,1_810_842,1_810_751,1_809_790,7_540),
            _=>return Err("c498b oracle context".into()),
        };
        let lease=fixture.leases[context].as_ref().ok_or("c498b retained lease")?;
        let prior=fixture.previous[context].as_ref().ok_or("c498b retained previous")?;
        if relation.owner()!=owner || fixture.record.owner!=owner
            || (lease.context(),lease.first_origin(),lease.last_origin(),
                lease.max_owner(),lease.cap_owner())!=(context,first,last,max_owner,owner)
            || !lease.c498_matches_parent(relation.parent_root(),relation.parent_total(),
                relation.parent_profile(),relation.cut_identity())
            || relation.parent_profile()!=c498_h21_profile()
            || relation.cut_identity()!=H21EligibleMapStage::descriptor().canonical_identity()
            || (prior.context,prior.owner)!=(context,previous)
            || (fixture.work.owner,fixture.work.height)!=(owner-1,last)
            || relation.record.roles[context].as_ref().map(|role|role.lease_index)!=Some(index)
            || relation.record.roles[1-context].is_some()
            || fixture.leases[1-context].is_some() || fixture.previous[1-context].is_some() {
            return Err("c498b oracle terminal/source identity".into());
        }
        let author=ScoreReplayAuthor {context,origin:last,previous_owner:previous,
            max_owner,cap_owner:owner};
        if relation.authors()[context]!=Some(author) || relation.authors()[1-context].is_some()
            || !relation.terms(1-context)?.is_empty() || relation.cells().len()!=2_048 {
            return Err("c498b oracle active census".into());
        }

        // Arithmetic may share the local emitter; all placement and external
        // aliases below are reconstructed from the fixed terminal tuple.
        let spec=score::Spec {active:true,origin_one:false,reducing:true,first:false,
            terminal:false,empty_terminal:false,maturity:[4_995,2_090][context],
            guard_total:None,expected:BigUint::from(0u8)};
        let values=score::produce(&spec,Some(&score::ConditionalInputs {
            w:fixture.work.w.clone(),v:lease.value().clone()}),&prior.r)?;
        let input_base=(owner<<20)+[677_501,685_693][context];
        let row_base=(owner<<19)+[487_421,502_652][context];
        let predecessor_base=(previous<<20)+[677_501,685_693][context];
        let layout=score::Layout::new();
        if values.len()!=2_048 || score::INPUT-score::LIVE!=54 {
            return Err("c498b oracle cell dimensions".into());
        }
        for (ordinal,&(wire,found,value)) in relation.cells().iter().enumerate() {
            if wire!=input_base+ordinal || found!=author || value!=values[ordinal]
                || (value!=Fr::zero() && value!=Fr::one())
                || (ordinal>=1_994 && value!=Fr::zero()) {
                return Err(format!("c498b oracle cell ordinal {ordinal}"));
            }
        }
        let mut terms=Vec::with_capacity(8_545);
        score::emit_local(&spec,|local| {
            let source=local.term;
            terms.push(Term {row:row_base+source.row,gate:Gate {
                left:if local.previous {predecessor_base+source.gate.left}
                    else {input_base+source.gate.left},
                right:input_base+source.gate.right,c0:source.gate.c0,c1:source.gate.c1,
                c2:source.gate.c2,c3:source.gate.c3}});
        })?;
        let zero=Fr::zero();let one=Fr::one();
        let cap_base=(owner<<20)+[1_000_770,1_002_818][context]+740;
        let work_base=((owner-1)<<20)+987_450;
        let mut reads=Vec::with_capacity(514);
        for bit in 0..225 {
            reads.push((predecessor_base+layout.r.start+bit,
                ScoreRelationReadAuthor::PreviousR {context,owner:previous},
                Fr::from(prior.r.bit(bit as u64) as u64)));
        }
        for bit in 0..65 {
            terms.push(Term {row:(owner<<19)+[491_629,506_860][context]+bit,
                gate:Gate {left:input_base+layout.sv.start+bit,right:cap_base+bit,
                    c0:zero,c1:one,c2:-one,c3:zero}});
            reads.push((cap_base+bit,ScoreRelationReadAuthor::Cap {
                context,origin:last,max_owner,cap_owner:owner},
                Fr::from(lease.value().bit(bit as u64) as u64)));
        }
        for bit in 0..224 {
            let row=(owner<<19)+[491_694,506_925][context]+bit;
            terms.push(Term {row,gate:Gate {left:input_base+layout.sw.start+bit,
                right:0,c0:zero,c1:one,c2:zero,c3:zero}});
            terms.push(Term {row,gate:Gate {left:work_base+bit,
                right:0,c0:zero,c1:-one,c2:zero,c3:zero}});
            reads.push((work_base+bit,ScoreRelationReadAuthor::WorkUpper {
                owner:owner-1,height:last},Fr::from(fixture.work.w.bit(bit as u64) as u64)));
        }
        let actual=relation.terms(context)?;
        if terms.len()!=8_545 || actual.len()!=terms.len()
            || reads.len()!=514 || relation.reads().len()!=reads.len() {
            return Err("c498b oracle term/read census".into());
        }
        for (ordinal,(found,expected)) in actual.iter().zip(&terms).enumerate() {
            if found!=expected {return Err(format!("c498b oracle term ordinal {ordinal}"));}
        }
        for (ordinal,(found,expected)) in relation.reads().iter().zip(&reads).enumerate() {
            if found!=expected {return Err(format!("c498b oracle read ordinal {ordinal}"));}
        }
        Ok(())
    }

    #[test]
    fn c498b_h21_parent_callback_retains_exact_clipped_sources()->Result<(),String> {
        let root=[7;32];let total=[8;28];let profile=c498_h21_profile();
        let leases=crate::h21_scheduled_max_cap::c498_clipped_score_leases_for_h21_parent(
            root,total,profile)?;
        assert_eq!(leases[0].parent(),leases[1].parent());
        assert_eq!(crate::h21_scheduled_max_cap::c498_clipped_score_leases_for_h21_parent(
            root,total,[0x74;32]).unwrap_err(),"c498 conditional fixed H21 profile");
        for (context,lease) in leases.into_iter().enumerate() {
            let owner=C498H21FixtureOwner::new(lease,root,total,profile,
                H21EligibleMapStage::source_maps()?)?;
            owner.with_relation(|relation,binding,pair| {
                assert!(binding.matches_sink(root,total,profile,
                    &H21EligibleMapStage::descriptor().canonical_identity(),relation.owner()));
                c498_borrow_probe::Probe::new(relation,binding,pair,context)?
                    .check(&owner.fixture,context,&owner.map_pair)
            })?;
        }
        Ok(())
    }

    #[test]
    fn c498b_h21_parent_context_and_order_faults_reject_with_recovery()->Result<(),String> {
        let root=[7;32];let total=[8;28];let profile=c498_h21_profile();
        let leases=crate::h21_scheduled_max_cap::c498_clipped_score_leases_for_h21_parent(
            root,total,profile)?;
        for (context,lease) in leases.into_iter().enumerate() {
            let owner=C498H21FixtureOwner::new(lease,root,total,profile,
                H21EligibleMapStage::source_maps()?)?;
            for field in 0..4 {
                owner.with_relation(|relation,binding,pair| {
                    let wrong=if field<3 {binding.mutated_field_for_test(field)}
                        else {binding.clone()};
                    let wrong_context=if field==3 {1-context} else {context};
                    assert!(c498_borrow_probe::Probe::new(relation,&wrong,pair,wrong_context).is_err(),
                        "isolated root/total/profile/context fault {field}");
                    Ok(())
                })?;
                owner.with_relation(|relation,binding,pair| {
                    c498_borrow_probe::Probe::new(relation,binding,pair,context)?
                        .check(&owner.fixture,context,&owner.map_pair)
                })?;
            }
            for fault in 0..5 {
                let mut bad=fixture_relation(&owner.fixture,&owner.identity);
                let expected=match fault {
                    0=>{
                        let first_work=8_545-448;
                        let terms=&mut bad.material.terms[context];
                        assert_eq!(terms[first_work].row,terms[first_work+1].row);
                        assert_ne!(terms[first_work],terms[first_work+1]);
                        terms.swap(first_work,first_work+1);
                        format!("c498b oracle term ordinal {first_work}")
                    },
                    1=>{bad.material.cells[2_047].2=Fr::one();
                        "c498b oracle cell ordinal 2047".into()},
                    2=>{bad.material.reads.swap(0,1);"c498b oracle read ordinal 0".into()},
                    3=>{bad.material.reads[225].2+=Fr::one();
                        "c498b oracle read ordinal 225".into()},
                    4=>{bad.material.reads[290].1=ScoreRelationReadAuthor::WorkUpper {
                        owner:owner.fixture.work.owner-1,height:owner.fixture.work.height};
                        "c498b oracle read ordinal 290".into()},
                    _=>unreachable!(),
                };
                assert_eq!(c498_check_h21_relation(&bad,&owner.fixture,context).unwrap_err(),expected);
                owner.with_relation(|relation,binding,pair| {
                    c498_borrow_probe::Probe::new(relation,binding,pair,context)?
                        .check(&owner.fixture,context,&owner.map_pair)
                })?;
            }
        }
        Ok(())
    }

    #[test]
    fn c498c_production_comparator_same_row_work_swap_rejects_and_recovers()->Result<(),String> {
        let root=[7;32]; let total=[8;28]; let profile=c498_h21_profile();
        for (context,lease) in crate::h21_scheduled_max_cap::c498_clipped_score_leases_for_h21_parent(
            root,total,profile)?.into_iter().enumerate() {
            let owner=C498H21FixtureOwner::new(lease,root,total,profile,
                H21EligibleMapStage::source_maps()?)?;
            let mut bad=fixture_relation(&owner.fixture,&owner.identity);
            let first_work=8_545-448;
            assert_eq!(bad.material.terms[context][first_work].row,
                bad.material.terms[context][first_work+1].row);
            assert_ne!(bad.material.terms[context][first_work],
                bad.material.terms[context][first_work+1]);
            bad.material.terms[context].swap(first_work,first_work+1);
            assert_eq!(crate::packed_owner_assembly::C498ClippedScoreSource::new(
                &bad,&owner.binding,&owner.map_pair,context).err(),
                Some(format!("C498 term ordinal {first_work}")));
            owner.with_relation(|relation,binding,pair| {
                crate::packed_owner_assembly::C498ClippedScoreSource::new(
                    relation,binding,pair,context).map(|_|())
            })?;
        }
        Ok(())
    }

    #[test]
    fn c498c_production_comparator_isolated_source_faults()->Result<(),String> {
        let root=[7;32]; let total=[8;28]; let profile=c498_h21_profile();
        for (context,lease) in crate::h21_scheduled_max_cap::c498_clipped_score_leases_for_h21_parent(
            root,total,profile)?.into_iter().enumerate() {
            let owner=C498H21FixtureOwner::new(lease,root,total,profile,
                H21EligibleMapStage::source_maps()?)?;
            for fault in 0..21 {
                let mut bad=fixture_relation(&owner.fixture,&owner.identity);
                match fault {
                    0=>{bad.material.cells.remove(0);},
                    1=>{bad.material.cells.pop();},
                    2=>{bad.material.cells.remove(1_994);},
                    3=>bad.material.cells.swap(0,1),
                    4=>bad.material.cells[0].1.previous_owner-=1,
                    5=>bad.material.cells[0].1.max_owner-=1,
                    6=>bad.material.cells[0].1.cap_owner-=1,
                    7=>bad.material.cells[0].1.origin-=1,
                    8=>bad.material.cells[0].1.context=1-context,
                    9=>bad.material.cells[2_047].2=Fr::one(),
                    10=>{bad.material.terms[context].remove(0);},
                    11=>bad.material.terms[context].swap(0,1),
                    12=>bad.material.terms[context][0].gate.c0+=Fr::one(),
                    13=>{bad.material.reads.remove(0);},
                    14=>bad.material.reads.swap(0,1),
                    15=>bad.material.reads[0].2+=Fr::one(),
                    16=>bad.material.reads[225].2+=Fr::one(),
                    17=>bad.material.reads[290].2+=Fr::one(),
                    18=>bad.material.reads[0].1=ScoreRelationReadAuthor::PreviousR {
                        context,owner:1_810_000},
                    19=>bad.material.reads[225].1=ScoreRelationReadAuthor::Cap {
                        context,origin:bad.owner()+1,max_owner:1_809_000,cap_owner:bad.owner()},
                    20=>bad.material.reads[290].1=ScoreRelationReadAuthor::WorkUpper {
                        owner:bad.owner()-2,height:bad.owner()+1},
                    _=>unreachable!(),
                }
                assert!(crate::packed_owner_assembly::C498ClippedScoreSource::new(
                    &bad,&owner.binding,&owner.map_pair,context).is_err(),"source fault {fault}");
                owner.with_relation(|relation,binding,pair| {
                    crate::packed_owner_assembly::C498ClippedScoreSource::new(
                        relation,binding,pair,context).map(|_|())
                })?;
            }
            for field in 0..6 {
                owner.with_relation(|relation,binding,pair| {
                    assert!(crate::packed_owner_assembly::C498ClippedScoreSource::new(
                        relation,&binding.mutated_field_for_test(field),pair,context).is_err());
                    Ok(())
                })?;
            }
            owner.with_relation(|relation,binding,pair| {
                for context in [1-context,2] {
                    assert!(crate::packed_owner_assembly::C498ClippedScoreSource::new(
                        relation,binding,pair,context).is_err());
                }
                Ok(())
            })?;
            let mut identity=owner.identity.clone();
            identity.map_bindings.swap(0,1);
            assert!(crate::packed_owner_assembly::C498ClippedScoreSource::new(
                &fixture_relation(&owner.fixture,&identity),&owner.binding,&owner.map_pair,context).is_err());
        }
        Ok(())
    }

    #[test]
    fn c498c_physical_capture_isolated_faults_and_fresh_recovery()->Result<(),String> {
        let root=[7;32]; let total=[8;28]; let profile=c498_h21_profile();
        for (context,lease) in crate::h21_scheduled_max_cap::c498_clipped_score_leases_for_h21_parent(
            root,total,profile)?.into_iter().enumerate() {
            let owner=C498H21FixtureOwner::new(lease,root,total,profile,
                H21EligibleMapStage::source_maps()?)?;
            owner.with_relation(|relation,binding,pair| {
                crate::packed_owner_assembly::c498_physical_fixture(
                    relation,binding,pair,context)
            })?;
        }
        Ok(())
    }

    fn relation_map_slack_fixture(owner:usize,maps:&[Map;2])
        ->super::super::super::h21_eligible_slack::H21EligibleSlackStage {
        use super::super::super::h21_eligible_slack::{H21EligibleSlackStage,SlackLease};
        let descriptor=H21EligibleMapStage::descriptor();
        let mut map_stage=synthetic_stage(owner,maps);
        for c in 0..2 {
            map_stage.claim_map_live(c,&vec![false;BANK53_MAP_LIVE_BITS]).unwrap();
            map_stage.map_terms[c]=crate::bank53_map::map_owner_terms_for_descriptor(
                &maps[c],owner as u64,c,descriptor).unwrap();
        }
        let mut stage=H21EligibleSlackStage::new(map_stage);
        for c in 0..2 {
            let generated=crate::legacy_envelope_map::OwnerRow {
                owner:owner as u64,binding:maps[c].binding(),
                bits:vec![false;crate::legacy_envelope_map::BANK],
            };
            SlackLease::from_generated(&stage.map_stage,c,&generated).unwrap()
                .admit_into(&mut stage).unwrap();
        }
        stage
    }

    // This constructor is confined to the Score module's unit tests. The
    // public source lease remains sealed and terminal-gated in production.
    fn fixture_relation<'a>(fixture:&'a RelationFixture,identity:&'a H21EligibleMapStage)
        ->H21ClosedScoreOwnerRelation<'a> {
        H21ClosedScoreOwnerRelation {record:&fixture.record,identity,
            material:fixture.material().unwrap()}
    }

    // Conditional metadata fixture for the ordinary recipe seam. The legacy
    // synthetic lease labels MAX at first_origin-1090; regular class MAX is
    // independently fixed below. Only those metadata labels are adapted.
    // This does not validate native MAX provenance, a full join, or a proof.
    fn canonical_class_metadata_fixture<'a>(fixture:&'a RelationFixture,
        identity:&'a H21EligibleMapStage)->H21ClosedScoreOwnerRelation<'a> {
        let maximum=match fixture.record.owner {
            846_015=>844_926,
            1_810_879=>1_809_790,
            _=>panic!("conditional class metadata fixture owner"),
        };
        let mut relation=fixture_relation(fixture,identity);
        let before_authors=relation.material.authors;
        let before_reads=relation.material.reads.clone();
        let before_terms=relation.material.terms.clone();
        let before_cells=relation.material.cells.clone();
        let mut author_changes=0;
        for author in relation.material.authors.iter_mut().flatten() {
            assert_ne!(author.max_owner,maximum);
            author.max_owner=maximum;
            author_changes+=1;
        }
        let mut read_changes=0;
        for (_,author,_) in &mut relation.material.reads {
            if let ScoreRelationReadAuthor::Cap {max_owner,..}=author {
                assert_ne!(*max_owner,maximum);
                *max_owner=maximum;
                read_changes+=1;
            }
        }
        assert_eq!(author_changes,before_authors.iter().flatten().count());
        assert_eq!(read_changes,65*author_changes);
        for context in 0..2 {
            let expected=before_authors[context].map(|mut author| {
                author.max_owner=maximum;author
            });
            assert_eq!(relation.material.authors[context],expected);
        }
        for (after,before) in relation.material.reads.iter().zip(&before_reads) {
            let mut expected=*before;
            if let ScoreRelationReadAuthor::Cap {max_owner,..}=&mut expected.1 {
                *max_owner=maximum;
            }
            assert_eq!(*after,expected);
        }
        assert_eq!(relation.material.reads.len(),before_reads.len());
        assert_eq!(relation.material.terms,before_terms);
        assert_eq!(relation.material.cells,before_cells);
        assert!(std::ptr::eq(relation.record,&fixture.record));
        assert!(std::ptr::eq(relation.identity,identity));
        relation
    }

    #[test]
    fn c567_ordinary_consumer_borrowed_relation_second_regular_and_sampled_tail() {
        let maps=synthetic_maps();
        for (owner,first,active) in [(846_015,845_889,[true,true]),
            (1_810_879,1_810_753,[true,false])] {
            let fixture=RelationFixture::new(first,owner+1,active);
            let identity=synthetic_stage(owner,&maps);
            let relation=canonical_class_metadata_fixture(&fixture,&identity);
            let plan=super::super::scored_owner_source::regular_score_equation_plan(
                owner,&relation).unwrap();
            assert_eq!(plan.owner(),owner);
            assert_eq!(plan.active(),active);
            assert_eq!(relation.reads().len(),514*active.iter().filter(|a|**a).count());
            assert_eq!(relation.terms(1).unwrap().is_empty(),!active[1]);
        }
    }

    #[test]
    fn c567_ordinary_consumer_real_relation_isolated_equation_and_read_faults() {
        let maps=synthetic_maps();
        for (owner,first,active) in [(846_015,845_889,[true,true]),
            (1_810_879,1_810_753,[true,false])] {
            let fixture=RelationFixture::new(first,owner+1,active);
            let identity=synthetic_stage(owner,&maps);
            let pristine=canonical_class_metadata_fixture(&fixture,&identity);
            for context in 0..2 {
                if !active[context] {continue;}
                for fault in 0..8 {
                    let mut bad=canonical_class_metadata_fixture(&fixture,&identity);
                    let read=context*514;
                    match fault {
                        0=>bad.material.terms[context][0].gate.c1+=Fr::one(),
                        1=>bad.material.terms[context][0].row+=1,
                        2=>bad.material.reads[read].0+=1,
                        3=>bad.material.reads[read+225].0+=1,
                        4=>bad.material.reads[read+290].0+=1,
                        5=>match &mut bad.material.reads[read].1 {
                            ScoreRelationReadAuthor::PreviousR {owner,..}=>*owner+=1,
                            _=>panic!("PreviousR fixture ordinal"),
                        },
                        6=>match &mut bad.material.reads[read+225].1 {
                            ScoreRelationReadAuthor::Cap {max_owner,..}=>*max_owner+=1,
                            _=>panic!("Cap fixture ordinal"),
                        },
                        _=>match &mut bad.material.reads[read+290].1 {
                            ScoreRelationReadAuthor::WorkUpper {height,..}=>*height+=1,
                            _=>panic!("WorkUpper fixture ordinal"),
                        },
                    }
                    let error=super::super::scored_owner_source::regular_score_equation_plan(
                        owner,&bad).unwrap_err();
                    if fault<2 {
                        let term=&pristine.material.terms[context][0];
                        assert_eq!(error,format!("Score class source equation owner {owner} context {context} ordinal 0 row {} left {} right {}",
                            term.row,term.gate.left,term.gate.right));
                    } else {
                        assert_eq!(error,"Score class source read order/operand/multiplicity");
                    }
                    super::super::scored_owner_source::regular_score_equation_plan(
                        owner,&pristine).unwrap();
                }
            }
        }
    }

    #[test]
    fn c567_ordinary_consumer_rejects_clipped_and_wrong_regular_owner() {
        let maps=synthetic_maps();
        for (context,first,last) in [(0,1_810_881,1_810_905),(1,1_810_753,1_810_842)] {
            let fixture=RelationFixture::new(first,last,[context==0,context==1]);
            let identity=synthetic_stage(last-1,&maps);
            let relation=fixture_relation(&fixture,&identity);
            let expected=super::super::Eligible08RegularScoreOwner::classify(last-1).unwrap_err();
            assert_eq!(super::super::scored_owner_source::regular_score_equation_plan(
                last-1,&relation).unwrap_err(),expected);
        }
        let fixture=RelationFixture::new(845_889,846_016,[true,true]);
        let identity=synthetic_stage(846_015,&maps);
        let relation=canonical_class_metadata_fixture(&fixture,&identity);
        assert_eq!(super::super::scored_owner_source::regular_score_equation_plan(
            846_143,&relation).unwrap_err(),"Score class source authors/activity");
    }

    #[test]
    fn c567_clipped_consumer_shared_recipe_both_scheduled_routes() {
        let maps=synthetic_maps();
        for lease in crate::h21_scheduled_max_cap::c498_clipped_score_leases().unwrap() {
            let context=lease.context();
            let fixture=c498_clipped_fixture(lease);
            let owner=fixture.record.owner;
            let identity=synthetic_stage(owner,&maps);
            let relation=fixture_relation(&fixture,&identity);
            let plan=relation.source_equation_plan(owner).unwrap();
            assert_eq!(plan.owner(),[1_810_904,1_810_841][context]);
            assert_eq!(plan.active(),[context==0,context==1]);
            assert_eq!(plan.authors()[context].unwrap().max_owner,
                [1_809_918,1_809_790][context]);
            assert_eq!(relation.reads().len(),514);
            assert!(relation.terms(1-context).unwrap().is_empty());
        }
    }

    #[test]
    fn c567_clipped_consumer_shared_recipe_isolated_equation_and_read_faults() {
        let maps=synthetic_maps();
        for lease in crate::h21_scheduled_max_cap::c498_clipped_score_leases().unwrap() {
            let context=lease.context();
            let fixture=c498_clipped_fixture(lease);
            let owner=fixture.record.owner;
            let identity=synthetic_stage(owner,&maps);
            let pristine=fixture_relation(&fixture,&identity);
            for fault in 0..8 {
                let mut bad=fixture_relation(&fixture,&identity);
                match fault {
                    0=>bad.material.terms[context][0].gate.c1+=Fr::one(),
                    1=>bad.material.terms[context][0].row+=1,
                    2=>bad.material.reads[0].0+=1,
                    3=>bad.material.reads[225].0+=1,
                    4=>bad.material.reads[290].0+=1,
                    5=>match &mut bad.material.reads[0].1 {
                        ScoreRelationReadAuthor::PreviousR {owner,..}=>*owner+=1,
                        _=>panic!("clipped PreviousR fixture ordinal"),
                    },
                    6=>match &mut bad.material.reads[225].1 {
                        ScoreRelationReadAuthor::Cap {max_owner,..}=>*max_owner+=1,
                        _=>panic!("clipped Cap fixture ordinal"),
                    },
                    _=>match &mut bad.material.reads[290].1 {
                        ScoreRelationReadAuthor::WorkUpper {height,..}=>*height+=1,
                        _=>panic!("clipped WorkUpper fixture ordinal"),
                    },
                }
                let error=bad.source_equation_plan(owner).unwrap_err();
                if fault<2 {
                    let term=&pristine.material.terms[context][0];
                    assert_eq!(error,format!("Score class source equation owner {owner} context {context} ordinal 0 row {} left {} right {}",
                        term.row,term.gate.left,term.gate.right));
                } else {
                    assert_eq!(error,"Score class source read order/operand/multiplicity");
                }
                pristine.source_equation_plan(owner).unwrap();
            }
        }
    }

    fn admit_c515c_structural_stage(
        stage: super::super::super::h21_eligible_slack::H21EligibleSlackStage,
        relation: Option<H21ClosedScoreOwnerRelation<'_>>,
        maps: &[Map; 2],
    ) -> Result<(super::super::super::h21_eligible_slack::H21EligibleSlackStage,
        [bool; 2]), String> {
        let owner = stage.map_stage.owner;
        let class = stage.map_stage.class;
        let root = stage.map_stage.parent_root;
        let total = stage.map_stage.parent_total;
        let profile = stage.map_stage.parent_profile;
        let cut = stage.map_stage.cut_identity.clone();
        let bindings = [maps[0].binding(), maps[1].binding()];
        admit_closed_owner_score_stage(stage, relation, owner, class, root, total,
            profile, &cut, [&bindings[0], &bindings[1]])
    }

    #[test]
    fn c515c_structural_only_relation_owner_and_status_join() {
        // These synthetic relations exercise tuple/Map/Slack stage structure
        // only. They do not call terminal_r or authenticate a complete stream.
        let maps = synthetic_maps();

        let first_identity = synthetic_stage(FIRST_MODERN_OWNER, &maps);
        let anchors = synthetic_anchors(&maps);
        let cap = Eligible08NativeSnapshot::first_modern_constant_d_for_test(
            first_identity.parent_root, first_identity.parent_total,
            first_identity.parent_profile, 16).unwrap();
        let w = BigUint::from(845_759u64);
        let original: [AnchorRecord; 2] = std::array::from_fn(|c|
            modern_score_material(&first_identity, H21EligibleMapStage::descriptor(),
                c, w.clone(), &cap, &anchors).unwrap());
        let leases: [ScoreEndpointLease; 2] = std::array::from_fn(|c|
            ScoreEndpointLease::synthetic_for_test(c, 845_760, 845_760, 32u8.into()));
        let record = ScoreEndpointRecord { owner: FIRST_MODERN_OWNER,
            roles: std::array::from_fn(|c| Some(ScoreEndpointRole {
                lease_index: 0, previous_owner: ANCHOR_OWNERS[1],
                bits: pack_score(&original[c].bits.iter()
                    .map(|&bit| Fr::from(bit as u64)).collect::<Vec<_>>()).unwrap(),
            })) };
        let previous = std::array::from_fn(|c| Some(ScorePreviousInput {
            context: c, owner: ANCHOR_OWNERS[1], r: anchors.second_r[c].value.clone(),
        }));
        let material = score_relation_material(H21EligibleMapStage::descriptor(), &record,
            [Some(&leases[0]), Some(&leases[1])], previous,
            ScoreWorkInput { owner: FIRST_MODERN_OWNER - 1, height: 845_760, w }).unwrap();
        let first_relation = H21ClosedScoreOwnerRelation {
            record: &record, identity: &first_identity, material,
        };
        let first_base = relation_map_slack_fixture(FIRST_MODERN_OWNER, &maps);
        let first_map_rows = first_base.map_stage.map_terms.clone();
        let first_slack_cells = first_base.slack_cells().clone();
        let first_slack_rows = first_base.slack_rows().clone();
        let first_score_rows = [first_relation.terms(0).unwrap().to_vec(),
            first_relation.terms(1).unwrap().to_vec()];
        let (first_stage, first_active) = admit_c515c_structural_stage(
            first_base, Some(first_relation), &maps).unwrap();
        assert_eq!(first_active, [true, true]);
        assert_eq!(first_stage.map_stage.map_terms, first_map_rows);
        assert_eq!(first_stage.slack_cells(), &first_slack_cells);
        assert_eq!(first_stage.slack_rows(), &first_slack_rows);
        assert_eq!(first_stage.score_rows(), &first_score_rows);
        assert_eq!(first_stage.score_cells().len(), 2 * score::INPUT);

        let regular = RelationFixture::new(845_761, 845_888, [true, true]);
        let regular_identity = synthetic_stage(regular.record.owner, &maps);
        let (regular_stage, regular_active) = admit_c515c_structural_stage(
            relation_map_slack_fixture(regular.record.owner, &maps),
            Some(fixture_relation(&regular, &regular_identity)), &maps).unwrap();
        assert_eq!(regular_active, [true, true]);
        assert_eq!(regular_stage.score_cells().len(), 2 * score::INPUT);

        // The reviewed terminal tail is context0-only at owner1810879;
        // context1-only would be a false structural fixture for this source.
        let tail = RelationFixture::new(845_761, 1_810_880, [true, false]);
        let tail_identity = synthetic_stage(tail.record.owner, &maps);
        let (tail_stage, tail_active) = admit_c515c_structural_stage(
            relation_map_slack_fixture(tail.record.owner, &maps),
            Some(fixture_relation(&tail, &tail_identity)), &maps).unwrap();
        assert_eq!(tail_active, [true, false]);
        assert_eq!(tail_stage.score_cells().len(), score::INPUT);

        let absent_owner = tail.record.owner + 1;
        let (absent_stage, absent_active) = admit_c515c_structural_stage(
            relation_map_slack_fixture(absent_owner, &maps), None, &maps).unwrap();
        assert_eq!(absent_active, [false, false]);
        assert!(absent_stage.score_cells().is_empty());
        assert!(absent_stage.score_rows().iter().all(Vec::is_empty));

        // Mutations are isolated against the same production admission helper.
        let owner = regular.record.owner;
        let base = || relation_map_slack_fixture(owner, &maps);
        let mut wrong_parent = regular_identity.clone();
        wrong_parent.parent_root[0] ^= 1;
        let relation = H21ClosedScoreOwnerRelation { record: &regular.record,
            identity: &wrong_parent, material: regular.material().unwrap() };
        assert!(admit_c515c_structural_stage(base(), Some(relation), &maps).is_err());

        let mut wrong_map = regular_identity.clone();
        wrong_map.map_bindings.swap(0, 1);
        let relation = H21ClosedScoreOwnerRelation { record: &regular.record,
            identity: &wrong_map, material: regular.material().unwrap() };
        assert!(admit_c515c_structural_stage(base(), Some(relation), &maps).is_err());

        let mut missing_context = regular.material().unwrap();
        missing_context.authors = [None, None];
        missing_context.terms = [Vec::new(), Vec::new()];
        let inactive_relation = H21ClosedScoreOwnerRelation {
            record: &regular.record, identity: &regular_identity,
            material: missing_context,
        };
        assert!(admit_c515c_structural_stage(
            base(), Some(inactive_relation), &maps).is_err());

        let mut wrong_context = regular.material().unwrap();
        wrong_context.cells[0].1.context = 2;
        let context_relation = H21ClosedScoreOwnerRelation {
            record: &regular.record, identity: &regular_identity,
            material: wrong_context,
        };
        assert!(admit_c515c_structural_stage(
            base(), Some(context_relation), &maps).err().unwrap()
            .contains("source tuple context/author"));

        let mut bad_tuple = regular.material().unwrap();
        bad_tuple.cells[1].0 = bad_tuple.cells[0].0;
        let tuple_relation = H21ClosedScoreOwnerRelation { record: &regular.record,
            identity: &regular_identity, material: bad_tuple };
        assert!(admit_c515c_structural_stage(
            base(), Some(tuple_relation), &maps).is_err());
    }

    struct C488FixtureOwner {
        fixture: RelationFixture,
        identity: H21EligibleMapStage,
        maps: [Map; 2],
    }
    impl C488FixtureOwner {
        fn new()->Self {
            let maps=synthetic_maps();
            let identity=synthetic_stage(845_887,&maps);
            Self {fixture:RelationFixture::c488(),identity,maps}
        }
        fn relation(&self)->H21ClosedScoreOwnerRelation<'_> {
            fixture_relation(&self.fixture,&self.identity)}
    }

    #[test]
    fn c488_synthetic_score_import_seam()->Result<(),String> {
        let owner=C488FixtureOwner::new();
        h21_score_import_seam::run_fixture(owner.relation())
    }

    #[test]
    fn c492_partial_adapter_signature_typechecks() {
        fn accepts_source_borrowed_partial(
            view: &crate::packed_owner_assembly::ScoredOwnerPackingView,
            expected: &crate::packed_owner_assembly::HeaderSourceBinding,
        ) -> Result<(), String> {
            view.stage_partial_score_slack(expected).map(|_| ())
        }
        let _ = accepts_source_borrowed_partial as fn(
            &crate::packed_owner_assembly::ScoredOwnerPackingView,
            &crate::packed_owner_assembly::HeaderSourceBinding,
        ) -> Result<(), String>;
    }

    #[test]
    fn c492_source_bound_partial_score_slack_regular845887()->Result<(),String> {
        c492_partial_score_slack_with_maps(synthetic_maps())
    }

    #[test]
    fn c495_fold_derived_alternate_exponents_replay_partial_score_slack()->Result<(),String> {
        let mut maps=Vec::new();
        for cut in H21EligibleMapStage::descriptor().terminals() {
            let folded=fold_cut_with(cut as u64,|source|Ok(match source {
                CandidateSource::HeaderDifficulty {height:1_820_100,..} =>
                    BigUint::from(1u8)<<55,
                CandidateSource::HeaderDifficulty {height:417_792|417_793,..} =>
                    BigUint::from(global_u_roster::RESET_CHILD_417792),
                _=>BigUint::from(global_u_roster::INITIAL_I),
            }))?;
            maps.push(map_for_fold(cut as u64,&folded)?.0);
        }
        let maps:[Map;2]=maps.try_into().map_err(|_|"C495 folded Map census")?;
        assert_eq!(maps.each_ref().map(|map|map.binding().e),[56,48]);
        // These scheduled candidate values exercise the production fold/Map
        // derivation, then only the structural writer core, never native custody.
        c492_partial_score_slack_with_maps(maps)
    }

    fn c492_partial_score_slack_with_maps(maps:[Map;2])->Result<(),String> {
        use crate::packed_owner_assembly::HeaderSourceBinding;
        use crate::packed_owner_assembly::h21_eligible_context::{ScoredOwnerPackedAuthor,
            ScoredOwnerPackedCell};
        use crate::packed_owner_assembly::h21_eligible_context::scored_owner_source::OpenScoredReadAuthor;

        const OWNER:usize=845_887;
        const PREVIOUS:usize=845_759;
        const MAX:usize=844_798;
        let owner=C488FixtureOwner {fixture:RelationFixture::c488(),
            identity:synthetic_stage(OWNER,&maps),maps};
        let mut stage=relation_map_slack_fixture(OWNER,&owner.maps);
        stage.admit_score_relation(owner.relation())?;
        let map=&stage.map_stage;
        let expected_maps=[owner.maps[0].binding(),owner.maps[1].binding()];
        let expected=HeaderSourceBinding::from_sink_for_test(map.parent_root,
            map.parent_total,map.parent_profile,map.cut_identity.clone(),OWNER);

        let mut packed=Vec::new();
        for (&local,&(author,value)) in stage.score_cells() {
            packed.push(ScoredOwnerPackedCell::synthetic_for_test(
                OWNER*(1<<20)+local,ScoredOwnerPackedAuthor::Score(author),value.is_one()));
        }
        for (&local,&(author,value)) in stage.slack_cells() {
            let crate::packed_owner_assembly::H21StageAuthor::Slack(context)=author else {
                return Err("C492 test Slack stage author".into());
            };
            packed.push(ScoredOwnerPackedCell::synthetic_for_test(
                OWNER*(1<<20)+local,ScoredOwnerPackedAuthor::Slack(context),value));
        }

        let mut selected=Vec::new();
        for (context,map_source) in owner.maps.iter().enumerate() {
            for import in map_source.imports(OWNER as u64)? {
                for bit in 0..import.width {
                    selected.push(crate::packed_owner_assembly::h21_eligible_context::OpenScoredRead {
                        wire:map_source.input_index(import,bit)?,
                        author:OpenScoredReadAuthor::Map {context,import,bit},
                        value:Fr::zero(),
                    });
                }
            }
        }
        for &(wire,author,value) in stage.score_imports() {
            let author=match author {
                ScoreRelationReadAuthor::PreviousR {context,owner} =>
                    OpenScoredReadAuthor::PreviousR {context,owner},
                ScoreRelationReadAuthor::WorkUpper {owner,height} =>
                    OpenScoredReadAuthor::WorkUpper {owner,height},
                ScoreRelationReadAuthor::Cap {context,origin,..} => {
                    packed.push(ScoredOwnerPackedCell::synthetic_for_test(wire,
                        ScoredOwnerPackedAuthor::Cap {context,origin},value.is_one()));
                    continue;
                },
            };
            selected.push(crate::packed_owner_assembly::h21_eligible_context::OpenScoredRead {wire,author,value});
        }
        for context in 0..2 {
            for bit in 0..224 {
                selected.push(crate::packed_owner_assembly::h21_eligible_context::OpenScoredRead {
                    wire:MAX*(1<<20)+[999_424,1_000_097][context]+bit,
                    author:OpenScoredReadAuthor::Max {context,end:MAX+2},value:Fr::zero(),
                });
            }
        }

        let result=crate::packed_owner_assembly::ScoredOwnerPackingView::
            admit_structural_fixture_for_test(&stage,&expected,&expected_maps,&packed,&selected,0)?;
        assert_eq!(result.terms,17_864);
        assert_eq!(result.row_leases,7_516);
        assert_eq!(result.assignments,4_870);
        assert_eq!(result.reservations,4_870);
        assert_eq!(result.score_reads,1_028);
        assert_eq!(result.negative_cases,26);
        assert!(!selected.is_empty());
        assert_eq!(result.selected_reads,selected.len());
        assert_eq!(result.retained_header_daa_active_operands,0);
        assert_eq!(stage.map_stage.owner,OWNER);
        assert_eq!(owner.fixture.work.owner,OWNER-1);
        assert_eq!(owner.fixture.work.height,OWNER+1);
        assert_eq!(owner.fixture.previous.iter().flatten().map(|r|r.owner).collect::<BTreeSet<_>>(),
            [PREVIOUS].into_iter().collect());

        let mut identity_negatives=0usize;
        for field in 0..5 {
            let wrong=match field {
                0=>HeaderSourceBinding::from_sink_for_test([0xff;32],map.parent_total,
                    map.parent_profile,map.cut_identity.clone(),OWNER),
                1=>HeaderSourceBinding::from_sink_for_test(map.parent_root,[0xff;28],
                    map.parent_profile,map.cut_identity.clone(),OWNER),
                2=>HeaderSourceBinding::from_sink_for_test(map.parent_root,map.parent_total,
                    [0xff;32],map.cut_identity.clone(),OWNER),
                3=>HeaderSourceBinding::from_sink_for_test(map.parent_root,map.parent_total,
                    map.parent_profile,vec![0xff],OWNER),
                4=>HeaderSourceBinding::from_sink_for_test(map.parent_root,map.parent_total,
                    map.parent_profile,map.cut_identity.clone(),OWNER+1),
                _=>unreachable!(),
            };
            let before=stage.clone();
            let rejected=crate::packed_owner_assembly::ScoredOwnerPackingView::
                admit_structural_fixture_for_test(&stage,&wrong,&expected_maps,&packed,&selected,0);
            assert!(crate::packed_owner_assembly::ScoredOwnerPackingView::
                is_expected_fixture_rejection_for_test(&rejected),
                "C492 identity negative {field} must be a source rejection, not an invariant failure");
            assert!(stage==before,"C492 isolated identity negative {field} mutated fixture source");
            identity_negatives+=1;
        }
        let mut wrong_maps=expected_maps.clone();
        wrong_maps[0]=Map::new_modern_global_u(expected_maps[0].n,expected_maps[0].h,
            expected_maps[0].e)?.binding();
        assert_eq!(wrong_maps[0].n,expected_maps[0].n);
        assert_eq!(wrong_maps[0].h,expected_maps[0].h);
        assert_eq!(wrong_maps[0].e,expected_maps[0].e);
        assert_eq!(wrong_maps[0].parent_root,expected_maps[0].parent_root);
        assert_ne!(wrong_maps[0],expected_maps[0],"C492 Map mode must differ");
        let before=stage.clone();
        let rejected=crate::packed_owner_assembly::ScoredOwnerPackingView::
            admit_structural_fixture_for_test(&stage,&expected,&wrong_maps,&packed,&selected,0);
        assert!(crate::packed_owner_assembly::ScoredOwnerPackingView::
            is_expected_fixture_rejection_for_test(&rejected),
            "C492 full Map mutant must be a source rejection, not an invariant failure");
        assert!(stage==before,"C492 wrong full Map binding mutated fixture source");
        identity_negatives+=1;

        let mut wrong_selector=expected_maps.clone();
        wrong_selector[0]=Map::new_modern_global_u_selected_lower(
            expected_maps[0].n,expected_maps[0].h,expected_maps[0].e,
            LowerSelector {source:LowerSource::HeaderDifficulty {height:841_730},
                branch:LowerBranch::Pivot(expected_maps[0].e-1)})?.binding();
        assert_eq!(wrong_selector[0].n,expected_maps[0].n);
        assert_eq!(wrong_selector[0].h,expected_maps[0].h);
        assert_eq!(wrong_selector[0].e,expected_maps[0].e);
        assert_eq!(wrong_selector[0].parent_root,expected_maps[0].parent_root);
        assert_ne!(wrong_selector[0],expected_maps[0],"C495 Map selector alone must differ");
        let before=stage.clone();
        let rejected=crate::packed_owner_assembly::ScoredOwnerPackingView::
            admit_structural_fixture_for_test(&stage,&expected,&wrong_selector,&packed,&selected,0);
        assert!(crate::packed_owner_assembly::ScoredOwnerPackingView::
            is_expected_fixture_rejection_for_test(&rejected),
            "C495 selector-only mutant must be a source rejection, not an invariant failure");
        assert!(stage==before,"C495 selector-only rejection mutated fixture source");
        identity_negatives+=1;

        let descriptor=H21EligibleMapStage::descriptor();
        let clipped_owner=descriptor.guards()[1]-1;
        let mut clipped=stage.clone();
        clipped.map_stage.owner=clipped_owner;
        let clipped_binding=HeaderSourceBinding::from_sink_for_test(map.parent_root,
            map.parent_total,map.parent_profile,map.cut_identity.clone(),clipped_owner);
        let before=clipped.clone();
        let rejected=crate::packed_owner_assembly::ScoredOwnerPackingView::
            admit_structural_fixture_for_test(&clipped,&clipped_binding,&expected_maps,&packed,&selected,0);
        assert!(crate::packed_owner_assembly::ScoredOwnerPackingView::
            is_expected_fixture_rejection_for_test(&rejected),
            "C492 clipped owner must be a source rejection, not an invariant failure");
        assert!(clipped==before,"C492 clipped regular-owner rejection mutated source");
        identity_negatives+=1;
        assert_eq!(identity_negatives,8);
        assert_eq!(result.negative_cases+identity_negatives,34);
        Ok(())
    }

    #[test]
    fn c489_scheduled_score_and_map_slack_selected_join()->Result<(),String> {
        let owner=C488FixtureOwner::new();
        h21_score_import_seam::run_c489_fixture(
            || owner.relation(),
            || relation_map_slack_fixture(845_887,&owner.maps))?;
        for field in 0..3 {
            let error=h21_score_import_seam::run_c489_fixture(
                || owner.relation(),
                || {
                    let mut stage=relation_map_slack_fixture(845_887,&owner.maps);
                    if field==0 {stage.map_stage.parent_root[0]^=1;}
                    else if field==1 {stage.map_stage.cut_identity[0]^=1;}
                    else {stage.map_stage.map_bindings[0].e^=1;}
                    stage
                }).err().unwrap_or_default();
            let expected=if field==2 {"c489 Score/Map/Slack parent/cut/owner"}
                else {"Eligible08 Score relation parent/cut/owner/duplicate"};
            if error!=expected {
                return Err(format!("c489 source parent/cut/binding mutant {field}: {error}"));
            }
        }
        Ok(())
    }

    #[test]
    fn c490_selected_score_map_slack_joins_relocated_physical_slice()->Result<(),String> {
        let owner=C488FixtureOwner::new();
        h21_score_import_seam::run_c490_fixture(
            || owner.relation(),
            || relation_map_slack_fixture(845_887,&owner.maps))?;
        for field in 0..3 {
            let error=h21_score_import_seam::run_c490_fixture(
                || owner.relation(),
                || {
                    let mut stage=relation_map_slack_fixture(845_887,&owner.maps);
                    if field==0 {stage.map_stage.parent_root[0]^=1;}
                    else if field==1 {stage.map_stage.cut_identity[0]^=1;}
                    else {stage.map_stage.map_bindings[0].e^=1;}
                    stage
                }).err().unwrap_or_default();
            let expected=if field==2 {"c489 Score/Map/Slack parent/cut/owner"}
                else {"Eligible08 Score relation parent/cut/owner/duplicate"};
            if error!=expected {
                return Err(format!("c490 source parent/cut/binding mutant {field}: {error}"));
            }
        }
        Ok(())
    }

    #[test]
    fn c188_score_map_slack_admission_retains_exact_cells_terms_reads_and_clipped_tails() {
        let maps=synthetic_maps();
        for (first,last,active) in [(845_760,845_760,[true,true]),
            (845_761,845_888,[true,true]),(1_810_881,1_810_905,[true,false]),
            (1_810_753,1_810_842,[false,true])] {
            let fixture=RelationFixture::new(first,last,active);
            let owner=fixture.record.owner;
            let identity=synthetic_stage(owner,&maps);
            let mut stage=relation_map_slack_fixture(owner,&maps);
            let map_before=stage.map_stage.clone();
            assert!(stage.map_stage.map_terms.iter().all(|terms|!terms.is_empty()));
            assert!(stage.map_stage.map_terms.iter().any(|terms| {
                let mut rows=std::collections::BTreeSet::new();
                terms.iter().any(|term|!rows.insert(term.row))
            }),"use real Map polynomials, preserving repeated terms per ROW");
            let material=fixture.material().unwrap();
            let expected_claims:BTreeMap<usize,(ScoreReplayAuthor,Fr)>=material.cells.iter()
                .map(|&(wire,author,value)|(wire-owner*WIDTH,(author,value))).collect();
            let expected_terms=material.terms;
            let expected_reads=material.reads;
            stage.admit_score_relation(fixture_relation(&fixture,&identity)).unwrap();
            assert!(stage.map_stage==map_before,"Score admission must preserve Map state");
            let (claims,terms,reads)=stage.score_snapshot_for_test();
            assert_eq!(claims,expected_claims,"all 2048 bits of each active context");
            assert_eq!(terms,expected_terms,"ordered terms and row multiplicity");
            assert_eq!(reads,expected_reads,"ordered typed physical read obligations");
            let active_count=active.iter().filter(|&&enabled|enabled).count();
            assert_eq!(claims.len(),active_count*score::INPUT);
            assert_eq!(reads.len(),active_count*(225+65+224));
            for c in 0..2 {
                assert_eq!(terms[c].is_empty(),!active[c]);
                assert_eq!(claims.values().filter(|(author,_)|author.context==c).count(),
                    if active[c] {score::INPUT} else {0});
            }
            let before=stage.clone();
            assert_eq!(stage.admit_score_relation(fixture_relation(&fixture,&identity)).unwrap_err(),
                "Eligible08 Score relation parent/cut/owner/duplicate");
            assert!(stage==before,"duplicate admission leaves every destination field unchanged");
        }
    }

    #[test]
    fn c188_score_map_slack_admission_identity_row_and_x_faults_are_atomic() {
        let maps=synthetic_maps();
        let fixture=RelationFixture::new(845_761,845_888,[true,true]);
        let owner=fixture.record.owner;
        let identity=synthetic_stage(owner,&maps);
        let pristine=relation_map_slack_fixture(owner,&maps);
        for field in 0..5 {
            let mut stage=pristine.clone();
            match field {
                0=>stage.map_stage.parent_root[0]^=1,
                1=>stage.map_stage.parent_total[0]^=1,
                2=>stage.map_stage.parent_profile[0]^=1,
                3=>stage.map_stage.cut_identity.push(1),
                4=>stage.map_stage.owner+=1,
                _=>unreachable!(),
            }
            let before=stage.clone();
            assert_eq!(stage.admit_score_relation(fixture_relation(&fixture,&identity)).unwrap_err(),
                "Eligible08 Score relation parent/cut/owner/duplicate");
            assert!(stage==before,"isolated identity fault {field} must be atomic");
        }
        for c in 0..2 {
            let mut stage=pristine.clone();
            let mut collision=stage.map_stage.map_terms[c][0].clone();
            collision.row=fixture.material().unwrap().terms[c][0].row;
            stage.map_stage.map_terms[c].push(collision);
            let before=stage.clone();
            assert_eq!(stage.admit_score_relation(fixture_relation(&fixture,&identity)).unwrap_err(),
                "Eligible08 Score/Map/Slack ROW writer collision");
            assert!(stage==before,"Map/Score ROW collision must preserve the destination");

            let mut stage=pristine.clone();
            stage.map_stage.claims.insert(SCORE_X[c],(H21StageAuthor::ScoreProbe(c),false));
            let before=stage.clone();
            assert_eq!(stage.admit_score_relation(fixture_relation(&fixture,&identity)).unwrap_err(),
                "Eligible08 Score X author/value/collision");
            assert!(stage==before,"an existing Score X claim must preserve the destination");
        }
    }
}

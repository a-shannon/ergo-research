//! Public-input-only Eligible08 structural relation. This diagnostic roster
//! is distinct from Historical51 and does not certify the final public S.
use super::{anchor_spec, modern_spec, score, ANCHOR_OWNERS, FIRST_MODERN_OWNER,
    SCORE_X, SCORE_ROW, V_ALIAS_ROW, W_ALIAS_ROW, UPPER_LOCAL};
use super::h21_score_class_equations::{ClassEquationPlan, emit_context};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{bank53_map::{self, CutDescriptor}, bank53_slack,
    daa_history_roster::DaaHistoryRoster, gkr::Gate,
    h21_scheduled_max_cap::{Plan as Scheduled, Writer},
    header_scheduled_retirement::Merge,
    legacy_envelope_map::{Map, LowerSelector, LowerSource, LowerBranch},
    sparse::Term, transcript::Transcript, wiring::{self, RightIndex, SourceDelta},
    work_tree_history_plan::WorkTreeHistoryPlan};

const WIDTH: usize = 1 << 20;
const ROWS: usize = 1 << 19;
const SLOTS: usize = 1 << 21;
const N: usize = 1_827_840;
const MAP_ROW: [usize; 2] = [477_074, 492_305];
const SLACK_ROW: [usize; 2] = [491_918, 507_149];
const PROFILE: &[u8] = b"nipopow-h21-eligible08-structural-roster-v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PublicMapParameters {
    pub(crate) terminal: usize,
    pub(crate) exponent: usize,
    pub(crate) lower: LowerSelector,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Family { Header, Max(usize), Cap(usize), Map(usize), Score(usize), Slack(usize) }

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OwnerCensus {
    pub(crate) header: usize,
    pub(crate) max: [usize; 2],
    pub(crate) cap: [usize; 2],
    pub(crate) map: [usize; 2],
    pub(crate) score: [usize; 2],
    pub(crate) slack: [usize; 2],
}

/// No native source, lease, witness bit or producer-selected term enters this
/// owning roster. Its immutable borrows are the public history construction.
pub(crate) struct H21StructuralRoster<'p> {
    parent: &'p WorkTreeHistoryPlan,
    daa: DaaHistoryRoster<'p>,
    scheduled: Scheduled,
    maps: [Map; 2],
    descriptor: Vec<u8>,
}

fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |z, (bit, value)|
        z * if index >> bit & 1 == 1 { *value } else { Fr::one() - value })
}
fn add(out: &mut [Fr; 4], value: [Fr; 4]) {
    for (a, b) in out.iter_mut().zip(value) { *a += b; }
}
fn dimensions(r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<(), String> {
    if (r.len(), u.len(), v.len()) != (40, 41, 41) {
        return Err("H21 structural coefficient dimensions".into());
    }
    Ok(())
}
fn point_fold(term: &Term, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let weight = eq(r, term.row) * eq(u, term.gate.left) * eq(v, term.gate.right);
    [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3].map(|c| weight * c)
}

impl<'p> H21StructuralRoster<'p> {
    pub(crate) fn from_public(parent: &'p WorkTreeHistoryPlan,
        parameters: [PublicMapParameters; 2]) -> Result<Self, String> {
        let (maps, descriptor) = Self::public_parts(parent, parameters)?;
        let daa = DaaHistoryRoster::compile(parent)?;
        let scheduled = Scheduled::eligible08();
        Merge::new(&daa, &scheduled)?;
        Ok(Self { parent, daa, scheduled, maps, descriptor })
    }

    /// Validate and encode the public identity without materializing the DAA
    /// circuits or their local witnesses. The owning context constructs them
    /// once, when it needs the actual relation callbacks.
    pub(crate) fn public_descriptor(parent: &'p WorkTreeHistoryPlan,
        parameters: [PublicMapParameters; 2]) -> Result<Vec<u8>, String> {
        Ok(Self::public_parts(parent, parameters)?.1)
    }

    fn public_parts(parent: &'p WorkTreeHistoryPlan,
        parameters: [PublicMapParameters; 2]) -> Result<([Map; 2], Vec<u8>), String> {
        let cut = CutDescriptor::eligible08();
        if (parent.headers(), parent.slot_log(), parent.slots()) != (N as u64, 21, SLOTS)
            || parameters.iter().enumerate().any(|(c, p)| p.terminal != cut.terminals()[c]) {
            return Err("H21 structural public geometry/cut".into());
        }
        let make = |p: PublicMapParameters| Map::new_modern_global_u_selected_lower(
            p.terminal as u64, 21, p.exponent, p.lower);
        let maps = [make(parameters[0])?, make(parameters[1])?];
        // The serializer attachment removed the old padding anchors on ALL
        // Bank53 wires. Never subtract fictional HEADER anchors here. Also
        // prove that the chosen new envelopes cannot share a retained row.
        for term in &parent.header_boundary().canonical_circuit().terms {
            let g = &term.gate;
            let used = [(!g.c1.is_zero() || !g.c3.is_zero(), g.left),
                (!g.c2.is_zero() || !g.c3.is_zero(), g.right)];
            if used.into_iter().any(|(live, wire)| live && (671_744..688_128).contains(&wire)) {
                return Err("H21 Bank53 has an unexpected retained HEADER consumer".into());
            }
            let row = place_header_row(term.row)?;
            if (475_136..507_536).contains(&row) {
                return Err("H21 structural placement collides with retained HEADER".into());
            }
        }
        let mut descriptor = PROFILE.to_vec();
        descriptor.extend(crate::header_order::MAINNET_GENESIS);
        descriptor.extend(parent.descriptor().root);
        descriptor.extend(parent.work_profile().total_be28);
        descriptor.extend(cut.canonical_identity());
        for n in [N, 21, SLOTS, WIDTH, ROWS, 41, 40, 477_074, 487_421, 491_629,
            491_694, 491_918, 492_305, 502_652, 506_860, 506_925, 507_149,
            507_536, 520_726, 5_757, 2_048, 387, 673, 6_419,
            ANCHOR_OWNERS[0], ANCHOR_OWNERS[1], FIRST_MODERN_OWNER] {
            descriptor.extend((n as u64).to_be_bytes());
        }
        for p in parameters {
            descriptor.extend((p.terminal as u64).to_be_bytes());
            descriptor.extend((p.exponent as u64).to_be_bytes());
            let (tag, value) = match p.lower.source {
                LowerSource::HeaderDifficulty { height } => (0u8, height),
                LowerSource::LegacyBound { q } => (1, q),
                LowerSource::InitialI => (2, 0),
                LowerSource::Reset417792 => (3, 0),
                LowerSource::Reset417793 => (4, 0),
            };
            descriptor.push(tag); descriptor.extend(value.to_be_bytes());
            let (tag, value) = match p.lower.branch {
                LowerBranch::Literal => (0u8, 0), LowerBranch::Equality => (1, 0),
                LowerBranch::Pivot(bit) => (2, bit),
            };
            descriptor.push(tag); descriptor.extend((value as u64).to_be_bytes());
        }
        Ok((maps, descriptor))
    }

    pub(crate) fn daa(&self) -> &DaaHistoryRoster<'p> { &self.daa }
    pub(crate) fn descriptor_bytes(&self) -> &[u8] { &self.descriptor }
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        self.parent.bind(transcript);
        transcript.append_bytes(b"H21-structural-roster", &self.descriptor);
    }

    pub(crate) fn visit_owner_terms(&self, owner: usize,
        mut sink: impl FnMut(Family, Term) -> Result<(), String>) -> Result<OwnerCensus, String> {
        if owner >= SLOTS { return Err("H21 structural owner outside domain".into()); }
        let mut census = OwnerCensus::default();
        let header = Merge::new(&self.daa, &self.scheduled)?.header_terms(owner)?;
        for mut term in header.terms {
            let local = term.row.checked_sub(owner * ROWS).ok_or("H21 HEADER owner")?;
            term.row = owner * ROWS + place_header_row(local)?;
            census.header += 1; sink(Family::Header, term)?;
        }
        self.scheduled.visit_owner(owner, |writer, term| {
            let family = match writer {
                Writer::Max { context, .. } => { census.max[context] += 1; Family::Max(context) },
                Writer::Cap { context, .. } => { census.cap[context] += 1; Family::Cap(context) },
            };
            sink(family, term)
        })?;
        for context in 0..2 {
            for mut term in bank53_map::map_owner_terms_for_descriptor(
                &self.maps[context], owner as u64, context, CutDescriptor::eligible08())? {
                let old = owner * ROWS + 409_600 + context * 32_768;
                let local = term.row.checked_sub(old).filter(|q| *q < 10_347)
                    .ok_or("H21 Map placement outside source envelope")?;
                term.row = owner * ROWS + MAP_ROW[context] + local;
                census.map[context] += 1; sink(Family::Map(context), term)?;
            }
            emit_score_owner(owner, context, &self.maps[context], |term| {
                census.score[context] += 1; sink(Family::Score(context), term)
            })?;
            for mut term in bank53_slack::slack_zero_terms(owner, context)? {
                let old = owner * ROWS + 409_600 + context * 32_768
                    + bank53_slack::SLACK_ROW_OFFSET;
                let local = term.row.checked_sub(old).filter(|q| *q < 387)
                    .ok_or("H21 Slack placement outside source envelope")?;
                term.row = owner * ROWS + SLACK_ROW[context] + local;
                census.slack[context] += 1; sink(Family::Slack(context), term)?;
            }
        }
        Ok(census)
    }

    /// Owner masks use fixed interval/residue kernels. No callback scans the
    /// 2^21-owner witness or enumerates all regular Score members.
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        dimensions(r, u, v)?;
        let mut out = Merge::new(&self.daa, &self.scheduled)?.placed_header_coefficients(r,u,v)?;
        add(&mut out, self.scheduled.coefficients(r,u,v)?);
        for context in 0..2 {
            add(&mut out, self.maps[context].bank53_coefficients_at(context, MAP_ROW[context], r,u,v)?);
            add(&mut out, score_coefficients(context, &self.maps[context], r,u,v)?);
            let owner = wiring::evaluate_shift(&r[19..], &u[20..], &v[20..],
                0, 0, SLOTS as u64, 0, RightIndex::GlobalZero)?;
            for bit in 0..387 {
                out[1] += owner * eq(&r[..19], SLACK_ROW[context] + bit)
                    * eq(&u[..20], 671_744 + context * 8192 + 7805 + bit) * eq(&v[..20], 0);
            }
        }
        Ok(out)
    }
}

fn place_header_row(row: usize) -> Result<usize, String> {
    if row < 393_216 { Ok(row) }
    else if row < 406_406 { Ok(row + 114_320) }
    else { Err("H21 retained HEADER ROW outside canonical envelopes".into()) }
}

fn score_active(owner: usize, context: usize) -> bool {
    ANCHOR_OWNERS.contains(&owner) || owner == FIRST_MODERN_OWNER
        || ClassEquationPlan::for_member(CutDescriptor::eligible08(), owner)
            .is_ok_and(|plan| plan.active()[context])
}

fn emit_score_owner(owner: usize, context: usize, map: &Map,
    mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<(), String> {
    let mut failure = None;
    let mut emit = |term| { if failure.is_none() { failure = sink(term).err(); } };
    if ANCHOR_OWNERS.contains(&owner) {
        // Reuse the exact canonical anchor Spec. Only its public dyadic U is
        // constant; W and (for the second anchor) previous R stay in X.
        let spec = anchor_spec(CutDescriptor::eligible08(), context, owner)?;
        let previous = if owner == ANCHOR_OWNERS[0] { owner } else { ANCHOR_OWNERS[0] };
        score::emit_local(&spec, |local| {
            let mut term = local.term;
            term.row += owner * ROWS + SCORE_ROW[context];
            term.gate.left += (if local.previous { previous } else { owner }) * WIDTH + SCORE_X[context];
            term.gate.right += owner * WIDTH + SCORE_X[context]; emit(term);
        })?;
        for bit in 0..65 {
            emit(Term { row: owner * ROWS + V_ALIAS_ROW[context] + bit,
                gate: Gate { left: owner * WIDTH + SCORE_X[context] + 224 + bit, right: 0,
                    c0: if bit == map.binding().e { -Fr::one() } else { Fr::zero() },
                    c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
        }
        emit_w(owner, context, &mut emit);
    } else if owner == FIRST_MODERN_OWNER {
        let a = super::ScoreReplayAuthor { context, origin: owner + 1,
            previous_owner: ANCHOR_OWNERS[1], max_owner: 844_670, cap_owner: owner };
        emit_context(a, &modern_spec(CutDescriptor::eligible08(), context)?, &mut emit)?;
    } else if let Ok(plan) = ClassEquationPlan::for_member(CutDescriptor::eligible08(), owner) {
        if plan.active()[context] { plan.emit(context, &mut emit)?; }
        else { emit_inactive_score(owner, context, &mut emit); }
    } else { emit_inactive_score(owner, context, &mut emit); }
    failure.map_or(Ok(()), Err)
}

fn emit_inactive_score(owner: usize, context: usize, mut sink: impl FnMut(Term)) {
    for bit in 0..2048 {
        sink(Term { row: owner * ROWS + SCORE_ROW[context] + bit,
            gate: Gate { left: owner * WIDTH + SCORE_X[context] + bit, right: 0,
                c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
    }
}
fn emit_w(owner: usize, context: usize, mut sink: impl FnMut(Term)) {
    for bit in 0..224 {
        let row = owner * ROWS + W_ALIAS_ROW[context] + bit;
        for (left, coefficient) in [(owner * WIDTH + SCORE_X[context] + bit, Fr::one()),
            ((owner - 1) * WIDTH + UPPER_LOCAL + bit, -Fr::one())] {
            sink(Term { row, gate: Gate { left, right: 0, c0: Fr::zero(),
                c1: coefficient, c2: Fr::zero(), c3: Fr::zero() } });
        }
    }
}

#[derive(Clone, Copy)]
struct ScoreWeights { same: Fr, previous: Fr, global_self: Fr, global_work: Fr }
fn modern_weights(context: usize, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<ScoreWeights, String> {
    let cut = CutDescriptor::eligible08(); let clipped = cut.guards()[context] - 1;
    let first = cut.modern_start() + 128 - 1;
    let regular = |delta, right| wiring::evaluate_residue_shift(r,u,v,delta,
        first as u64, clipped as u64, 7, (first % 128) as u64, right);
    let exact = |o, source, right| eq(r,o) * eq(u,source)
        * eq(v, if right { o } else { 0 });
    let previous = ClassEquationPlan::for_member(cut, clipped)?.authors()[context]
        .ok_or("H21 clipped Score author")?.previous_owner;
    Ok(ScoreWeights {
        same: regular(SourceDelta::Sub(0), RightIndex::SameRow)?
            + exact(clipped,clipped,true) + exact(FIRST_MODERN_OWNER,FIRST_MODERN_OWNER,true),
        previous: regular(SourceDelta::Sub(128), RightIndex::SameRow)?
            + exact(clipped,previous,true) + exact(FIRST_MODERN_OWNER,ANCHOR_OWNERS[1],true),
        global_self: regular(SourceDelta::Sub(0), RightIndex::GlobalZero)?
            + exact(clipped,clipped,false) + exact(FIRST_MODERN_OWNER,FIRST_MODERN_OWNER,false),
        global_work: regular(SourceDelta::Sub(1), RightIndex::GlobalZero)?
            + exact(clipped,clipped-1,false) + exact(FIRST_MODERN_OWNER,FIRST_MODERN_OWNER-1,false),
    })
}

fn score_coefficients(context: usize, map: &Map, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
    let weights = modern_weights(context, &r[19..], &u[20..], &v[20..])?;
    let mut out = [Fr::zero(); 4];
    score::emit_local(&modern_spec(CutDescriptor::eligible08(), context)?, |local| {
        let g = local.term.gate;
        let weight = if local.previous { weights.previous } else { weights.same }
            * eq(&r[..19], SCORE_ROW[context] + local.term.row)
            * eq(&u[..20], SCORE_X[context] + g.left) * eq(&v[..20], SCORE_X[context] + g.right);
        for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]) { *sum += weight*c; }
    })?;
    for bit in 0..65 {
        let weight = weights.same * eq(&r[..19], V_ALIAS_ROW[context] + bit)
            * eq(&u[..20], SCORE_X[context] + 224 + bit)
            * eq(&v[..20], [1_000_770,1_002_818][context] + 740 + bit);
        out[1] += weight; out[2] -= weight;
    }
    for bit in 0..224 {
        out[1] += eq(&r[..19], W_ALIAS_ROW[context] + bit) * eq(&v[..20], 0)
            * (weights.global_self * eq(&u[..20], SCORE_X[context] + bit)
                - weights.global_work * eq(&u[..20], UPPER_LOCAL + bit));
    }
    let mut active = weights.global_self;
    for owner in ANCHOR_OWNERS {
        active += eq(&r[19..], owner) * eq(&u[20..], owner) * eq(&v[20..], 0);
        emit_score_owner(owner, context, map, |term| { add(&mut out, point_fold(&term,r,u,v)); Ok(()) })?;
    }
    let all = wiring::evaluate_shift(&r[19..], &u[20..], &v[20..],
        0,0,SLOTS as u64,0,RightIndex::GlobalZero)?;
    for bit in 0..2048 {
        out[1] += (all-active) * eq(&r[..19], SCORE_ROW[context] + bit)
            * eq(&u[..20], SCORE_X[context] + bit) * eq(&v[..20], 0);
    }
    Ok(out)
}

#[path = "h21_structural_roster_tests.rs"]
mod tests;

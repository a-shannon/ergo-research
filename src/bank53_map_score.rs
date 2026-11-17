//! Bounded test prototype for the two-context physical Map/Score overlay.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{
    gkr::Gate,
    legacy_envelope_map::{Map, BASE as MAP_BASE},
    origin_score::{Layout as ScoreLayout},
    origin_score_map::Plan,
    sparse::Term,
};
use crate::bank53_map::{
    bank53_history_bounds, context_ok, exact_zero_tail, translate_map_terms,
    owner_input_base, HistoryBounds, BANK53_F, BANK53_H, BANK53_N, CONTEXT_INPUT_BASE,
    CONTEXT_ROW_BASE, CONTEXTS, INPUT_STRIDE, MAP_LIVE, MAP_ROW_STRIDE, MAP_TAIL_COUNT, MAP_TAIL_END,
    MAP_TAIL_START, ROW_STRIDE,
};
pub(crate) use crate::bank53_map::map_owner_terms;

const SCORE_INPUT_STRIDE: usize = 1 << 11;
const SCORE_ROW_STRIDE: usize = 1 << 13;
const SCORE_INPUT_OFFSET: usize = 5_757;
const SCORE_ROW_OFFSET: usize = 16_384;
const W_ALIAS_ROW_OFFSET: usize = 28_672;
const WORK_W_BASE: usize = 987_450;
const WORK_W_WIDTH: usize = 224;
use crate::bank53_slack::{SLACK_INPUT_START, SLACK_ZERO_COUNT, SLACK_ROW_OFFSET};
pub(crate) use crate::bank53_slack::slack_zero_terms;
const _: () = assert!(SLACK_ROW_OFFSET == W_ALIAS_ROW_OFFSET + WORK_W_WIDTH);
const SCORE_OWNER_TERM_CAP: usize = 10_000;
const FIRST_MODERN_OWNER: usize = 845_759;

fn score_plan_spec(plan: &Plan, owner: usize, context: usize) -> Result<crate::origin_score::Spec, String> {
    context_ok(context)?;
    if plan.profiles() != 1 || plan.count() == 0
        || plan.owner_log() > 21 || plan.slots() > (1usize << 21) {
        return Err("bank53 Score plan geometry".into());
    }
    if plan.owner_log() == 21 {
        bank53_history_bounds(BANK53_N, BANK53_H)?;
        let expected_count = if context == 0 { BANK53_F } else { BANK53_H };
        if plan.count() != expected_count as usize {
            return Err("bank53 Score context endpoint must be f or h".into());
        }
    }
    if !plan.spec(0, 0)?.origin_one {
        return Err("bank53 Score plan must begin at origin one".into());
    }
    let spec = plan.spec(0, owner)?;
    let terminal = plan.spec(0, plan.count() - 1)?;
    if !terminal.terminal {
        return Err("bank53 Score plan must include its full reducing prefix".into());
    }
    let expected_maturity = if context == 0 { 43_410 } else { 17_867 };
    if plan.spec(0, 0)?.maturity != expected_maturity {
        return Err("bank53 Score context maturity/mode mismatch".into());
    }
    let input_local = CONTEXT_INPUT_BASE + context * 8_192 + SCORE_INPUT_OFFSET;
    let row_local = CONTEXT_ROW_BASE + context * 32_768 + SCORE_ROW_OFFSET;
    if input_local + 2_048 > INPUT_STRIDE || row_local + SCORE_ROW_STRIDE > ROW_STRIDE {
        return Err("bank53 Score lane bounds".into());
    }
    Ok(spec)
}

fn score_geometry(plan: &Plan, owner: usize, context: usize) -> Result<crate::origin_score::Spec, String> {
    let spec = score_plan_spec(plan, owner, context)?;
    if spec.active && owner >= FIRST_MODERN_OWNER {
        return Err("bank53 adapter does not support active modern Score origins".into());
    }
    Ok(spec)
}

fn score_input(index: usize, plan: &Plan, context: usize) -> Result<usize, String> {
    let source_owner = index / SCORE_INPUT_STRIDE;
    let local = index % SCORE_INPUT_STRIDE;
    if source_owner >= plan.slots() { return Err("bank53 Score input owner".into()); }
    let base = owner_input_base(source_owner as u64)?;
    base.checked_add(CONTEXT_INPUT_BASE + context * 8_192 + SCORE_INPUT_OFFSET + local)
        .ok_or_else(|| "bank53 Score input coordinate overflow".into())
}

fn score_row(index: usize, owner: usize, context: usize) -> Result<usize, String> {
    let old_base = owner.checked_mul(SCORE_ROW_STRIDE)
        .ok_or("bank53 Score source row overflow")?;
    let local = index.checked_sub(old_base).ok_or("bank53 Score row owner underflow")?;
    if local >= SCORE_ROW_STRIDE { return Err("bank53 Score term escapes owner rows".into()); }
    owner.checked_mul(ROW_STRIDE)
        .and_then(|base| base.checked_add(CONTEXT_ROW_BASE + context * 32_768 + SCORE_ROW_OFFSET + local))
        .ok_or_else(|| "bank53 Score physical row overflow".into())
}

/// Emit one Score owner and its active canonical W alias rows. No modern V
/// provenance is supplied or implied by this local tuple adapter.
pub(crate) fn score_owner_terms(plan: &Plan, owner: usize, context: usize) -> Result<Vec<Term>, String> {
    let spec = score_geometry(plan, owner, context)?;
    let emitted = plan.emit_owner(0, owner, |_| {})?;
    if emitted + 2 * WORK_W_WIDTH + SLACK_ZERO_COUNT > SCORE_OWNER_TERM_CAP {
        return Err("bank53 Score owner materialization cap".into());
    }
    let mut out = Vec::with_capacity(emitted + 2 * WORK_W_WIDTH + SLACK_ZERO_COUNT);
    plan.emit_owner(0, owner, |term| out.push(term))?;
    for term in &mut out {
        term.row = score_row(term.row, owner, context)?;
        term.gate.left = score_input(term.gate.left, plan, context)?;
        term.gate.right = score_input(term.gate.right, plan, context)?;
    }
    if spec.active {
        out.extend(w_alias_terms(owner, context)?);
    }
    out.extend(slack_zero_terms(owner, context)?);
    Ok(out)
}

fn w_alias_terms(owner: usize, context: usize) -> Result<Vec<Term>, String> {
    context_ok(context)?;
    if owner >= (1usize << 21) { return Err("bank53 W alias owner".into()); }
    let row_base = owner.checked_mul(ROW_STRIDE)
        .and_then(|base| base.checked_add(CONTEXT_ROW_BASE + context * 32_768 + W_ALIAS_ROW_OFFSET))
        .ok_or("bank53 W alias row base overflow")?;
    let score_base = owner_input_base(owner as u64)?
        .checked_add(CONTEXT_INPUT_BASE + context * 8_192 + SCORE_INPUT_OFFSET)
        .ok_or("bank53 Score W alias input overflow")?;
    let mut out = Vec::with_capacity(if owner == 0 { WORK_W_WIDTH } else { 2 * WORK_W_WIDTH });
    for bit in 0..WORK_W_WIDTH {
        let row = row_base.checked_add(bit).ok_or("bank53 W alias row overflow")?;
        let score = score_base.checked_add(ScoreLayout::new().sw.start + bit)
            .ok_or("bank53 Score W coordinate overflow")?;
        out.push(Term { row, gate: Gate { left: score, right: 0,
            c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() }});
        if owner > 0 {
            let work_owner = owner_input_base((owner - 1) as u64)?;
            let work = work_owner.checked_add(WORK_W_BASE + bit)
                .ok_or("bank53 WORK W coordinate overflow")?;
            out.push(Term { row, gate: Gate { left: 0, right: work,
                c0: Fr::zero(), c1: Fr::zero(), c2: -Fr::one(), c3: Fr::zero() }});
        }
    }
    Ok(out)
}

/// Analytic coefficient contribution for active Score.sw-to-W aliases.
/// Owner selectors are evaluated once; the fixed 224-bit ports are then summed.
pub(crate) fn w_alias_coefficients(
    plan: &Plan,
    owner: usize,
    context: usize,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> Result<[Fr; 4], String> {
    let spec = score_geometry(plan, owner, context)?;
    let h = plan.owner_log();
    if (r.len(), u.len(), v.len()) != (19 + h, 20 + h, 20 + h) {
        return Err("bank53 W alias coefficient dimensions".into());
    }
    let mut out = [Fr::zero(); 4];
    if !spec.active { return Ok(out); }
    let row_owner = eq(&r[19..], owner);
    let u_score_owner = eq(&u[20..], owner);
    let v_zero_owner = eq(&v[20..], 0);
    let u_zero_owner = eq(&u[20..], 0);
    let v_work_owner = if owner > 0 { eq(&v[20..], owner - 1) } else { Fr::zero() };
    let row_base = CONTEXT_ROW_BASE + context * 32_768 + W_ALIAS_ROW_OFFSET;
    let score_base = CONTEXT_INPUT_BASE + context * 8_192 + SCORE_INPUT_OFFSET;
    let v_zero_local = eq(&v[..20], 0);
    let u_zero_local = eq(&u[..20], 0);
    for bit in 0..WORK_W_WIDTH {
        let row = eq(&r[..19], row_base + bit);
        let score = eq(&u[..20], score_base + ScoreLayout::new().sw.start + bit);
        out[1] += row_owner * row * u_score_owner * score * v_zero_owner * v_zero_local;
        if owner > 0 {
            let work = eq(&v[..20], WORK_W_BASE + bit);
            out[2] -= row_owner * row * u_zero_owner * u_zero_local * v_work_owner * work;
        }
    }
    Ok(out)
}

/// Coefficients of the explicit B[7805..8192)=0 constraints when requested
/// for an owner. The lane is disjoint from the W aliases.
pub(crate) fn slack_zero_coefficients(
    plan: &Plan,
    owner: usize,
    context: usize,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> Result<[Fr; 4], String> {
    score_plan_spec(plan, owner, context)?;
    let h = plan.owner_log();
    if (r.len(), u.len(), v.len()) != (19 + h, 20 + h, 20 + h) {
        return Err("bank53 slack coefficient dimensions".into());
    }
    let mut out = [Fr::zero(); 4];
    let row_owner = eq(&r[19..], owner);
    let u_owner = eq(&u[20..], owner);
    let v_zero_owner = eq(&v[20..], 0);
    let v_zero_local = eq(&v[..20], 0);
    let row_base = CONTEXT_ROW_BASE + context * 32_768 + SLACK_ROW_OFFSET;
    let input_base = CONTEXT_INPUT_BASE + context * 8_192;
    for offset in 0..SLACK_ZERO_COUNT {
        let row = eq(&r[..19], row_base + offset);
        let left = eq(&u[..20], input_base + SLACK_INPUT_START + offset);
        out[1] += row_owner * row * u_owner * left * v_zero_owner * v_zero_local;
    }
    Ok(out)
}

fn eq(bits: &[Fr], index: usize) -> Fr {
    bits.iter().enumerate().fold(Fr::one(), |acc, (bit, value)| {
        acc * if (index >> bit) & 1 == 1 { *value } else { Fr::one() - value }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    use crate::origin_score_map::{GuardPolicy, Mode, Profile};

    fn map(n: u64, h: usize) -> Map {
        Map::new(n, h, 8).expect("bounded map")
    }

    fn plan(count: usize, mode: Mode) -> Plan {
        plan_with_prefix(count, mode, count)
    }

    fn plan_with_prefix(count: usize, mode: Mode, prefix: usize) -> Plan {
        Plan::new(1, count, vec![Profile { mode, prefix,
            expected: BigUint::from(0u8), guard: GuardPolicy::Disabled }]).expect("bounded plan")
    }

    fn points(h: usize, row_owner: usize) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
        let mut r: Vec<_> = (0..19).map(|i| Fr::from((i + 2) as u64)).collect();
        r.extend((0..h).map(|bit| Fr::from(((row_owner >> bit) & 1) as u64)));
        let mut u: Vec<_> = (0..20).map(|i| Fr::from((i + 3) as u64)).collect();
        u.extend((0..h).map(|bit| Fr::from((bit + 5) as u64)));
        let mut v: Vec<_> = (0..20).map(|i| Fr::from((i + 7) as u64)).collect();
        v.extend((0..h).map(|bit| Fr::from((bit + 11) as u64)));
        (r, u, v)
    }

    fn full_nonboolean_points(h: usize) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
        let mut r: Vec<_> = (0..19).map(|i| Fr::from((i + 2) as u64)).collect();
        r.extend((0..h).map(|bit| Fr::from((bit + 3) as u64)));
        let mut u: Vec<_> = (0..20).map(|i| Fr::from((i + 5) as u64)).collect();
        u.extend((0..h).map(|bit| Fr::from((bit + 7) as u64)));
        let mut v: Vec<_> = (0..20).map(|i| Fr::from((i + 11) as u64)).collect();
        v.extend((0..h).map(|bit| Fr::from((bit + 13) as u64)));
        (r, u, v)
    }

    fn tuple_coefficients(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let mut out = [Fr::zero(); 4];
        for term in terms {
            let weight = eq(r, term.row) * eq(u, term.gate.left) * eq(v, term.gate.right);
            for (sum, c) in out.iter_mut().zip([
                term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3,
            ]) { *sum += weight * c; }
        }
        out
    }

    fn is_tail_helper(index: usize, owner: u64) -> bool {
        index.checked_sub(owner as usize * INPUT_STRIDE).map_or(false, |local| {
            (MAP_BASE + MAP_TAIL_START..MAP_BASE + MAP_TAIL_END).contains(&local)
        })
    }

    #[test]
    fn pinned_history_bounds_accept_and_reject_the_exact_edge() {
        let bounds = bank53_history_bounds(BANK53_N, BANK53_H).expect("pinned bounds");
        assert_eq!(bounds, HistoryBounds { n: 1_827_840, h: 1_827_775, f: 1_827_838 });
        assert!(bank53_history_bounds(BANK53_H + 63, BANK53_H).is_err());
        assert!(bank53_history_bounds(BANK53_N, BANK53_H + 1).is_err());
    }

    #[test]
    fn retires_only_exact_tail_gates_for_each_owner_class() {
        let m = map(BANK53_N, 21);
        for owner in [100u64, 959, 845_759, BANK53_N] {
            let all = m.terms(owner).expect("raw Map terms");
            let raw: Vec<_> = all.iter().filter(|term| {
                (owner as usize * MAP_ROW_STRIDE + MAP_TAIL_START
                    ..owner as usize * MAP_ROW_STRIDE + MAP_TAIL_END).contains(&term.row)
            }).cloned().collect();
            assert_eq!(raw.len(), MAP_TAIL_COUNT);
            for (offset, term) in raw.iter().enumerate() {
                exact_zero_tail(term, owner, MAP_TAIL_START + offset).expect("exact tail identity");
            }
            assert!(all.iter().filter(|term| {
                !(owner as usize * MAP_ROW_STRIDE + MAP_TAIL_START
                    ..owner as usize * MAP_ROW_STRIDE + MAP_TAIL_END).contains(&term.row)
            }).all(|term| !is_tail_helper(term.gate.left, owner)
                && !is_tail_helper(term.gate.right, owner)));
            let translated = map_owner_terms(&m, owner, 0).expect("physical Map owner");
            assert_eq!(translated.len() + MAP_TAIL_COUNT, all.len());
            assert!(translated.iter().all(|term| {
                let local = term.row % ROW_STRIDE;
                !(CONTEXT_ROW_BASE + MAP_TAIL_START
                    ..CONTEXT_ROW_BASE + MAP_TAIL_END).contains(&local)
            }));
        }
    }

    #[test]
    fn wrong_zero_tail_identity_and_context_owner_bounds_fail_closed() {
        let m = map(BANK53_N, 21);
        let mut raw = m.terms(100).unwrap();
        let row = 100 * MAP_ROW_STRIDE + MAP_TAIL_START;
        let bad = raw.iter_mut().find(|term| term.row == row).unwrap();
        bad.gate.c1 = Fr::from(2u64);
        assert!(translate_map_terms(&m, 100, 0, &raw).is_err());
        let mut retained = m.terms(100).unwrap();
        let retained_row = 100 * MAP_ROW_STRIDE;
        let live = retained.iter_mut().find(|term| term.row == retained_row).unwrap();
        live.gate.left = 100 * INPUT_STRIDE + MAP_BASE + MAP_TAIL_START;
        assert!(translate_map_terms(&m, 100, 0, &retained).is_err());
        assert!(map_owner_terms(&m, 100, CONTEXTS).is_err());
        assert!(map_owner_terms(&m, m.slots(), 0).is_err());
        assert!(map_owner_terms(&m, 100, 1).is_err());
        let p = plan(7, Mode::Sampled);
        assert!(score_owner_terms(&p, p.slots(), 0).is_err());
        assert!(score_owner_terms(&p, 0, CONTEXTS).is_err());
    }

    #[test]
    fn h3_map_score_and_w_alias_coefficients_match_translated_tuples() {
        let m = map(7, 3);
        let p = plan(7, Mode::Sampled);
        let (r, u, v) = full_nonboolean_points(3);
        let mt: Vec<_> = (0..m.slots()).flat_map(|owner| {
            map_owner_terms(&m, owner, 0).unwrap()
        }).collect();
        assert_eq!(tuple_coefficients(&mt, &r, &u, &v),
            m.bank53_coefficients(0, &r, &u, &v).unwrap());

        let st: Vec<_> = (0..p.slots()).flat_map(|owner| {
            score_owner_terms(&p, owner, 0).unwrap()
        }).collect();
        let score_lane = CONTEXT_ROW_BASE + SCORE_ROW_OFFSET;
        let score_terms: Vec<_> = st.iter().filter(|term| {
            (score_lane..score_lane + SCORE_ROW_STRIDE).contains(&(term.row % ROW_STRIDE))
        }).cloned().collect();
        assert_eq!(tuple_coefficients(&score_terms, &r, &u, &v),
            p.bank53_coefficients(0, &r, &u, &v).unwrap());
        let alias_terms: Vec<_> = st.iter().filter(|term| {
            (CONTEXT_ROW_BASE + W_ALIAS_ROW_OFFSET
                ..CONTEXT_ROW_BASE + W_ALIAS_ROW_OFFSET + WORK_W_WIDTH)
                .contains(&(term.row % ROW_STRIDE))
        }).cloned().collect();
        assert_eq!(tuple_coefficients(&alias_terms, &r, &u, &v),
            (0..p.slots()).fold([Fr::zero(); 4], |mut sum, owner| {
                let next = w_alias_coefficients(&p, owner, 0, &r, &u, &v).unwrap();
                for (slot, value) in sum.iter_mut().zip(next) { *slot += value; }
                sum
            }));
        let slack_terms: Vec<_> = st.iter().filter(|term| {
            (CONTEXT_ROW_BASE + SLACK_ROW_OFFSET
                ..CONTEXT_ROW_BASE + SLACK_ROW_OFFSET + SLACK_ZERO_COUNT)
                .contains(&(term.row % ROW_STRIDE))
        }).cloned().collect();
        assert_eq!(tuple_coefficients(&slack_terms, &r, &u, &v),
            (0..p.slots()).fold([Fr::zero(); 4], |mut sum, owner| {
                let next = slack_zero_coefficients(&p, owner, 0, &r, &u, &v).unwrap();
                for (slot, value) in sum.iter_mut().zip(next) { *slot += value; }
                sum
            }));

        let origin_one = score_owner_terms(&p, 0, 0).unwrap();
        let origin_one_aliases: Vec<_> = origin_one.into_iter().filter(|term| {
            (CONTEXT_ROW_BASE + W_ALIAS_ROW_OFFSET
                ..CONTEXT_ROW_BASE + W_ALIAS_ROW_OFFSET + WORK_W_WIDTH)
                .contains(&(term.row % ROW_STRIDE))
        }).collect();
        assert_eq!(origin_one_aliases.len(), WORK_W_WIDTH);
        assert!(origin_one_aliases.iter().all(|term|
            term.gate.c1 == Fr::one() && term.gate.c2.is_zero()));
    }

    #[test]
    fn h21_overlay_differentials_cover_tier_context_and_padding() {
        for context in 0..CONTEXTS {
            let m = if context == 0 { map(BANK53_N, 21) } else { map(BANK53_H, 21) };
            let p = if context == 0 {
                plan(BANK53_F as usize, Mode::Sampled)
            } else {
                plan(BANK53_H as usize, Mode::Exact)
            };
            let owner = 9_151usize;
            let (r, u, v) = points(21, owner);
            let mt = map_owner_terms(&m, owner as u64, context).unwrap();
            assert_eq!(tuple_coefficients(&mt, &r, &u, &v),
                m.bank53_coefficients(context, &r, &u, &v).unwrap());
            let st = score_owner_terms(&p, owner, context).unwrap();
            let score_lane = CONTEXT_ROW_BASE + context * 32_768 + SCORE_ROW_OFFSET;
            let score_terms: Vec<_> = st.iter().filter(|term| {
                (score_lane..score_lane + SCORE_ROW_STRIDE).contains(&(term.row % ROW_STRIDE))
            }).cloned().collect();
            assert_eq!(tuple_coefficients(&score_terms, &r, &u, &v),
                p.bank53_coefficients(context, &r, &u, &v).unwrap());
            let alias_terms: Vec<_> = st.iter().filter(|term| {
                let alias = CONTEXT_ROW_BASE + context * 32_768 + W_ALIAS_ROW_OFFSET;
                (alias..alias + WORK_W_WIDTH).contains(&(term.row % ROW_STRIDE))
            }).cloned().collect();
            assert_eq!(tuple_coefficients(&alias_terms, &r, &u, &v),
                w_alias_coefficients(&p, owner, context, &r, &u, &v).unwrap());
            let slack_lane = CONTEXT_ROW_BASE + context * 32_768 + SLACK_ROW_OFFSET;
            let slack_terms: Vec<_> = st.iter().filter(|term| {
                (slack_lane..slack_lane + SLACK_ZERO_COUNT)
                    .contains(&(term.row % ROW_STRIDE))
            }).cloned().collect();
            assert_eq!(tuple_coefficients(&slack_terms, &r, &u, &v),
                slack_zero_coefficients(&p, owner, context, &r, &u, &v).unwrap());
        }
        let sampled = plan(BANK53_F as usize, Mode::Sampled);
        let padding = sampled.slots() - 1;
        let terms = score_owner_terms(&sampled, padding, 0).unwrap();
        assert!(!terms.iter().any(|term| {
            (CONTEXT_ROW_BASE + W_ALIAS_ROW_OFFSET
                ..CONTEXT_ROW_BASE + W_ALIAS_ROW_OFFSET + WORK_W_WIDTH)
                .contains(&(term.row % ROW_STRIDE))
        }));
        let slack_lane = CONTEXT_ROW_BASE + SLACK_ROW_OFFSET;
        assert_eq!(terms.iter().filter(|term| {
            (slack_lane..slack_lane + SLACK_ZERO_COUNT)
                .contains(&(term.row % ROW_STRIDE))
        }).count(), SLACK_ZERO_COUNT);
    }

    #[test]
    fn score_adapter_binds_context_prefix_and_rejects_modern_origins() {
        let sampled = plan(BANK53_F as usize, Mode::Sampled);
        let exact = plan(BANK53_H as usize, Mode::Exact);
        assert!(score_owner_terms(&plan(BANK53_F as usize, Mode::Exact), 0, 0).is_err());
        assert!(score_owner_terms(&plan(BANK53_H as usize, Mode::Sampled), 0, 1).is_err());
        assert!(score_owner_terms(&plan(BANK53_F as usize - 1, Mode::Sampled), 0, 0).is_err());
        assert!(score_owner_terms(&plan_with_prefix(7, Mode::Sampled, 6), 0, 0).is_err());
        let shifted = Plan::new(2, 7, vec![Profile { mode: Mode::Sampled, prefix: 7,
            expected: BigUint::from(0u8), guard: GuardPolicy::Disabled }]).unwrap();
        assert!(score_owner_terms(&shifted, 0, 0).is_err());
        let modern = plan(845_760, Mode::Sampled);
        assert!(score_owner_terms(&modern, 845_759, 0).is_err());
        let (r, u, v) = points(modern.owner_log(), 845_759);
        assert!(w_alias_coefficients(&modern, 845_759, 0, &r, &u, &v).is_err());
        let modern_slack = slack_zero_terms(845_759, 0).unwrap();
        assert_eq!(modern_slack.len(), SLACK_ZERO_COUNT);
        assert_eq!(tuple_coefficients(&modern_slack, &r, &u, &v),
            slack_zero_coefficients(&modern, 845_759, 0, &r, &u, &v).unwrap());

        let sampled_map = map(BANK53_N, 21);
        for owner in [BANK53_N - 2, BANK53_N - 1] {
            let terms = map_owner_terms(&sampled_map, owner, 0)
                .expect("Map last-work/padding geometry");
            assert_eq!(terms.len() + MAP_TAIL_COUNT, sampled_map.terms(owner).unwrap().len());
            let work_guard = sampled_map.active_intervals(owner).unwrap()
                .iter().any(|&(lo, hi)| lo == MAP_BASE && hi == MAP_BASE + 673);
            assert_eq!(work_guard, owner == BANK53_N - 2);
        }
        let exact_map = map(BANK53_H, 21);
        for owner in [BANK53_H - 2, BANK53_H - 1] {
            let terms = map_owner_terms(&exact_map, owner, 1)
                .expect("exact-cut Map last-work/padding geometry");
            assert_eq!(terms.len() + MAP_TAIL_COUNT, exact_map.terms(owner).unwrap().len());
            let work_guard = exact_map.active_intervals(owner).unwrap()
                .iter().any(|&(lo, hi)| lo == MAP_BASE && hi == MAP_BASE + 673);
            assert_eq!(work_guard, owner == BANK53_H - 2);
        }
        for (plan, context) in [(&sampled, 0), (&exact, 1)] {
            let last = plan.count() - 1;
            let last_spec = plan.spec(0, last).unwrap();
            assert!(last_spec.active && last_spec.terminal);
            assert!(score_owner_terms(plan, last, context).is_err(),
                "last genuine modern Score owner must reject materialization");
            let padding = plan.count();
            assert!(!plan.spec(0, padding).unwrap().active);
            let padding_terms = score_owner_terms(plan, padding, context)
                .expect("first padding Score geometry and slack constraints");
            assert!(!padding_terms.iter().any(|term| {
                let alias = CONTEXT_ROW_BASE + context * 32_768 + W_ALIAS_ROW_OFFSET;
                (alias..alias + WORK_W_WIDTH).contains(&(term.row % ROW_STRIDE))
            }));
            let slack = CONTEXT_ROW_BASE + context * 32_768 + SLACK_ROW_OFFSET;
            assert_eq!(padding_terms.iter().filter(|term| {
                (slack..slack + SLACK_ZERO_COUNT).contains(&(term.row % ROW_STRIDE))
            }).count(), SLACK_ZERO_COUNT);
        }
    }
}

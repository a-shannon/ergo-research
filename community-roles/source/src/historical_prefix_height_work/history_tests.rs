use super::*;
use crate::{work_tree_layout::Endpoints, work_tree_wiring::eq_index};
use ark_ff::Field;
use std::{collections::BTreeMap, sync::OnceLock};

fn small() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(5, 3, [7; 32], [0; 28]).unwrap())
}

fn large() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| WorkTreeHistoryPlan::compile((1 << 21) - 1, 21, [7; 32], [0; 28]).unwrap())
}

fn point(log: usize, index: usize) -> Vec<Fr> {
    (0..log).map(|b| Fr::from(((index >> b) & 1) as u64)).collect()
}

fn dense(log: usize, seed: u64) -> Vec<Fr> {
    (0..log).map(|b| Fr::from(seed + 13 * b as u64)).collect()
}

fn terms(role: &HeightWork<'_>, owner: u64) -> (Vec<Term>, OwnerCounts) {
    let mut out = Vec::new();
    let counts = role.visit_owner_terms(owner, |t| { out.push(t); Ok(()) }).unwrap();
    assert_eq!(out.len(), counts.height + counts.numeric);
    (out, counts)
}

fn direct(ts: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for t in ts {
        let w = eq_index(r, t.row) * eq_index(u, t.gate.left) * eq_index(v, t.gate.right);
        for (o, c) in out.iter_mut().zip([t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3]) {
            *o += w * c;
        }
    }
    out
}

fn residual(ts: &[Term], row: usize, values: &BTreeMap<usize, Fr>) -> Fr {
    ts.iter().filter(|t| t.row == row).map(|t| {
        let a = values.get(&t.gate.left).copied().unwrap_or_default();
        let b = values.get(&t.gate.right).copied().unwrap_or_default();
        t.gate.c0 + t.gate.c1 * a + t.gate.c2 * b + t.gate.c3 * a * b
    }).sum()
}

fn keys(ts: &[Term]) -> Vec<(usize, usize, usize, [Fr; 4])> {
    ts.iter().map(|t| (t.row, t.gate.left, t.gate.right,
        [t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3])).collect()
}

#[test]
fn generic_small_emitter_matches_direct_all_channel_polynomial() {
    let role = HeightWork::compile_history(small()).unwrap();
    assert_eq!((role.input_log(), role.row_log(), role.slots()), (23, 9, 8));
    let all: Vec<_> = (0..8).flat_map(|c| terms(&role, c).0).collect();
    assert_eq!(all.len(), 5 * 32 + 225 + 3 * 448);
    for seed in [3, 17, 83] {
        let (r, u, v) = (dense(9, seed), dense(23, seed + 1), dense(23, seed + 2));
        assert_eq!(role.coefficients(&r, &u, &v).unwrap(), direct(&all, &r, &u, &v));
    }
    assert!(role.circuit().unwrap_err().contains("owner streaming"));
}

#[test]
fn generic_height_fault_is_detected_and_omission_is_load_bearing() {
    let role = HeightWork::compile_history(small()).unwrap();
    let (ts, counts) = terms(&role, 4);
    assert_eq!(counts, OwnerCounts { height: 32, numeric: 448 });
    let mut good = BTreeMap::new();
    // Literal serializer interval, independent of the production height map.
    for b in 0..32 { good.insert(4 * (1 << 20) + 525682 + b, Fr::from((5u64 >> b) & 1)); }
    assert_eq!(residual(&ts, 4 * 32, &good), Fr::zero());
    let mut bad = good.clone();
    bad.insert(4 * (1 << 20) + 525682, Fr::zero());
    assert_eq!(residual(&ts, 4 * 32, &bad), -Fr::one());
    let omitted: Vec<_> = ts.into_iter().filter(|t| t.row != 4 * 32).collect();
    assert_eq!(residual(&omitted, 4 * 32, &bad), Fr::zero());
    assert_eq!(good.len(), bad.len());
    assert_eq!(good.iter().filter(|(k, v)| bad.get(k) != Some(v)).count(), 1);
}

#[test]
fn generic_numeric_fault_is_detected_and_omission_is_load_bearing() {
    let role = HeightWork::compile_history(small()).unwrap();
    let (ts, _) = terms(&role, 4);
    let row = 32 * 8 + 4;
    let good = BTreeMap::new();
    // Both work endpoints zero is a local numeric-relation control, not a
    // valid decoded-work/history witness. Parent decoder positivity is inherited.
    assert_eq!(residual(&ts, row, &good), Fr::zero());
    for bit in [0, 63, 223] {
        let mut bad = good.clone();
        bad.insert(3 * (1 << 20) + 987674 + bit, Fr::one());
        assert_eq!(residual(&ts, row, &bad), Fr::from(2u64).pow([bit as u64]));
        let omitted: Vec<_> = ts.iter().filter(|t| t.row != row).cloned().collect();
        assert_eq!(residual(&omitted, row, &bad), Fr::zero());
        assert_eq!(bad.len(), 1);
    }
}

#[test]
fn generic_owner_tag_padding_global_zero_and_dimensions_are_isolated() {
    let role = HeightWork::compile_history(small()).unwrap();
    for c in 5..8 {
        assert_eq!(terms(&role, c), (Vec::new(), OwnerCounts::default()));
    }
    let mut invoked = false;
    assert!(role.visit_owner_terms(8, |_| { invoked = true; Ok(()) }).is_err());
    assert!(!invoked);
    let (r, u, v) = (point(9, 32 * 8 + 4), point(23, 3 * (1 << 20) + 987674), point(23, 0));
    assert_eq!(role.coefficients(&r, &u, &v).unwrap(), [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]);
    let wrong_zero = point(23, 4 * (1 << 20));
    assert_eq!(role.coefficients(&r, &u, &wrong_zero).unwrap(), [Fr::zero(); 4]);
    let padding_tag = point(9, 32 * 8 + 8 + 4);
    assert_eq!(role.coefficients(&padding_tag, &u, &v).unwrap(), [Fr::zero(); 4]);
    let padding_owner = point(9, 32 * 8 + 5);
    let padding_work = point(23, 4 * (1 << 20) + 987674);
    assert_eq!(role.coefficients(&padding_owner, &padding_work, &v).unwrap(), [Fr::zero(); 4]);
    for delta in [-1isize, 1] {
        assert!(role.coefficients(&vec![Fr::zero(); (9isize + delta) as usize], &u, &v).is_err());
        assert!(role.coefficients(&r, &vec![Fr::zero(); (23isize + delta) as usize], &v).is_err());
        assert!(role.coefficients(&r, &u, &vec![Fr::zero(); (23isize + delta) as usize]).is_err());
    }
}

#[test]
fn generic_legacy_terms_selectors_and_binding_remain_separate() {
    for n in [3, 4] {
        let parent = WorkTreeHistoryPlan::compile(n, 2, [7; 32], [0; 28]).unwrap();
        let legacy = HeightWork::new(&parent).unwrap();
        let generic = HeightWork::compile_history(&parent).unwrap();
        let emitted: Vec<_> = (0..4).flat_map(|c| terms(&generic, c).0).collect();
        let old = legacy.circuit().unwrap();
        let mut a = keys(&emitted); let mut b = keys(&old.terms);
        a.sort_by_key(|t| (t.0, t.1, t.2)); b.sort_by_key(|t| (t.0, t.1, t.2));
        assert_eq!(a, b);
        let (r, u, v) = (dense(8, 19), dense(22, 23), dense(22, 29));
        assert_eq!(legacy.coefficients(&r, &u, &v), generic.coefficients(&r, &u, &v));
        let mut lt = Transcript::new(b"generic-height-work-test"); legacy.bind(&mut lt);
        let mut gt = Transcript::new(b"generic-height-work-test"); generic.bind(&mut gt);
        assert_eq!(lt.challenges(), 0); assert_eq!(gt.challenges(), 0);
        assert_ne!(lt.challenge_scalar(b"after-bind"), gt.challenge_scalar(b"after-bind"));
    }
    assert!(HeightWork::new(small()).is_err());
}

#[test]
fn generic_large_owner_stream_and_polynomial_keep_full_slot_bits() {
    let role = HeightWork::compile_history(large()).unwrap();
    assert_eq!((role.input_log(), role.row_log(), role.slots()), (41, 27, 1 << 21));
    assert!(role.circuit().is_err());
    let s = 1usize << 21;
    // Native action counts at frontiers are literal; no production classifier
    // or source-index helpers generate the expected values.
    for (c, numeric) in [(0, 0), (1, 225), (1024, 448), (2048, 0), (3072, 0),
        (9216, 0), (417791, 225), (417792, 225), (844672, 0), (844673, 448), (s - 2, 448)] {
        let (ts, counts) = terms(&role, c as u64);
        assert_eq!(counts, OwnerCounts { height: 32, numeric }, "owner{c}");
        assert!(ts.len() <= 480);
        for b in [0, 31] {
            let (r, u, v) = (point(27, c * 32 + b), point(41, c * (1 << 20) + 525682 + b), point(41, c * (1 << 20)));
            assert_eq!(role.coefficients(&r, &u, &v).unwrap(),
                [-Fr::from((((c + 1) >> b) & 1) as u64), Fr::one(), Fr::zero(), Fr::zero()]);
        }
        if numeric != 0 {
            let (r, u, v) = (point(27, 32 * s + c), point(41, (c - 1) * (1 << 20) + 987674 + 223), point(41, 0));
            assert_eq!(role.coefficients(&r, &u, &v).unwrap(), direct(&ts, &r, &u, &v));
            let mut wrong = r.clone(); wrong[20] = Fr::one() - wrong[20];
            assert_ne!(role.coefficients(&wrong, &u, &v).unwrap(), role.coefficients(&r, &u, &v).unwrap());
        }
    }
    let (ts, counts) = terms(&role, (s - 1) as u64);
    assert!(ts.is_empty()); assert_eq!(counts, OwnerCounts::default());
    let (r, u, v) = (point(27, 32 * s + s - 1), point(41, (s - 2) * (1 << 20) + 987674), point(41, 0));
    assert_eq!(role.coefficients(&r, &u, &v).unwrap(), [Fr::zero(); 4]);
    // Non-Boolean row and low-wire points with Boolean owner inputs retain one
    // height owner and its at most two numeric uses. No all-history enumeration.
    let leaf = (1 << 20) + 17;
    let mut u = dense(20, 11); u.extend(point(21, leaf));
    let v = point(41, 0); let r = dense(27, 7);
    let expected: Vec<_> = [leaf, leaf + 1, leaf + 2].into_iter().flat_map(|c| terms(&role, c as u64).0).collect();
    assert_eq!(role.coefficients(&r, &u, &v).unwrap(), direct(&expected, &r, &u, &v));
}

#[test]
fn generic_transcript_binds_geometry_template_and_numeric_parent_join() {
    fn challenge(role: &HeightWork<'_>) -> Fr {
        let mut t = Transcript::new(b"generic-height-work-bindings");
        role.bind(&mut t);
        assert_eq!(t.challenges(), 0);
        t.challenge_scalar(b"bound")
    }
    let baseline = challenge(&HeightWork::compile_history(small()).unwrap());
    assert_eq!(baseline, challenge(&HeightWork::compile_history(small()).unwrap()));
    // These isolated descriptor mutations test binding coverage, not admission
    // or validity of a witness. Parent-ID/work variation is inherited unchanged.
    let mut changed = HeightWork::compile_history(small()).unwrap();
    changed.headers += 1;
    assert_ne!(baseline, challenge(&changed));
    let mut changed = HeightWork::compile_history(small()).unwrap();
    changed.slot_log += 1;
    assert_ne!(baseline, challenge(&changed));
    let mut changed = HeightWork::compile_history(small()).unwrap();
    changed.height = HeaderHeightLayout::compile(6, 3).unwrap();
    assert_ne!(baseline, challenge(&changed));
    assert!(WorkTreeHistoryPlan::compile(5, 4, [7; 32], [0; 28]).is_err());

    // Frozen N5/S8 encoding from the contract, followed by the independently
    // owned numeric producer. Omitting the wrapper's parent join must diverge.
    let mut expected = Transcript::new(b"generic-height-work-bindings");
    expected.append_bytes(b"historical-prefix-height-work-profile", b"historical-prefix-height-work-owner-stream-v1");
    for (label, value) in [
        ("version", 1), ("n", 5), ("slot-log", 3), ("slots", 8),
        ("input-log", 23), ("row-log", 9), ("height-rows", 256),
        ("height-terms", 160), ("numeric-base", 256),
    ] {
        expected.append_u64(format!("historical-prefix-height-work-{label}").as_bytes(), value);
    }
    expected.append_bytes(b"historical-prefix-height-work-row-convention",
        b"LSB-first;height=32*owner+bit;numeric=32*slots+owner;tag-bit=slot-log+5;numeric-unused-low-bits=zero");
    let height = HeaderHeightLayout::compile(5, 3).unwrap();
    expected.append_bytes(b"historical-prefix-height-work-height-template", height.fingerprint().as_bytes());
    DaaWorkActions::new(small()).unwrap().bind(&mut expected);
    assert_eq!(baseline, expected.challenge_scalar(b"bound"));
}

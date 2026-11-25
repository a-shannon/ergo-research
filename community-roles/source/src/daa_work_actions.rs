#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInteger, Field, PrimeField};
    use num_bigint::BigUint;
    use std::{collections::BTreeMap, sync::OnceLock};

    fn plan3() -> &'static WorkTreeHistoryPlan {
        static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
        PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(3, 2, [7; 32], [0; 28]).unwrap())
    }
    fn plan_large() -> &'static WorkTreeHistoryPlan {
        static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
        PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(1 << 21, 21, [9; 32], [0; 28]).unwrap())
    }
    fn point(bits: usize, index: usize) -> Vec<Fr> {
        (0..bits)
            .map(|b| Fr::from(((index >> b) & 1) as u64))
            .collect()
    }
    fn dense(bits: usize, seed: u64) -> Vec<Fr> {
        (0..bits).map(|b| Fr::from(seed + 19 * b as u64)).collect()
    }
    fn terms(f: &DaaWorkActions<'_>, owner: usize) -> Vec<Term> {
        let mut out = Vec::new();
        let count = f
            .visit_owner(owner, |t| {
                out.push(t);
                Ok(())
            })
            .unwrap();
        assert_eq!(count, out.len());
        out
    }

    #[test]
    fn c367_numeric_lane2_reads_exact_prior_work_endpoints() {
        let source = DaaWorkActions::new(plan_large()).unwrap();
        let emitted = terms(&source, 845_759);
        let work = Endpoints::new().work;
        assert_eq!(work, (987_674..987_898).collect::<Vec<_>>());
        assert_eq!(emitted.len(), 448);
        for (index, term) in emitted.iter().enumerate() {
            let source_owner = if index % 2 == 0 { 845_758 } else { 845_757 };
            let local = work[index / 2];
            assert_eq!(term.row, 845_759);
            assert_eq!(term.gate.left, source_owner * WIDTH + local);
            assert_eq!(term.gate.right, 0);
            assert!(!(crate::daa_history_roster::BANKS[2].0..
                crate::daa_history_roster::BANKS[2].1).contains(&local));
        }
    }

    // Independent native schedule oracle; no production action/mask calls.
    fn oracle_action(n: usize, c: usize) -> NumericAction {
        if c == 0 || c >= n {
            return NumericAction::None;
        }
        if c == 1 {
            return NumericAction::Constant(0x011765000000);
        }
        if c == 417791 || c == 417792 {
            return NumericAction::Constant(0x6f98d5000000);
        }
        if c == 1024 {
            return NumericAction::EqualParent;
        }
        let period = if c >= 844672 { 128 } else { 1024 };
        if c % period == 0 {
            NumericAction::None
        } else {
            NumericAction::EqualParent
        }
    }

    fn oracle_terms(n: usize, c: usize) -> Vec<Term> {
        let selected = oracle_action(n, c);
        if selected == NumericAction::None {
            return vec![];
        }
        let e = Endpoints::new();
        let mut out = Vec::new();
        // Separate loops/order, integer powers and literal owner coordinates.
        for (back, sign) in [(1, Fr::one()), (2, -Fr::one())] {
            if back == 2 && selected != NumericAction::EqualParent {
                continue;
            }
            for b in 0..224 {
                out.push(Term {
                    row: c,
                    gate: Gate {
                        left: (c - back) * (1 << 20) + e.work[b],
                        right: 0,
                        c0: Fr::zero(),
                        c1: sign * Fr::from(2u64).pow([b as u64]),
                        c2: Fr::zero(),
                        c3: Fr::zero(),
                    },
                });
            }
        }
        if let NumericAction::Constant(value) = selected {
            out.push(Term {
                row: c,
                gate: Gate {
                    left: 0,
                    right: 0,
                    c0: -Fr::from(value),
                    c1: Fr::zero(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            });
        }
        out
    }

    fn key(t: &Term) -> (usize, usize, usize, [[u64; 4]; 4]) {
        (
            t.row,
            t.gate.left,
            t.gate.right,
            [t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3].map(|x| x.into_bigint().0),
        )
    }
    fn direct(ts: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let mut out = [Fr::zero(); 4];
        for t in ts {
            let g = &t.gate;
            let w = eq_index(r, t.row) * eq_index(u, g.left) * eq_index(v, g.right);
            for (o, c) in out.iter_mut().zip([g.c0, g.c1, g.c2, g.c3]) {
                *o += w * c;
            }
        }
        out
    }
    fn frontiers() -> Vec<usize> {
        let mut owners = vec![0, 1, 2, 3];
        for boundary in [
            1024, 2048, 3072, 4096, 5120, 6144, 7168, 8192, 9216, 417791, 417792, 418816, 844544,
            844672, 844800,
        ] {
            for c in boundary - 1..=boundary + 1 {
                owners.push(c);
            }
        }
        owners.sort_unstable();
        owners.dedup();
        owners
    }

    #[test]
    fn native_schedule_clipping_and_every_action_frontier() {
        for c in frontiers() {
            for n in [c.max(3), (c + 1).max(3), (c + 2).max(3)] {
                let h = n.next_power_of_two().trailing_zeros() as usize;
                let d = ScheduleDomain::new(n as u64, h).unwrap();
                if c >= n.next_power_of_two() {
                    assert_eq!(
                        action(&d, c),
                        Err("numeric DAA owner outside slot domain".into())
                    );
                } else {
                    assert_eq!(action(&d, c).unwrap(), oracle_action(n, c), "N{n} c{c}");
                }
                assert_eq!(
                    action(&d, n.next_power_of_two()),
                    Err("numeric DAA owner outside slot domain".into())
                );
                if n < n.next_power_of_two() {
                    assert_eq!(action(&d, n).unwrap(), NumericAction::None);
                }
            }
        }
        let d = ScheduleDomain::new(9218, 14).unwrap();
        // Covers all early short-window cases and the first mature boundary.
        for c in 0..9218 {
            assert_eq!(action(&d, c).unwrap(), oracle_action(9218, c), "c{c}");
        }
    }

    #[test]
    fn weighted_producer_and_analytic_consumer_match_independent_oracle() {
        let small = DaaWorkActions::new(plan3()).unwrap();
        assert_eq!((small.row_log(), small.input_log()), (2, 22));
        let expected: Vec<_> = (0..4).flat_map(|c| oracle_terms(3, c)).collect();
        let mut actual: Vec<_> = (0..4)
            .flat_map(|c| terms(&small, c))
            .map(|t| key(&t))
            .collect();
        let mut keys: Vec<_> = expected.iter().map(key).collect();
        actual.sort();
        keys.sort();
        assert_eq!(actual, keys);
        assert_eq!(terms(&small, 1).len(), 225);
        assert_eq!(terms(&small, 2).len(), 448);
        for seed in [3, 47] {
            let r = dense(2, seed);
            let u = dense(22, seed + 1);
            let v = dense(22, seed + 2);
            assert_eq!(
                small.coefficients(&r, &u, &v).unwrap(),
                direct(&expected, &r, &u, &v)
            );
        }
        let large = DaaWorkActions::new(plan_large()).unwrap();
        assert_eq!((large.row_log(), large.input_log()), (21, 41));
        let mut owners = frontiers();
        owners.push((1 << 21) - 1);
        for c in owners {
            let expected = oracle_terms(1 << 21, c);
            let mut keys: Vec<_> = expected.iter().map(key).collect();
            keys.sort();
            let mut actual: Vec<_> = terms(&large, c).iter().map(key).collect();
            actual.sort();
            assert_eq!(actual, keys, "owner{c}");
            // Boolean row isolates one owner; dense endpoints populate all channels.
            let r = point(21, c);
            let u = dense(41, 61);
            let v = dense(41, 71);
            assert_eq!(
                large.coefficients(&r, &u, &v).unwrap(),
                direct(&expected, &r, &u, &v),
                "owner{c}"
            );
        }
        // Mixed row challenge at the large dimension; fixed input coordinate
        // permits at most the child and parent of one work leaf.
        for leaf in [0, 1023, 2047, 417790, 844671, (1 << 21) - 2] {
            let r = dense(21, 17);
            let u = point(41, leaf * WIDTH + Endpoints::new().work[223]);
            let v = point(41, 0);
            let expected: Vec<_> = [leaf + 1, leaf + 2]
                .into_iter()
                .filter(|&c| c < 1 << 21)
                .flat_map(|c| oracle_terms(1 << 21, c))
                .collect();
            assert_eq!(
                large.coefficients(&r, &u, &v).unwrap(),
                direct(&expected, &r, &u, &v)
            );
        }
    }

    fn put(values: &mut BTreeMap<usize, Fr>, slot: usize, wires: &[usize], n: &BigUint) {
        for (b, &w) in wires.iter().enumerate() {
            values.insert(slot * WIDTH + w, Fr::from(n.bit(b as u64) as u64));
        }
    }
    fn assignment(slot: usize, compact: u32, lower: &BigUint) -> BTreeMap<usize, Fr> {
        let e = Endpoints::new();
        let work = work_tree_work::native_decode(compact).unwrap();
        let upper = lower + &work;
        assert!(upper.bits() <= 224);
        let mut values = BTreeMap::new();
        put(&mut values, slot, &e.n_bits, &BigUint::from(compact));
        put(&mut values, slot, &e.lower, lower);
        put(&mut values, slot, &e.work, &work);
        put(&mut values, slot, &e.upper, &upper);
        put(
            &mut values,
            slot,
            &e.work_minus_one,
            &(&work - BigUint::from(1u64)),
        );
        values.insert(
            slot * WIDTH + e.exponent[(compact >> 24) as usize],
            Fr::one(),
        );
        values
    }
    fn residual(t: &Term, values: &BTreeMap<usize, Fr>) -> Fr {
        let g = &t.gate;
        let x = values.get(&g.left).copied().unwrap_or_default();
        let y = values.get(&g.right).copied().unwrap_or_default();
        g.c0 + g.c1 * x + g.c2 * y + g.c3 * x * y
    }
    fn valid_decoder(f: &DaaWorkActions<'_>, slot: usize, values: &BTreeMap<usize, Fr>) {
        let mut rows = BTreeMap::<usize, Fr>::new();
        f.parent
            .work_boundary()
            .emit_slot(slot, |t| {
                *rows.entry(t.row).or_default() += residual(&t, values);
            })
            .unwrap();
        assert!(rows.values().all(|x| x.is_zero()), "decoder slot{slot}");
    }
    fn pair(f: &DaaWorkActions<'_>, c: usize, parent: u32, child: u32) -> BTreeMap<usize, Fr> {
        let mut values = assignment(c - 2, parent, &BigUint::from(0u64));
        let child_values = assignment(
            c - 1,
            child,
            &work_tree_work::native_decode(parent).unwrap(),
        );
        values.extend(child_values);
        valid_decoder(f, c - 2, &values);
        valid_decoder(f, c - 1, &values);
        // Actual B4 interval-continuity family also accepts the recomputed pair.
        let link = f
            .parent
            .work_boundary()
            .links()
            .iter()
            .find(|x| x.name == "work_interval_continuity")
            .unwrap();
        let e = Endpoints::new();
        assert_eq!(link.left_wires, e.lower);
        assert_eq!(link.right_wires, e.upper);
        for (&left, &right) in link.left_wires.iter().zip(&link.right_wires) {
            assert_eq!(
                values[&((c - 1) * WIDTH + left)],
                values[&((c - 2) * WIDTH + right)]
            );
        }
        values
    }
    fn action_residual(f: &DaaWorkActions<'_>, c: usize, values: &BTreeMap<usize, Fr>) -> Fr {
        terms(f, c).iter().map(|t| residual(t, values)).sum()
    }

    #[test]
    fn numeric_faults_fail_with_valid_recomputed_decoders_and_aliases() {
        let f = DaaWorkActions::new(plan_large()).unwrap();
        work_tree_work::integer_bound().unwrap();
        let modulus = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
        assert!((BigUint::from(1u64) << 225usize) < modulus);
        assert!(work_tree_work::native_decode(0x1d010000).is_err());
        for c in [2, 1024, 9217, 844673] {
            let equal_aliases = pair(&f, c, 0x0101ffff, 0x020001ff);
            assert!(action_residual(&f, c, &equal_aliases).is_zero());
            for (parent, child, wanted) in [
                (0x03000001, 0x03000002, Fr::one()),
                (0x03000002, 0x03000001, -Fr::one()),
            ] {
                let values = pair(&f, c, parent, child);
                assert_eq!(action_residual(&f, c, &values), wanted, "owner{c}");
            }
        }
        for c in [417791, 417792] {
            for parent in [0x03000001, 0x03000002] {
                let values = pair(&f, c, parent, 0x066f98d5);
                assert!(
                    action_residual(&f, c, &values).is_zero(),
                    "no carry at reset{c}"
                );
                let bad = pair(&f, c, parent, 0x066f98d4);
                assert_eq!(action_residual(&f, c, &bad), -Fr::from(1u64 << 24));
            }
        }
        let valid = assignment(0, 0x06011765, &BigUint::from(0u64));
        valid_decoder(&f, 0, &valid);
        assert!(action_residual(&f, 1, &valid).is_zero());
        let bad = assignment(0, 0x06011764, &BigUint::from(0u64));
        valid_decoder(&f, 0, &bad);
        assert_eq!(action_residual(&f, 1, &bad), -Fr::from(1u64 << 24));
    }

    #[test]
    fn genesis_constant_is_native_raw_identity_not_an_oracle() {
        let fixture: serde_json::Value = serde_json::from_str(include_str!(
            "../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"
        ))
        .unwrap();
        let hex = fixture["networks"]["mainnet"]["source_headers_hex"][0]
            .as_str()
            .unwrap();
        let raw: Vec<_> = hex
            .as_bytes()
            .chunks_exact(2)
            .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
            .collect();
        assert_eq!(raw.len(), 278);
        let id = ergo_header_core::blake2b256(&raw);
        assert_eq!(id, MAINNET_GENESIS);
        let header = ergo_header_core::Header::decode(&raw, Some(&id)).unwrap();
        assert_eq!((header.height, header.n_bits), (1, GENESIS_NBITS));
        assert_eq!(
            work_tree_work::native_decode(header.n_bits).unwrap(),
            BigUint::from(GENESIS_WORK)
        );
        assert_eq!(
            BigUint::parse_bytes(crate::daa_finish::INITIAL_DIFFICULTY_HEX.as_bytes(), 16).unwrap(),
            BigUint::from(GENESIS_WORK)
        );
        assert_eq!(
            work_tree_work::native_decode(0x066f98d5).unwrap(),
            BigUint::from(RESET_WORK)
        );
        assert_eq!(
            native::V2_RESET_CHILDREN.map(|h| h as usize - 1),
            [CONSTANTS[1].0, CONSTANTS[2].0]
        );
    }

    #[test]
    fn coordinate_and_mask_mutants_are_observable_in_each_channel() {
        let f = DaaWorkActions::new(plan_large()).unwrap();
        let r = point(21, 1024);
        let actual = terms(&f, 1024);
        // Each source, coefficient sign and right-zero coordinate has its own
        // test point; no unrelated parser or domain failure masks the mismatch.
        for index in [0, 1, 2 * 223, 2 * 223 + 1] {
            let g = &actual[index].gate;
            let u = point(41, g.left);
            let v = point(41, 0);
            let expected = f.coefficients(&r, &u, &v).unwrap();
            assert!(!expected[1].is_zero());
            for mutation in 0..3 {
                let mut bad = actual.clone();
                match mutation {
                    0 => bad[index].gate.left ^= WIDTH,
                    1 => bad[index].gate.right = 1024 * WIDTH,
                    _ => bad[index].gate.c1 = -bad[index].gate.c1,
                }
                assert_ne!(
                    direct(&bad, &r, &u, &v),
                    expected,
                    "gate{index} mutation{mutation}"
                );
            }
        }
        let v_local = point(41, 1024 * WIDTH);
        assert_eq!(
            f.coefficients(&r, &point(41, actual[0].gate.left), &v_local)
                .unwrap(),
            [Fr::zero(); 4]
        );
        for c in [1, 417791, 417792] {
            let r = point(21, c);
            let zero = point(41, 0);
            let expected = f.coefficients(&r, &zero, &zero).unwrap();
            assert_eq!(
                expected[0],
                -Fr::from(CONSTANTS.iter().find(|x| x.0 == c).unwrap().1)
            );
            let mut bad = terms(&f, c);
            let last = bad.last_mut().unwrap();
            last.gate.c0 += Fr::one();
            assert_ne!(direct(&bad, &r, &zero, &zero), expected);
            let mut bad = terms(&f, c);
            bad.last_mut().unwrap().gate.left = c * WIDTH;
            assert_ne!(direct(&bad, &r, &zero, &zero), expected);
        }
        // Adding carry at any omitted short/mature owner introduces a nonzero
        // coefficient; dropping singleton/reset similarly changes the family.
        for c in [
            2048, 3072, 4096, 5120, 6144, 7168, 8192, 9216, 844672, 844800,
        ] {
            let r = point(21, c);
            let u = point(41, (c - 1) * WIDTH + Endpoints::new().work[0]);
            let v = point(41, 0);
            assert_eq!(f.coefficients(&r, &u, &v).unwrap(), [Fr::zero(); 4]);
            let bad = vec![Term {
                row: c,
                gate: Gate {
                    left: (c - 1) * WIDTH + Endpoints::new().work[0],
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            }];
            assert_ne!(direct(&bad, &r, &u, &v), [Fr::zero(); 4]);
        }
    }

    #[test]
    fn dimensions_sink_failures_and_bound_dependencies_fail_closed() {
        let f = DaaWorkActions::new(plan3()).unwrap();
        let r = dense(2, 3);
        let u = dense(22, 5);
        let v = dense(22, 7);
        for component in 0..3 {
            for extend in [false, true] {
                let mut points = [r.clone(), u.clone(), v.clone()];
                if extend {
                    points[component].push(Fr::one());
                } else {
                    points[component].pop();
                }
                assert_eq!(
                    f.coefficients(&points[0], &points[1], &points[2]),
                    Err("numeric DAA coefficient point dimensions rejected".into())
                );
            }
        }
        let mut calls = 0;
        assert_eq!(
            f.visit_owner(4, |_| {
                calls += 1;
                Ok(())
            }),
            Err("numeric DAA owner outside slot domain".into())
        );
        assert_eq!(calls, 0);
        for owner in [0, 3] {
            assert_eq!(
                f.visit_owner(owner, |_| {
                    calls += 1;
                    Err("should not run".into())
                }),
                Ok(0)
            );
        }
        assert_eq!(calls, 0);
        for owner in [1, 2] {
            for fail_at in [1, 224, if owner == 1 { 225 } else { 448 }] {
                let mut count = 0;
                assert_eq!(
                    f.visit_owner(owner, |_| {
                        count += 1;
                        if count == fail_at {
                            Err("sink sentinel".into())
                        } else {
                            Ok(())
                        }
                    }),
                    Err("sink sentinel".into())
                );
                assert_eq!(count, fail_at);
            }
        }
        let mut parent_transcript = Transcript::new(b"numeric-daa-test");
        f.parent.bind(&mut parent_transcript);
        let challenge = |binding: &Binding, include_parent: bool| {
            let mut transcript = if include_parent {
                parent_transcript.clone()
            } else {
                Transcript::new(b"numeric-daa-test")
            };
            binding.append(&mut transcript);
            transcript.challenge_scalar(b"r")
        };
        let expected = challenge(&f.binding, true);
        let mut transcript = Transcript::new(b"numeric-daa-test");
        f.bind(&mut transcript);
        assert_eq!(transcript.challenge_scalar(b"r"), expected);
        assert_ne!(challenge(&f.binding, false), expected);
        macro_rules! altered {
            ($body:expr) => {{
                let mut b = f.binding.clone();
                ($body)(&mut b);
                assert_ne!(challenge(&b, true), expected);
            }};
        }
        altered!(|b: &mut Binding| b.schema.push('x'));
        altered!(|b: &mut Binding| b.headers += 1);
        altered!(|b: &mut Binding| b.slot_log += 1);
        altered!(|b: &mut Binding| b.slots += 1);
        altered!(|b: &mut Binding| b.row_log += 1);
        altered!(|b: &mut Binding| b.input_log += 1);
        altered!(|b: &mut Binding| b.coordinates.push('x'));
        altered!(|b: &mut Binding| b.work_schema.push('x'));
        altered!(|b: &mut Binding| b.native_work_sha256.push('x'));
        altered!(|b: &mut Binding| b.canonical_nbits_required = !b.canonical_nbits_required);
        altered!(|b: &mut Binding| b.genesis_nbits ^= 1);
        altered!(|b: &mut Binding| b.singleton_height += 1);
        for i in 0..224 {
            altered!(|b: &mut Binding| b.work_wires[i] ^= 1);
        }
        for i in 0..32 {
            altered!(|b: &mut Binding| b.genesis_id[i] ^= 1);
        }
        for i in 0..3 {
            altered!(|b: &mut Binding| b.constants[i].0 += 1);
            altered!(|b: &mut Binding| b.constants[i].1 ^= 1);
            altered!(|b: &mut Binding| b.mature_schedule[i] += 1);
        }
        for i in 0..7 {
            altered!(|b: &mut Binding| b.short_owners[i] += 1);
        }
    }
}
// Numeric native DAA actions on already decoded positive U224 work endpoints.
// Requires all parent producers under the same commitment; not a history proof.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use serde::Serialize;

use crate::{
    daa_header_window::{self as native, Action},
    daa_integer::Epoch,
    daa_schedule_wiring::{evaluate_mature_shift, ScheduleDomain},
    gkr::Gate,
    header_order::MAINNET_GENESIS,
    sparse::Term,
    transcript::Transcript,
    wiring::{evaluate_shift, RightIndex},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{Endpoints, WIDTH},
    work_tree_wiring::eq_index,
    work_tree_work,
};

const INPUT_LOG: usize = 20;
const WORK_BITS: usize = 224;
const GENESIS_NBITS: u32 = 0x06011765;
const GENESIS_WORK: u64 = 0x011765000000;
const RESET_WORK: u64 = 0x6f98d5000000;
const SHORT_OWNERS: [usize; 7] = [2048, 3072, 4096, 5120, 6144, 7168, 8192];
const CONSTANTS: [(usize, u64); 3] = [
    (1, GENESIS_WORK),
    (417791, RESET_WORK),
    (417792, RESET_WORK),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NumericAction {
    None,
    EqualParent,
    Constant(u64),
}

fn action(domain: &ScheduleDomain, owner: usize) -> Result<NumericAction, String> {
    if owner >= 1usize << domain.slot_log() {
        return Err("numeric DAA owner outside slot domain".into());
    }
    if owner == 0 || owner as u64 >= domain.upper_bound() {
        return Ok(NumericAction::None);
    }
    if owner == 1 {
        return Ok(NumericAction::Constant(GENESIS_WORK));
    }
    let plan = native::for_child_height((owner + 1) as u32)?;
    Ok(match plan.action() {
        Action::Carry => NumericAction::EqualParent,
        Action::FixedV2 => NumericAction::Constant(RESET_WORK),
        Action::Retarget(Epoch::Legacy) if plan.sample_heights().len() == 1 => {
            NumericAction::EqualParent
        }
        Action::Retarget(_) => NumericAction::None,
    })
}

#[derive(Clone, Serialize)]
struct Binding {
    schema: String,
    headers: u64,
    slot_log: usize,
    slots: usize,
    row_log: usize,
    input_log: usize,
    coordinates: String,
    work_wires: Vec<usize>,
    work_schema: String,
    native_work_sha256: String,
    canonical_nbits_required: bool,
    genesis_id: [u8; 32],
    genesis_nbits: u32,
    constants: [(usize, u64); 3],
    singleton_height: u32,
    short_owners: [usize; 7],
    mature_schedule: [u64; 3],
}

impl Binding {
    fn append(&self, transcript: &mut Transcript) {
        transcript.append_bytes(
            b"numeric-daa-work-actions",
            &serde_json::to_vec(self).expect("infallible numeric DAA binding"),
        );
    }
}

/// The borrowed immutable plan makes producer dependencies mandatory at
/// construction. Integration must still put their relations in the same proof.
pub(crate) struct DaaWorkActions<'a> {
    parent: &'a WorkTreeHistoryPlan,
    domain: ScheduleDomain,
    binding: Binding,
    powers: [Fr; WORK_BITS],
}

impl<'a> DaaWorkActions<'a> {
    pub(crate) fn endpoint_parent(&self) -> &WorkTreeHistoryPlan { self.parent }

    /// Inverse routing of this numeric source only; formal GLOBAL0 is retained.
    pub(crate) fn visit_endpoint_terms(&self, left: bool, slot: usize,
        mut sink: impl FnMut(Term)->Result<(),String>) -> Result<usize,String> {
        let slots=1usize.checked_shl(self.domain.slot_log() as u32).ok_or("numeric endpoint slots overflow")?;
        if slot>=slots {return Err("numeric endpoint owner outside slot domain".into());}
        let mut emitted=0usize;
        let mut send=|t:Term| {sink(t)?;emitted=emitted.checked_add(1).ok_or("numeric endpoint count overflow")?;Ok(())};
        if !left {
            if slot==0 {
                for owner in 1..self.domain.upper_bound() as usize {
                    self.visit_owner(owner,&mut send)?;
                }
            }
        } else {
            for delta in [1usize,2] {
                if let Some(owner)=slot.checked_add(delta).filter(|owner|*owner<slots) {
                    self.visit_owner(owner,|t| {
                        // Constants are emitted once by the separate source roster below.
                        if t.gate.left!=0 && t.gate.left/WIDTH==slot {send(t)?;}
                        Ok(())
                    })?;
                }
            }
            if slot==0 {
                for (owner,_) in CONSTANTS {
                    if owner<slots {
                        self.visit_owner(owner,|t| {if t.gate.left==0 {send(t)?;}Ok(())})?;
                    }
                }
            }
        }
        Ok(emitted)
    }

    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan) -> Result<Self, String> {
        work_tree_work::integer_bound()?;
        let domain = ScheduleDomain::new(parent.headers(), parent.slot_log())?;
        let wires = Endpoints::new().work;
        if WIDTH != 1 << INPUT_LOG
            || wires.len() != WORK_BITS
            || wires.iter().any(|&wire| wire >= WIDTH)
        {
            return Err("numeric DAA endpoint geometry changed".into());
        }
        let profile = parent.work_profile();
        profile.validate()?;
        let binding = Binding {
            schema: "native-daa-work-actions-weighted-v1".into(),
            headers: parent.headers(),
            slot_log: parent.slot_log(),
            slots: parent.slots(),
            row_log: parent.slot_log(),
            input_log: INPUT_LOG + parent.slot_log(),
            coordinates: "row=child-height-1; child-leaf=row-1; parent-leaf=row-2; linear-right=GLOBAL0; constant-left=GLOBAL0; LSB-first".into(),
            work_wires: wires,
            work_schema: profile.schema.clone(),
            native_work_sha256: profile.native_work_sha256.clone(),
            canonical_nbits_required: profile.canonical_nbits_required,
            genesis_id: MAINNET_GENESIS,
            genesis_nbits: GENESIS_NBITS,
            constants: CONSTANTS,
            singleton_height: 1025,
            short_owners: SHORT_OWNERS,
            mature_schedule: [native::MAINNET_LEGACY_EPOCH_LENGTH,
                native::MAINNET_EIP37_EPOCH_LENGTH, native::EIP37_FIRST_CHILD as u64],
        };
        let mut powers = [Fr::one(); WORK_BITS];
        for bit in 1..WORK_BITS {
            powers[bit] = powers[bit - 1] + powers[bit - 1];
        }
        Ok(Self {
            parent,
            domain,
            binding,
            powers,
        })
    }

    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        self.parent.bind(transcript);
        self.binding.append(transcript);
    }

    pub(crate) fn row_log(&self) -> usize {
        self.domain.slot_log()
    }
    pub(crate) fn input_log(&self) -> usize {
        INPUT_LOG + self.domain.slot_log()
    }

    pub(crate) fn visit_owner(
        &self,
        owner: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<usize, String> {
        let selected = action(&self.domain, owner)?;
        if selected == NumericAction::None {
            return Ok(0);
        }
        let mut emitted = 0;
        let mut emit = |left, c0, c1| {
            sink(Term {
                row: owner,
                gate: Gate {
                    left,
                    right: 0,
                    c0,
                    c1,
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            })?;
            emitted += 1;
            Ok::<(), String>(())
        };
        for (bit, &wire) in self.binding.work_wires.iter().enumerate() {
            emit((owner - 1) * WIDTH + wire, Fr::zero(), self.powers[bit])?;
            if selected == NumericAction::EqualParent {
                emit((owner - 2) * WIDTH + wire, Fr::zero(), -self.powers[bit])?;
            }
        }
        if let NumericAction::Constant(value) = selected {
            emit(0, -Fr::from(value), Fr::zero())?;
        }
        Ok(emitted)
    }

    fn equality_shift(&self, r: &[Fr], u: &[Fr], v: &[Fr], offset: u64) -> Result<Fr, String> {
        let upper = self.domain.upper_bound();
        let mut weight = evaluate_shift(r, u, v, offset, 2, upper, 0, RightIndex::GlobalZero)?;
        for epoch in [Epoch::Legacy, Epoch::Eip] {
            weight -= evaluate_mature_shift(
                epoch,
                &self.domain,
                r,
                u,
                v,
                offset,
                RightIndex::GlobalZero,
            )?;
        }
        for owner in SHORT_OWNERS
            .into_iter()
            .chain(CONSTANTS[1..].iter().map(|p| p.0))
        {
            if (owner as u64) < upper {
                weight -= evaluate_shift(
                    r,
                    u,
                    v,
                    offset,
                    owner as u64,
                    owner as u64 + 1,
                    0,
                    RightIndex::GlobalZero,
                )?;
            }
        }
        Ok(weight)
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != self.row_log() || u.len() != self.input_log() || v.len() != self.input_log() {
            return Err("numeric DAA coefficient point dimensions rejected".into());
        }
        let (u_low, u_high) = u.split_at(INPUT_LOG);
        let (v_low, v_high) = v.split_at(INPUT_LOG);
        let work_weight: Fr = self
            .binding
            .work_wires
            .iter()
            .enumerate()
            .map(|(bit, &wire)| self.powers[bit] * eq_index(u_low, wire))
            .sum();
        let mut linear = self.equality_shift(r, u_high, v_high, 1)?
            - self.equality_shift(r, u_high, v_high, 2)?;
        let mut constant = Fr::zero();
        for (owner, value) in CONSTANTS {
            if (owner as u64) < self.domain.upper_bound() {
                linear += evaluate_shift(
                    r,
                    u_high,
                    v_high,
                    1,
                    owner as u64,
                    owner as u64 + 1,
                    0,
                    RightIndex::GlobalZero,
                )?;
                constant -= Fr::from(value) * eq_index(r, owner);
            }
        }
        Ok([
            constant * eq_index(u, 0) * eq_index(v, 0),
            linear * work_weight * eq_index(v_low, 0),
            Fr::zero(),
            Fr::zero(),
        ])
    }
}

//! H21 role-1 algebraic differential at a 16-bit cut, with two adjacent owners.
//! Coefficients come from the complete production callback; Boolean input bits
//! cover each full owner domain as deterministic packed data. This is not a
//! byte-table kernel or an authenticated proof.

use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    gkr,
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use ark_bn254::Fr;
use ark_ff::{Field, One, Zero};

const HEADERS: u64 = 1_827_840;
const SLOT_LOG: usize = 21;
const OWNERS: [usize; 2] = [9_214, 9_215];
const INPUT_BITS: usize = 20;
const INPUTS: usize = 1 << INPUT_BITS;
const ROWS: usize = 1 << 19;
const CUT: usize = 16;
const CUT_WIDTH: usize = INPUTS >> CUT;
const EMITTED_PER_OWNER: usize = 396_561;

struct State {
    a: Vec<Fr>,
    b: Vec<Fr>,
    x: Vec<Fr>,
}

impl State {
    fn zeros(width: usize) -> Self {
        Self { a: vec![Fr::zero(); width], b: vec![Fr::zero(); width],
            x: vec![Fr::zero(); width] }
    }
    fn width(&self) -> usize {
        assert_eq!(self.a.len(), self.b.len());
        assert_eq!(self.a.len(), self.x.len());
        self.a.len()
    }
}

struct OwnerData {
    state: State,
    packed: Vec<u8>,
    weighted: Vec<WeightedTerm>,
}

struct WeightedTerm {
    left: usize,
    a: Fr,
    b: Fr,
}

fn synthetic_bit(owner: usize, local: usize) -> bool {
    let mixed = (local as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .rotate_left(17) ^ (owner as u64).wrapping_mul(0xd1b5_4a32_d192_ed03);
    (mixed & 7) == 0 || ((local ^ owner) & 127) == 0
}

fn packed_bit(bytes: &[u8], local: usize) -> Fr {
    Fr::from(((bytes[local >> 3] >> (local & 7)) & 1) as u64)
}

impl OwnerData {
    fn new(owner: usize) -> Self {
        let mut packed = vec![0u8; INPUTS / 8];
        let mut state = State::zeros(INPUTS);
        for local in 0..INPUTS {
            if synthetic_bit(owner, local) {
                packed[local >> 3] |= 1 << (local & 7);
                state.x[local] = Fr::one();
            }
        }
        Self { state, packed, weighted: Vec::with_capacity(EMITTED_PER_OWNER) }
    }
}

/// Admit the entire source stream once, with its physical shape and census.
fn visit_owner(
    roster: &DaaHistoryRoster<'_>, owner: usize,
    mut sink: impl FnMut(&Term, usize, usize, usize) -> Result<(), String>,
) {
    assert_eq!(roster.owner_class(owner as u64).expect("owner class"), OwnerClass::Carry);
    let row_base = owner.checked_mul(ROWS).expect("row base");
    let input_base = owner.checked_mul(INPUTS).expect("input base");
    let mut observed = 0usize;
    let counts = roster.visit_header_terms(owner as u64, |term| {
        let row = term.row.checked_sub(row_base).ok_or("row before owner")?;
        let left = term.gate.left.checked_sub(input_base).ok_or("left before owner")?;
        let right = term.gate.right.checked_sub(input_base).ok_or("right before owner")?;
        if row >= ROWS || left >= INPUTS || right >= INPUTS {
            return Err("role-1 callback term escapes physical owner".into());
        }
        observed = observed.checked_add(1).ok_or("callback count overflow")?;
        sink(&term, row, left, right)
    }).expect("bounded H21 role-1 callback");
    assert_eq!(observed, counts.emitted, "observed owner callback count");
    assert_eq!(observed, EMITTED_PER_OWNER, "complete owner callback census");
    assert_eq!(counts.omitted_worktree, 78_194);
    assert_eq!(counts.omitted_mature_a4, 0);
    assert_eq!(counts.omitted_short_a4, 0);
}

fn dense_coefficients(
    roster: &DaaHistoryRoster<'_>, owners: &mut [OwnerData; 2],
    row_weights: &[Fr],
) -> Fr {
    let mut direct_claim = Fr::zero();
    for j in 0..2 {
        visit_owner(roster, OWNERS[j], |term, row, left, right| {
            let weight = row_weights[row];
            let left_value = packed_bit(&owners[j].packed, left);
            let right_value = packed_bit(&owners[j].packed, right);
            direct_claim += weight * (term.gate.c0 + term.gate.c1 * left_value
                + term.gate.c2 * right_value
                + term.gate.c3 * left_value * right_value);
            let a = weight * (term.gate.c1 + term.gate.c3 * right_value);
            let b = weight * (term.gate.c0 + term.gate.c2 * right_value);
            owners[j].state.a[left] += a;
            owners[j].state.b[left] += b;
            owners[j].weighted.push(WeightedTerm { left, a, b });
            Ok(())
        });
        assert_eq!(owners[j].weighted.len(), EMITTED_PER_OWNER);
    }
    direct_claim
}

/// Independent cut construction: project the admitted, source-derived support
/// without reading the dense A/B tables, and fold *all* packed input bits.
fn compact_cut(owners: &[OwnerData; 2], prefix: &[Fr]) -> [State; 2] {
    assert_eq!(prefix.len(), 1 << CUT);
    let mut cut = [State::zeros(CUT_WIDTH), State::zeros(CUT_WIDTH)];
    for j in 0..2 {
        for local in 0..INPUTS {
            if !packed_bit(&owners[j].packed, local).is_zero() {
                cut[j].x[local >> CUT] += prefix[local & ((1 << CUT) - 1)];
            }
        }
        for term in &owners[j].weighted {
            let weight = prefix[term.left & ((1 << CUT) - 1)];
            cut[j].a[term.left >> CUT] += term.a * weight;
            cut[j].b[term.left >> CUT] += term.b * weight;
        }
    }
    cut
}

fn direct_round(states: [&State; 2]) -> [Fr; 3] {
    let mut q = [Fr::zero(); 3];
    for state in states {
        let width = state.width();
        assert!(width >= 2 && width.is_power_of_two());
        for pair in 0..width / 2 {
            let i = 2 * pair;
            let da = state.a[i + 1] - state.a[i];
            let db = state.b[i + 1] - state.b[i];
            let dx = state.x[i + 1] - state.x[i];
            q[0] += state.a[i] * state.x[i] + state.b[i];
            q[1] += state.a[i] * dx + da * state.x[i] + db;
            q[2] += da * dx;
        }
    }
    q
}

/// Endpoint evaluation and interpolation, separate from direct coefficients.
fn interpolated_round(states: [&State; 2]) -> [Fr; 3] {
    let mut values = [Fr::zero(); 3];
    for state in states {
        for pair in 0..state.width() / 2 {
            let i = 2 * pair;
            for (t, value) in values.iter_mut().enumerate() {
                let z = Fr::from(t as u64);
                let a = state.a[i] + z * (state.a[i + 1] - state.a[i]);
                let b = state.b[i] + z * (state.b[i + 1] - state.b[i]);
                let x = state.x[i] + z * (state.x[i + 1] - state.x[i]);
                *value += a * x + b;
            }
        }
    }
    let two = Fr::from(2u64);
    let c2 = (values[2] - two * values[1] + values[0])
        * two.inverse().expect("2 invertible in Fr");
    let c1 = values[1] - values[0] - c2;
    [values[0], c1, c2]
}

fn fold_dense(state: &mut State, challenge: Fr) {
    gkr::fold(&mut state.a, challenge);
    gkr::fold(&mut state.b, challenge);
    gkr::fold(&mut state.x, challenge);
}

fn fold_compact(state: &mut State, challenge: Fr) {
    let half = state.width() / 2;
    for values in [&mut state.a, &mut state.b, &mut state.x] {
        for i in 0..half {
            let low = values[2 * i];
            let high = values[2 * i + 1];
            values[i] = (Fr::one() - challenge) * low + challenge * high;
        }
        values.truncate(half);
    }
}

fn initial_claim(states: [&State; 2]) -> Fr {
    states.into_iter().fold(Fr::zero(), |acc, state| {
        acc + (0..state.width()).fold(Fr::zero(), |sum, i| {
            sum + state.a[i] * state.x[i] + state.b[i]
        })
    })
}

#[test]
fn adjacent_h21_role1_cut16_matches_dense_oracle_and_owner_round() {
    assert_eq!(OWNERS[0] ^ 1, OWNERS[1], "adjacent owner coordinate");
    let plan = WorkTreeHistoryPlan::compile(HEADERS, SLOT_LOG, [0x35; 32], [0x35; 28])
        .expect("pinned H21 fixture plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("H21 DAA roster");

    // Owner-high coordinates select exactly these adjacent IDs. The low owner
    // coordinate is not evaluated until its sumcheck round after all 20 local
    // rounds; applying its weight here would count it twice.
    let row_point: Vec<_> = (0..19).map(|bit| Fr::from((3 * bit + 2) as u64)).collect();
    let row_weights = gkr::eq_weights(&row_point);
    assert_eq!(row_weights.len(), ROWS);

    let mut owners = [OwnerData::new(OWNERS[0]), OwnerData::new(OWNERS[1])];
    let direct_claim = dense_coefficients(&roster, &mut owners, &row_weights);
    let mut claim = initial_claim([&owners[0].state, &owners[1].state]);
    assert_eq!(claim, direct_claim, "direct source gate evaluation equals A/B reduction");
    assert!(!claim.is_zero(), "synthetic witness must give a nonzero initial claim");

    let challenges: Vec<_> = (0..INPUT_BITS).map(|round| Fr::from((5 * round + 3) as u64)).collect();
    for (round, challenge) in challenges.iter().take(CUT).enumerate() {
        let q = direct_round([&owners[0].state, &owners[1].state]);
        assert_eq!(q[0] + gkr::eval_polynomial(&q, Fr::one()), claim,
            "dense local sumcheck identity at round {round}");
        claim = gkr::eval_polynomial(&q, *challenge);
        for owner in &mut owners { fold_dense(&mut owner.state, *challenge); }
    }

    let prefix = gkr::eq_weights(&challenges[..CUT]);
    let mut compact = compact_cut(&owners, &prefix);
    for j in 0..2 {
        assert_eq!(owners[j].state.width(), CUT_WIDTH);
        assert_eq!(compact[j].a, owners[j].state.a, "A at cut, owner {j}");
        assert_eq!(compact[j].b, owners[j].state.b, "B at cut, owner {j}");
        assert_eq!(compact[j].x, owners[j].state.x, "full-domain X at cut, owner {j}");
        assert!(compact[j].x[CUT_WIDTH / 2..].iter().any(|value| !value.is_zero()),
            "exterior half must participate in the packed X fold");
    }
    assert_eq!(initial_claim([&compact[0], &compact[1]]), claim,
        "independent cut claim");

    // Mutant: folding A*X as one linear table erases the degree-two term.
    let first_cut_round = direct_round([&compact[0], &compact[1]]);
    assert!(!first_cut_round[2].is_zero(), "actual cut needs a quadratic term");
    let r16 = challenges[CUT];
    let linearized = first_cut_round[0]
        + r16 * (gkr::eval_polynomial(&first_cut_round, Fr::one()) - first_cut_round[0]);
    assert_ne!(linearized, gkr::eval_polynomial(&first_cut_round, r16),
        "nonlinear-fold mutant must be detected");

    for round in CUT..INPUT_BITS {
        let dense_q = direct_round([&owners[0].state, &owners[1].state]);
        let compact_q = interpolated_round([&compact[0], &compact[1]]);
        assert_eq!(compact_q, dense_q, "degree-two message at local round {round}");
        assert_eq!(compact_q[0] + gkr::eval_polynomial(&compact_q, Fr::one()), claim,
            "shared local sumcheck claim at round {round}");
        let challenge = challenges[round];
        claim = gkr::eval_polynomial(&compact_q, challenge);
        for owner in &mut owners { fold_dense(&mut owner.state, challenge); }
        for state in &mut compact { fold_compact(state, challenge); }
        for j in 0..2 {
            assert_eq!(compact[j].a, owners[j].state.a, "A after round {round}, owner {j}");
            assert_eq!(compact[j].b, owners[j].state.b, "B after round {round}, owner {j}");
            assert_eq!(compact[j].x, owners[j].state.x, "X after round {round}, owner {j}");
        }
    }

    // The first owner round is formed only after both owner contributions are
    // present. Interpolation tests its cross-owner quadratic product.
    assert_eq!(compact[0].width(), 1);
    assert_eq!(compact[1].width(), 1);
    let owner_state = [
        compact[0].a[0], compact[1].a[0],
        compact[0].b[0], compact[1].b[0],
        compact[0].x[0], compact[1].x[0],
    ];
    let [a0, a1, b0, b1, x0, x1] = owner_state;
    let owner_q = [
        a0 * x0 + b0,
        a0 * (x1 - x0) + (a1 - a0) * x0 + (b1 - b0),
        (a1 - a0) * (x1 - x0),
    ];
    assert!(!owner_q[2].is_zero(), "two owners must expose a cross-owner product");
    assert_eq!(owner_q[0] + gkr::eval_polynomial(&owner_q, Fr::one()), claim,
        "first owner-round sumcheck identity");
    let owner_challenge = Fr::from(7u64);
    let owner_result = gkr::eval_polynomial(&owner_q, owner_challenge);
    let interpolated_result =
        (a0 + owner_challenge * (a1 - a0))
            * (x0 + owner_challenge * (x1 - x0))
            + b0 + owner_challenge * (b1 - b0);
    assert_eq!(owner_result, interpolated_result, "owner-round terminal expression");
    let cross_owner_mutant = owner_q[0]
        + owner_challenge * (gkr::eval_polynomial(&owner_q, Fr::one()) - owner_q[0]);
    assert_ne!(cross_owner_mutant, owner_result,
        "independent owner products cannot be linearly folded");
    println!("C262_H21_TWO_OWNER_CUT16_PASS owners=9214,9215 local_rounds=20 cut=16 full_domain_bits_per_owner={INPUTS} source_terms_per_owner={EMITTED_PER_OWNER} owner_round=1 source_byte_table=false authenticated_proof=false");
}

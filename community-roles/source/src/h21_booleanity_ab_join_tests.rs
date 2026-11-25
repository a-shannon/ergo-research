//! Bounded H21 Carry-pair A/B initializer; no production admission or proof.
//! Family qualification and residual partitioning are cold, explicit costs.
//! The hot producer sees no family Terms, oracle arrays, or folded X advice.
use crate::{daa_history_roster::{DaaHistoryRoster, OwnerClass}, gkr::{self, Gate},
    sparse::Term, work_tree_history_plan::WorkTreeHistoryPlan};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

const OWNERS: [usize; 2] = [9_214, 9_215];
const INPUTS: usize = 1 << 20;
const ROWS: usize = 1 << 19;
const ROW: usize = 35_592;
const X: usize = 524_288;
const USED: usize = 69_680;
const FAMILY: usize = 131_072;
const TOTAL: usize = 396_561;
const RESIDUAL: usize = TOTAL - FAMILY;
const CUT: usize = 16;

fn sha(bytes: &[u8]) -> String {
    crate::native_prefix_auth_plan::role0_sha256(bytes).unwrap().iter()
        .map(|b| format!("{b:02X}")).collect()
}

fn source_pins() {
    for (bytes, pin) in [
        (&include_bytes!("serializer.rs")[..], "52C6D954F0E11EAE2749DCE34692941C457BEB50F598FFEED16848383071323A"),
        (&include_bytes!("daa_history_roster.rs")[..], "5C4CDFACE845FD7A8BFFE562ADC3BC1356CE1F30A7CBA7623F8EC03280BD5152"),
        (&include_bytes!("header_history_boundary.rs")[..], "C110376EF38F70A2B64EEE96E2322E5520796F8CE1DEE68349D459B6FF4C6BF5"),
        (&include_bytes!("gkr.rs")[..], "9865DEF9F349BE8C63DE92CD8E0419480DAD1964C9AFCF7B2FE933003D99A751"),
        (&include_bytes!("sparse.rs")[..], "7C0B197105F2B567B03BF3FA050ABED7CEE257C16BBA04B331FD4A8ECAA7CD12"),
        (&include_bytes!("work_tree_history_plan.rs")[..], "4F74DB124431BDF5AC425A8D7BDE1B5C5CE5A7E29EDF174A34C3C09D80759E2D"),
    ] { assert_eq!(sha(bytes), pin, "sealed source bytes"); }
}

fn expected(i: usize) -> Term {
    assert!(i < FAMILY);
    Term { row: ROW + i, gate: Gate { left: X + i,
        right: if i < USED { X + i } else { X }, c0: Fr::zero(),
        c1: if i < USED { -Fr::one() } else { Fr::one() }, c2: Fr::zero(),
        c3: if i < USED { Fr::one() } else { Fr::zero() } } }
}

fn family_identity(i: usize, t: &Term) -> Result<(), &'static str> {
    if i >= FAMILY || t != &expected(i) { Err("family ordered tuple identity") } else { Ok(()) }
}

fn family_count(count: usize) -> Result<(), &'static str> {
    if count == FAMILY { Ok(()) } else { Err("family multiplicity") }
}

// This is the actual H21 visitor, including retirement and checked owner windows.
fn visit(roster: &DaaHistoryRoster<'_>, owner: usize, mut f: impl FnMut(Term)) {
    assert_eq!(roster.owner_class(owner as u64).unwrap(), OwnerClass::Carry);
    let mut seen = 0;
    let counts = roster.visit_header_terms(owner as u64, |mut t| {
        t.row = t.row.checked_sub(owner * ROWS).ok_or("row before owner")?;
        t.gate.left = t.gate.left.checked_sub(owner * INPUTS).ok_or("left before owner")?;
        t.gate.right = t.gate.right.checked_sub(owner * INPUTS).ok_or("right before owner")?;
        if t.row >= ROWS || t.gate.left >= INPUTS || t.gate.right >= INPUTS {
            return Err("H21 tuple escapes owner".into());
        }
        f(t); seen += 1; Ok(())
    }).unwrap();
    assert_eq!((seen, counts.emitted, counts.omitted_worktree,
        counts.omitted_mature_a4, counts.omitted_short_a4), (TOTAL, TOTAL, 78_194, 0, 0));
}

struct Seal { residual: Vec<Term>, qualification_callbacks: usize }
impl Seal {
    fn qualify(roster: &DaaHistoryRoster<'_>) -> Self {
        source_pins();
        let mut residual = Vec::with_capacity(RESIDUAL);
        for (j, owner) in OWNERS.into_iter().enumerate() {
            let (mut family, mut rest) = (0, 0);
            visit(roster, owner, |t| {
                if (ROW..ROW + FAMILY).contains(&t.row) {
                    family_identity(family, &t).unwrap(); family += 1;
                } else {
                    if j == 0 { residual.push(t); }
                    else { assert_eq!(residual[rest], t, "Carry residual topology differs"); }
                    rest += 1;
                }
            });
            family_count(family).unwrap();
            assert_eq!(rest, RESIDUAL);
        }
        assert_eq!(residual.len(), RESIDUAL);
        Self { residual, qualification_callbacks: 2 * TOTAL }
    }
}

// Private immutable owner/packet capability; it grants no production authority.
struct Packet { owner: usize, bytes: Vec<u8>, digest: String }
impl Packet {
    fn fixture(owner: usize) -> Self {
        let mut bytes: Vec<u8> = (0..INPUTS / 8).map(|i|
            ((i * 37 + (i / 251) * 19 + owner * 13) & 255) as u8).collect();
        bytes[(X + USED) / 8..(X + FAMILY) / 8].fill(0);
        set_bit(&mut bytes, 0, owner & 1 != 0);
        set_bit(&mut bytes, X, owner & 1 == 0);
        set_bit(&mut bytes, X + 1, false); // visible sign/omission site with X[X]=1.
        set_bit(&mut bytes, X + USED - 1, false); // last-used omission is observable.
        set_bit(&mut bytes, X + FAMILY, true); // adjacent bank survives later X folds.
        let digest = sha(&bytes);
        Self { owner, bytes, digest }
    }
    fn bit(&self, i: usize) -> Fr { Fr::from(((self.bytes[i / 8] >> (i & 7)) & 1) as u64) }
    fn padding(&self) -> Result<(), &'static str> {
        if self.bytes[(X + USED) / 8..(X + FAMILY) / 8].iter().any(|b| *b != 0) {
            Err("nonzero serializer padding")
        } else { Ok(()) }
    }
}
fn set_bit(bytes: &mut [u8], i: usize, value: bool) {
    if value { bytes[i / 8] |= 1 << (i & 7); } else { bytes[i / 8] &= !(1 << (i & 7)); }
}

struct Prepared { local: Vec<Fr>, owner_factors: [Fr; 2], signed: [Vec<Fr>; 2] }
impl Prepared {
    fn new() -> Self {
        let r: Vec<Fr> = (0..19).map(|j| Fr::from((3 * j + 2) as u64)).collect();
        let local = gkr::eq_weights(&r);
        // A genuine 21-coordinate row-owner point, supported on this sibling pair.
        // Its low coordinate is independent of the later input-owner challenge.
        let row_owners: Vec<Fr> = (0..21).map(|j| if j == 0 { Fr::from(13u64) }
            else { Fr::from(((OWNERS[0] >> j) & 1) as u64) }).collect();
        let owner_factors = std::array::from_fn(|j| row_owners.iter().enumerate()
            .fold(Fr::one(), |w, (k, r)| w * if (OWNERS[j] >> k) & 1 == 1 { *r } else { Fr::one() - r }));
        assert_eq!(owner_factors, [-Fr::from(12u64), Fr::from(13u64)]);
        let signed = std::array::from_fn(|j| (0..FAMILY).map(|i| {
            let weight = owner_factors[j] * local[ROW + i];
            if i < USED { -weight } else { weight }
        }).collect());
        Self { local, owner_factors, signed }
    }
}

#[derive(Default, Debug, PartialEq, Eq, serde::Serialize)]
struct HotCost {
    aligned_loads: usize, loaded_bytes: usize, family_bit_tests: usize,
    shifts: usize, masks: usize, divisions: usize, fr_conversions: usize,
    fr_muls: usize, fr_adds: usize, family_assignments: usize, residual_callbacks: usize,
    zeroed_vector_bytes: usize, prepared_weight_reads: usize,
}
impl HotCost {
    fn mul(&mut self, a: Fr, b: Fr) -> Fr { self.fr_muls += 1; a * b }
    fn add(&mut self, a: Fr, b: Fr) -> Fr { self.fr_adds += 1; a + b }
    fn right(&mut self, packet: &Packet, i: usize) -> Fr {
        self.divisions += 1; self.masks += 2; self.shifts += 1; self.fr_conversions += 1;
        Fr::from(((packet.bytes[i / 8] >> (i & 7)) & 1) as u64)
    }
    fn check(&self, packet: &Packet) {
        let used_ones = packet.bytes[X / 8..(X + USED) / 8].iter()
            .map(|b| b.count_ones() as usize).sum::<usize>();
        assert_eq!(self, &Self { aligned_loads: 1_089, loaded_bytes: 8_712,
            family_bit_tests: USED, shifts: USED + RESIDUAL, masks: USED + 2 * RESIDUAL,
            divisions: RESIDUAL, fr_conversions: RESIDUAL, fr_muls: 5 * RESIDUAL,
            fr_adds: 4 * RESIDUAL, family_assignments: FAMILY, residual_callbacks: RESIDUAL,
            zeroed_vector_bytes: 2 * INPUTS * std::mem::size_of::<Fr>(),
            prepared_weight_reads: FAMILY - used_ones });
    }
}
struct AB { a: Vec<Fr>, b: Vec<Fr> }
impl AB {
    fn zero() -> Self { Self { a: vec![Fr::zero(); INPUTS], b: vec![Fr::zero(); INPUTS] } }
    fn fold(&mut self, r: Fr) { gkr::fold(&mut self.a, r); gkr::fold(&mut self.b, r); }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum InitFault { None, Sign, Omit, LastUsedMask, PadAsBoolean, ConflateGlobalZero, RowShift }

fn initialize_family(p: &Prepared, j: usize, packet: &Packet, a: &mut [Fr], cost: &mut HotCost) {
    initialize_family_fault(p, j, packet, a, cost, InitFault::None)
}
fn initialize_family_fault(p: &Prepared, j: usize, packet: &Packet, a: &mut [Fr],
    cost: &mut HotCost, fault: InitFault) {
    assert_eq!(packet.owner, OWNERS[j], "packet owner identity");
    assert_eq!(packet.bytes.len(), INPUTS / 8);
    assert_eq!(a.len(), FAMILY);
    for word in 0..USED.div_ceil(64) {
        let byte = X / 8 + word * 8;
        let bits = u64::from_le_bytes(packet.bytes[byte..byte + 8].try_into().unwrap());
        cost.aligned_loads += 1; cost.loaded_bytes += 8;
        for lane in 0..(USED - word * 64).min(64) {
            let i = word * 64 + lane;
            cost.family_bit_tests += 1; cost.shifts += 1; cost.masks += 1;
            let bit = if fault == InitFault::ConflateGlobalZero && i == 0 {
                (packet.bytes[0] & 1) as u64
            } else { (bits >> lane) & 1 };
            a[i] = if bit == 0 { cost.prepared_weight_reads += 1; p.signed[j][i] } else { Fr::zero() };
            if i == 1 && fault == InitFault::Sign { a[i] = -a[i]; }
            if (i == 1 && fault == InitFault::Omit)
                || (i == USED - 1 && fault == InitFault::LastUsedMask) { a[i] = Fr::zero(); }
            if i == 1 && fault == InitFault::RowShift {
                a[i] = -p.owner_factors[j] * p.local[ROW + i + 1];
            }
            cost.family_assignments += 1;
        }
    }
    for i in USED..FAMILY {
        a[i] = p.signed[j][i]; cost.family_assignments += 1; cost.prepared_weight_reads += 1;
    }
    if fault == InitFault::PadAsBoolean { a[USED] = -a[USED]; }
}

fn produce(seal: &Seal, p: &Prepared, j: usize, packet: &Packet) -> (AB, HotCost) {
    let mut out = AB::zero();
    let mut cost = HotCost { zeroed_vector_bytes: 2 * INPUTS * std::mem::size_of::<Fr>(), ..HotCost::default() };
    initialize_family(p, j, packet, &mut out.a[X..X + FAMILY], &mut cost);
    for t in &seal.residual {
        let g = &t.gate;
        let weight = cost.mul(p.owner_factors[j], p.local[t.row]);
        let xr = cost.right(packet, g.right);
        let a_product = cost.mul(g.c3, xr);
        let a_sum = cost.add(g.c1, a_product);
        let a = cost.mul(weight, a_sum);
        out.a[g.left] = cost.add(out.a[g.left], a);
        let b_product = cost.mul(g.c2, xr);
        let b_sum = cost.add(g.c0, b_product);
        let b = cost.mul(weight, b_sum);
        out.b[g.left] = cost.add(out.b[g.left], b);
        cost.residual_callbacks += 1;
    }
    cost.check(packet); (out, cost)
}

// Independent literal oracle: all actual roster Terms, no descriptor/partition.
fn oracle(roster: &DaaHistoryRoster<'_>, p: &Prepared, j: usize, packet: &Packet) -> (AB, Fr) {
    let mut out = AB::zero(); let mut direct = Fr::zero();
    visit(roster, OWNERS[j], |t| {
        let g = t.gate; let weight = p.owner_factors[j] * p.local[t.row];
        let xl = packet.bit(g.left); let xr = packet.bit(g.right);
        direct += weight * (g.c0 + g.c1 * xl + g.c2 * xr + g.c3 * xl * xr);
        out.a[g.left] += weight * (g.c1 + g.c3 * xr);
        out.b[g.left] += weight * (g.c0 + g.c2 * xr);
    });
    (out, direct)
}

fn message(states: &[AB; 2], x: &[Vec<Fr>; 2]) -> [Fr; 3] {
    let mut q = [Fr::zero(); 3];
    for j in 0..2 {
        let local = gkr::quadratic_message(&states[j].a, &states[j].b, &x[j]);
        for k in 0..3 { q[k] += local[k]; }
    }
    q
}

fn identity_mutants() {
    for i in [0, USED - 1, USED, FAMILY - 1] {
        let good = expected(i); family_identity(i, &good).unwrap();
        let mut bad = good.clone(); bad.row += 1;
        assert!(family_identity(i, &bad).is_err());
        let mut bad = good.clone(); bad.gate.left += INPUTS;
        assert!(family_identity(i, &bad).is_err());
        let mut bad = good.clone(); bad.gate.c1 = -bad.gate.c1;
        assert!(family_identity(i, &bad).is_err());
        let mut bad = good.clone(); bad.gate.c0 = Fr::one();
        assert!(family_identity(i, &bad).is_err());
        let mut bad = good.clone(); bad.gate.c2 = Fr::one();
        assert!(family_identity(i, &bad).is_err());
    }
    let mut pad = expected(USED); pad.gate.right = 0;
    assert!(family_identity(USED, &pad).is_err(), "padding right is owner-local serializer zero");
    let mut boundary = expected(USED); boundary.gate.right = X + USED;
    boundary.gate.c1 = -Fr::one(); boundary.gate.c3 = Fr::one();
    assert!(family_identity(USED, &boundary).is_err(), "padding is not Booleanity");
    let mut missing_c3 = expected(1); missing_c3.gate.c3 = Fr::zero();
    assert!(family_identity(1, &missing_c3).is_err());
    assert!(family_count(FAMILY - 1).is_err()); assert!(family_count(FAMILY + 1).is_err());
}

// Expected deltas are frozen analytic functions of the declared row point,
// independently recomputed before the candidate mutant is evaluated.
fn independent_weight(i: usize) -> Fr {
    let row = ROW + i;
    let mut w = -Fr::from(12u64); // owner9214's row-owner factor, not its U challenge.
    for j in 0..19 {
        let r = Fr::from((3 * j + 2) as u64);
        w *= if (row >> j) & 1 == 1 { r } else { Fr::one() - r };
    }
    w
}
fn initializer_mutants(p: &Prepared, packet: &Packet) {
    let mut baseline = vec![Fr::zero(); FAMILY];
    initialize_family(p, 0, packet, &mut baseline, &mut HotCost::default());
    // Each fault changes one A coordinate; all other family cells must match.
    let cases = [
        (InitFault::Sign, 1, independent_weight(1) + independent_weight(1)),
        (InitFault::Omit, 1, independent_weight(1)),
        (InitFault::LastUsedMask, USED - 1, independent_weight(USED - 1)),
        (InitFault::PadAsBoolean, USED, -(independent_weight(USED) + independent_weight(USED))),
        (InitFault::ConflateGlobalZero, 0, -independent_weight(0)),
        (InitFault::RowShift, 1, independent_weight(1) - independent_weight(2)),
    ];
    for (fault, index, expected_delta) in cases {
        assert!(!expected_delta.is_zero(), "isolated mutant must be sensitive");
        let mut mutant = vec![Fr::zero(); FAMILY];
        initialize_family_fault(p, 0, packet, &mut mutant, &mut HotCost::default(), fault);
        for i in 0..FAMILY {
            assert_eq!(mutant[i] - baseline[i], if i == index { expected_delta } else { Fr::zero() },
                "isolated family initializer delta at {i}, selected index {index}");
        }
    }
}

#[test]
fn c295_h21_booleanity_ab_join_full_local_and_first_owner_round() {
    identity_mutants();
    let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x35; 32], [0x35; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&plan).unwrap();
    let qualify_start = std::time::Instant::now();
    let seal = Seal::qualify(&roster);
    let qualification_ns = qualify_start.elapsed().as_nanos();
    let prepare_start = std::time::Instant::now();
    let prepared = Prepared::new();
    let preparation_ns = prepare_start.elapsed().as_nanos();
    let packets = OWNERS.map(Packet::fixture);
    for packet in &packets { packet.padding().unwrap(); assert_eq!(sha(&packet.bytes), packet.digest); }
    initializer_mutants(&prepared, &packets[0]);
    let mut hot = Vec::with_capacity(2);
    let mut producer_ns = Vec::with_capacity(2);
    let mut candidate: [AB; 2] = std::array::from_fn(|j| {
        let start = std::time::Instant::now();
        let (state, cost) = produce(&seal, &prepared, j, &packets[j]);
        producer_ns.push(start.elapsed().as_nanos()); hot.push(cost); state
    });
    let mut direct = Fr::zero();
    let mut literal: [AB; 2] = std::array::from_fn(|j| {
        let (state, value) = oracle(&roster, &prepared, j, &packets[j]); direct += value; state
    });
    let mut x: [Vec<Fr>; 2] = std::array::from_fn(|j|
        (0..INPUTS).map(|i| packets[j].bit(i)).collect());
    for j in 0..2 { assert_eq!(candidate[j].a, literal[j].a); assert_eq!(candidate[j].b, literal[j].b); }
    let reduced: Fr = (0..2).flat_map(|j| (0..INPUTS).map(move |i| (j, i)))
        .map(|(j, i)| candidate[j].a[i] * x[j][i] + candidate[j].b[i]).sum();
    assert_eq!(reduced, direct, "independent direct gates equal weighted A/B reduction");

    // At byte/word boundary the last 16 padding lanes must be ignored by A.
    let mut pad_packet = Packet::fixture(OWNERS[0]);
    set_bit(&mut pad_packet.bytes, X + USED, true);
    assert_eq!(pad_packet.padding(), Err("nonzero serializer padding"));
    let pad_delta = prepared.owner_factors[0] * prepared.local[ROW + USED];
    assert!(!pad_delta.is_zero()); // literal padding residual changes by exactly W.
    let mut family = vec![Fr::zero(); FAMILY]; let mut pad_family = vec![Fr::zero(); FAMILY];
    let mut family_cost = HotCost::default(); let mut pad_cost = HotCost::default();
    initialize_family(&prepared, 0, &packets[0], &mut family, &mut family_cost);
    initialize_family(&prepared, 0, &pad_packet, &mut pad_family, &mut pad_cost);
    assert_eq!(family, pad_family, "padding X must not change family initial A");
    assert_eq!(family_cost, pad_cost);
    // Global X(o,0) differs from source-zero; the family never reads global X0.
    set_bit(&mut pad_packet.bytes, 0, true);
    initialize_family(&prepared, 0, &pad_packet, &mut pad_family, &mut HotCost::default());
    assert_eq!(family, pad_family, "global X0 invariant for family initializer");
    let t = expected(USED);
    assert_eq!(pad_delta * pad_packet.bit(t.gate.left), pad_delta);
    drop(family); drop(pad_family);

    // Isolated initial-A omission/sign controls at used i=1, where (X0,X1)=(1,0).
    // Mutant-minus-baseline first U vectors are [0,W,-W] and [0,2W,-2W].
    let w = prepared.owner_factors[0] * prepared.local[ROW + 1];
    for delta in [w, w + w] {
        assert!(!delta.is_zero());
        let a0 = [Fr::zero(), Fr::zero()]; let b = [Fr::zero(); 2];
        let a1 = [Fr::zero(), delta]; let pair_x = [Fr::one(), Fr::zero()];
        let base = gkr::quadratic_message(&a0, &b, &pair_x);
        let mutant = gkr::quadratic_message(&a1, &b, &pair_x);
        assert_eq!([mutant[0] - base[0], mutant[1] - base[1], mutant[2] - base[2]],
            [Fr::zero(), delta, -delta]);
    }

    let initial_capacity = candidate.iter().chain(literal.iter())
        .map(|s| s.a.capacity() + s.b.capacity()).sum::<usize>()
        + x.iter().map(Vec::capacity).sum::<usize>();
    let mut claim = reduced;
    let challenges: Vec<Fr> = (0..20).map(|k| Fr::from((5 * k + 3) as u64)).collect();
    for round in 0..20 {
        let q = message(&candidate, &x); let reference = message(&literal, &x);
        assert_eq!(q, reference, "full initial A/B downstream message round {round}");
        assert_eq!(q[0] + gkr::eval_polynomial(&q, Fr::one()), claim);
        if round == CUT { assert!(!q[2].is_zero(), "cut needs quadratic coefficient"); }
        let challenge = challenges[round]; claim = gkr::eval_polynomial(&q, challenge);
        for j in 0..2 {
            candidate[j].fold(challenge); literal[j].fold(challenge); gkr::fold(&mut x[j], challenge);
            assert_eq!(candidate[j].a, literal[j].a); assert_eq!(candidate[j].b, literal[j].b);
        }
        if round + 1 == CUT {
            let prefix = gkr::eq_weights(&challenges[..CUT]);
            for j in 0..2 {
                let mut direct_x = vec![Fr::zero(); INPUTS >> CUT];
                for i in 0..INPUTS { direct_x[i >> CUT] += packets[j].bit(i) * prefix[i & ((1 << CUT) - 1)]; }
                assert_eq!(direct_x, x[j], "independent complete-X cut owner {j}");
                let neighbor_delta = prefix[(X + FAMILY) & ((1 << CUT) - 1)];
                assert!(!neighbor_delta.is_zero(), "adjacent-bank bit influences cut X");
            }
        }
    }
    let (a0, a1) = (candidate[0].a[0], candidate[1].a[0]);
    let (b0, b1) = (candidate[0].b[0], candidate[1].b[0]);
    let (x0, x1) = (x[0][0], x[1][0]);
    let q = [a0 * x0 + b0, a0 * (x1 - x0) + (a1 - a0) * x0 + b1 - b0,
        (a1 - a0) * (x1 - x0)];
    assert_eq!(q[0] + gkr::eval_polynomial(&q, Fr::one()), claim);
    assert!(!q[2].is_zero(), "owner handoff must expose cross-owner product");
    let owner_challenge = Fr::from(7u64);
    let actual = gkr::eval_polynomial(&q, owner_challenge);
    assert_eq!(actual, (a0 + owner_challenge * (a1 - a0)) * (x0 + owner_challenge * (x1 - x0))
        + b0 + owner_challenge * (b1 - b0));
    assert_ne!(actual, q[0] + owner_challenge * (gkr::eval_polynomial(&q, Fr::one()) - q[0]));

    assert_eq!(seal.qualification_callbacks, 2 * TOTAL);
    assert_eq!(std::mem::size_of::<Fr>(), 32); assert_eq!(std::mem::size_of::<Term>(), 152);
    println!("C295_H21_BOOL_AB_JOIN {}", serde_json::json!({
        "schema": 1, "owners": OWNERS, "family_terms_each": FAMILY, "residual_terms_each": RESIDUAL,
        "cold_source_callbacks": seal.qualification_callbacks, "oracle_callbacks": 2 * TOTAL,
        "signed_weight_prepare_muls": 2 * FAMILY, "signed_weight_prepare_negs": 2 * USED,
        "signed_weight_capacity_bytes": prepared.signed.iter().map(|v| v.capacity() * 32).sum::<usize>(),
        "residual_capacity_bytes": seal.residual.capacity() * 152,
        "local_row_weights_capacity_bytes": prepared.local.capacity() * 32,
        "packets_capacity_bytes": packets.iter().map(|v| v.bytes.capacity()).sum::<usize>(),
        "candidate_and_oracle_AB_shared_X_capacity_bytes": initial_capacity * 32,
        "hot": hot, "packet_sha256": packets.iter().map(|v| v.digest.as_str()).collect::<Vec<_>>(),
        "qualification_ns": qualification_ns, "preparation_ns": preparation_ns,
        "instrumented_producer_ns": producer_ns,
        "local_rounds": 20, "cut": CUT, "owner_rounds": 1, "family_padding_validation": true,
        "baseline_residual_validation": false, "initializer_mutants": 6,
        "authenticated_proof": false, "all_owner_cost": false
    }));
}

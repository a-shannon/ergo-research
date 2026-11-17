//! Equation-only census and verifier differential for the N1984 filtered Map.
//! This checks a new relation over a frozen public parent profile; it is not a
//! proof, an authenticated native-input join, or an equivalence claim to Map.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    legacy_envelope_map::{
        Import, Kind, LowerBranch, LowerSelector, LowerSource, Map, OwnerRow, BANK, BASE, D_LOCAL,
        RATIO, SMAX, T_LOCAL,
    },
    packed_owner_assembly::{same_x_stage1b_n1984_fixture, SameXStage1bFixture},
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const N: u64 = 1984;
const H: usize = 11;
const OWNERS: usize = 1 << H;
const ROW_BITS: usize = 14;
const ROWS: usize = 1 << ROW_BITS;
const ROW_DOMAIN: usize = 1 << (ROW_BITS + H);
const WIRE_BITS: usize = 20;
const WIRE_WIDTH: usize = 1 << WIRE_BITS;
const WIRE_DOMAIN: usize = 1 << (WIRE_BITS + H);
const HELPER_BASE: usize = 671_744;
const LIVE_HELPERS: usize = 5_757;
const D_OWNERS: u64 = 1983;
const Q1_OWNER: u64 = 1983;
const D_TERMS: usize = 2_491;
const Q1_TERMS: usize = 8_520;
const FILTERED_TOTAL: usize = 4_948_173;
const EXPECTED_Q1: u64 = 22_538_929_735_599;

fn frozen_map() -> (SameXStage1bFixture, Map) {
    let fixture = same_x_stage1b_n1984_fixture().expect("frozen public N1984 fixture");
    assert_eq!(fixture.q1, EXPECTED_Q1, "frozen public q1 source pin");
    let plan = WorkTreeHistoryPlan::compile(N, H, fixture.root, fixture.total)
        .expect("frozen public N1984 parent profile");
    let map = Map::from_parent_modern_global_u(
        &plan,
        47,
        LowerSelector {
            source: LowerSource::Reset417792,
            branch: LowerBranch::Literal,
        },
    )
    .expect("e47 Reset417792 literal Map bound to the frozen profile");
    assert_eq!(map.binding().parent_root, Some(fixture.root));
    (fixture, map)
}

fn expected_imports(owner: u64) -> Vec<Import> {
    if owner < D_OWNERS {
        vec![Import {
            owner,
            local: D_LOCAL,
            width: 224,
            kind: Kind::Difficulty,
        }]
    } else if owner == Q1_OWNER {
        vec![
            Import {
                owner: 1023,
                local: T_LOCAL,
                width: 64,
                kind: Kind::Timestamp,
            },
            Import {
                owner: 1982,
                local: D_LOCAL,
                width: 224,
                kind: Kind::Difficulty,
            },
            Import {
                owner: 1983,
                local: T_LOCAL,
                width: 64,
                kind: Kind::Timestamp,
            },
        ]
    } else {
        Vec::new()
    }
}

fn fixture_slot(owner: u64) -> usize {
    match owner {
        1023 => 0,
        1982 => 1,
        1983 => 2,
        _ => panic!("owner {owner} is not represented in the frozen Stage1b fixture"),
    }
}

fn packed_word(fixture: &SameXStage1bFixture, owner: u64, local: usize, width: usize) -> BigInt {
    assert!(local + width <= WIRE_WIDTH);
    let bytes = &fixture.owner_slices[fixture_slot(owner)];
    let mut value = BigInt::from(0u8);
    for bit in 0..width {
        let index = local + bit;
        if ((bytes[index / 8] >> (index % 8)) & 1) != 0 {
            value += BigInt::from(1u8) << bit;
        }
    }
    value
}

fn imports_from_fixture(
    map: &Map,
    fixture: &SameXStage1bFixture,
    owner: u64,
) -> crate::legacy_envelope_map::Inputs {
    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for import in map.imports(owner).expect("typed import roster") {
        inputs
            .put(
                map,
                import,
                &packed_word(fixture, import.owner, import.local, import.width),
            )
            .expect("decode exact typed import from frozen owner slice");
    }
    inputs
}

fn synthetic_inputs(map: &Map, owner: u64) -> crate::legacy_envelope_map::Inputs {
    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for import in map.imports(owner).expect("typed import roster") {
        let value = match import.kind {
            Kind::Difficulty => BigInt::from(1u8),
            Kind::Timestamp if import.owner == 1023 => BigInt::from(1_000_000u64),
            Kind::Timestamp => {
                BigInt::from(1_000_000u64 + 2 * crate::legacy_envelope_map::TE as u64)
            }
        };
        inputs
            .put(map, import, &value)
            .expect("bounded synthetic typed input");
    }
    inputs
}

fn active_wire(intervals: &[(usize, usize)], local: usize) -> bool {
    intervals
        .iter()
        .any(|&(start, end)| start <= local && local < end)
}

fn zero_cell(term: &Term, owner: u64, row_local: usize) {
    assert_eq!(term.row, owner as usize * ROWS + row_local);
    assert_eq!(
        term.gate.left,
        owner as usize * WIRE_WIDTH + BASE + row_local
    );
    assert_eq!(term.gate.right, owner as usize * WIRE_WIDTH);
    assert_eq!(term.gate.c0, Fr::zero());
    assert_eq!(term.gate.c1, Fr::one());
    assert_eq!(term.gate.c2, Fr::zero());
    assert_eq!(term.gate.c3, Fr::zero());
}

fn boolean_cell(term: &Term, owner: u64, row_local: usize) {
    let helper = owner as usize * WIRE_WIDTH + BASE + row_local;
    assert_eq!(term.row, owner as usize * ROWS + row_local);
    assert_eq!(term.gate.left, helper);
    assert_eq!(term.gate.right, helper);
    assert_eq!(term.gate.c0, Fr::zero());
    assert_eq!(term.gate.c1, -Fr::one());
    assert_eq!(term.gate.c2, Fr::zero());
    assert_eq!(term.gate.c3, Fr::one());
}

fn expected_filtered(map: &Map, owner: u64) -> Vec<Term> {
    let source = map.terms(owner).expect("complete source Map terms");
    assert!(source.len() <= 200_000, "owner {owner} exceeded source cap");
    let active = map
        .active_intervals(owner)
        .expect("source active intervals");
    let row_base = owner as usize * ROWS;
    let mut retained = Vec::with_capacity(source.len());
    for mut term in source {
        let row_local = term
            .row
            .checked_sub(row_base)
            .expect("row under owner base");
        assert!(row_local < ROWS, "owner {owner} row outside 14-bit block");
        if row_local < BANK {
            let helper_local = BASE + row_local;
            if !active_wire(&active, helper_local) {
                zero_cell(&term, owner, row_local);
                continue;
            }
            boolean_cell(&term, owner, row_local);
        }
        for wire in [&mut term.gate.left, &mut term.gate.right] {
            let wire_owner = *wire / WIRE_WIDTH;
            let local = *wire % WIRE_WIDTH;
            if wire_owner == owner as usize && (BASE..BASE + LIVE_HELPERS).contains(&local) {
                *wire = wire_owner * WIRE_WIDTH + HELPER_BASE + local - BASE;
            } else if wire_owner == owner as usize
                && (BASE + LIVE_HELPERS..BASE + BANK).contains(&local)
            {
                panic!("retained owner {owner} term reads omitted helper {local}");
            }
        }
        retained.push(term);
    }
    retained
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Placement {
    row: usize,
    left_owner_delta: i64,
    left_local: usize,
    right_owner_delta: i64,
    right_local: usize,
    c0: Fr,
    c1: Fr,
    c2: Fr,
    c3: Fr,
}

fn placements(owner: u64, terms: &[Term]) -> Vec<Placement> {
    terms
        .iter()
        .map(|term| {
            assert!(term.row < ROW_DOMAIN, "row outside 25-bit address space");
            assert!(
                term.gate.left < WIRE_DOMAIN && term.gate.right < WIRE_DOMAIN,
                "input outside 31-bit address space"
            );
            let lo = term.gate.left / WIRE_WIDTH;
            let ro = term.gate.right / WIRE_WIDTH;
            assert!(lo < OWNERS && ro < OWNERS);
            let ll = term.gate.left % WIRE_WIDTH;
            let rl = term.gate.right % WIRE_WIDTH;
            for (wire_owner, local) in [(lo, ll), (ro, rl)] {
                if wire_owner == owner as usize
                    && (HELPER_BASE..HELPER_BASE + LIVE_HELPERS).contains(&local)
                {
                    continue;
                }
                assert!(
                    !(wire_owner == owner as usize && (BASE..BASE + BANK).contains(&local)),
                    "raw Map helper lane survived for owner {owner}: {local}"
                );
            }
            Placement {
                row: term.row - owner as usize * ROWS,
                left_owner_delta: lo as i64 - owner as i64,
                left_local: ll,
                right_owner_delta: ro as i64 - owner as i64,
                right_local: rl,
                c0: term.gate.c0,
                c1: term.gate.c1,
                c2: term.gate.c2,
                c3: term.gate.c3,
            }
        })
        .collect()
}

fn expected_support(owner: u64) -> BTreeSet<usize> {
    let mut rows = BTreeSet::new();
    match owner {
        0..=1982 => {
            rows.extend(0..673);
            rows.extend(7898..8124);
            rows.extend(8125..8350);
        }
        1983 => {
            rows.extend(RATIO - BASE..RATIO - BASE + 503);
            rows.extend(SMAX - BASE..SMAX - BASE + 278);
            rows.extend(8350..8484);
            rows.extend(9822..10010);
            rows.extend(10032..10123);
        }
        _ => {}
    }
    rows
}

fn assert_typed_active_reads(
    owner: u64,
    terms: &[Term],
    imports: &[Import],
    active: &[(usize, usize)],
) {
    let imported = |wire: usize| {
        let wire_owner = (wire / WIRE_WIDTH) as u64;
        let local = wire % WIRE_WIDTH;
        imports.iter().any(|item| {
            item.owner == wire_owner && item.local <= local && local < item.local + item.width
        })
    };
    for term in terms {
        let gate = &term.gate;
        for wire in [
            (gate.c1 != Fr::zero()).then_some(gate.left),
            (gate.c2 != Fr::zero()).then_some(gate.right),
            (gate.c3 != Fr::zero()).then_some(gate.left),
            (gate.c3 != Fr::zero()).then_some(gate.right),
        ]
        .into_iter()
        .flatten()
        {
            let wire_owner = (wire / WIRE_WIDTH) as u64;
            let local = wire % WIRE_WIDTH;
            if wire_owner == owner && (BASE..BASE + BANK).contains(&local) {
                assert!(
                    active_wire(active, local),
                    "retained term reads omitted helper {local}"
                );
            } else if !imported(wire) {
                assert_eq!(
                    wire_owner, owner,
                    "foreign read outside typed imports: {wire}"
                );
                assert!(
                    (HELPER_BASE..HELPER_BASE + LIVE_HELPERS).contains(&local),
                    "own read outside retained helper lane: {local}"
                );
            }
        }
    }
}

fn packed_bit(bytes: &[u8], local: usize) -> Fr {
    Fr::from(((bytes[local / 8] >> (local % 8)) & 1) as u64)
}

fn fixture_read(fixture: &SameXStage1bFixture, index: usize) -> Result<Fr, String> {
    let owner = (index / WIRE_WIDTH) as u64;
    let local = index % WIRE_WIDTH;
    Ok(packed_bit(
        &fixture.owner_slices[fixture_slot(owner)],
        local,
    ))
}

fn row_read(
    row: &OwnerRow,
    inputs: &crate::legacy_envelope_map::Inputs,
    index: usize,
) -> Result<Fr, String> {
    let owner = (index / WIRE_WIDTH) as u64;
    let local = index % WIRE_WIDTH;
    if owner == row.owner && (HELPER_BASE..HELPER_BASE + LIVE_HELPERS).contains(&local) {
        Ok(Fr::from(u64::from(row.bit(BASE + local - HELPER_BASE)?)))
    } else {
        Ok(Fr::from(u64::from(inputs.bit(owner, local)?)))
    }
}

fn residuals(
    terms: &[Term],
    mut read: impl FnMut(usize) -> Result<Fr, String>,
) -> Result<BTreeMap<usize, Fr>, String> {
    let mut sums = BTreeMap::<usize, Fr>::new();
    for term in terms {
        let gate = &term.gate;
        let mut value = gate.c0;
        if !gate.c1.is_zero() {
            value += gate.c1 * read(gate.left)?;
        }
        if !gate.c2.is_zero() {
            value += gate.c2 * read(gate.right)?;
        }
        if !gate.c3.is_zero() {
            value += gate.c3 * read(gate.left)? * read(gate.right)?;
        }
        *sums.entry(term.row).or_insert(Fr::zero()) += value;
    }
    Ok(sums
        .into_iter()
        .filter(|(_, value)| !value.is_zero())
        .collect())
}

fn local_residual_rows(rows: BTreeMap<usize, Fr>, owner: u64) -> BTreeSet<usize> {
    rows.into_keys()
        .map(|row| row - owner as usize * ROWS)
        .collect()
}

fn eq(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |acc, (bit, coordinate)| {
            acc * if (index >> bit) & 1 == 1 {
                *coordinate
            } else {
                Fr::one() - coordinate
            }
        })
}

fn eq_table(point: &[Fr]) -> Vec<Fr> {
    let mut values = vec![Fr::one()];
    for coordinate in point {
        let old_len = values.len();
        values.resize(old_len * 2, Fr::zero());
        for index in 0..old_len {
            let old = values[index];
            values[index] = old * (Fr::one() - coordinate);
            values[index + old_len] = old * coordinate;
        }
    }
    values
}

fn seeded_point(local_bits: usize, owner: Option<u64>, seed: u64) -> Vec<Fr> {
    let owner_bits = H;
    let mut point = (0..local_bits)
        .map(|i| Fr::from(seed + (i as u64 * 7) + 2))
        .collect::<Vec<_>>();
    match owner {
        Some(owner) => point.extend((0..owner_bits).map(|bit| Fr::from((owner >> bit) & 1))),
        None => point.extend((0..owner_bits).map(|bit| Fr::from(seed + bit as u64 + 3))),
    }
    point
}

fn points_for_owner(
    row_owner: u64,
    input_owner: u64,
    right_owner: u64,
    seed: u64,
) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    (
        seeded_point(ROW_BITS, Some(row_owner), seed),
        seeded_point(WIRE_BITS, Some(input_owner), seed + 31),
        seeded_point(WIRE_BITS, Some(right_owner), seed + 63),
    )
}

fn explicit_coefficients(map: &Map, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    assert_eq!(
        (r.len(), u.len(), v.len()),
        (ROW_BITS + H, WIRE_BITS + H, WIRE_BITS + H)
    );
    let row_local = eq_table(&r[..ROW_BITS]);
    let left_local = eq_table(&u[..WIRE_BITS]);
    let right_local = eq_table(&v[..WIRE_BITS]);
    let row_owner = eq_table(&r[ROW_BITS..]);
    let left_owner = eq_table(&u[WIRE_BITS..]);
    let right_owner = eq_table(&v[WIRE_BITS..]);
    let mut sum = [Fr::zero(); 4];
    for owner in 0..OWNERS as u64 {
        if row_owner[owner as usize].is_zero() {
            continue;
        }
        for term in map
            .filtered_terms(owner)
            .expect("one-owner filtered source stream")
        {
            let ro = term.row / ROWS;
            let rr = term.row % ROWS;
            let lo = term.gate.left / WIRE_WIDTH;
            let ll = term.gate.left % WIRE_WIDTH;
            let vo = term.gate.right / WIRE_WIDTH;
            let vl = term.gate.right % WIRE_WIDTH;
            let weight = row_owner[ro]
                * row_local[rr]
                * left_owner[lo]
                * left_local[ll]
                * right_owner[vo]
                * right_local[vl];
            if weight.is_zero() {
                continue;
            }
            for (index, coefficient) in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
                .into_iter()
                .enumerate()
            {
                sum[index] += weight * coefficient;
            }
        }
    }
    sum
}

fn assert_analytic_matches(map: &Map, r: &[Fr], u: &[Fr], v: &[Fr]) {
    let explicit = explicit_coefficients(map, r, u, v);
    let analytic = map
        .filtered_coefficients(r, u, v)
        .expect("filtered analytic callback");
    assert_eq!(
        analytic, explicit,
        "filtered coefficients at fixed field point"
    );
}

fn basis_point(row: usize, left: usize, right: usize) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    let bits = |value: usize, width: usize| -> Vec<Fr> {
        (0..width)
            .map(|bit| Fr::from(((value >> bit) & 1) as u64))
            .collect()
    };
    (
        bits(row, ROW_BITS + H),
        bits(left, WIRE_BITS + H),
        bits(right, WIRE_BITS + H),
    )
}

fn assert_point(map: &Map, point: (Vec<Fr>, Vec<Fr>, Vec<Fr>)) {
    assert_analytic_matches(map, &point.0, &point.1, &point.2);
}

#[test]
fn n1984_filtered_relation_census_witness_mutants_and_equation_differential() {
    let (fixture, map) = frozen_map();
    let old_d = map.terms(1023).expect("old D source terms");
    let old_q1 = map.terms(Q1_OWNER).expect("old q1 source terms");
    let old_pad = map.terms(1984).expect("old padding source terms");
    assert_eq!(old_d.len(), 9_716);
    assert_eq!(old_q1.len(), 15_637);
    assert_eq!(old_pad.len(), BANK);
    assert_eq!(
        1983 * old_d.len() + old_q1.len() + 64 * old_pad.len(),
        19_787_937
    );

    let d_template = expected_filtered(&map, 1023);
    let d_placement = placements(1023, &d_template);
    let q1_template = expected_filtered(&map, Q1_OWNER);
    let pad_template = expected_filtered(&map, 1984);
    assert_eq!(d_template.len(), D_TERMS);
    assert_eq!(q1_template.len(), Q1_TERMS);
    assert!(pad_template.is_empty());
    assert_eq!(d_placement.len(), D_TERMS);
    assert_eq!(map.imports(Q1_OWNER).unwrap(), expected_imports(Q1_OWNER));

    let mut roster_terms = 0usize;
    let mut roster_support = 0usize;
    let mut all_global_rows = BTreeSet::new();
    for owner in 0..OWNERS as u64 {
        let imports = map.imports(owner).expect("owner typed import census");
        assert_eq!(imports, expected_imports(owner), "owner {owner} imports");
        let source = expected_filtered(&map, owner);
        let filtered = map.filtered_terms(owner).expect("filtered owner terms");
        assert!(
            filtered.len() <= 200_000,
            "owner {owner} filtered materialization cap"
        );
        assert_eq!(
            filtered, source,
            "owner {owner} exact filter and helper placement"
        );
        assert_typed_active_reads(
            owner,
            &source,
            &imports,
            &map.active_intervals(owner).unwrap(),
        );
        let normalized = placements(owner, &source);
        if owner < D_OWNERS {
            assert_eq!(
                normalized, d_placement,
                "D class placement template owner {owner}"
            );
            assert_eq!(source.len(), D_TERMS);
        } else if owner == Q1_OWNER {
            assert_eq!(
                normalized.len(),
                Q1_TERMS,
                "all q1 terms preserve exact placement"
            );
            assert_eq!(normalized, placements(Q1_OWNER, &q1_template));
            assert_eq!(source.len(), Q1_TERMS);
        } else {
            assert!(
                source.is_empty(),
                "padding owner {owner} must have empty F support"
            );
        }
        let support = source.iter().map(|term| term.row).collect::<BTreeSet<_>>();
        let local_support = support
            .iter()
            .map(|row| row - owner as usize * ROWS)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            local_support,
            expected_support(owner),
            "owner {owner} exact row support"
        );
        for row in support {
            assert!(row < ROW_DOMAIN);
            assert!(all_global_rows.insert(row), "global row collision at {row}");
        }
        roster_terms += source.len();
        roster_support += local_support.len();

        // The deterministic generator may write helpers only in F's Boolean
        // scopes. The frozen q1 imports preserve the exact public source words.
        let inputs = if owner == Q1_OWNER {
            imports_from_fixture(&map, &fixture, owner)
        } else {
            synthetic_inputs(&map, owner)
        };
        let generated = map
            .generate(owner, &inputs)
            .expect("deterministic Map helper row");
        let active = map.active_intervals(owner).unwrap();
        for offset in 0..BANK {
            let local = BASE + offset;
            if !active_wire(&active, local) {
                assert!(
                    !generated.bit(local).unwrap(),
                    "generator writes omitted helper owner {owner} local {local}"
                );
            }
        }
    }
    assert_eq!(roster_terms, FILTERED_TOTAL);
    assert_eq!(roster_support, 2_230_086);
    assert_eq!(all_global_rows.len(), roster_support);

    // The Stage1b fixture is pinned to the frozen root/total/q1 profile. Read
    // its real context-0 helper lane and typed imported owner slices directly.
    let q1_frozen_terms = map.filtered_terms(Q1_OWNER).unwrap();
    let frozen_residuals = residuals(&q1_frozen_terms, |index| fixture_read(&fixture, index))
        .expect("frozen q1 context-0 packed inputs");
    assert!(
        frozen_residuals.is_empty(),
        "frozen q1 witness residuals: {frozen_residuals:?}"
    );

    // Mutate one D comparison helper, its carry, and its prefix-OR helper in
    // isolation. Each failure includes the intended guard equation row.
    let d_inputs = imports_from_fixture(&map, &fixture, 1023);
    let d_row = map
        .generate(1023, &d_inputs)
        .expect("frozen D import helper row");
    let d_terms = map.filtered_terms(1023).unwrap();
    assert!(
        residuals(&d_terms, |index| row_read(&d_row, &d_inputs, index))
            .unwrap()
            .is_empty()
    );
    for (helper, intended) in [
        (BASE, [7899usize, usize::MAX, usize::MAX]),
        (BASE + 225, [7899usize, 7900usize, usize::MAX]),
        (BASE + 449 + 100, [8225usize, 8226usize, usize::MAX]),
    ] {
        let mut mutant = d_row.clone();
        mutant.flip(helper).unwrap();
        let rows = local_residual_rows(
            residuals(&d_terms, |index| row_read(&mutant, &d_inputs, index)).unwrap(),
            1023,
        );
        for expected in intended.into_iter().filter(|row| *row != usize::MAX) {
            assert!(
                rows.contains(&expected),
                "D helper {helper} missed residual row {expected}: {rows:?}"
            );
        }
    }

    let q1_inputs = imports_from_fixture(&map, &fixture, Q1_OWNER);
    let q1_row = map
        .generate(Q1_OWNER, &q1_inputs)
        .expect("q1 helper row from frozen imports");
    let q1_terms = map.filtered_terms(Q1_OWNER).unwrap();
    assert!(
        residuals(&q1_terms, |index| row_read(&q1_row, &q1_inputs, index))
            .unwrap()
            .is_empty()
    );
    let mut q1_b_upper_mutant = q1_row.clone();
    q1_b_upper_mutant.flip(SMAX + 48).unwrap();
    let q1_faults = local_residual_rows(
        residuals(&q1_terms, |index| {
            row_read(&q1_b_upper_mutant, &q1_inputs, index)
        })
        .unwrap(),
        Q1_OWNER,
    );
    assert!(
        q1_faults.contains(&10032),
        "q1 B-upper high-bit mutant did not hit row 10032: {q1_faults:?}"
    );

    // This mutation is intentionally outside F. It documents the accepted-set
    // relaxation: an omitted bank bit is unconstrained and has no consumers.
    let mut omitted = q1_row.clone();
    omitted.flip(BASE + 1_176).unwrap();
    assert!(
        residuals(&q1_terms, |index| row_read(&omitted, &q1_inputs, index))
            .unwrap()
            .is_empty(),
        "omitted helper bit is deliberately outside the filtered relation"
    );

    // Four Boolean-owner points (selected D, tier-0 boundary, q1 foreign D,
    // padding) and a non-Boolean owner point whose eq weights cover all slots.
    for (row_owner, left_owner, right_owner, seed) in [
        (1023, 1023, 1023, 5),
        (959, 959, 959, 11),
        (1983, 1982, 1983, 17),
        (2047, 2047, 2047, 23),
    ] {
        let (r, u, v) = points_for_owner(row_owner, left_owner, right_owner, seed);
        assert_analytic_matches(&map, &r, &u, &v);
    }
    let r = seeded_point(ROW_BITS, None, 29);
    let u = seeded_point(WIRE_BITS, None, 37);
    let v = seeded_point(WIRE_BITS, None, 43);
    assert_analytic_matches(&map, &r, &u, &v);

    // Basis points hit both ends of the live D-helper lane, the omitted row,
    // q1's imported D and B-upper rows, and the final owner/input addresses.
    for point in [
        basis_point(0, HELPER_BASE, HELPER_BASE),
        basis_point(672, HELPER_BASE + 672, HELPER_BASE + 672),
        basis_point(673, BASE + 673, 0),
        basis_point(
            Q1_OWNER as usize * ROWS + 8350,
            1982 * WIRE_WIDTH + D_LOCAL,
            Q1_OWNER as usize * WIRE_WIDTH,
        ),
        basis_point(
            Q1_OWNER as usize * ROWS + 10032,
            Q1_OWNER as usize * WIRE_WIDTH + HELPER_BASE + SMAX + 48 - BASE,
            Q1_OWNER as usize * WIRE_WIDTH,
        ),
        basis_point(
            2047 * ROWS + ROWS - 1,
            2047 * WIRE_WIDTH + WIRE_WIDTH - 1,
            2047 * WIRE_WIDTH + WIRE_WIDTH - 1,
        ),
    ] {
        assert_point(&map, point);
    }

    // F is intentionally a different accepted relation: old Map has a unit
    // C1 at the omitted D row 673, while the filtered callback has no support.
    let omitted_basis = basis_point(673, BASE + 673, 0);
    let old = map
        .coefficients(&omitted_basis.0, &omitted_basis.1, &omitted_basis.2)
        .expect("old Map coefficient at omitted bank row");
    let filtered = map
        .filtered_coefficients(&omitted_basis.0, &omitted_basis.1, &omitted_basis.2)
        .expect("filtered coefficient at omitted bank row");
    assert_eq!(old[1], Fr::one());
    assert_eq!(filtered[1], Fr::zero());

    // Isolated foreign-owner substitution changes the explicit equation at
    // the exact q1 D-import basis point; no owner-local alias is accepted.
    let mut foreign_mutant = q1_terms.clone();
    let selected = foreign_mutant
        .iter_mut()
        .find(|term| {
            term.row == Q1_OWNER as usize * ROWS + 8350
                && term.gate.left == 1982 * WIRE_WIDTH + D_LOCAL
                && !term.gate.c1.is_zero()
        })
        .expect("q1 row 8350 foreign D consumer");
    selected.gate.left = 1983 * WIRE_WIDTH + D_LOCAL;
    let point = basis_point(
        Q1_OWNER as usize * ROWS + 8350,
        1982 * WIRE_WIDTH + D_LOCAL,
        Q1_OWNER as usize * WIRE_WIDTH,
    );
    let original_sum = explicit_at_terms(&q1_terms, &point.0, &point.1, &point.2);
    let mutated_sum = explicit_at_terms(&foreign_mutant, &point.0, &point.1, &point.2);
    assert_ne!(
        original_sum, mutated_sum,
        "foreign import owner mutation must alter q1 equation"
    );
}

fn explicit_at_terms(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let mut sum = [Fr::zero(); 4];
    for term in terms {
        let weight = eq(r, term.row) * eq(u, term.gate.left) * eq(v, term.gate.right);
        for (index, coefficient) in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
            .into_iter()
            .enumerate()
        {
            sum[index] += weight * coefficient;
        }
    }
    sum
}

fn h21_point(local_bits: usize, owner_bits: usize, owner: u64, seed: u64) -> Vec<Fr> {
    let mut point = (0..local_bits)
        .map(|bit| Fr::from(seed + bit as u64 * 3 + 2))
        .collect::<Vec<_>>();
    point.extend((0..owner_bits).map(|bit| Fr::from((owner >> bit) & 1)));
    point
}

fn expected_h21_tier8_imports(q: u64) -> Vec<Import> {
    let anchor = q * 1024 + 959;
    let mut imports = vec![Import {
        owner: anchor,
        local: D_LOCAL,
        width: 224,
        kind: Kind::Difficulty,
    }];
    for i in 0..8 {
        let (difficulty_owner, end_owner, start_owner) = if i == 7 {
            (q * 1024 + 958, anchor, (q - 1) * 1024 + 1023)
        } else {
            let shift = 7 - i as u64;
            (
                (q - shift) * 1024 + 1022,
                (q - shift) * 1024 + 1023,
                (q - shift - 1) * 1024 + 1023,
            )
        };
        imports.push(Import {
            owner: difficulty_owner,
            local: D_LOCAL,
            width: 224,
            kind: Kind::Difficulty,
        });
        for owner in [end_owner, start_owner] {
            imports.push(Import {
                owner,
                local: T_LOCAL,
                width: 64,
                kind: Kind::Timestamp,
            });
        }
    }
    imports.sort();
    imports.dedup();
    imports
}

#[test]
fn h21_q8_q9_filtered_equation_matches_source_only_analytic_diagnostic() {
    const N_H21: u64 = 1_827_840;
    const H_H21: usize = 21;

    let map = Map::new_modern_global_u(N_H21, H_H21, 47)
        .expect("requested H21 modern global-U diagnostic Map");
    for q in [8u64, 9] {
        let owner = q * 1024 + 959;
        assert_eq!(owner, if q == 8 { 9_151 } else { 10_175 });
        assert_eq!(owner / 1024, q, "source-derived tier index");
        assert_eq!(map.tier(owner).unwrap(), Some(8));
        let imports = map.imports(owner).expect("tier8 typed imports");
        assert_eq!(imports, expected_h21_tier8_imports(q));
        assert_eq!(imports.len(), 18, "exact typed D/time endpoint roster");
        let difficulty_owners = imports
            .iter()
            .filter(|item| item.kind == Kind::Difficulty)
            .map(|item| item.owner)
            .collect::<BTreeSet<_>>();
        let timestamp_owners = imports
            .iter()
            .filter(|item| item.kind == Kind::Timestamp)
            .map(|item| item.owner)
            .collect::<BTreeSet<_>>();

        let active = map.active_intervals(owner).expect("H21 owner active banks");
        let active_bank_count = active.iter().map(|(start, end)| end - start).sum::<usize>();
        assert_eq!(active_bank_count, LIVE_HELPERS);
        let terms = map
            .filtered_terms(owner)
            .expect("bounded one-owner filtered term stream");
        assert!(terms.len() <= 200_000, "one-owner source cap for {owner}");
        let support = terms
            .iter()
            .map(|term| term.row - owner as usize * ROWS)
            .collect::<BTreeSet<_>>();
        let expected_bank_rows = active
            .iter()
            .flat_map(|&(start, end)| (start - BASE)..(end - BASE))
            .collect::<BTreeSet<_>>();
        assert_eq!(expected_bank_rows.len(), active_bank_count);
        assert!(expected_bank_rows.is_subset(&support), "every active bank row remains in F");
        assert!(
            (0..BANK).filter(|row| !expected_bank_rows.contains(row)).all(|row| !support.contains(&row)),
            "omitted bank rows have no filtered F support for {owner}"
        );
        assert_typed_active_reads(owner, &terms, &imports, &active);

        let r = h21_point(ROW_BITS, H_H21, owner, 19);
        let local_owner_points = [
            (owner, owner),
            (*difficulty_owners.iter().find(|&&candidate| candidate != owner).unwrap(), owner),
            (owner, *timestamp_owners.iter().find(|&&candidate| candidate != owner).unwrap()),
        ];
        for (u_owner, v_owner) in local_owner_points {
            let u = h21_point(WIRE_BITS, H_H21, u_owner, 31);
            let v = h21_point(WIRE_BITS, H_H21, v_owner, 47);
            let analytic = map
                .filtered_coefficients_h21_source_only_diagnostic(owner, &r, &u, &v)
                .expect("separate H21 source-only analytic F callback");
            assert_eq!(
                analytic,
                explicit_at_terms(&terms, &r, &u, &v),
                "all four coefficients for Boolean owner{owner} and non-Boolean locals; u_owner={u_owner}, v_owner={v_owner}"
            );
        }

        // One isolated source-owner mutation must fail the existing typed-import
        // guard before it can be treated as a valid F term.
        let mut malformed = map.terms(owner).expect("bounded original owner source");
        assert!(malformed.len() <= 200_000, "source term cap for {owner}");
        let allowed_owners = imports.iter().map(|item| item.owner).collect::<BTreeSet<_>>();
        let bad_owner = (0..map.slots())
            .find(|candidate| *candidate != owner && !allowed_owners.contains(candidate))
            .expect("unimported H21 owner for isolated mutation");
        let (term_index, is_left, local) = malformed
            .iter()
            .enumerate()
            .find_map(|(index, term)| {
                for (is_left, wire, used) in [
                    (true, term.gate.left, !term.gate.c1.is_zero() || !term.gate.c3.is_zero()),
                    (false, term.gate.right, !term.gate.c2.is_zero() || !term.gate.c3.is_zero()),
                ] {
                    let source_owner = (wire / WIRE_WIDTH) as u64;
                    let local = wire % WIRE_WIDTH;
                    if used && source_owner != owner && allowed_owners.contains(&source_owner) {
                        return Some((index, is_left, local));
                    }
                }
                None
            })
            .expect("owner source term that reads a typed foreign import");
        let bad_wire = bad_owner as usize * WIRE_WIDTH + local;
        if is_left {
            malformed[term_index].gate.left = bad_wire;
        } else {
            malformed[term_index].gate.right = bad_wire;
        }
        assert!(map
            .filter_source_terms(owner, malformed)
            .unwrap_err()
            .contains("foreign input outside typed imports"));

        println!(
            "h21_filtered_source_only q={} owner={} tier=8 filtered_terms={} active_bank_rows={} imported_endpoints={} result=pass",
            q,
            owner,
            terms.len(),
            active_bank_count,
            imports.len()
        );
    }
}

#[test]
#[ignore = "explicit bounded N1984 no-proof throughput diagnostic"]
fn n1984_filtered_map_no_proof_throughput_diagnostic() {
    use std::{hint::black_box, time::Instant};

    let (_fixture, map) = frozen_map();

    let terms_started = Instant::now();
    let mut terms_count = 0usize;
    let mut max_owner_terms = 0usize;
    for owner in 0..OWNERS as u64 {
        let terms = map.filtered_terms(owner).expect("filtered owner terms");
        max_owner_terms = max_owner_terms.max(terms.len());
        terms_count += terms.len();
        drop(terms);
    }
    let terms_elapsed = terms_started.elapsed();
    assert_eq!(terms_count, FILTERED_TOTAL);
    assert!(max_owner_terms <= 200_000);
    let terms_per_sec = terms_count as f64 / terms_elapsed.as_secs_f64();
    println!(
        "filtered_terms owners={} terms={} max_owner_terms={} elapsed_ms={:.3} terms_per_sec={:.3}",
        OWNERS,
        terms_count,
        max_owner_terms,
        terms_elapsed.as_secs_f64() * 1000.0,
        terms_per_sec
    );

    let r = seeded_point(ROW_BITS, None, 29);
    let u = seeded_point(WIRE_BITS, None, 37);
    let v = seeded_point(WIRE_BITS, None, 43);
    let expected = map
        .filtered_coefficients(&r, &u, &v)
        .expect("analytic filtered coefficients");
    let coefficients_started = Instant::now();
    for _ in 0..100 {
        let actual = black_box(&map)
            .filtered_coefficients(black_box(&r), black_box(&u), black_box(&v))
            .expect("analytic filtered coefficients");
        assert_eq!(black_box(actual), expected);
    }
    let coefficients_elapsed = coefficients_started.elapsed();
    println!(
        "filtered_coefficients invocations=100 elapsed_ms={:.3} invocations_per_sec={:.3} coefficient={:?}",
        coefficients_elapsed.as_secs_f64() * 1000.0,
        100.0 / coefficients_elapsed.as_secs_f64(),
        expected
    );
}

// This pilot owns only D/T imports and generated F helpers. It deliberately
// makes no NativePrefix, Bank53, HEADER-authentication, or proof claim at H21.
const H21_Q9_OWNER: u64 = 10_175;
const H21_Q9_HEIGHTS: [u32; 10] = [
    2048, 3072, 4096, 5120, 6144, 7168, 8192, 9216, 10176, 10177,
];
const H21_F_ROW_WIDTH: usize = 1 << 19;
const H21_F_ROW_BASE: usize = 409_600;

fn h21_q9_physical_terms(map: &Map) -> (Vec<Import>, Vec<Term>, BTreeSet<usize>) {
    let imports = map.imports(H21_Q9_OWNER).expect("q9 typed import roster");
    assert_eq!(imports, expected_h21_tier8_imports(9));
    assert_eq!(imports.len(), 18);
    let owners = imports.iter().map(|item| item.owner).collect::<BTreeSet<_>>();
    assert_eq!(owners.len(), 17, "original-width owner rows");
    let heights = imports.iter().map(|item| match item.kind {
        Kind::Difficulty => u32::try_from(item.owner + 2).unwrap(),
        Kind::Timestamp => u32::try_from(item.owner + 1).unwrap(),
    }).collect::<BTreeSet<_>>();
    assert_eq!(heights, H21_Q9_HEIGHTS.into_iter().collect());
    let active = map.active_intervals(H21_Q9_OWNER).unwrap();
    assert_eq!(active.iter().map(|(a, b)| b - a).sum::<usize>(), LIVE_HELPERS);
    let mut allowed = imports.iter().flat_map(|item| {
        (item.local..item.local + item.width)
            .map(move |local| item.owner as usize * WIRE_WIDTH + local)
    }).collect::<BTreeSet<_>>();
    allowed.extend(active.iter().flat_map(|&(a, b)| (a..b).map(|local| {
        H21_Q9_OWNER as usize * WIRE_WIDTH + HELPER_BASE + local - BASE
    })));
    let mut terms = map.filtered_terms(H21_Q9_OWNER).expect("bounded q9 F terms");
    assert_eq!(terms.len(), 68_229, "frozen q9 F term census");
    assert!(terms.len() <= 200_000);
    assert_typed_active_reads(H21_Q9_OWNER, &terms, &imports, &active);
    let mut census = BTreeSet::new();
    for term in &mut terms {
        let local = term.row.checked_sub(H21_Q9_OWNER as usize * ROWS).unwrap();
        assert!(local < ROWS && H21_F_ROW_BASE + local < H21_F_ROW_WIDTH);
        term.row = H21_Q9_OWNER as usize * H21_F_ROW_WIDTH + H21_F_ROW_BASE + local;
        for wire in [
            (!term.gate.c1.is_zero() || !term.gate.c3.is_zero()).then_some(term.gate.left),
            (!term.gate.c2.is_zero() || !term.gate.c3.is_zero()).then_some(term.gate.right),
        ].into_iter().flatten() {
            assert!(allowed.contains(&wire), "active q9 wire outside typed allowlist: {wire}");
            census.insert(wire);
        }
    }
    assert_eq!(census, allowed, "exact active D/T/helper read census");
    (imports, terms, allowed)
}

fn h21_q9_read(rows: &BTreeMap<u64, Vec<u8>>, allowed: &BTreeSet<usize>, index: usize)
    -> Result<Fr, String>
{
    if !allowed.contains(&index) {
        return Err(format!("q9 packed read outside typed allowlist: {index}"));
    }
    let owner = (index / WIRE_WIDTH) as u64;
    let row = rows.get(&owner).ok_or("q9 packed owner absent")?;
    if row.len() != WIRE_WIDTH / 8 { return Err("q9 packed width".into()); }
    Ok(packed_bit(row, index % WIRE_WIDTH))
}

#[test]
fn h21_q9_physical_port_census_rejects_unlisted_reads() {
    let map = Map::new_modern_global_u(1_827_840, 21, 47).unwrap();
    let (_, terms, allowed) = h21_q9_physical_terms(&map);
    assert!(!terms.is_empty());
    assert!(h21_q9_read(&BTreeMap::new(), &allowed, 0).is_err());
    assert!(h21_q9_read(&BTreeMap::new(), &allowed, *allowed.first().unwrap()).is_err());
}

#[test]
#[ignore = "explicit ten-RAW H21 q9 packed-port diagnostic; run only in bounded Job"]
fn h21_q9_real_header_packed_ports_and_physical_f_residuals() {
    use std::{fs, io::Read, path::{Path, PathBuf}};
    use serde::Deserialize;
    use crate::native_prefix_auth_plan::role0_sha256;

    fn sha(bytes: &[u8]) -> String {
        role0_sha256(bytes).unwrap().iter().map(|b| format!("{b:02X}")).collect()
    }
    fn bounded(path: &Path, cap: u64) -> Vec<u8> {
        let mut file = fs::File::open(path).expect("open pinned q9 input");
        let size = file.metadata().unwrap().len();
        assert!(size > 0 && size <= cap, "q9 input size outside cap");
        let mut bytes = Vec::new();
        (&mut file).take(cap + 1).read_to_end(&mut bytes).unwrap();
        assert_eq!(bytes.len() as u64, size, "q9 input size changed");
        bytes
    }
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct RawPin { height: u32, file: String, offset: u64, bytes: u64, sha256: String }
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct FramePin { bytes: u64, sha256: String, anchor_height: u32, tip_height: u32 }
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct PrefixPin { last_height: u32, bytes: u64, opaque_tail_bytes: u64 }
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Manifest {
        format: String, test_only: bool, validation_scope: String,
        frame: FramePin, prefix: PrefixPin, max_read_request: u64,
        source_pins_sha256: BTreeMap<String, String>, canonical_json: String,
        headers: Vec<RawPin>,
    }

    let dir = PathBuf::from(std::env::var_os("NIPOPOW_H21_Q9_HEADERS_DIR").expect("q9 RAW directory env"));
    let manifest_path = PathBuf::from(std::env::var_os("NIPOPOW_H21_Q9_HEADERS_MANIFEST")
        .expect("q9 manifest path env"));
    let pin = std::env::var("NIPOPOW_H21_Q9_HEADERS_MANIFEST_SHA256").expect("independent q9 manifest SHA256 env");
    assert!(pin.len() == 64 && pin.bytes().all(|b| b.is_ascii_digit() || (b'A'..=b'F').contains(&b)),
        "canonical uppercase SHA256");
    let manifest_bytes = bounded(&manifest_path, 32_768);
    assert_eq!(sha(&manifest_bytes), pin, "independent q9 manifest pin");
    let json: serde_json::Value = serde_json::from_slice(&manifest_bytes).unwrap();
    let mut canonical = serde_json::to_vec(&json).unwrap();
    canonical.push(b'\n');
    assert_eq!(canonical, manifest_bytes, "canonical sorted compact LF manifest");
    let manifest: Manifest = serde_json::from_slice(&manifest_bytes).expect("strict q9 manifest schema");
    assert_eq!(manifest.format, "H21-Q9-RAW-EXTRACT-1");
    assert!(manifest.test_only);
    assert_eq!(manifest.validation_scope, "prefix-structure-and-whole-file-identity");
    assert_eq!(manifest.canonical_json, "ascii-sort-keys-compact-lf-v1");
    assert_eq!(manifest.frame.bytes, 1_321_781_831);
    assert_eq!(manifest.frame.sha256, "a68d86562a56c5b71cf2180e4762bf8775b1061b6953bff7281ec50b7ee52c5e");
    assert_eq!((manifest.frame.anchor_height, manifest.frame.tip_height), (1_827_839, 1_827_840));
    assert_eq!(manifest.prefix.last_height, 10_177);
    assert!(manifest.prefix.bytes > 0 && manifest.prefix.bytes < manifest.frame.bytes);
    assert_eq!(manifest.prefix.bytes + manifest.prefix.opaque_tail_bytes, manifest.frame.bytes);
    assert!(manifest.max_read_request > 0 && manifest.max_read_request <= 1_048_576);
    assert_eq!(manifest.source_pins_sha256, BTreeMap::from([
        ("MainnetReceiverFrameAssembler.scala".into(), "ba231f96c7ae1b63c2ba4ad81e74c39982e2c5d7a86cc16a2e41cc96b28bfd35".into()),
        ("BootstrapVerifierSourceV1.scala".into(), "c63f1d6814419b5ca14f00194d30eb6dc66a9bdf3da989d21f62c455db13ecf0".into()),
    ]));
    assert_eq!(manifest.headers.len(), H21_Q9_HEIGHTS.len());
    let mut headers = BTreeMap::new();
    let mut previous_end = 0u64;
    for (entry, height) in manifest.headers.iter().zip(H21_Q9_HEIGHTS) {
        assert_eq!(entry.height, height, "exact sorted q9 height roster");
        assert_eq!(entry.file, format!("header-{height:07}.bin"), "q9 RAW basename only");
        assert!(entry.bytes > 0 && entry.bytes <= 514);
        let end = entry.offset.checked_add(entry.bytes).expect("q9 RAW extent overflow");
        assert!(entry.offset >= previous_end && end <= manifest.prefix.bytes);
        previous_end = end;
        let bytes = bounded(&dir.join(&entry.file), 514);
        assert_eq!(bytes.len() as u64, entry.bytes);
        assert_eq!(sha(&bytes).to_ascii_lowercase(), entry.sha256, "q9 RAW content pin");
        let header = ergo_header_core::Header::decode(&bytes, None).expect("canonical q9 RAW decode");
        assert_eq!(header.height, height, "q9 RAW embedded height");
        assert_eq!(header.encode().unwrap(), bytes, "canonical q9 RAW reencode");
        assert!(headers.insert(height, header).is_none());
    }

    let map = Map::new_modern_global_u(1_827_840, 21, 47).unwrap();
    assert_eq!(map.binding().parent_root, None, "no borrowed N1984 parent profile");
    let (imports, terms, allowed) = h21_q9_physical_terms(&map);
    let mut rows = imports.iter().map(|item| (item.owner, vec![0u8; WIRE_WIDTH / 8]))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(rows.len(), 17);
    let serializer = crate::serializer::build(None).expect("bounded serializer template");
    assert_eq!(serializer.circuit.input_len, crate::header_hash::SERIALIZER_WIDTH);
    assert_eq!(serializer.layout.fields.timestamp,
        std::array::from_fn(|bit| T_LOCAL + bit - crate::header_hash::SERIALIZER_OFFSET));
    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for item in &imports {
        let mut bits = Vec::with_capacity(item.width);
        match item.kind {
            Kind::Difficulty => {
                assert_eq!((item.local, item.width), (D_LOCAL, 224));
                let header = &headers[&u32::try_from(item.owner + 2).unwrap()];
                let difficulty = crate::work_tree_work::native_decode(header.n_bits).unwrap();
                assert!(difficulty.bits() <= 224 && difficulty != num_bigint::BigUint::from(0u8));
                bits.extend((0..224).map(|bit| difficulty.bit(bit as u64)));
            }
            Kind::Timestamp => {
                assert_eq!((item.local, item.width), (T_LOCAL, 64));
                let header = &headers[&u32::try_from(item.owner + 1).unwrap()];
                let fields = crate::serializer::Fields::from_header(header).unwrap();
                let assignment = serializer.assign(&fields);
                for (bit, wire) in serializer.layout.fields.timestamp.iter().enumerate() {
                    let value = assignment[*wire];
                    assert!(value == Fr::zero() || value == Fr::one());
                    assert_eq!(value == Fr::one(), (header.timestamp as u64 >> bit) & 1 != 0);
                    bits.push(value == Fr::one());
                }
            }
        }
        let row = rows.get_mut(&item.owner).unwrap();
        let mut word = BigInt::from(0u8);
        for (bit, set) in bits.into_iter().enumerate() {
            if set {
                row[(item.local + bit) / 8] |= 1 << ((item.local + bit) % 8);
                word += BigInt::from(1u8) << bit;
            }
        }
        inputs.put(&map, item.clone(), &word).expect("exact native-derived typed input");
    }
    drop(serializer);
    let generated = map.generate(H21_Q9_OWNER, &inputs).expect("q9 F helpers from native-derived imports");
    let row = rows.get_mut(&H21_Q9_OWNER).unwrap();
    for offset in 0..LIVE_HELPERS {
        if generated.bit(BASE + offset).unwrap() {
            row[(HELPER_BASE + offset) / 8] |= 1 << ((HELPER_BASE + offset) % 8);
        }
    }
    assert!(residuals(&terms, |index| h21_q9_read(&rows, &allowed, index)).unwrap().is_empty(),
        "q9 real-derived packed physical F residuals");

    // Change only the foreign start-time sign bit; retain every helper and
    // every other imported bit. The guard's physical output must detect it.
    let mutant_owner = 2047u64;
    let mutant_local = T_LOCAL + 63;
    let mutant_wire = mutant_owner as usize * WIRE_WIDTH + mutant_local;
    assert!(allowed.contains(&mutant_wire));
    rows.get_mut(&mutant_owner).unwrap()[mutant_local / 8] ^= 1 << (mutant_local % 8);
    let faults = residuals(&terms, |index| h21_q9_read(&rows, &allowed, index)).unwrap();
    let intended = H21_Q9_OWNER as usize * H21_F_ROW_WIDTH + H21_F_ROW_BASE + 10_008;
    assert!(faults.contains_key(&intended), "foreign T sign-bit mutant misses physical local10008");
    println!("H21_Q9_PACKED_PORTS_PASS headers=10 owners=17 width={} helpers={} terms={} active_reads={} positive_residuals=0 mutant_local10008=nonzero authentication=unclaimed proof=none",
        WIRE_WIDTH, LIVE_HELPERS, terms.len(), allowed.len());
}

#[test]
fn n1984_filtered_source_rejects_isolated_malformed_terms() {
    let (_fixture, map) = frozen_map();
    let ordinary = map.terms(0).expect("complete ordinary source terms");

    let mut bad_zero = ordinary.clone();
    bad_zero[673].gate.c1 = Fr::zero();
    assert!(map
        .filter_source_terms(0, bad_zero)
        .unwrap_err()
        .contains("malformed dropped zero-cell gate"));

    let mut bad_boolean = ordinary.clone();
    bad_boolean[0].gate.c3 = Fr::zero();
    assert!(map
        .filter_source_terms(0, bad_boolean)
        .unwrap_err()
        .contains("malformed active Boolean bank gate"));

    let mut bad_retired = ordinary.clone();
    bad_retired[BANK].gate.left = BASE + LIVE_HELPERS;
    assert!(map
        .filter_source_terms(0, bad_retired)
        .unwrap_err()
        .contains("retired helper input"));

    let mut bad_packed = ordinary.clone();
    bad_packed[BANK].gate.left = HELPER_BASE;
    assert!(map
        .filter_source_terms(0, bad_packed)
        .unwrap_err()
        .contains("source already uses packed helper coordinate"));

    let mut bad_row = ordinary;
    bad_row[0].row = ROWS;
    assert!(map
        .filter_source_terms(0, bad_row)
        .unwrap_err()
        .contains("row/input owner collision"));

    let mut bad_foreign = map.terms(Q1_OWNER).expect("complete q1 source terms");
    let q1_d = bad_foreign
        .iter()
        .position(|term| {
            term.row == Q1_OWNER as usize * ROWS + 8350
                && term.gate.left == 1982 * WIRE_WIDTH + D_LOCAL
                && !term.gate.c1.is_zero()
        })
        .expect("q1 imported D term");
    bad_foreign[q1_d].gate.left = 1981 * WIRE_WIDTH + D_LOCAL;
    assert!(map
        .filter_source_terms(Q1_OWNER, bad_foreign)
        .unwrap_err()
        .contains("foreign input outside typed imports"));
}

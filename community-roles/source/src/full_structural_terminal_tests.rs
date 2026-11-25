use super::*;

// Use the actual admitted snapshot's two clipped endpoints. Compare independent
// literal interpolation with the delta in the public verifier's wiring.
#[test]
fn full_score_binds_each_existing_terminal_bit_on_both_inverse_partitions() -> Result<(), String> {
    let cut = CutDescriptor::eligible08();
    let params = cut.terminals().map(|terminal| PublicMapParameters { terminal, exponent: 55,
        lower: LowerSelector { source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54) } });
    let parent = WorkTreeHistoryPlan::compile(N as u64, 21, [0x31; 32], [0x42; 28])?;
    let mut roster = H21StructuralRoster::from_public(&parent, params)?;
    let owners = cut.guards().map(|guard| guard - 1);
    let expected: [[u8; 29]; 2] = std::array::from_fn(|c| std::array::from_fn(|b|
        if b == 0 { c as u8 } else { (b * 13 + c * 97) as u8 }));
    let point = |n: usize, seed: usize| -> Vec<Fr> {
        (0..n).map(|i| Fr::from((seed + 17 * i) as u64)).collect()
    };
    let (r, u, v) = (point(40, 2), point(41, 5), point(41, 11));
    let plain = roster.coefficients(&r, &u, &v)?;
    let terminal_rows = |owner:usize,c:usize| {
        let first = owner * ROWS + SCORE_ROW[c] + score::group("terminal").start;
        first..first + 225
    };
    for (c, &owner) in owners.iter().enumerate() {
        let occupied = terminal_rows(owner, c);
        roster.visit_owner_terms(owner, |_, t| {
            assert!(!occupied.contains(&t.row), "base relation already occupies a terminal row"); Ok(())
        })?;
        for left in [true, false] {
            assert!(candidate_destinations(&roster.scheduled, &roster.maps, Family::Score(c),
                left, owner)?.contains(owner));
        }
    }
    roster.bind_terminal_scores(expected);
    let mut delta = [Fr::zero(); 4];
    let basis = |point: &[Fr], index: usize| -> Fr {
        point.iter().enumerate().fold(Fr::one(), |acc, (i, x)|
            acc * if (index >> i) & 1 == 0 { Fr::one() - x } else { *x })
    };
    for (c, &owner) in owners.iter().enumerate() {
        let rows = terminal_rows(owner, c);
        let mut observed = Vec::new();
        roster.visit_owner_terms(owner, |family, t| {
            if rows.contains(&t.row) { assert_eq!(family, Family::Score(c)); observed.push(t); }
            Ok(())
        })?;
        assert_eq!(observed.len(), 225);
        for (bit, term) in observed.iter().enumerate() {
            let row = rows.start + bit;
            let wire = owner * WIDTH + SCORE_X[c] + score::Layout::new().r.start + bit;
            let want = Fr::from(u64::from((expected[c][28 - bit/8] >> (bit%8)) & 1));
            assert_eq!((term.row, term.gate.left, term.gate.right), (row, wire, wire));
            assert_eq!([term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3],
                [-want, Fr::one(), Fr::zero(), Fr::zero()]);
            assert!((term.gate.c0 + want).is_zero());
            assert!(!(term.gate.c0 + Fr::one() - want).is_zero());
            let weight = basis(&r, row) * basis(&u, wire) * basis(&v, wire);
            delta[0] -= want * weight;
            delta[1] += weight;
        }
        for left in [true, false] {
            let mut visited = Vec::new();
            roster.visit_endpoint_selected(left, owner, Some(&[owner]), |family, t| {
                if rows.contains(&t.row) { assert_eq!(family, Family::Score(c)); visited.push(t); }
                Ok(())
            })?;
            assert_eq!(visited, observed);
        }
    }
    let actual = roster.coefficients(&r, &u, &v)?;
    for i in 0..4 { assert_eq!(actual[i], plain[i] + delta[i]); }
    Ok(())
}

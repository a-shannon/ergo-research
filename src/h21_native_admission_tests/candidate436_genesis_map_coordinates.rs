//! No-frame coordinate differential for the Genesis and era-seam Map rows.
//! This checks term translation, not the authentic Map values or a full X.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::bank53_map::{
    self, CutDescriptor, CONTEXT_INPUT_BASE, CONTEXT_ROW_BASE, INPUT_STRIDE,
    MAP_LIVE, MAP_ROW_STRIDE, MAP_TAIL_END, MAP_TAIL_START, ROW_STRIDE,
};
use crate::legacy_envelope_map::{Map, BASE as MAP_BASE};
use crate::sparse::Term;
use crate::work_tree_history_plan::WorkTreeHistoryPlan;

const N: usize = 1_827_840;
const SLOTS: usize = 1 << 21;
const CONTEXT_BITS: usize = 8_192;
const CONTEXT_ROWS: usize = 32_768;
const TAIL_COUNT: usize = MAP_TAIL_END - MAP_TAIL_START;

fn expected_input(index: usize, owner: usize, context: usize) -> Result<usize, String> {
    let owner_base = owner.checked_mul(INPUT_STRIDE).ok_or("C436 owner input overflow")?;
    if index < owner_base || index >= owner_base + INPUT_STRIDE {
        return Ok(index); // A foreign HEADER/Work import keeps its global X address.
    }
    let local = index - owner_base;
    if (MAP_BASE..MAP_BASE + MAP_LIVE).contains(&local) {
        return Ok(owner_base + CONTEXT_INPUT_BASE + context * CONTEXT_BITS + local - MAP_BASE);
    }
    if (MAP_BASE + MAP_TAIL_START..MAP_BASE + MAP_TAIL_END).contains(&local) {
        return Err("C436 retained Map term reads a retired zero tail".into());
    }
    Ok(index)
}

fn expected_physical_terms(source: &[Term], owner: usize, context: usize)
    -> Result<(Vec<Term>, usize), String>
{
    if context >= 2 || owner >= SLOTS { return Err("C436 owner/context outside H21".into()); }
    let old_row_base = owner.checked_mul(MAP_ROW_STRIDE).ok_or("C436 old row overflow")?;
    let owner_input = owner.checked_mul(INPUT_STRIDE).ok_or("C436 input base overflow")?;
    let physical_row_base = owner.checked_mul(ROW_STRIDE)
        .and_then(|v| v.checked_add(CONTEXT_ROW_BASE + context * CONTEXT_ROWS))
        .ok_or("C436 physical row overflow")?;
    let mut tail_seen = vec![false; TAIL_COUNT];
    let mut retained = Vec::with_capacity(source.len());
    for term in source {
        let local_row = term.row.checked_sub(old_row_base)
            .filter(|v| *v < MAP_ROW_STRIDE).ok_or("C436 Map source ROW outside owner")?;
        if (MAP_TAIL_START..MAP_TAIL_END).contains(&local_row) {
            let index = local_row - MAP_TAIL_START;
            if tail_seen[index] { return Err("C436 duplicated tail ROW".into()); }
            tail_seen[index] = true;
            let g = &term.gate;
            if g.left != owner_input + MAP_BASE + local_row || g.right != owner_input
                || g.c0 != Fr::zero() || g.c1 != Fr::one()
                || g.c2 != Fr::zero() || g.c3 != Fr::zero()
            { return Err("C436 malformed explicit zero-tail gate".into()); }
            continue;
        }
        let mut next = term.clone();
        next.row = physical_row_base + local_row;
        next.gate.left = expected_input(term.gate.left, owner, context)?;
        next.gate.right = expected_input(term.gate.right, owner, context)?;
        retained.push(next);
    }
    if tail_seen.iter().any(|seen| !*seen) {
        return Err("C436 incomplete explicit zero-tail ROWs".into());
    }
    Ok((retained, TAIL_COUNT))
}

fn require_ordered_exact(actual: &[Term], expected: &[Term]) -> Result<(), String> {
    if actual.len() != expected.len() { return Err("C436 translated term count".into()); }
    for (ordinal, (a, e)) in actual.iter().zip(expected).enumerate() {
        if a != e { return Err(format!("C436 translated term mismatch ordinal {ordinal}")); }
    }
    Ok(())
}

#[test]
fn c436_genesis_and_era_map_term_coordinates_without_frame() {
    let plan = WorkTreeHistoryPlan::compile(N as u64, 21, [0x36; 32], [0x36; 28])
        .expect("C436 H21 source-only plan");
    let cut = CutDescriptor::eligible08();
    let terminals = cut.terminals();
    assert_eq!(terminals[0], N);
    let maps = [
        Map::new_modern_global_u(terminals[0] as u64, 21, 55).unwrap(),
        Map::new_modern_global_u(terminals[1] as u64, 21, 48).unwrap(),
    ];
    // These constructors deliberately omit the actual selected-lower winner:
    // choosing it requires the authenticated prefix and remains open here.
    let mask = plan.physical_assignment_replacement_mask(0).unwrap();
    assert_eq!(mask.len(), INPUT_STRIDE);
    for context in 0..2 {
        let active = maps[context].active_intervals(0).unwrap();
        assert_eq!(active, vec![(MAP_BASE, MAP_BASE + 673)]);
        let first = CONTEXT_INPUT_BASE + context * CONTEXT_BITS;
        assert_eq!(expected_input(MAP_BASE, 0, context).unwrap(), first);
        assert_eq!(expected_input(MAP_BASE + 672, 0, context).unwrap(), first + 672);
        assert!(mask[first..first + 673].iter().all(|replaced| !*replaced));
    }
    assert_eq!(maps[0].tier(417_727).unwrap(), None, "q407 excluded");
    assert!(maps[0].tier(843_711).unwrap().is_some(), "last pre-cap anchor");
    assert_eq!(maps[0].tier(844_735).unwrap(), None, "post-cap anchor absent");
    assert!(!maps[1].active_intervals((terminals[1] - 2) as u64).unwrap().is_empty(),
        "Map1 last live base owner");
    assert!(maps[1].active_intervals((terminals[1] - 1) as u64).unwrap().is_empty(),
        "Map1 terminal predecessor has no base import");
    assert!(maps[1].active_intervals(terminals[1] as u64).unwrap().is_empty(),
        "Map1 post-terminal owner has no base import");
    assert!(!maps[0].active_intervals((terminals[1] - 1) as u64).unwrap().is_empty(),
        "Map0 remains live across Map1 terminal");
    let owners = [0, 417_727, 843_711, 843_775, 843_776, 844_671, 844_672,
        845_759, terminals[1] - 2, terminals[1] - 1, terminals[1], N - 1, N, SLOTS - 1];
    let mut retained_total = 0usize;
    let mut tail_total = 0usize;
    for owner in owners {
        for context in 0..2 {
            let source = maps[context].terms(owner as u64)
                .expect("C436 direct symbolic Map source terms");
            let actual = bank53_map::translate_map_terms_for_descriptor(
                &maps[context], owner as u64, context, &source, cut,
            ).expect("C436 canonical physical Map translation");
            let (expected, tail) = expected_physical_terms(&source, owner, context)
                .expect("C436 independent ordered coordinate oracle");
            require_ordered_exact(&actual, &expected).unwrap();
            assert_eq!(tail, TAIL_COUNT);
            retained_total += actual.len();
            tail_total += tail;
            if owner == 0 && context == 0 {
                assert!(bank53_map::translate_map_terms_for_descriptor(
                    &maps[0], 0, 1, &source, cut).is_err(), "context swap");
                let source1 = maps[1].terms(0).unwrap();
                assert!(bank53_map::translate_map_terms_for_descriptor(
                    &maps[1], 0, 1, &source1, CutDescriptor::diagnostic08()).is_err(),
                    "context1 cut endpoint substitution");
                let tail_index = source.iter().position(|term|
                    (MAP_TAIL_START..MAP_TAIL_END).contains(&term.row))
                    .expect("C436 source contains first zero-tail row");
                let mut omitted = source.clone(); omitted.remove(tail_index);
                assert!(bank53_map::translate_map_terms_for_descriptor(
                    &maps[0], 0, 0, &omitted, cut).is_err(), "missing tail");
                let mut duplicated = source.clone(); duplicated.push(source[tail_index].clone());
                assert!(bank53_map::translate_map_terms_for_descriptor(
                    &maps[0], 0, 0, &duplicated, cut).is_err(), "duplicate tail");
                let mut bad_zero = source.clone(); bad_zero[tail_index].gate.c1 = Fr::zero();
                assert!(bank53_map::translate_map_terms_for_descriptor(
                    &maps[0], 0, 0, &bad_zero, cut).is_err(), "noncanonical tail");
                let mut bad_row = expected.clone(); bad_row[0].row += 1;
                assert!(require_ordered_exact(&actual, &bad_row).is_err(), "row coordinate");
                let mut bad_input = expected.clone(); bad_input[0].gate.left += 1;
                assert!(require_ordered_exact(&actual, &bad_input).is_err(), "input coordinate");
                let mut bad_coefficient = expected.clone(); bad_coefficient[0].gate.c0 += Fr::one();
                assert!(require_ordered_exact(&actual, &bad_coefficient).is_err(), "coefficient");
                let mut bad_order = expected.clone();
                let distinct = (1..bad_order.len()).find(|i| bad_order[*i] != bad_order[0]).unwrap();
                bad_order.swap(0, distinct);
                assert!(require_ordered_exact(&actual, &bad_order).is_err(), "term order");
            }
        }
    }
    println!("C436_MAP_COORDINATE_DIAGNOSTIC owners={} contexts=2 retained_terms={} retired_zero_tail_terms={} genesis_global_x_first={}",
        owners.len(), retained_total, tail_total, CONTEXT_INPUT_BASE);
    println!("C436_GENESIS_MAP_COORDINATE_PASS geometry_only=true selected_lower_open=true profile_binding_open=true source_author_open=true full_x=false proof=false client=false");
}

//! Bounded H3/H4 boundary-term composition across the frozen B1/B2/B3/B4 emitters.
//! This builds a candidate sparse circuit; it does not prove a satisfying witness.
use crate::{
    header_compact_links, sparse::{Circuit, Term}, work_tree_fixed_hash as fixed,
    work_tree_layout as layout, work_tree_leaf_hash as leaf,
    work_tree_wiring::{self as topology, Descriptor}, work_tree_work as work,
};

const EXPECTED_TERMS: usize = 956_504;
const EXPECTED_H4_TERMS: usize = 967_665;
const MAX_TERMS: usize = 1 << 20;
const DAA_BITS: usize = 224;
const EXPECTED_H4_EARLY_DAA_TERMS: usize = EXPECTED_H4_TERMS + 3 * DAA_BITS;

/// Mainnet genesis initial difficulty, numerically decoded from `011765000000`.
/// The reference is the pinned node-admission configuration matched to the
/// existing native difficulty source; this is not a raw compact-header value.
pub const GENESIS_DIFFICULTY: u64 = 0x0117_6500_0000;

#[derive(Clone, Debug)]
pub struct Composition {
    pub circuit: Circuit,
    pub live_rows: usize,
    pub reserved_rows: usize,
    pub component_rows: Vec<(String, usize)>,
    pub removed_legacy_terms_per_slot: usize,
}

fn append_shifted(out: &mut Vec<Term>, terms: impl IntoIterator<Item = Term>,
                  row_offset: usize, input_offset: usize) {
    for mut term in terms {
        term.row += row_offset;
        term.gate.left += input_offset;
        term.gate.right += input_offset;
        out.push(term);
    }
}

fn reserve_terms(out: &[Term], additional: usize) -> Result<(), String> {
    if additional > MAX_TERMS.saturating_sub(out.len()) {
        return Err(format!("composed boundary exceeds MAX_TERMS ({MAX_TERMS})"));
    }
    Ok(())
}

/// Compose the exact H3 row domains. Public root and total are bound by the
/// source profiles; caller still supplies the common witness to GKR.
pub fn h3(root: [u8; 32], total_be28: [u8; 28]) -> Result<Composition, String> {
    compose(3, root, total_be28)
}

/// Compose the exact H4 row domains under the same global term cap as H3.
/// H4-specific term counts are derived from the component constructors and
/// emitters; only the frozen H3 counts remain literal regression checks.
pub fn h4(root: [u8; 32], total_be28: [u8; 28]) -> Result<Composition, String> {
    compose(4, root, total_be28)
}

/// Add the early Mainnet DAA inheritance equalities to the unchanged H4
/// composition. Slots 0, 1, and 2 represent children 2, 3, and 4; slot 3 is
/// padding and receives no DAA terms. B4 work bits are numeric child nBits.
pub fn h4_early_daa(root: [u8; 32], total_be28: [u8; 28]) -> Result<Composition, String> {
    let mut composed = h4(root, total_be28)?;
    let endpoints = layout::inspect_baseline()?.endpoints;
    if endpoints.work.len() != DAA_BITS {
        return Err("B4 work endpoint width differs from 224 bits".into());
    }

    let term_end = composed.circuit.terms.len().checked_add(3 * DAA_BITS)
        .ok_or("early DAA term count overflow")?;
    reserve_terms(&composed.circuit.terms, 3 * DAA_BITS)?;
    if term_end != EXPECTED_H4_EARLY_DAA_TERMS {
        return Err(format!("early DAA term count mismatch: {term_end}"));
    }
    composed.circuit.terms.try_reserve(3 * DAA_BITS)
        .map_err(|_| "early DAA term allocation failed")?;

    let row_start = composed.reserved_rows;
    let row_end = row_start.checked_add(3 * DAA_BITS).ok_or("early DAA row count overflow")?;
    if row_end > composed.circuit.row_count
        || composed.circuit.terms.iter().any(|term| term.row >= row_start) {
        return Err("early DAA row range overlaps existing terms or exceeds the circuit".into());
    }
    let input_len = composed.circuit.input_len;
    let mut work_wires = Vec::with_capacity(DAA_BITS);
    for &wire in &endpoints.work {
        if wire >= layout::WIDTH { return Err("B4 work endpoint outside one input slot".into()); }
        work_wires.push(wire);
    }

    let slot2_base = layout::WIDTH.checked_mul(2).ok_or("height-4 DAA slot offset overflow")?;
    let one = ark_bn254::Fr::from(1u64);
    for bit in 0..DAA_BITS {
        let initial_bit = if bit < u64::BITS as usize { (GENESIS_DIFFICULTY >> bit) & 1 } else { 0 };
        let wire = work_wires[bit];
        if wire >= input_len { return Err("genesis DAA wire outside public input".into()); }
        composed.circuit.terms.push(Term { row: row_start + bit, gate: crate::gkr::Gate {
            left: wire, right: 0, c0: -ark_bn254::Fr::from(initial_bit),
            c1: one, c2: ark_bn254::Fr::zero(), c3: ark_bn254::Fr::zero(),
        }});
    }

    for bit in 0..DAA_BITS {
        let wire = work_wires[bit];
        let slot1_wire = layout::WIDTH.checked_add(wire).ok_or("height-3 work wire overflow")?;
        if slot1_wire >= input_len { return Err("height-3 DAA wire outside public input".into()); }
        composed.circuit.terms.push(Term { row: row_start + DAA_BITS + bit, gate: crate::gkr::Gate {
            left: slot1_wire, right: wire, c0: ark_bn254::Fr::zero(),
            c1: one, c2: -one, c3: ark_bn254::Fr::zero(),
        }});
    }

    for bit in 0..DAA_BITS {
        let wire = work_wires[bit];
        let slot1_wire = layout::WIDTH.checked_add(wire).ok_or("height-3 work wire overflow")?;
        let slot2_wire = slot2_base.checked_add(wire).ok_or("height-4 work wire overflow")?;
        if slot2_wire >= input_len { return Err("height-4 DAA wire outside public input".into()); }
        composed.circuit.terms.push(Term { row: row_start + 2 * DAA_BITS + bit, gate: crate::gkr::Gate {
            left: slot2_wire, right: slot1_wire, c0: ark_bn254::Fr::zero(),
            c1: one, c2: -one, c3: ark_bn254::Fr::zero(),
        }});
    }

    composed.component_rows.try_reserve(3).map_err(|_| "early DAA component allocation failed")?;
    composed.component_rows.extend([
        ("daa-genesis".into(), DAA_BITS),
        ("daa-inherit-height3".into(), DAA_BITS),
        ("daa-inherit-height4".into(), DAA_BITS),
    ]);
    composed.reserved_rows = row_end;
    composed.live_rows = composed.live_rows.checked_add(3 * DAA_BITS)
        .ok_or("early DAA live row count overflow")?;
    if composed.circuit.terms.len() != EXPECTED_H4_EARLY_DAA_TERMS
        || composed.component_rows.iter().map(|(_, rows)| *rows).sum::<usize>() != composed.reserved_rows {
        return Err("early DAA composition counts are inconsistent".into());
    }
    Ok(composed)
}

fn compose(headers: usize, root: [u8; 32], total_be28: [u8; 28]) -> Result<Composition, String> {
    if !matches!(headers, 3 | 4) { return Err("composition supports exactly H3 or H4".into()); }
    let d = Descriptor::new(headers, root)?;
    let baseline = layout::inspect_baseline()?;
    let old = header_compact_links::build(None)?;
    let legacy = &old.base.base.base.boundary;
    if legacy.input_len != layout::WIDTH || legacy.row_count != 1 << 19
        || legacy.terms.len() != baseline.inventory.old_boundary_terms
        || layout::hash_terms(&legacy.terms) != baseline.inventory.old_boundary_blake2b256 {
        return Err("legacy H3 boundary no longer matches the checked inventory".into());
    }

    let mut retired = vec![false; legacy.row_count];
    for item in &baseline.inventory.retired {
        if item.last_row >= retired.len() { return Err("retired legacy row outside boundary".into()); }
        for row in item.first_row..=item.last_row {
            if retired[row] { return Err("overlapping legacy retirement ranges".into()); }
            retired[row] = true;
        }
    }
    // B3 replaces 26 zero anchors in the old global-padding range. They are
    // verified by replacement_inventory(), but are intentionally not part of
    // the earlier B1 inventory because those coordinates were reserved later.
    let typed = baseline.inventory.retired.iter().find(|r| r.role == "typed_endpoints")
        .ok_or("missing checked B1 endpoint anchor inventory")?;
    let aux_first = typed.first_row.checked_sub(layout::ENDPOINT_BASE - leaf::AUX)
        .ok_or("B3 auxiliary anchor row underflow")?;
    for i in 0..leaf::AUX_BITS {
        let row = aux_first + i;
        if row >= retired.len() || retired[row] { return Err("B3 auxiliary anchor row overlap/range".into()); }
        let first = legacy.terms.partition_point(|t| t.row < row);
        let end = legacy.terms.partition_point(|t| t.row <= row);
        let expected = Term { row, gate: crate::gkr::Gate { left: leaf::AUX + i, right: 0,
            c0: ark_bn254::Fr::zero(), c1: ark_bn254::Fr::from(1u64),
            c2: ark_bn254::Fr::zero(), c3: ark_bn254::Fr::zero() } };
        if legacy.terms.get(first..end) != Some(std::slice::from_ref(&expected)) {
            return Err(format!("B3 auxiliary anchor mismatch at row {row}"));
        }
        retired[row] = true;
    }
    let removed = baseline.inventory.checked_retired_terms + leaf::AUX_BITS;
    let actual_removed = legacy.terms.iter().filter(|t| retired[t.row]).count();
    if actual_removed != removed || legacy.terms.iter().any(|t| t.row >= retired.len()) {
        return Err("legacy anchor retirement count mismatch".into());
    }

    let mut terms = Vec::with_capacity(EXPECTED_TERMS.min(MAX_TERMS));
    let mut components = Vec::new();
    let mut row_base = 0usize;
    for slot in 0..d.slots {
        let before = terms.len();
        let kept = legacy.terms.iter().filter(|t| !retired[t.row]).cloned().collect::<Vec<_>>();
        reserve_terms(&terms, kept.len())?;
        append_shifted(&mut terms, kept, row_base, slot * layout::WIDTH);
        components.push((format!("legacy-slot-{slot}"), legacy.row_count));
        row_base += legacy.row_count;
        if headers == 3 && terms.len() - before != baseline.inventory.unrelated_terms_retained - leaf::AUX_BITS {
            return Err("legacy retained terms-per-slot changed".into());
        }
    }

    let tree = topology::Topology::new(&baseline, d.headers, root)?;
    let before_b1 = terms.len();
    for family in &tree.families {
        let c = family.enumerate(&tree.descriptor, MAX_TERMS)?;
        reserve_terms(&terms, c.terms.len())?;
        append_shifted(&mut terms, c.terms, row_base, 0);
        components.push((format!("b1:{}", family.name), c.row_count));
        row_base += c.row_count;
    }
    if headers == 3 && terms.len() - before_b1 != 33_580 {
        return Err("B1 materialized term count differs from fresh receipt".into());
    }

    let engine = fixed::engine()?;
    let profile2 = fixed::FixedProfile::new(d.headers, root)?;
    let counts2 = fixed::count(engine, &profile2)?;
    let new_b2 = counts2.new_boundary_terms as usize;
    reserve_terms(&terms, new_b2)?;
    let before_b2 = terms.len();
    for slot in 0..d.slots {
        fixed::emit_slot(engine, &profile2, slot, |term| {
            let local = term.row - slot * fixed::ROW_WIDTH;
            let role = profile2.role(slot).expect("slot range is frozen");
            // B1 already carries these exact endpoint-to-core equalities.
            let repeated_child_alias = matches!(role, fixed::Role::Node { .. })
                && (512 + 6 * 8..512 + 70 * 8).contains(&local);
            let repeated_digest_alias = !matches!(role, fixed::Role::Dummy)
                && (fixed::DIGEST_ROW..fixed::DIGEST_ROW + 256).contains(&local);
            if !repeated_child_alias && !repeated_digest_alias {
                let mut shifted = term;
                shifted.row += row_base;
                terms.push(shifted);
            }
        })?;
    }
    if terms.len() - before_b2 != new_b2 || (headers == 3 && new_b2 != 7_250) {
        return Err(format!("B2 unique term count mismatch: emitted {}, expected {new_b2}", terms.len() - before_b2));
    }
    components.push(("b2-fixed".into(), counts2.padded_boundary_rows as usize));
    row_base += counts2.padded_boundary_rows as usize;

    let profile3 = leaf::LeafProfile::new(d.headers, root)?;
    let boundary3 = leaf::compile(engine, profile3)?;
    let count3 = leaf::count(engine, &boundary3)?;
    let new_b3 = count3["new_boundary_terms"].as_u64().ok_or("B3 term count missing")? as usize;
    reserve_terms(&terms, new_b3)?;
    let before_b3 = terms.len();
    for slot in 0..d.slots {
        boundary3.emit_slot(slot, |mut term| { term.row += row_base; terms.push(term); })?;
    }
    let padded3 = count3["padded_boundary_rows"].as_u64().ok_or("B3 padded rows missing")? as usize;
    if terms.len() - before_b3 != new_b3 || (headers == 3 && new_b3 != 61_588) {
        return Err("B3 materialized term count differs from fresh receipt".into());
    }
    components.push(("b3-leaf".into(), padded3));
    row_base += padded3;

    let profile4 = work::WorkProfile::new(d.headers, root, total_be28)?;
    let boundary4 = work::compile(&baseline, profile4)?;
    let count4 = work::count(&boundary4)?;
    let new_b4 = count4["new_total_terms"].as_u64().ok_or("B4 term count missing")? as usize;
    reserve_terms(&terms, new_b4)?;
    let before_b4 = terms.len();
    for slot in 0..d.slots {
        boundary4.emit_slot(slot, |mut term| { term.row += row_base; terms.push(term); })?;
    }
    components.push(("b4-work-local".into(), work::LOCAL_ROW_WIDTH * d.slots));
    row_base += work::LOCAL_ROW_WIDTH * d.slots;
    let links = boundary4.links();
    let mut link_rows = 0usize;
    for link in links {
        let c = link.enumerate(&d, MAX_TERMS)?;
        link_rows += c.row_count;
        append_shifted(&mut terms, c.terms, row_base, 0);
        components.push((format!("b4:{}", link.name), c.row_count));
        row_base += c.row_count;
    }
    if terms.len() - before_b4 != new_b4
        || (headers == 3 && new_b4 != 7_202)
        || count4["new_link_terms"].as_u64().is_none()
        || link_rows == 0 {
        return Err("B4 local/link materialization differs from fresh receipt".into());
    }

    if (headers == 3 && terms.len() != EXPECTED_TERMS) || terms.len() > MAX_TERMS {
        return Err(format!("composed boundary term budget mismatch: {}", terms.len()));
    }
    let padded_rows = row_base.checked_next_power_of_two().ok_or("row count overflow")?;
    if headers == 3 && padded_rows != 1 << 22 {
        return Err(format!("composed row domain changed: {padded_rows}"));
    }
    if terms.iter().any(|t| t.row >= padded_rows || t.gate.left >= d.slots * layout::WIDTH
        || t.gate.right >= d.slots * layout::WIDTH) {
        return Err("composed term outside public input/row domain".into());
    }
    let live_rows = terms.iter().map(|t| t.row).collect::<std::collections::BTreeSet<_>>().len();
    Ok(Composition { circuit: Circuit { input_len: d.slots * layout::WIDTH,
        row_count: padded_rows, terms }, live_rows, reserved_rows: row_base, component_rows: components,
        removed_legacy_terms_per_slot: removed })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn h3_components_materialize_into_one_disjoint_bounded_circuit() {
        let composed = h3([0; 32], [0; 28]).unwrap();
        assert_eq!(composed.circuit.input_len, 1 << 22);
        assert_eq!(composed.circuit.row_count, 1 << 22);
        assert_eq!(composed.circuit.terms.len(), EXPECTED_TERMS);
        assert_eq!(composed.removed_legacy_terms_per_slot, 209_632);
        assert_eq!(composed.live_rows, 862_310);
        assert_eq!(composed.reserved_rows, 2_297_856);
        assert_eq!(composed.component_rows.iter().map(|(_, rows)| *rows).sum::<usize>(), composed.reserved_rows);
        assert!(composed.reserved_rows < composed.circuit.row_count);
        assert!(composed.component_rows.iter().any(|(name, rows)| name == "b4:work_first_lower_zero" && *rows > 0));
        assert!(composed.component_rows.iter().any(|(name, rows)| name == "b4:work_interval_continuity" && *rows > 0));
        assert!(composed.component_rows.iter().any(|(name, rows)| name == "b4:work_public_total" && *rows > 0));

        // The new B3 selectors must be able to be one-hot after the old zero
        // anchors are removed. This is a focused satisfiability check, not a
        // witness for the complete composed circuit.
        let leaf_base = composed.component_rows.iter().take_while(|(name, _)| name != "b3-leaf")
            .map(|(_, rows)| *rows).sum::<usize>();
        let engine = fixed::engine().unwrap();
        let b3 = leaf::compile(engine, leaf::LeafProfile::new(3, [0; 32]).unwrap()).unwrap();
        let one_hot = b3.family("genuine_last_one_hot").unwrap();
        let selector_value = |wire: usize| if wire == leaf::AUX { ark_bn254::Fr::from(1u64) }
            else { ark_bn254::Fr::zero() };
        let residual = composed.circuit.terms.iter().filter(|t| t.row == leaf_base + one_hot.start)
            .map(|t| { let g = &t.gate; g.c0 + g.c1 * selector_value(g.left)
                + g.c2 * selector_value(g.right) + g.c3 * selector_value(g.left) * selector_value(g.right) })
            .sum::<ark_bn254::Fr>();
        assert!(residual.is_zero());

        let baseline = layout::inspect_baseline().unwrap();
        let typed = baseline.inventory.retired.iter().find(|r| r.role == "typed_endpoints").unwrap();
        let aux_first = typed.first_row - (layout::ENDPOINT_BASE - leaf::AUX);
        for row in aux_first..aux_first + leaf::AUX_BITS {
            assert!(!composed.circuit.terms.iter().any(|t| t.row == row));
        }
        // Reintroducing even the first legacy anchor makes selector[0]=1 fail.
        let reintroduced_anchor = ark_bn254::Fr::from(1u64) * selector_value(leaf::AUX);
        assert!(!reintroduced_anchor.is_zero());
    }

    #[test]
    fn h4_composition_reuses_components_within_the_global_term_cap() {
        let composed = h4([0; 32], [0; 28]).unwrap();
        assert_eq!(composed.circuit.input_len, 1 << 22);
        assert_eq!(composed.circuit.terms.len(), EXPECTED_H4_TERMS);
        assert_eq!(composed.live_rows, 859_697);
        assert_eq!(composed.reserved_rows, 2_299_904);
        assert_eq!(composed.circuit.row_count, 4_194_304);
        assert!(composed.circuit.terms.len() <= MAX_TERMS);
        assert_eq!(composed.component_rows.iter().map(|(_, rows)| *rows).sum::<usize>(), composed.reserved_rows);
        assert_eq!(composed.removed_legacy_terms_per_slot, 209_632);
        assert!(composed.component_rows.iter().any(|(name, _)| name == "legacy-slot-3"));
        assert!(composed.component_rows.iter().any(|(name, rows)| name == "b4:work_first_lower_zero" && *rows > 0));
        assert!(composed.component_rows.iter().any(|(name, rows)| name == "b4:work_interval_continuity" && *rows > 0));
        assert!(composed.component_rows.iter().any(|(name, rows)| name == "b4:work_public_total" && *rows > 0));
    }

    #[test]
    fn h4_early_daa_appends_exact_bounded_inheritance_relations() {
        let base = h4([0; 32], [0; 28]).unwrap();
        let extended = h4_early_daa([0; 32], [0; 28]).unwrap();
        let base_terms = base.circuit.terms.len();
        let daa_terms = &extended.circuit.terms[base_terms..];
        let work = layout::inspect_baseline().unwrap().endpoints.work;
        let rows = base.reserved_rows;

        assert_eq!(base_terms, EXPECTED_H4_TERMS);
        assert_eq!(extended.circuit.terms.len(), EXPECTED_H4_EARLY_DAA_TERMS);
        assert_eq!(daa_terms.len(), 3 * DAA_BITS);
        assert_eq!(extended.circuit.terms[..base_terms], base.circuit.terms);
        assert_eq!(extended.circuit.input_len, 1 << 22);
        assert_eq!(extended.circuit.row_count, 4_194_304);
        assert_eq!(extended.circuit.row_count, base.circuit.row_count);
        assert_eq!(extended.live_rows, base.live_rows + 3 * DAA_BITS);
        assert_eq!(extended.reserved_rows, rows + 3 * DAA_BITS);
        assert_eq!(extended.component_rows.iter().map(|(_, n)| *n).sum::<usize>(), extended.reserved_rows);
        assert!(extended.circuit.terms.len() <= MAX_TERMS);
        assert!(base.circuit.terms.iter().all(|term| term.row < rows));
        assert!(extended.component_rows.iter().any(|(name, n)| name == "daa-genesis" && *n == DAA_BITS));
        assert!(extended.component_rows.iter().any(|(name, n)| name == "daa-inherit-height3" && *n == DAA_BITS));
        assert!(extended.component_rows.iter().any(|(name, n)| name == "daa-inherit-height4" && *n == DAA_BITS));

        let zero = ark_bn254::Fr::zero();
        let one = ark_bn254::Fr::from(1u64);
        for bit in 0..DAA_BITS {
            let genesis = if bit < u64::BITS as usize { (GENESIS_DIFFICULTY >> bit) & 1 } else { 0 };
            let anchor = &daa_terms[bit];
            assert_eq!(anchor.row, rows + bit);
            assert_eq!(anchor.gate.left, work[bit]);
            assert_eq!(anchor.gate.right, 0);
            assert_eq!(anchor.gate.c0, -ark_bn254::Fr::from(genesis));
            assert_eq!(anchor.gate.c1, one);
            assert_eq!(anchor.gate.c2, zero);
            assert_eq!(anchor.gate.c3, zero);

            let height3 = &daa_terms[DAA_BITS + bit];
            assert_eq!(height3.row, rows + DAA_BITS + bit);
            assert_eq!(height3.gate.left, layout::WIDTH + work[bit]);
            assert_eq!(height3.gate.right, work[bit]);
            assert_eq!(height3.gate.c0, zero);
            assert_eq!(height3.gate.c1, one);
            assert_eq!(height3.gate.c2, -one);
            assert_eq!(height3.gate.c3, zero);

            let height4 = &daa_terms[2 * DAA_BITS + bit];
            assert_eq!(height4.row, rows + 2 * DAA_BITS + bit);
            assert_eq!(height4.gate.left, 2 * layout::WIDTH + work[bit]);
            assert_eq!(height4.gate.right, layout::WIDTH + work[bit]);
            assert_eq!(height4.gate.c0, zero);
            assert_eq!(height4.gate.c1, one);
            assert_eq!(height4.gate.c2, -one);
            assert_eq!(height4.gate.c3, zero);
        }

        // Evaluate only the 672 new rows against a virtual witness. This keeps
        // the check small while checking both satisfying values and one-bit
        // deviations without allocating the 2^22 input vector.
        let value = |wire: usize, flipped: Option<usize>| {
            let slot = wire / layout::WIDTH;
            let local = wire % layout::WIDTH;
            let bit = local.checked_sub(work[0]);
            let mut bit_value = bit.filter(|&i| i < work.len() && work[i] == local)
                .map(|i| if i < u64::BITS as usize { (GENESIS_DIFFICULTY >> i) & 1 } else { 0 })
                .unwrap_or(0);
            if slot >= 3 { bit_value = 0; }
            if flipped == Some(wire) { bit_value ^= 1; }
            ark_bn254::Fr::from(bit_value)
        };
        let residual = |term: &Term, flipped: Option<usize>| {
            let a = value(term.gate.left, flipped);
            let b = value(term.gate.right, flipped);
            term.gate.c0 + term.gate.c1 * a + term.gate.c2 * b + term.gate.c3 * a * b
        };
        for term in daa_terms {
            assert!(term.row >= rows && term.row < extended.reserved_rows);
            assert!(term.gate.left < 3 * layout::WIDTH && term.gate.right < 3 * layout::WIDTH);
            assert!(residual(term, None).is_zero(), "satisfying early DAA row {}", term.row);
            assert!(!residual(term, Some(term.gate.left)).is_zero(), "single-bit deviation escaped row {}", term.row);
        }
    }
}
use ark_ff::Zero;

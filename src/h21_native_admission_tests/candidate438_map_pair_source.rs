//! Stage 0: no-frame Genesis Map ROW coactivity and candidate relocation.
//! This checks the current DAA ROW batch against exact Eligible08 Map terms;
//! it does not admit relocated rows to native RowPlan or load a proof frame.

use std::collections::BTreeSet;

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    bank53_map::{self, CutDescriptor, CONTEXT_ROW_BASE, MAP_ROW_STRIDE, MAP_TAIL_END,
        MAP_TAIL_START, ROW_STRIDE},
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    header_daa_row_placement::{Relation, RowPlan},
    h21_row_support::{relocate, Family},
    h21_scheduled_max_cap::Plan as ScheduledPlan,
    legacy_envelope_map::Map,
    native_owner_exports::NativeExports,
    packed_owner_assembly::{Eligible08MapPairLease, HeaderSourceBinding,
        H21EligibleContext, MapPairSourceAuthor, NativeOwnerProducer, NativePrefix,
        validate_native_plan_input},
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const N: usize = 1_827_840;
const SLOTS: usize = 1 << 21;
const OWNER_ROW_BITS: usize = 1 << 20;
const OWNER_ROW_BYTES: usize = OWNER_ROW_BITS / 8;
const BANK53_BASE: usize = 671_744;
const BANK53_CONTEXT_BITS: usize = 8_192;
const BANK53_MAP_LIVE_BITS: usize = bank53_map::MAP_LIVE;
const CONTEXT_ROW_STRIDE: usize = 32_768;
const MAP_SOURCE_SPAN: usize = 10_347;
const RELOCATED_BAND: std::ops::Range<usize> = 477_074..507_536;

fn independent_input(index: usize, owner: usize, context: usize) -> Result<usize, String> {
    let owner_base = owner.checked_mul(1 << 20).ok_or("C438 input owner overflow")?;
    if !(owner_base..owner_base + (1 << 20)).contains(&index) {
        return Ok(index);
    }
    let local = index - owner_base;
    let map_base = crate::legacy_envelope_map::BASE;
    if (map_base..map_base + bank53_map::MAP_LIVE).contains(&local) {
        return Ok(owner_base + bank53_map::CONTEXT_INPUT_BASE + context * 8_192
            + local - map_base);
    }
    if (map_base + MAP_TAIL_START..map_base + MAP_TAIL_END).contains(&local) {
        return Err("C438 retained Map term reads a retired helper tail".into());
    }
    Ok(index)
}

fn independent_translation(source: &[Term], owner: usize, context: usize)
    -> Result<Vec<Term>, String>
{
    if owner >= SLOTS || context > 1 {
        return Err("C438 owner/context outside H21".into());
    }
    let old_base = owner.checked_mul(MAP_ROW_STRIDE).ok_or("C438 source row overflow")?;
    let row_end = old_base.checked_add(MAP_ROW_STRIDE).ok_or("C438 source row end overflow")?;
    let owner_input = owner.checked_mul(1 << 20).ok_or("C438 input base overflow")?;
    let row_base = owner.checked_mul(ROW_STRIDE)
        .and_then(|x| x.checked_add(CONTEXT_ROW_BASE + context * CONTEXT_ROW_STRIDE))
        .ok_or("C438 physical row base overflow")?;
    let mut tail = vec![false; MAP_TAIL_END - MAP_TAIL_START];
    let mut out = Vec::with_capacity(source.len().saturating_sub(tail.len()));
    for term in source {
        if !(old_base..row_end).contains(&term.row) {
            return Err("C438 source ROW outside Map owner bank".into());
        }
        let q = term.row - old_base;
        if (MAP_TAIL_START..MAP_TAIL_END).contains(&q) {
            let seen = &mut tail[q - MAP_TAIL_START];
            if *seen { return Err("C438 duplicate exact-zero tail row".into()); }
            let g = &term.gate;
            if g.left != owner_input + crate::legacy_envelope_map::BASE + q
                || g.right != owner_input || g.c0 != Fr::zero() || g.c1 != Fr::one()
                || g.c2 != Fr::zero() || g.c3 != Fr::zero() {
                return Err("C438 noncanonical exact-zero tail gate".into());
            }
            *seen = true;
            continue;
        }
        let mut moved = term.clone();
        moved.row = row_base.checked_add(q).ok_or("C438 translated row overflow")?;
        moved.gate.left = independent_input(moved.gate.left, owner, context)?;
        moved.gate.right = independent_input(moved.gate.right, owner, context)?;
        out.push(moved);
    }
    if tail.iter().any(|seen| !*seen) { return Err("C438 incomplete zero-tail census".into()); }
    Ok(out)
}

fn same_ordered_terms(actual: &[Term], expected: &[Term]) -> Result<(), String> {
    if actual.len() != expected.len() { return Err("C438 term count differs".into()); }
    for (ordinal, (a, e)) in actual.iter().zip(expected).enumerate() {
        if a != e { return Err(format!("C438 first full-tuple divergence at ordinal {ordinal}")); }
    }
    Ok(())
}

#[test]
fn c438_genesis_map_row_coactivity_no_frame() {
    let plan = WorkTreeHistoryPlan::compile(N as u64, 21, [0x38; 32], [0x38; 28])
        .expect("C438 source-only parent plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("C438 DAA history roster");
    assert_eq!(roster.owner_class(0).unwrap(), OwnerClass::Genesis);
    let cut = CutDescriptor::eligible08();
    let terminals = cut.terminals();
    assert_eq!(terminals, [N, 1_810_842]);
    let maps = [
        Map::new_modern_global_u(terminals[0] as u64, 21, 55).unwrap(),
        Map::new_modern_global_u(terminals[1] as u64, 21, 48).unwrap(),
    ];
    let schedule = ScheduledPlan::eligible08();
    let row_plan = RowPlan::new(&roster, &schedule).expect("exact Eligible08 ROW plan");
    let batch = row_plan.stage_owner(0).expect("actual Genesis owner0 ROW batch");
    let batch_rows = batch.terms().map(|(_, term)| term.row).collect::<BTreeSet<_>>();
    let lane3 = batch.terms().filter(|(relation, _)| *relation == Relation::DaaLane(3))
        .map(|(_, term)| term.row).collect::<BTreeSet<_>>();
    assert_eq!(lane3.len(), 81_920, "Genesis full zero lane source rows");
    assert!(lane3.iter().all(|row| (393_216..475_136).contains(row)));

    let mut retained = [Vec::<Term>::new(), Vec::<Term>::new()];
    let mut source_terms = [Vec::<Term>::new(), Vec::<Term>::new()];
    let mut raw_intersections = [0usize; 2];
    for context in 0..2 {
        source_terms[context] = maps[context].terms(0).expect("C438 symbolic Map source terms");
        assert!(source_terms[context].iter().all(|term|
            (0..MAP_SOURCE_SPAN).contains(&(term.row % MAP_ROW_STRIDE))),
            "C438 every source term fits its C145 Map-family row span");
        let translated = bank53_map::translate_map_terms_for_descriptor(
            &maps[context], 0, context, &source_terms[context], cut,
        ).expect("C438 exact Eligible08 source translation and tail retirement");
        let oracle = independent_translation(&source_terms[context], 0, context)
            .expect("C438 independent ordered translation oracle");
        same_ordered_terms(&translated, &oracle).unwrap();
        assert_eq!(source_terms[context].len() - translated.len(), MAP_TAIL_END - MAP_TAIL_START);
        assert_eq!(translated.len(), source_terms[context].len() - (MAP_TAIL_END - MAP_TAIL_START));
        let map_rows = translated.iter().map(|term| term.row).collect::<BTreeSet<_>>();
        raw_intersections[context] = map_rows.intersection(&lane3).count();
        assert_eq!(raw_intersections[context], map_rows.len(),
            "C438 every retained Map ROW collides with actual Genesis lane3");
        retained[context] = translated;
    }

    let mut relocated = [Vec::<Term>::new(), Vec::<Term>::new()];
    for context in 0..2 {
        relocated[context] = retained[context].iter()
            .map(|term| relocate(Family::Map(context), 0, term).expect("C145 Map relocation"))
            .collect();
        assert_eq!(relocated[context].len(), retained[context].len());
        for (ordinal, (before, after)) in retained[context].iter().zip(&relocated[context]).enumerate() {
            let mut expected = before.clone();
            expected.row = 0; // overwritten below by the independently derived offset
            let source_local = before.row - (CONTEXT_ROW_BASE + context * CONTEXT_ROW_STRIDE);
            expected.row = [477_074, 492_305][context] + source_local;
            if after != &expected { panic!("C438 relocation tuple divergence context={context} ordinal={ordinal}"); }
            assert!(RELOCATED_BAND.contains(&after.row));
            assert!(!batch_rows.contains(&after.row), "C438 relocated Map intersects actual owner0 ROW batch");
        }
    }
    let relocated_rows0 = relocated[0].iter().map(|t| t.row).collect::<BTreeSet<_>>();
    let relocated_rows1 = relocated[1].iter().map(|t| t.row).collect::<BTreeSet<_>>();
    assert!(relocated_rows0.is_disjoint(&relocated_rows1), "C438 Map destination spans overlap");
    assert!(relocated_rows0.is_disjoint(&batch_rows) && relocated_rows1.is_disjoint(&batch_rows));

    // Missing/duplicate retained terms do not qualify as successful source
    // translation even though the low-level translator only owns tail checks.
    for context in 0..2 {
        let first_live = source_terms[context].iter().position(|t|
            !(MAP_TAIL_START..MAP_TAIL_END).contains(&(t.row % MAP_ROW_STRIDE)))
            .expect("C438 live source term");
        let mut omitted = source_terms[context].clone(); omitted.remove(first_live);
        let translated = bank53_map::translate_map_terms_for_descriptor(
            &maps[context], 0, context, &omitted, cut,
        ).expect("C438 omission reaches ordered census");
        assert!(same_ordered_terms(&translated, &retained[context]).is_err(), "C438 omitted live term accepted");
        let mut duplicated = source_terms[context].clone(); duplicated.push(source_terms[context][first_live].clone());
        let translated = bank53_map::translate_map_terms_for_descriptor(
            &maps[context], 0, context, &duplicated, cut,
        ).expect("C438 duplicate reaches ordered census");
        assert!(same_ordered_terms(&translated, &retained[context]).is_err(), "C438 duplicate live term accepted");

        let first_tail = source_terms[context].iter().position(|t|
            (MAP_TAIL_START..MAP_TAIL_END).contains(&(t.row % MAP_ROW_STRIDE)))
            .expect("C438 explicit tail source term");
        let mut missing_tail = source_terms[context].clone(); missing_tail.remove(first_tail);
        assert!(bank53_map::translate_map_terms_for_descriptor(
            &maps[context], 0, context, &missing_tail, cut).is_err(), "C438 missing tail accepted");
        let mut duplicate_tail = source_terms[context].clone();
        duplicate_tail.push(source_terms[context][first_tail].clone());
        assert!(bank53_map::translate_map_terms_for_descriptor(
            &maps[context], 0, context, &duplicate_tail, cut).is_err(), "C438 duplicate tail accepted");
        let mut bad_tail = source_terms[context].clone(); bad_tail[first_tail].gate.c1 = Fr::zero();
        assert!(bank53_map::translate_map_terms_for_descriptor(
            &maps[context], 0, context, &bad_tail, cut).is_err(), "C438 malformed tail accepted");

        let mut shifted = relocated[context].clone(); shifted[0].row += 1;
        assert!(same_ordered_terms(&shifted, &relocated[context]).is_err(), "C438 shifted relocated ROW accepted");
        let mut changed_gate = relocated[context].clone(); changed_gate[0].gate.left += 1;
        assert!(same_ordered_terms(&changed_gate, &relocated[context]).is_err(), "C438 changed gate operand accepted");
    }

    println!("C438_GENESIS_ROW_DIAGNOSTIC owner=0 class=Genesis daa_lane3_terms={} map_source_terms={},{} map_retained_terms={},{} pre_relocation_lane3_intersections={},{} relocated_rows={},{}", lane3.len(), source_terms[0].len(), source_terms[1].len(), retained[0].len(), retained[1].len(), raw_intersections[0], raw_intersections[1], relocated_rows0.len(), relocated_rows1.len());
    println!("C438_GENESIS_ROW_GEOMETRY_FEASIBLE_OPEN owner=0 map_contexts=2 daa_lane3_collision=true relocated_disjoint=true native_rowplan_admission=false frame=false proof=false client=false");
}

#[test]
fn c438_map_pair_lease_no_frame_fail_closed() {
    use crate::legacy_envelope_map::{Kind, LowerBranch, LowerSelector, LowerSource};
    use crate::packed_owner_assembly::{
        c438_map_pair_claim_probe_for_test, preflight_map_pair_reservation,
        resolve_typed_map_import, Eligible08MapPairLease, HeaderSourceBinding,
        MapPairSourceAuthor,
    };

    let cut = CutDescriptor::eligible08();
    let terminals = cut.terminals();
    let selected_lower = LowerSelector {
        source: LowerSource::HeaderDifficulty { height: 841_729 },
        branch: LowerBranch::Pivot(54),
    };
    let maps = [
        Map::new_modern_global_u_selected_lower(
            terminals[0] as u64, 21, 55, selected_lower,
        ).unwrap(),
        Map::new_modern_global_u_selected_lower(
            terminals[1] as u64, 21, 55, selected_lower,
        ).unwrap(),
    ];
    let make = |owner: usize, class: OwnerClass| {
        let binding = HeaderSourceBinding::from_sink_for_test(
            [0x43; 32], [0x44; 28], [0x45; 32], cut.canonical_identity(), owner,
        );
        let lease = Eligible08MapPairLease::synthetic_valid_for_test(
            binding.clone(), owner, class, maps.clone(),
        ).unwrap();
        (binding, lease)
    };
    let owner = 0usize;
    let class = OwnerClass::Genesis;
    let (binding, good) = make(owner, class);
    let cells = good.checked_cells(&binding, owner, class).unwrap();
    assert_eq!(cells.len(), 11_514);
    assert_eq!(good.imports().len(), 2 * 224);
    assert!(good.imports().iter().all(|item| item.author() == MapPairSourceAuthor::Tree));
    assert_eq!(resolve_typed_map_import(Kind::Difficulty, None, Some(false)).unwrap(),
        (MapPairSourceAuthor::Tree, false));
    assert!(resolve_typed_map_import(Kind::Difficulty, None, None).is_err(),
        "an unresolved source cannot become an implicit zero");
    assert!(resolve_typed_map_import(Kind::Difficulty, Some(false), Some(false)).is_err());
    assert!(resolve_typed_map_import(Kind::Difficulty, Some(false), None).is_err());
    assert_eq!(resolve_typed_map_import(Kind::Timestamp, Some(false), None).unwrap(),
        (MapPairSourceAuthor::Header, false));
    assert!(resolve_typed_map_import(Kind::Timestamp, None, Some(false)).is_err());
    let mask = vec![false; 1 << 20];
    let reserved = preflight_map_pair_reservation(&good, &binding, owner, class, &mask).unwrap();
    assert_eq!(reserved.iter().filter(|bit| **bit).count(), 11_514);
    assert!(reserved[671_744] && reserved[671_744 + 5_756]);
    assert!(reserved[679_936] && reserved[679_936 + 5_756]);
    assert!(!reserved[671_744 + 5_757] && !reserved[679_936 + 5_757]);
    assert!(!good.reserves_local(671_744 + 5_757));
    assert_eq!(c438_map_pair_claim_probe_for_test(
        &good, &binding, owner, class, &mask, Some(671_744 + 5_757),
    ).unwrap(), 11_514);
    for prior in [671_744, 679_936 + 5_756] {
        // The probe preclaims the same zero value as the synthetic Map cell:
        // value equality must never turn a second author into permission.
        let overlap = c438_map_pair_claim_probe_for_test(
            &good, &binding, owner, class, &mask, Some(prior),
        ).unwrap_err();
        assert!(overlap.contains("overlaps"), "unexpected rejection: {overlap}");
    }

    for field in 0..6 {
        let wrong = binding.mutated_field_for_test(field);
        assert!(good.checked_cells(&wrong, owner, class).is_err(), "binding field {field}");
    }
    assert!(good.checked_cells(&binding, owner, OwnerClass::Initial).is_err());
    assert!(good.checked_cells(&binding, owner + 1, class).is_err());
    let mut wrong_mask = mask.clone(); wrong_mask[671_744] = true;
    assert!(preflight_map_pair_reservation(&good, &binding, owner, class, &wrong_mask).is_err());
    let mut other_mask = mask.clone(); other_mask[671_744 + 5_757] = true;
    assert_eq!(preflight_map_pair_reservation(
        &good, &binding, owner, class, &other_mask,
    ).unwrap().iter().filter(|bit| **bit).count(), 11_514);

    let mut swapped = good.clone(); swapped.swap_cell_contexts_for_test();
    assert!(swapped.checked_cells(&binding, owner, class).is_err());
    for index in [0, 5_756, 5_757, 11_513] {
        let mut missing = good.clone(); missing.remove_cell_for_test(index);
        assert!(missing.checked_cells(&binding, owner, class).is_err(), "missing cell {index}");
        let mut duplicate = good.clone(); duplicate.duplicate_cell_for_test(index);
        assert!(duplicate.checked_cells(&binding, owner, class).is_err(), "duplicate cell {index}");
    }
    let mut non_boolean = good.clone(); non_boolean.mutate_cell_value_for_test(0, 2);
    assert!(non_boolean.checked_cells(&binding, owner, class).is_err());
    let mut non_map = good.clone(); non_map.shift_cell_wire_for_test(5_756, 1);
    assert!(preflight_map_pair_reservation(&non_map, &binding, owner, class, &mask).is_err());
    let mut author = good.clone(); author.mutate_import_author_for_test(0, MapPairSourceAuthor::Header);
    assert!(author.checked_cells(&binding, owner, class).is_err());
    let mut unresolved = good.clone(); unresolved.imports_mut_for_test().remove(0);
    assert!(unresolved.checked_cells(&binding, owner, class).is_err());
    let mut non_boolean_import = good.clone(); non_boolean_import.mutate_import_value_for_test(0, 2);
    assert!(non_boolean_import.checked_cells(&binding, owner, class).is_err());
    let mut source_layout = good.clone(); source_layout.mutate_import_binding_field_for_test(0, 4);
    assert!(source_layout.checked_cells(&binding, owner, class).is_err());
    let mut missing_term = good.clone();
    let mut terms = missing_term.terms(0).unwrap().to_vec(); terms.remove(0);
    missing_term.replace_terms_for_test(0, terms).unwrap();
    assert!(missing_term.checked_cells(&binding, owner, class).is_err());
    let mut wrong_lower = good.clone();
    wrong_lower.replace_map_for_test(0,
        Map::new_modern_global_u(terminals[0] as u64, 21, 55).unwrap()).unwrap();
    assert!(wrong_lower.checked_cells(&binding, owner, class).is_err(),
        "selected lower binding changed");
    let mut wrong_exponent = good.clone();
    wrong_exponent.replace_map_for_test(1,
        Map::new_modern_global_u(terminals[1] as u64, 21, 54).unwrap()).unwrap();
    assert!(wrong_exponent.checked_cells(&binding, owner, class).is_err(),
        "Map exponent changed");
    for context in 0..2 {
        let mut missing_tail = good.clone(); missing_tail.tails_mut_for_test()[context].pop();
        assert!(missing_tail.checked_cells(&binding, owner, class).is_err());
        let mut duplicate_tail = good.clone(); duplicate_tail.tails_mut_for_test()[context].push(0);
        assert!(duplicate_tail.checked_cells(&binding, owner, class).is_err());
        let mut nonzero_tail = good.clone(); nonzero_tail.tails_mut_for_test()[context][0] = 1;
        assert!(nonzero_tail.checked_cells(&binding, owner, class).is_err());
    }

    // An anchor with a nonzero tier imports serializer timestamps as Header,
    // in addition to Tree-owned difficulty. This remains synthetic geometry.
    let anchor_owner = 1_983usize;
    let (anchor_binding, anchor) = make(anchor_owner, OwnerClass::Initial);
    let timestamp = anchor.imports().iter().position(|item| item.kind() == Kind::Timestamp)
        .expect("tier-one anchor timestamp import");
    assert_eq!(anchor.imports()[timestamp].author(), MapPairSourceAuthor::Header);
    let mut wrong_timestamp_author = anchor.clone();
    wrong_timestamp_author.mutate_import_author_for_test(timestamp, MapPairSourceAuthor::Tree);
    assert!(wrong_timestamp_author.checked_cells(
        &anchor_binding, anchor_owner, OwnerClass::Initial,
    ).is_err());

    println!("C438_MAP_PAIR_NO_FRAME_PASS two_contexts=true exact_live_cells=11514 wrong_binding_rejected=true missing_duplicate_zero_rejected=true frame=false proof=false client=false");
}

fn packed_bit(bytes: &[u8], local_wire: usize) -> bool {
    bytes[local_wire / 8] & (1 << (local_wire % 8)) != 0
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed single-process bounded Job required"]
fn c438_authenticated_owner0_and_eip_seam_map_pair_source() -> Result<(), String> {
    let path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("pinned H21 frame path required")?;
    let path = std::path::Path::new(&path);
    if !path.is_absolute() {
        return Err("C438 H21 frame path must be absolute".into());
    }
    let before = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != super::FRAME_BYTES {
        return Err("C438 pinned H21 frame regular-file/length preflight".into());
    }
    let file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    if file.metadata().map_err(|e| e.to_string())?.len() != super::FRAME_BYTES {
        return Err("C438 opened H21 frame length".into());
    }
    let mut frame = super::FrameReader::new(
        std::io::BufReader::with_capacity(super::CHUNK, file), super::FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C438 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != super::PREFIX_BYTES
        || extensions != super::EXTENSIONS
    {
        return Err("C438 H21 frame prefix/extension census".into());
    }
    frame.finish(super::PREFIX_BYTES, super::TAIL_BYTES, super::FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, super::H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let context = H21EligibleContext::new(&plan, &prefix)?;
    let exports = NativeExports::new_for_history(&plan, &prefix)?;
    let owners = [0usize, 844_671, 844_672];
    for owner in owners {
        let class = roster.owner_class(owner as u64)?;
        let binding = HeaderSourceBinding::for_plan(&plan, owner)?;
        let lease: Eligible08MapPairLease = context.map_pair_lease(owner)?;
        let cells = lease.checked_cells(&binding, owner, class)?;
        if lease.binding() != &binding || cells.len() != 11_514 {
            return Err(format!("C438 owner{owner} paired parent/live census"));
        }

        let mut header_imports = 0usize;
        let mut tree_imports = 0usize;
        for import in lease.imports() {
            let required_author = match import.kind() {
                crate::legacy_envelope_map::Kind::Difficulty => MapPairSourceAuthor::Tree,
                crate::legacy_envelope_map::Kind::Timestamp => MapPairSourceAuthor::Header,
            };
            if import.author() != required_author
                || import.value() > 1
                || import.value() != exports.bit(import.physical_wire())? as u8
            {
                return Err(format!("C438 owner{owner} imported source author/value mismatch"));
            }
            match import.author() {
                MapPairSourceAuthor::Header => header_imports += 1,
                MapPairSourceAuthor::Tree => tree_imports += 1,
            }
        }

        let ordinary = producer.produce(owner)?;
        let mapped = producer.produce_with_map_pair_lease(owner, &lease)?;
        if ordinary.owner() != owner || mapped.owner() != owner
            || ordinary.packed_bytes().len() != OWNER_ROW_BYTES
            || mapped.packed_bytes().len() != OWNER_ROW_BYTES
        {
            return Err(format!("C438 owner{owner} packed row identity/size"));
        }
        let owner_base = owner.checked_mul(OWNER_ROW_BITS)
            .ok_or("C438 owner wire base overflow")?;
        let (generated_bindings, generated_spans) =
            context.generated_map_pair_for_test(owner)?;
        for map_context in 0..2 {
            if &generated_bindings[map_context] != lease.map_binding(map_context)?
                || generated_spans[map_context].len() != BANK53_MAP_LIVE_BITS
            {
                return Err(format!("C438 owner{owner} Map{map_context} direct generator binding/span"));
            }
            for offset in 0..BANK53_MAP_LIVE_BITS {
                let index = map_context * BANK53_MAP_LIVE_BITS + offset;
                let cell = cells.get(index).ok_or("C438 ordered Map lease cell missing")?;
                let local = BANK53_BASE + map_context * BANK53_CONTEXT_BITS + offset;
                let wire = owner_base.checked_add(local)
                    .ok_or("C438 expected Map physical wire overflow")?;
                if cell.context() != map_context || cell.offset() != offset
                    || cell.physical_wire() != wire || !lease.reserves_local(local)
                    || cell.value() != generated_spans[map_context][offset]
                    || packed_bit(mapped.packed_bytes(), local)
                        != generated_spans[map_context][offset]
                {
                    return Err(format!("C438 owner{owner} Map{map_context} direct span/lease/final mismatch offset={offset}"));
                }
            }
        }
        for local in 0..OWNER_ROW_BITS {
            if !lease.reserves_local(local)
                && packed_bit(mapped.packed_bytes(), local)
                    != packed_bit(ordinary.packed_bytes(), local)
            {
                return Err(format!("C438 owner{owner} non-Map source drift local={local}"));
            }
        }

        for map_context in 0..2 {
            let map_binding = lease.map_binding(map_context)?;
            if map_binding.n != [1_827_840, 1_810_842][map_context] as u64
                || map_binding.h != 21
                || map_binding.parent_root.is_some()
            {
                return Err(format!("C438 owner{owner} Map{map_context} cut binding"));
            }
            let local = BANK53_BASE + map_context * BANK53_CONTEXT_BITS;
            let generated = generated_spans[map_context][0];
            let ordinary_value = packed_bit(ordinary.packed_bytes(), local);
            let final_value = packed_bit(mapped.packed_bytes(), local);
            if final_value != generated {
                return Err(format!("C438 owner{owner} Map{map_context} first helper final value"));
            }
            let selected_lower_binding = format!("{:?}", map_binding);
            if !selected_lower_binding.contains("lower_selector")
                || !["HeaderDifficulty", "LegacyBound", "InitialI",
                    "Reset417792", "Reset417793"].iter()
                    .any(|source| selected_lower_binding.contains(source))
            {
                return Err(format!("C438 owner{owner} Map{map_context} lower identity absent"));
            }
            println!("C438_MAP_PAIR_SOURCE owner={owner} context={map_context} class={class:?} exponent={} local={local} ordinary_header={ordinary_value} generated_map={generated} final_value={final_value} final_author=Map({map_context}) selected_lower_binding={selected_lower_binding} imports_header={header_imports} imports_tree={tree_imports}", map_binding.e);
            if owner == 0 && map_context == 0 && ordinary_value {
                return Err("C438 owner0 ordinary HEADER source at first Map0 helper was not zero".into());
            }
        }
    }
    let after = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !after.is_file() || after.file_type().is_symlink() || after.len() != super::FRAME_BYTES {
        return Err("C438 pinned H21 frame changed during source test".into());
    }
    println!("C438_AUTHENTIC_MAP_PAIR_SOURCE_PASS owners=0,844671,844672 contexts=2 imported_sources_bound=true packed_live_bits_match=true proof=false client=false");
    Ok(())
}

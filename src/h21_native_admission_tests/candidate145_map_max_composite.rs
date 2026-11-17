//! c145 selected Map0 + scheduled MAX composition; c150 extends the same
//! atomic destination with the source-selected packed Map1 cut.
//! No proof, client, or full-history witness is implied.

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::Fr;
use ark_ff::Zero;

use super::super::candidate135_native_values::{active_addresses, Origin, X};
use super::{Candidate as BaseCandidate, Destination as BaseDestination, ParentId, Sources};
use crate::{
    bank53_map,
    daa_history_roster::WIDTH,
    h21_local_merged_ledger::{close_native_carry, NativeCarryLedger, RowWriter, XWriter},
    h21_row_support::{relocate, Family},
    h21_scheduled_max_cap::Writer as ScheduledWriter,
    legacy_envelope_map::{
        Binding, Import, Kind as ImportKind, LowerBranch, LowerSelector, LowerSource, Map,
    },
    packed_owner_assembly::{NativeOwnerProducer, NativePackedRow},
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const OWNER: usize = 844_670;
const NEXT_OWNER: usize = 844_798;
const MAP_LIVE: std::ops::Range<usize> = 671_744..677_501;
const MAP_PHYSICAL: std::ops::Range<usize> = 671_744..679_936;
const MAP_CONTEXT_STRIDE: usize = 8_192;
const MAX_BASE: [usize; 2] = [999_424, 1_000_097];

fn map_live(context: usize) -> Result<std::ops::Range<usize>, String> {
    if context > 1 {
        return Err("c150 Map context".into());
    }
    let start = MAP_LIVE.start + context * MAP_CONTEXT_STRIDE;
    Ok(start..start + MAP_LIVE.len())
}

fn pinned_parent() -> WorkTreeHistoryPlan {
    let root = decode_hex::<32>("93F74871644F3644E8CCA9579C353006CB12FF50064F82E7660AB5AC552A307B");
    let total = decode_hex::<28>("0000000000000000000000000000000000000094E7A1372670000000");
    WorkTreeHistoryPlan::compile(1_827_840, 21, root, total).unwrap()
}

fn decode_hex<const N: usize>(text: &str) -> [u8; N] {
    assert_eq!(text.len(), N * 2);
    let mut bytes = [0u8; N];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[index * 2..index * 2 + 2], 16).unwrap();
    }
    bytes
}

fn term_multiset(terms: &[Term]) -> BTreeMap<usize, Vec<(crate::gkr::Gate, usize)>> {
    let mut out = BTreeMap::new();
    for term in terms {
        let gates = out.entry(term.row).or_insert_with(Vec::new);
        if let Some((_, count)) = gates.iter_mut().find(|(gate, _)| gate == &term.gate) {
            *count += 1;
        } else {
            gates.push((term.gate.clone(), 1));
        }
    }
    out
}

fn same_term_multiset(left: &[Term], right: &[Term]) -> bool {
    let left = term_multiset(left);
    let right = term_multiset(right);
    left.len() == right.len()
        && left.iter().all(|(row, gates)| {
            right.get(row).is_some_and(|other| {
                gates.len() == other.len()
                    && gates.iter().all(|(gate, count)| {
                        other.iter().any(|(other_gate, other_count)| {
                            gate == other_gate && count == other_count
                        })
                    })
            })
        })
}

#[test]
fn c145_noframe_map0_relocated_occurrences_and_live_lease() {
    let plan = pinned_parent();
    let map = Map::from_parent_modern_global_u(
        &plan,
        55,
        LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        },
    )
    .unwrap();
    let physical = bank53_map::map_owner_terms(&map, OWNER as u64, 0).unwrap();
    let relocated = physical
        .iter()
        .map(|term| relocate(Family::Map(0), OWNER, term).unwrap())
        .collect::<Vec<_>>();
    let local = close_native_carry(&plan).unwrap();
    let source_map = local.relocated_map_terms(0).unwrap();

    assert_eq!(physical.len(), source_map.len());
    assert!(same_term_multiset(&relocated, &source_map));
    let map_rows = relocated
        .iter()
        .map(|term| term.row)
        .collect::<BTreeSet<_>>();
    let physical_rows = physical
        .iter()
        .map(|term| term.row)
        .collect::<BTreeSet<_>>();
    let local_rows = local.row_addresses().into_iter().collect::<BTreeSet<_>>();
    let relocated_intersection = map_rows.intersection(&local_rows).count();
    let physical_intersection = physical_rows.intersection(&local_rows).count();
    let mut physical_writer_breakdown = BTreeMap::<RowWriter, usize>::new();
    for row in physical_rows.intersection(&local_rows) {
        let writer = *local.rows().get(row).expect("intersection row has writer");
        *physical_writer_breakdown.entry(writer).or_default() += 1;
    }
    assert_eq!(relocated_intersection, map_rows.len());
    assert_eq!(physical_intersection, map_rows.len());
    assert_eq!(
        physical_writer_breakdown,
        BTreeMap::from([(RowWriter::Daa(3), map_rows.len())])
    );
    assert!(map_rows
        .iter()
        .all(|row| { local.rows().get(row) == Some(&RowWriter::Relocated(Family::Map(0))) }));

    let owner_base = OWNER * WIDTH;
    for local_x in MAP_LIVE.clone() {
        assert_eq!(
            local.x_writer_at(owner_base + local_x),
            Some(XWriter::Map(0))
        );
    }
    assert!((MAP_LIVE.end..MAP_PHYSICAL.end)
        .all(|local_x| local.x_writer_at(owner_base + local_x) != Some(XWriter::Map(0))));
    assert!(local.x_domains().iter().all(|(writer, domain)| {
        *writer != XWriter::Map(0)
            || (owner_base + MAP_LIVE.start <= domain.start
                && domain.end <= owner_base + MAP_LIVE.end)
    }));

    let imports = map.imports(OWNER as u64).unwrap();
    let active = active_addresses(&physical);
    let mut typed_read_addresses = BTreeSet::new();
    for address in &active {
        let source_owner = address / WIDTH;
        let local_x = address % WIDTH;
        if source_owner == OWNER && MAP_LIVE.contains(&local_x) {
            continue;
        }
        let matching = imports
            .iter()
            .filter(|import| {
                import.owner as usize == source_owner
                    && import.local <= local_x
                    && local_x < import.local + import.width
            })
            .count();
        assert_eq!(
            matching, 1,
            "Map active READ lacks one typed import at {address}"
        );
        typed_read_addresses.insert(*address);
    }

    let max_counts = [0usize, 1].map(|context| {
        local
            .scheduled_max_terms()
            .iter()
            .filter(|(writer, _)| {
                *writer
                    == ScheduledWriter::Max {
                        context,
                        end: OWNER + 2,
                    }
            })
            .count()
    });
    assert_eq!(max_counts, [2_690; 2]);
    let mut work_terms = Vec::new();
    plan.work_boundary()
        .emit_slot(OWNER, |term| work_terms.push(term))
        .unwrap();
    let (header_terms, _) =
        super::super::candidate135_native_values::collect_header_nbits_terms(&plan).unwrap();
    let max_terms = local
        .scheduled_max_terms()
        .iter()
        .map(|(_, term)| term.clone())
        .collect::<Vec<_>>();
    let work_active = active_addresses(&work_terms);
    let max_active = active_addresses(&max_terms);
    let cross_active = active_addresses(&header_terms);
    let selected_active = work_active
        .union(&max_active)
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&cross_active)
        .copied()
        .collect::<BTreeSet<_>>();
    let live_addresses = MAP_LIVE
        .clone()
        .map(|local_x| owner_base + local_x)
        .collect::<BTreeSet<_>>();
    let overlap_count = |terms: &[Term]| {
        active_addresses(terms)
            .intersection(&live_addresses)
            .count()
    };
    let work_live_overlap = overlap_count(&work_terms);
    let max_live_overlap = overlap_count(&max_terms);
    let cross_live_overlap = overlap_count(&header_terms);
    assert_eq!(
        cross_live_overlap, 0,
        "HEADER successor still reads transferred Map live cells"
    );
    assert_eq!(work_live_overlap, 0);
    assert_eq!(max_live_overlap, 0);
    let map_read_addresses = active
        .difference(&live_addresses)
        .copied()
        .collect::<BTreeSet<_>>();
    assert_eq!(typed_read_addresses, map_read_addresses);
    let map_selected_x_overlap = map_read_addresses
        .intersection(&selected_active)
        .copied()
        .collect::<BTreeSet<_>>();
    let selected_max_local = (0..2)
        .flat_map(|context| (0..673).map(move |offset| owner_base + MAX_BASE[context] + offset))
        .collect::<BTreeSet<_>>();
    let map_selected_max_local_overlap = map_read_addresses
        .intersection(&selected_max_local)
        .copied()
        .collect::<BTreeSet<_>>();
    assert!(
        map_selected_max_local_overlap.is_empty(),
        "Map typed READ overlaps a scheduled MAX writer"
    );
    let selected_next_r = (0..2)
        .flat_map(|context| (0..224).map(move |bit| NEXT_OWNER * WIDTH + MAX_BASE[context] + bit))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        max_active.intersection(&selected_next_r).count(),
        selected_next_r.len(),
        "c136 selected MAX does not activate all 448 next-R reads"
    );
    let map_selected_next_r_overlap = map_read_addresses
        .intersection(&selected_next_r)
        .copied()
        .collect::<BTreeSet<_>>();
    let selected_non_native = selected_next_r
        .union(&selected_max_local)
        .copied()
        .collect::<BTreeSet<_>>();
    let selected_native = selected_active
        .difference(&selected_non_native)
        .copied()
        .collect::<BTreeSet<_>>();
    for address in &map_selected_next_r_overlap {
        let local_x = address % WIDTH;
        let matches = imports
            .iter()
            .filter(|import| {
                import.owner as usize == NEXT_OWNER
                    && import.local <= local_x
                    && local_x < import.local + import.width
            })
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(matches.len(), 1, "Map next-R READ lacks exact typed import");
        let context = (0..2)
            .find(|context| (MAX_BASE[*context]..MAX_BASE[*context] + 224).contains(&local_x))
            .expect("selected next-R address has exact MAX context");
        let tag = MapCellTag::ForeignImport {
            owner: NEXT_OWNER,
            context: 0,
            import: matches[0],
        };
        assert!(typed_alias_matches(
            tag,
            Origin::MaxForeignRead {
                owner: NEXT_OWNER,
                context,
            },
            *address,
        ));
    }
    let map_selected_native_overlap = map_read_addresses
        .intersection(&selected_native)
        .copied()
        .collect::<BTreeSet<_>>();
    for address in &map_selected_native_overlap {
        let owner = address / WIDTH;
        let matches = imports
            .iter()
            .filter(|import| {
                import.owner as usize == owner
                    && import.local <= address % WIDTH
                    && address % WIDTH < import.local + import.width
            })
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(matches.len(), 1, "Map native READ lacks exact typed import");
        let tag = if owner == OWNER {
            MapCellTag::OwnImport {
                owner,
                context: 0,
                import: matches[0],
            }
        } else {
            MapCellTag::ForeignImport {
                owner,
                context: 0,
                import: matches[0],
            }
        };
        assert!(typed_alias_matches(tag, Origin::Native { owner }, *address));
    }
    let allowed_overlap = map_selected_next_r_overlap
        .union(&map_selected_native_overlap)
        .copied()
        .collect::<BTreeSet<_>>();
    assert_eq!(map_selected_x_overlap, allowed_overlap);
    for context in 0..2 {
        let start = owner_base + MAX_BASE[context];
        for offset in 0..673 {
            assert_eq!(
                local.x_writer_at(start + offset),
                Some(XWriter::Max(context)),
                "scheduled MAX context {context} lease offset {offset}"
            );
        }
    }

    println!(
        "C145_NOFRAME_MAP0_PASS physical_terms={} relocated_terms={} physical_rows={} map_rows={} local_rows={} relocated_row_intersection={} physical_row_intersection={} physical_row_writers={:?} live_map_cells={} physical_reserved_cells={} typed_map_reads={} scheduled_max_terms={:?} live_x_overlap_work={} live_x_overlap_MAX={} live_x_overlap_HEADERsuccessor={} map_selected_x_overlap={} map_selected_next_r_overlap={} map_selected_max_local_overlap={} map_selected_native_overlap={} row_multiset_exact=true tail_not_map_writer=true",
        physical.len(),
        relocated.len(),
        physical_rows.len(),
        map_rows.len(),
        local_rows.len(),
        relocated_intersection,
        physical_intersection,
        physical_writer_breakdown,
        MAP_LIVE.len(),
        MAP_PHYSICAL.len(),
        typed_read_addresses.len(),
        max_counts,
        work_live_overlap,
        max_live_overlap,
        cross_live_overlap,
        map_selected_x_overlap.len(),
        map_selected_next_r_overlap.len(),
        map_selected_max_local_overlap.len(),
        map_selected_native_overlap.len(),
    );
}

#[test]
fn c145_noframe_composite_kernel_is_role_scoped_and_atomic() {
    let work = Term {
        row: 707,
        gate: crate::gkr::Gate {
            left: 0,
            right: 0,
            c0: Fr::from(1u64),
            c1: Fr::zero(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    };
    let cross = Term {
        row: 707,
        gate: crate::gkr::Gate {
            left: 0,
            right: 0,
            c0: -Fr::from(1u64),
            c1: Fr::zero(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    };
    let concatenated = vec![work.clone(), cross.clone()];
    assert_eq!(
        evaluate_numeric(&concatenated, &BTreeMap::new())
            .unwrap()
            .get(&707),
        Some(&Fr::zero()),
        "raw-ROW cross-role mutant must collide in the legacy projection"
    );
    let empty: &[Term] = &[];
    let opposite_roles = [
        ("Work", std::slice::from_ref(&work)),
        ("MAX", empty),
        ("Map", empty),
        ("CROSS", std::slice::from_ref(&cross)),
    ];
    assert!(require_zero_roles(&opposite_roles, &BTreeMap::new())
        .unwrap_err()
        .contains("Work residual row707"));

    let no_roles = [
        ("Work", empty),
        ("MAX", empty),
        ("Map", empty),
        ("CROSS", empty),
    ];
    let last = OWNER * WIDTH + MAP_LIVE.end - 1;
    let earlier = last - 1;
    let duplicate_cells = BTreeMap::from([
        (
            earlier,
            MapCell {
                value: Fr::from(1u64),
                tag: MapCellTag::LiveWriter {
                    owner: OWNER,
                    context: 0,
                },
            },
        ),
        (
            last,
            MapCell {
                value: Fr::from(1u64),
                tag: MapCellTag::LiveWriter {
                    owner: OWNER,
                    context: 0,
                },
            },
        ),
    ]);
    let mut x = BTreeMap::from([(last, Fr::from(1u64))]);
    let mut provenance = BTreeMap::from([(
        last,
        CompositeProvenance::Base(Origin::Native { owner: OWNER }),
    )]);
    let x_before = x.clone();
    let provenance_before = provenance.clone();
    assert!(stage_common_x(&x, &provenance, &duplicate_cells, &no_roles)
        .unwrap_err()
        .contains("Map live X writer collision"));
    assert_eq!(x, x_before, "late writer collision changed source X");
    assert_eq!(
        provenance, provenance_before,
        "late writer collision changed source provenance"
    );

    let foreign_max_address = NEXT_OWNER * WIDTH + MAX_BASE[1] + 7;
    let foreign_import = Import {
        owner: NEXT_OWNER as u64,
        local: MAX_BASE[1] + 7,
        width: 1,
        kind: ImportKind::Difficulty,
    };
    let foreign_tag = MapCellTag::ForeignImport {
        owner: NEXT_OWNER,
        context: 0,
        import: foreign_import,
    };
    assert!(typed_alias_matches(
        foreign_tag,
        Origin::MaxForeignRead {
            owner: NEXT_OWNER,
            context: 1,
        },
        foreign_max_address,
    ));
    assert!(!typed_alias_matches(
        foreign_tag,
        Origin::MaxForeignRead {
            owner: NEXT_OWNER,
            context: 0,
        },
        foreign_max_address,
    ));
    assert!(!typed_alias_matches(
        foreign_tag,
        Origin::MaxForeignRead {
            owner: NEXT_OWNER - 1,
            context: 1,
        },
        foreign_max_address,
    ));
    let valid_alias_x = BTreeMap::from([(foreign_max_address, Fr::from(1u64))]);
    let valid_alias_provenance = BTreeMap::from([(
        foreign_max_address,
        CompositeProvenance::Base(Origin::MaxForeignRead {
            owner: NEXT_OWNER,
            context: 1,
        }),
    )]);
    let valid_alias_cell = BTreeMap::from([(
        foreign_max_address,
        MapCell {
            value: Fr::from(1u64),
            tag: foreign_tag,
        },
    )]);
    let (aliased_x, aliased_provenance) = stage_common_x(
        &valid_alias_x,
        &valid_alias_provenance,
        &valid_alias_cell,
        &no_roles,
    )
    .unwrap();
    assert_eq!(aliased_x, valid_alias_x);
    assert_eq!(aliased_provenance, valid_alias_provenance);

    let own_max_address = OWNER * WIDTH + MAX_BASE[0];
    let wrong_import = Import {
        owner: OWNER as u64,
        local: MAX_BASE[0],
        width: 1,
        kind: ImportKind::Difficulty,
    };
    let wrong_cells = BTreeMap::from([(
        own_max_address,
        MapCell {
            value: Fr::from(1u64),
            tag: MapCellTag::OwnImport {
                owner: OWNER,
                context: 0,
                import: wrong_import,
            },
        },
    )]);
    let mut wrong_x = BTreeMap::from([(own_max_address, Fr::from(1u64))]);
    let mut wrong_provenance = BTreeMap::from([(
        own_max_address,
        CompositeProvenance::Base(Origin::MaxLocal {
            owner: OWNER,
            context: 0,
        }),
    )]);
    let wrong_x_before = wrong_x.clone();
    let wrong_provenance_before = wrong_provenance.clone();
    assert!(
        stage_common_x(&wrong_x, &wrong_provenance, &wrong_cells, &no_roles)
            .unwrap_err()
            .contains("typed READ alias provenance/value")
    );
    assert_eq!(
        wrong_x, wrong_x_before,
        "wrong typed alias changed source X"
    );
    assert_eq!(
        wrong_provenance, wrong_provenance_before,
        "wrong typed alias changed source provenance"
    );

    let parent = ParentId {
        headers: 1,
        slot_log: 1,
        root: [1; 32],
        total: [2; 28],
        profile: [3; 32],
    };
    let mut projected_x = X::default();
    projected_x.cells.insert(
        OWNER * WIDTH + 17,
        (Fr::from(1u64), Origin::Native { owner: OWNER }),
    );
    let mut base_destination = BaseDestination::default();
    base_destination.parent = Some(parent);
    base_destination.x = projected_x.clone();
    let rows = BTreeSet::new();
    let domains = Vec::new();
    let before_projection = base_destination.clone();
    assert!(candidate_projection_matches_parts(
        Some(parent),
        None,
        &rows,
        &domains,
        empty,
        empty,
        &projected_x,
        &base_destination,
    ));
    base_destination
        .x
        .cells
        .get_mut(&(OWNER * WIDTH + 17))
        .unwrap()
        .0 = Fr::zero();
    let mutated_snapshot = base_destination.clone();
    assert!(!candidate_projection_matches_parts(
        Some(parent),
        None,
        &rows,
        &domains,
        empty,
        empty,
        &projected_x,
        &base_destination,
    ));
    assert_eq!(
        base_destination, mutated_snapshot,
        "base binding check mutated the destination"
    );
    assert_ne!(before_projection, mutated_snapshot);
}

#[test]
fn c150_noframe_map0_map1_share_one_x_and_fail_closed() {
    let plan = pinned_parent();
    let selector = LowerSelector {
        source: LowerSource::HeaderDifficulty { height: 841_729 },
        branch: LowerBranch::Pivot(54),
    };
    let source_map0 = Map::from_parent_modern_global_u(&plan, 55, selector).unwrap();
    let source_map1 = Map::new_modern_global_u_selected_lower(1_827_775, 21, 55, selector).unwrap();
    let source_terms0 = bank53_map::map_owner_terms(&source_map0, OWNER as u64, 0)
        .unwrap()
        .iter()
        .map(|term| relocate(Family::Map(0), OWNER, term).unwrap())
        .collect::<Vec<_>>();
    let source_terms1 = bank53_map::map_owner_terms(&source_map1, OWNER as u64, 1)
        .unwrap()
        .iter()
        .map(|term| relocate(Family::Map(1), OWNER, term).unwrap())
        .collect::<Vec<_>>();
    let ledger = close_native_carry(&plan).unwrap();
    let expected_terms0 = ledger.relocated_map_terms(0).unwrap();
    let expected_terms1 = ledger.relocated_map_terms(1).unwrap();
    assert!(same_term_multiset(&source_terms0, &expected_terms0));
    assert!(same_term_multiset(&source_terms1, &expected_terms1));
    let rows0 = source_terms0
        .iter()
        .map(|term| term.row)
        .collect::<BTreeSet<_>>();
    let rows1 = source_terms1
        .iter()
        .map(|term| term.row)
        .collect::<BTreeSet<_>>();
    assert!(
        rows0.is_disjoint(&rows1),
        "ledger Map0/Map1 ROW families collided"
    );
    let mut omitted_map1_terms = source_terms1.clone();
    omitted_map1_terms.pop();
    assert!(
        !same_term_multiset(&omitted_map1_terms, &expected_terms1),
        "omitted Map1 ROW term was accepted"
    );
    let parent = ParentId {
        headers: 1_827_840,
        slot_log: 21,
        root: [0x41; 32],
        total: [0x42; 28],
        profile: [0x43; 32],
    };
    let map0_x = OWNER * WIDTH + map_live(0).unwrap().start + 3;
    let map1_x = OWNER * WIDTH + map_live(1).unwrap().start + 7;
    let d_x = OWNER * WIDTH + 987_674 + 3;
    let d_import = Import {
        owner: OWNER as u64,
        local: 987_674 + 3,
        width: 1,
        kind: ImportKind::Difficulty,
    };
    let map1_import = Import {
        owner: OWNER as u64,
        local: map0_x % WIDTH,
        width: 1,
        kind: ImportKind::Difficulty,
    };
    let map0_cells = BTreeMap::from([
        (
            map0_x,
            MapCell {
                value: Fr::from(1u64),
                tag: MapCellTag::LiveWriter {
                    owner: OWNER,
                    context: 0,
                },
            },
        ),
        (
            d_x,
            MapCell {
                value: Fr::from(1u64),
                tag: MapCellTag::OwnImport {
                    owner: OWNER,
                    context: 0,
                    import: d_import,
                },
            },
        ),
    ]);
    let map0 = MapXStage {
        parent,
        owner: OWNER,
        context: 0,
        cells: &map0_cells,
        relocated_terms: &[],
    };
    let map1_cells = BTreeMap::from([
        (
            map0_x,
            MapCell {
                value: Fr::from(1u64),
                tag: MapCellTag::OwnImport {
                    owner: OWNER,
                    context: 1,
                    import: map1_import,
                },
            },
        ),
        (
            map1_x,
            MapCell {
                value: Fr::from(0u64),
                tag: MapCellTag::LiveWriter {
                    owner: OWNER,
                    context: 1,
                },
            },
        ),
        (
            d_x,
            MapCell {
                value: Fr::from(1u64),
                tag: MapCellTag::OwnImport {
                    owner: OWNER,
                    context: 1,
                    import: d_import,
                },
            },
        ),
    ]);
    let map1 = MapXStage {
        parent,
        owner: OWNER,
        context: 1,
        cells: &map1_cells,
        relocated_terms: &[],
    };
    let empty: &[Term] = &[];
    let before_x = BTreeMap::from([(d_x, Fr::from(1u64))]);
    let before_provenance = BTreeMap::from([(
        d_x,
        CompositeProvenance::Base(Origin::Native { owner: OWNER }),
    )]);
    let (paired_x, paired_provenance) = stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0,
        &map1,
        empty,
        empty,
        empty,
    )
    .unwrap();
    assert_eq!(
        paired_x.len(),
        3,
        "both Maps share base D and Map0's live X while adding disjoint Map1 live X"
    );
    assert_eq!(paired_x.get(&map0_x), Some(&Fr::from(1u64)));
    assert_eq!(paired_x.get(&map1_x), Some(&Fr::from(0u64)));
    assert_eq!(
        paired_x.get(&d_x),
        Some(&Fr::from(1u64)),
        "both Map contexts read the same base-native D value"
    );
    assert_eq!(
        paired_provenance.get(&map0_x),
        Some(&CompositeProvenance::Map(MapCellTag::LiveWriter {
            owner: OWNER,
            context: 0
        }))
    );
    assert_eq!(
        paired_provenance.get(&map1_x),
        Some(&CompositeProvenance::Map(MapCellTag::LiveWriter {
            owner: OWNER,
            context: 1
        }))
    );
    assert!(map_live(0).unwrap().end <= map_live(1).unwrap().start);

    let claims = paired_x
        .iter()
        .map(|(address, value)| {
            let provenance = paired_provenance
                .get(address)
                .copied()
                .expect("every paired X value has provenance");
            classify_selected_x(*address, *value, provenance).unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        claims.iter().map(|claim| claim.value).collect::<Vec<_>>(),
        vec![Fr::from(1u64), Fr::zero(), Fr::from(1u64)],
        "writer and import claims preserve their selected X values",
    );
    assert_eq!(
        claims
            .iter()
            .filter(|claim| claim.classification == SelectedXClassification::Writer)
            .count(),
        3,
        "both selected Map live cells and the existing D cell remain writers",
    );
    assert_eq!(
        claims
            .iter()
            .filter(|claim| claim.classification == SelectedXClassification::ImportedRead)
            .count(),
        0,
        "the paired destination retains its canonical writer provenance",
    );
    let import_read = classify_selected_x(
        d_x,
        paired_x[&d_x],
        CompositeProvenance::Map(MapCellTag::OwnImport {
            owner: OWNER,
            context: 0,
            import: d_import,
        }),
    )
    .unwrap();
    assert_eq!(
        import_read.classification,
        SelectedXClassification::ImportedRead,
        "the source Map OwnImport tag remains classified as a read",
    );
    assert_eq!(import_read.value, paired_x[&d_x]);

    let required_map1 = Term {
        row: 900,
        gate: crate::gkr::Gate {
            left: map1_x,
            right: 0,
            c0: Fr::zero(),
            c1: Fr::from(1u64),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    };
    let omitted_cells = BTreeMap::new();
    let omitted_terms = vec![required_map1.clone()];
    let omitted = MapXStage {
        cells: &omitted_cells,
        relocated_terms: &omitted_terms,
        ..MapXStage {
            parent,
            owner: OWNER,
            context: 1,
            cells: &omitted_cells,
            relocated_terms: &[],
        }
    };
    assert!(stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0,
        &omitted,
        empty,
        empty,
        empty
    )
    .unwrap_err()
    .contains("Map1 selected X missing"));
    assert_eq!(
        before_x,
        BTreeMap::from([(d_x, Fr::from(1u64))]),
        "failed pair staging mutated base X"
    );
    assert_eq!(
        before_provenance.get(&d_x),
        Some(&CompositeProvenance::Base(Origin::Native { owner: OWNER })),
        "failed pair staging mutated base provenance"
    );

    let nonzero = Term {
        row: 901,
        gate: crate::gkr::Gate {
            left: 0,
            right: 0,
            c0: Fr::from(1u64),
            c1: Fr::zero(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    };
    let work_bad = vec![nonzero.clone()];
    assert!(stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0,
        &map1,
        &work_bad,
        empty,
        empty
    )
    .unwrap_err()
    .contains("Work residual row901"));
    let max_bad = vec![nonzero.clone()];
    assert!(stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0,
        &map1,
        empty,
        &max_bad,
        empty
    )
    .unwrap_err()
    .contains("MAX residual row901"));
    let map0_bad = vec![nonzero.clone()];
    let map0_nonzero = MapXStage {
        relocated_terms: &map0_bad,
        ..MapXStage {
            parent,
            owner: OWNER,
            context: 0,
            cells: &map0_cells,
            relocated_terms: &[],
        }
    };
    assert!(stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0_nonzero,
        &map1,
        empty,
        empty,
        empty
    )
    .unwrap_err()
    .contains("Map0 residual row901"));
    let map1_bad = vec![nonzero.clone()];
    let map1_nonzero = MapXStage {
        relocated_terms: &map1_bad,
        ..MapXStage {
            parent,
            owner: OWNER,
            context: 1,
            cells: &map1_cells,
            relocated_terms: &[],
        }
    };
    assert!(stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0,
        &map1_nonzero,
        empty,
        empty,
        empty
    )
    .unwrap_err()
    .contains("Map1 residual row901"));
    let cross_bad = vec![nonzero];
    assert!(stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0,
        &map1,
        empty,
        empty,
        &cross_bad
    )
    .unwrap_err()
    .contains("CROSS residual row901"));

    let mut collision_x = BTreeMap::from([(map1_x, Fr::from(1u64))]);
    let mut collision_provenance = BTreeMap::from([(
        map1_x,
        CompositeProvenance::Base(Origin::Native { owner: OWNER }),
    )]);
    let before_collision_x = collision_x.clone();
    let before_collision_provenance = collision_provenance.clone();
    assert!(stage_map_pair_x(
        &collision_x,
        &collision_provenance,
        &map0,
        &map1,
        empty,
        empty,
        empty
    )
    .unwrap_err()
    .contains("Map live X writer collision"));
    assert_eq!(collision_x, before_collision_x);
    assert_eq!(collision_provenance, before_collision_provenance);

    let bad_alias = BTreeMap::from([(
        map0_x,
        MapCell {
            value: Fr::from(0u64),
            tag: MapCellTag::OwnImport {
                owner: OWNER,
                context: 1,
                import: map1_import,
            },
        },
    )]);
    let bad_terms = [];
    let bad_map1 = MapXStage {
        cells: &bad_alias,
        relocated_terms: &bad_terms,
        ..MapXStage {
            parent,
            owner: OWNER,
            context: 1,
            cells: &map1_cells,
            relocated_terms: &[],
        }
    };
    assert!(stage_map_pair_x(
        &before_x,
        &before_provenance,
        &map0,
        &bad_map1,
        empty,
        empty,
        empty
    )
    .unwrap_err()
    .contains("typed READ alias provenance/value"));
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MapCellTag {
    LiveWriter {
        owner: usize,
        context: usize,
    },
    OwnImport {
        owner: usize,
        context: usize,
        import: Import,
    },
    ForeignImport {
        owner: usize,
        context: usize,
        import: Import,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MapCell {
    value: Fr,
    tag: MapCellTag,
}

#[derive(Clone)]
struct MapCandidate {
    parent: ParentId,
    binding: Binding,
    owner: usize,
    context: usize,
    map: Map,
    imports: Vec<Import>,
    row: NativePackedRow,
    foreign_rows: BTreeMap<usize, NativePackedRow>,
    physical_terms: Vec<Term>,
    relocated_terms: Vec<Term>,
    cells: BTreeMap<usize, MapCell>,
}

#[derive(Clone)]
struct MapSourceLoan {
    row: NativePackedRow,
    foreign_rows: BTreeMap<usize, NativePackedRow>,
}

struct MapXStage<'a> {
    parent: ParentId,
    owner: usize,
    context: usize,
    cells: &'a BTreeMap<usize, MapCell>,
    relocated_terms: &'a [Term],
}

impl<'a> From<&'a MapCandidate> for MapXStage<'a> {
    fn from(map: &'a MapCandidate) -> Self {
        Self {
            parent: map.parent,
            owner: map.owner,
            context: map.context,
            cells: &map.cells,
            relocated_terms: &map.relocated_terms,
        }
    }
}

fn packed_row_bit(row: &NativePackedRow, address: usize) -> Result<Fr, String> {
    let owner = address / WIDTH;
    if row.owner() != owner || row.packed_bytes().len() != WIDTH / 8 {
        return Err("c145 source row/address identity".into());
    }
    let local = address % WIDTH;
    Ok(Fr::from(
        ((row.packed_bytes()[local / 8] >> (local % 8)) & 1) as u64,
    ))
}

fn map_cells(
    owner: usize,
    context: usize,
    imports: &[Import],
    row: &NativePackedRow,
    foreign_rows: &BTreeMap<usize, NativePackedRow>,
    active: &BTreeSet<usize>,
) -> Result<BTreeMap<usize, MapCell>, String> {
    if owner != OWNER || context > 1 {
        return Err("c145 Map owner/context".into());
    }
    let live = map_live(context)?;
    let owner_base = owner * WIDTH;
    let mut cells = BTreeMap::new();
    for local_x in live {
        let address = owner_base + local_x;
        cells.insert(
            address,
            MapCell {
                value: packed_row_bit(row, address)?,
                tag: MapCellTag::LiveWriter { owner, context },
            },
        );
    }
    for &address in active {
        if cells.contains_key(&address) {
            continue;
        }
        let source_owner = address / WIDTH;
        let local_x = address % WIDTH;
        let matching = imports
            .iter()
            .filter(|import| {
                import.owner as usize == source_owner
                    && import.local <= local_x
                    && local_x < import.local + import.width
            })
            .copied()
            .collect::<Vec<_>>();
        if matching.len() != 1 {
            return Err(format!(
                "c145 active Map READ has {} typed imports at {address}",
                matching.len()
            ));
        }
        let import = matching[0];
        let (source_row, tag) = if source_owner == owner {
            (
                row,
                MapCellTag::OwnImport {
                    owner: source_owner,
                    context,
                    import,
                },
            )
        } else {
            (
                foreign_rows
                    .get(&source_owner)
                    .ok_or_else(|| format!("c145 missing typed foreign row {source_owner}"))?,
                MapCellTag::ForeignImport {
                    owner: source_owner,
                    context,
                    import,
                },
            )
        };
        if cells
            .insert(
                address,
                MapCell {
                    value: packed_row_bit(source_row, address)?,
                    tag,
                },
            )
            .is_some()
        {
            return Err(format!("c145 duplicate Map cell {address}"));
        }
    }
    Ok(cells)
}

impl MapCandidate {
    fn stage(
        plan: &WorkTreeHistoryPlan,
        prefix: &super::NativePrefix,
        base: &BaseCandidate,
        expected: ParentId,
        context: usize,
    ) -> Result<(Self, MapSourceLoan), String> {
        let map = match context {
            0 => Map::from_parent_modern_global_u(
                plan,
                55,
                LowerSelector {
                    source: LowerSource::HeaderDifficulty { height: 841_729 },
                    branch: LowerBranch::Pivot(54),
                },
            )?,
            1 => {
                let cuts =
                    super::super::candidate138_native_global_u::fold_native_global_u_cut_pair(
                        plan, prefix,
                    )?;
                let cut = &cuts[1];
                if cut.cut != 1_827_775
                    || cut.envelope.exponent != 55
                    || cut.lower_owner != 841_727
                    || cut.selected_lower.source
                        != (LowerSource::HeaderDifficulty { height: 841_729 })
                    || cut.selected_lower.branch != LowerBranch::Pivot(54)
                {
                    return Err("c150 Map1 source-selected cut changed".into());
                }
                let selected = Map::new_modern_global_u_selected_lower(
                    cut.cut,
                    21,
                    cut.envelope.exponent,
                    cut.selected_lower,
                )?;
                if selected.binding() != cut.consumer_binding
                    || selected.binding().parent_root.is_some()
                {
                    return Err("c150 Map1 rootless consumer binding changed".into());
                }
                selected
            }
            _ => return Err("c150 Map context".into()),
        };
        let imports = map.imports(OWNER as u64)?;
        let producer = NativeOwnerProducer::new_for_history(plan, prefix)?;
        let source_row = if context == 0 {
            producer.produce_bank53_map_h21_for_test(OWNER, &map, 0)?
        } else {
            producer.produce_bank53_map1_cut_h21_for_test(OWNER, 1, &map, &map.binding())?
        };
        let row = source_row.clone();
        let foreign_owners = imports
            .iter()
            .filter_map(|import| {
                let owner = import.owner as usize;
                (owner != OWNER).then_some(owner)
            })
            .collect::<BTreeSet<_>>();
        let mut foreign_rows = BTreeMap::new();
        let mut source_foreign_rows = BTreeMap::new();
        for owner in foreign_owners {
            let source_row = producer.produce(owner)?;
            foreign_rows.insert(owner, source_row.clone());
            source_foreign_rows.insert(owner, source_row);
        }
        drop(producer);
        let physical_terms = bank53_map::map_owner_terms(&map, OWNER as u64, context)?;
        let relocated_terms = physical_terms
            .iter()
            .map(|term| relocate(Family::Map(context), OWNER, term))
            .collect::<Result<Vec<_>, _>>()?;
        let active = active_addresses(&physical_terms);
        let cells = map_cells(OWNER, context, &imports, &row, &foreign_rows, &active)?;
        let candidate = Self {
            parent: expected,
            binding: map.binding(),
            owner: OWNER,
            context,
            map,
            imports,
            row,
            foreign_rows,
            physical_terms,
            relocated_terms,
            cells,
        };
        let source_loan = MapSourceLoan {
            row: source_row,
            foreign_rows: source_foreign_rows,
        };
        candidate.validate(plan, prefix, base, expected, &source_loan)?;
        Ok((candidate, source_loan))
    }

    fn validate(
        &self,
        plan: &WorkTreeHistoryPlan,
        prefix: &super::NativePrefix,
        base: &BaseCandidate,
        expected: ParentId,
        source_loan: &MapSourceLoan,
    ) -> Result<(), String> {
        if self.owner != OWNER || self.context > 1 {
            return Err("c145 Map owner/context identity".into());
        }
        if self.parent != expected || ParentId::from_source(plan, prefix)? != expected {
            return Err("c145 Map parent identity".into());
        }
        let expected_map = if self.context == 0 {
            Map::from_parent_modern_global_u(
                plan,
                55,
                LowerSelector {
                    source: LowerSource::HeaderDifficulty { height: 841_729 },
                    branch: LowerBranch::Pivot(54),
                },
            )?
        } else {
            let cuts = super::super::candidate138_native_global_u::fold_native_global_u_cut_pair(
                plan, prefix,
            )?;
            let cut = &cuts[1];
            if cut.cut != 1_827_775
                || cut.envelope.exponent != 55
                || cut.lower_owner != 841_727
                || cut.selected_lower.source != (LowerSource::HeaderDifficulty { height: 841_729 })
                || cut.selected_lower.branch != LowerBranch::Pivot(54)
            {
                return Err("c150 Map1 validation source-selected cut changed".into());
            }
            Map::new_modern_global_u_selected_lower(
                cut.cut,
                21,
                cut.envelope.exponent,
                cut.selected_lower,
            )?
        };
        if self.binding != expected_map.binding() || self.binding != self.map.binding() {
            return Err("c145 Map binding identity".into());
        }
        let imports = self.map.imports(OWNER as u64)?;
        if self.imports != imports {
            return Err("c145 Map typed import identity".into());
        }
        if self.context == 0 {
            self.row
                .validate_bank53_map_identity_for_history_test(plan, &self.map, OWNER, 0)?;
            source_loan
                .row
                .validate_bank53_map_identity_for_history_test(plan, &self.map, OWNER, 0)?;
        } else {
            let cuts = super::super::candidate138_native_global_u::fold_native_global_u_cut_pair(
                plan, prefix,
            )?;
            let binding = &cuts[1].consumer_binding;
            if self.map.binding() != *binding {
                return Err("c150 Map1 source binding identity".into());
            }
            crate::packed_owner_assembly::validate_native_map1_cut_consumer_for_test(
                plan,
                prefix,
                &self.map,
                binding,
                &self.row,
                &self.foreign_rows,
            )?;
            crate::packed_owner_assembly::validate_native_map1_cut_consumer_for_test(
                plan,
                prefix,
                &self.map,
                binding,
                &source_loan.row,
                &source_loan.foreign_rows,
            )?;
        }
        if self.row.packed_bytes() != source_loan.row.packed_bytes() {
            return Err("c145 Map source row bytes mismatch".into());
        }
        let required_foreign = imports
            .iter()
            .filter_map(|import| {
                let owner = import.owner as usize;
                (owner != OWNER).then_some(owner)
            })
            .collect::<BTreeSet<_>>();
        if self.foreign_rows.keys().copied().collect::<BTreeSet<_>>() != required_foreign {
            return Err("c145 Map foreign-row census".into());
        }
        if source_loan
            .foreign_rows
            .keys()
            .copied()
            .collect::<BTreeSet<_>>()
            != required_foreign
        {
            return Err("c145 Map foreign source-row census".into());
        }
        for owner in &required_foreign {
            let candidate_row = self
                .foreign_rows
                .get(owner)
                .ok_or("c145 Map candidate foreign row missing")?;
            let source_row = source_loan
                .foreign_rows
                .get(owner)
                .ok_or("c145 Map foreign source row missing")?;
            candidate_row.validate_identity_for_history_test(plan, prefix, *owner)?;
            candidate_row.validate_source_copy_for_history_test(
                source_row,
                *owner,
                expected.root,
                expected.total,
            )?;
        }
        if self.context == 0 {
            crate::packed_owner_assembly::validate_native_bank53_map_consumer(
                plan,
                prefix,
                &self.map,
                OWNER,
                0,
                &self.row,
                &self.foreign_rows,
            )?;
        }

        let physical = bank53_map::map_owner_terms(&self.map, OWNER as u64, self.context)?;
        if !same_term_multiset(&self.physical_terms, &physical) {
            return Err("c145 Map physical source tuple multiset".into());
        }
        let relocated = physical
            .iter()
            .map(|term| relocate(Family::Map(self.context), OWNER, term))
            .collect::<Result<Vec<_>, _>>()?;
        if !same_term_multiset(&self.relocated_terms, &relocated) {
            return Err("c145 Map relocated source tuple multiset".into());
        }
        let local_map_terms = base.local.relocated_map_terms(self.context)?;
        if !same_term_multiset(&self.relocated_terms, &local_map_terms) {
            return Err("c145 Map LOCAL occurrence multiset".into());
        }
        let map_rows = relocated
            .iter()
            .map(|term| term.row)
            .collect::<BTreeSet<_>>();
        if map_rows.iter().any(|row| {
            base.local.rows().get(row) != Some(&RowWriter::Relocated(Family::Map(self.context)))
        }) {
            return Err("c145 relocated Map ROW writer identity".into());
        }
        let physical_rows = physical
            .iter()
            .map(|term| term.row)
            .collect::<BTreeSet<_>>();
        let local_rows = base
            .local
            .row_addresses()
            .into_iter()
            .collect::<BTreeSet<_>>();
        let physical_intersection = physical_rows
            .intersection(&local_rows)
            .copied()
            .collect::<Vec<_>>();
        if physical_intersection.len() != physical_rows.len()
            || physical_intersection
                .iter()
                .any(|row| base.local.rows().get(row) != Some(&RowWriter::Daa(3)))
        {
            return Err("c145 unrelocated Map ROW namespace collision changed".into());
        }

        let owner_base = OWNER * WIDTH;
        let live = map_live(self.context)?;
        for local_x in live.clone() {
            if base.local.x_writer_at(owner_base + local_x) != Some(XWriter::Map(self.context)) {
                return Err("c145 Map0 live writer lease".into());
            }
        }
        if (live.end..live.start + MAP_PHYSICAL.len()).any(|local_x| {
            base.local.x_writer_at(owner_base + local_x) == Some(XWriter::Map(self.context))
        }) {
            return Err("c145 Map physical tail incorrectly claimed".into());
        }
        if base.local.x_domains().iter().any(|(writer, domain)| {
            *writer == XWriter::Map(self.context)
                && !(owner_base + live.start <= domain.start && domain.end <= owner_base + live.end)
        }) {
            return Err("c145 Map domain exceeds live lease".into());
        }

        let live_addresses = live
            .clone()
            .map(|local_x| owner_base + local_x)
            .collect::<BTreeSet<_>>();
        let max_terms = base
            .max
            .iter()
            .map(|(_, term)| term.clone())
            .collect::<Vec<_>>();
        for (name, terms) in [
            ("Work", base.work.as_slice()),
            ("MAX", max_terms.as_slice()),
            ("HEADER successor", base.cross.as_slice()),
        ] {
            if active_addresses(terms)
                .iter()
                .any(|address| live_addresses.contains(address))
            {
                return Err(format!(
                    "c145 transferred Map live X remains active in {name}"
                ));
            }
        }

        let active = active_addresses(&physical);
        let cells = map_cells(
            OWNER,
            self.context,
            &imports,
            &self.row,
            &self.foreign_rows,
            &active,
        )?;
        if self.cells != cells
            || self
                .cells
                .keys()
                .filter(|address| {
                    (owner_base + live.start..owner_base + live.end).contains(address)
                })
                .count()
                != live.len()
        {
            return Err("c145 Map source cell/provenance census".into());
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompositeProvenance {
    Base(Origin),
    Map(MapCellTag),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SelectedXClassification {
    Writer,
    ImportedRead,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SelectedXClaim {
    pub(super) address: usize,
    pub(super) value: Fr,
    pub(super) classification: SelectedXClassification,
}

fn classify_selected_x(
    address: usize,
    value: Fr,
    provenance: CompositeProvenance,
) -> Result<SelectedXClaim, String> {
    let address_owner = address / WIDTH;
    let classification = match provenance {
        CompositeProvenance::Base(Origin::Native { owner }) => {
            if owner != address_owner {
                return Err(format!("c145 native X owner/address mismatch at {address}"));
            }
            SelectedXClassification::Writer
        }
        CompositeProvenance::Base(Origin::MaxLocal { owner, .. }) => {
            if owner != address_owner {
                return Err(format!(
                    "c145 MAX-local X owner/address mismatch at {address}"
                ));
            }
            SelectedXClassification::Writer
        }
        CompositeProvenance::Base(Origin::MaxForeignRead { owner, .. }) => {
            if owner != address_owner {
                return Err(format!(
                    "c145 MAX-read X owner/address mismatch at {address}"
                ));
            }
            SelectedXClassification::ImportedRead
        }
        CompositeProvenance::Map(MapCellTag::LiveWriter { owner, .. }) => {
            if owner != address_owner {
                return Err(format!(
                    "c145 Map writer X owner/address mismatch at {address}"
                ));
            }
            SelectedXClassification::Writer
        }
        CompositeProvenance::Map(MapCellTag::OwnImport { owner, import, .. })
        | CompositeProvenance::Map(MapCellTag::ForeignImport { owner, import, .. }) => {
            let local = address % WIDTH;
            let import_end = import
                .local
                .checked_add(import.width)
                .ok_or_else(|| format!("c145 Map import X range overflow at {address}"))?;
            if owner != address_owner
                || import.owner as usize != owner
                || import.local > local
                || import_end > WIDTH
                || local >= import_end
            {
                return Err(format!(
                    "c145 Map import X provenance mismatch at {address}"
                ));
            }
            SelectedXClassification::ImportedRead
        }
    };
    Ok(SelectedXClaim {
        address,
        value,
        classification,
    })
}

#[derive(Clone)]
pub(super) struct CompositeDestination {
    parent: Option<ParentId>,
    base: BaseDestination,
    x: BTreeMap<usize, Fr>,
    provenance: BTreeMap<usize, CompositeProvenance>,
    map_binding: Option<Binding>,
    map_imports: Vec<Import>,
    map_cells: BTreeMap<usize, MapCell>,
    map_terms: Vec<Term>,
    map1_binding: Option<Binding>,
    map1_imports: Vec<Import>,
    map1_cells: BTreeMap<usize, MapCell>,
    map1_terms: Vec<Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CompositeSnapshot {
    parent: Option<ParentId>,
    base: BaseDestination,
    x: BTreeMap<usize, Fr>,
    provenance: BTreeMap<usize, CompositeProvenance>,
    map_binding: Option<Binding>,
    map_imports: Vec<Import>,
    map_cells: BTreeMap<usize, MapCell>,
    map_terms: BTreeMap<usize, Vec<(crate::gkr::Gate, usize)>>,
    map1_binding: Option<Binding>,
    map1_imports: Vec<Import>,
    map1_cells: BTreeMap<usize, MapCell>,
    map1_terms: BTreeMap<usize, Vec<(crate::gkr::Gate, usize)>>,
}

fn candidate_projection_matches_parts(
    parent: Option<ParentId>,
    local: Option<&NativeCarryLedger>,
    local_rows: &BTreeSet<usize>,
    domains: &[std::ops::Range<usize>],
    work: &[Term],
    cross: &[Term],
    x: &X,
    destination: &BaseDestination,
) -> bool {
    destination.parent == parent
        && destination.local.as_ref() == local
        && local_rows.is_subset(&destination.local_rows)
        && domains
            .iter()
            .all(|domain| destination.occupied_x.iter().any(|prior| prior == domain))
        && destination.work == work
        && destination.cross == cross
        && x.cells
            .iter()
            .all(|(address, cell)| destination.x.cells.get(address) == Some(cell))
}

fn candidate_projection_matches(
    base: &BaseCandidate,
    destination: &BaseDestination,
    expected: ParentId,
) -> bool {
    let rows = base
        .local
        .row_addresses()
        .into_iter()
        .collect::<BTreeSet<_>>();
    let domains = base
        .local
        .x_domains()
        .into_iter()
        .map(|(_, domain)| domain)
        .collect::<Vec<_>>();
    base.parent == expected
        && candidate_projection_matches_parts(
            Some(expected),
            Some(&base.local),
            &rows,
            &domains,
            &base.work,
            &base.cross,
            &base.x,
            destination,
        )
}

fn validate_base_publication(
    base: &BaseCandidate,
    destination: &BaseDestination,
    plan: &WorkTreeHistoryPlan,
    prefix: &super::NativePrefix,
    expected: ParentId,
    sources: Sources<'_>,
) -> Result<(), String> {
    if !candidate_projection_matches(base, destination, expected) {
        return Err("c145 base destination/candidate projection mismatch".into());
    }
    let mut prior = destination.clone();
    prior.local = None;
    prior.work.clear();
    prior.cross.clear();
    for row in base.local.row_addresses() {
        if !prior.local_rows.remove(&row) {
            return Err("c145 base publication missing candidate ROW".into());
        }
    }
    for (_, domain) in base.local.x_domains() {
        let Some(index) = prior
            .occupied_x
            .iter()
            .position(|previous| previous == &domain)
        else {
            return Err("c145 base publication missing candidate X domain".into());
        };
        prior.occupied_x.remove(index);
    }
    for (address, cell) in &base.x.cells {
        if prior.x.cells.remove(address) != Some(*cell) {
            return Err("c145 base publication candidate X value/provenance mismatch".into());
        }
    }
    prior.parent = Some(expected);
    prior.publish(base, plan, prefix, expected, sources)?;
    if prior != *destination {
        return Err("c145 base destination is not exact candidate publication".into());
    }
    Ok(())
}

fn typed_alias_matches(tag: MapCellTag, origin: Origin, address: usize) -> bool {
    let (owner, context, import, own) = match tag {
        MapCellTag::OwnImport {
            owner,
            context,
            import,
        } => (owner, context, import, true),
        MapCellTag::ForeignImport {
            owner,
            context,
            import,
        } => (owner, context, import, false),
        MapCellTag::LiveWriter { .. } => return false,
    };
    let local_x = address % WIDTH;
    if context > 1
        || owner as u64 != import.owner
        || address / WIDTH != owner
        || own != (owner == OWNER)
        || local_x < import.local
        || local_x - import.local >= import.width
    {
        return false;
    }
    match origin {
        Origin::Native {
            owner: source_owner,
        } => source_owner == owner,
        Origin::MaxLocal { .. } => false,
        Origin::MaxForeignRead {
            owner: source_owner,
            context: max_context,
        } => {
            source_owner == owner
                && source_owner == NEXT_OWNER
                && max_context < 2
                && (MAX_BASE[max_context]..MAX_BASE[max_context] + 224).contains(&local_x)
        }
    }
}

fn typed_map_alias_matches(incoming: MapCellTag, prior: MapCellTag, address: usize) -> bool {
    let (incoming_owner, incoming_context, incoming_import) = match incoming {
        MapCellTag::OwnImport {
            owner,
            context,
            import,
        }
        | MapCellTag::ForeignImport {
            owner,
            context,
            import,
        } => (owner, context, import),
        MapCellTag::LiveWriter { .. } => return false,
    };
    let (prior_owner, prior_context, prior_import) = match prior {
        MapCellTag::LiveWriter { owner, context } => {
            if context != 0
                || address / WIDTH != owner
                || !map_live(0).is_ok_and(|r| r.contains(&(address % WIDTH)))
            {
                return false;
            }
            (owner, context, None)
        }
        MapCellTag::OwnImport {
            owner,
            context,
            import,
        }
        | MapCellTag::ForeignImport {
            owner,
            context,
            import,
        } => (owner, context, Some(import)),
    };
    let local_x = address % WIDTH;
    incoming_context == 1
        && incoming_owner as u64 == incoming_import.owner
        && address / WIDTH == incoming_owner
        && incoming_import.local <= local_x
        && local_x - incoming_import.local < incoming_import.width
        && prior_context == 0
        && prior_owner == incoming_owner
        && prior_import.is_none_or(|import| {
            import.owner == incoming_import.owner
                && import.local <= local_x
                && local_x - import.local < import.width
        })
}

fn require_zero_roles(roles: &[(&str, &[Term])], x: &BTreeMap<usize, Fr>) -> Result<(), String> {
    for (name, terms) in roles {
        let residuals = evaluate_numeric(terms, x)?;
        if let Some((row, _)) = residuals
            .into_iter()
            .find(|(_, residual)| !residual.is_zero())
        {
            return Err(format!("c145 combined {name} residual row{row}"));
        }
    }
    Ok(())
}

fn stage_common_x(
    x: &BTreeMap<usize, Fr>,
    provenance: &BTreeMap<usize, CompositeProvenance>,
    cells: &BTreeMap<usize, MapCell>,
    roles: &[(&str, &[Term])],
) -> Result<(BTreeMap<usize, Fr>, BTreeMap<usize, CompositeProvenance>), String> {
    if x.keys().copied().collect::<BTreeSet<_>>()
        != provenance.keys().copied().collect::<BTreeSet<_>>()
    {
        return Err("c145 destination X provenance census".into());
    }
    let mut next_x = x.clone();
    let mut next_provenance = provenance.clone();
    for (&address, cell) in cells {
        match cell.tag {
            MapCellTag::LiveWriter { owner, context }
                if owner == OWNER
                    && context <= 1
                    && address / WIDTH == OWNER
                    && map_live(context)?.contains(&(address % WIDTH)) =>
            {
                if next_x.contains_key(&address) {
                    return Err(format!("c145 Map live X writer collision at {address}"));
                }
                next_x.insert(address, cell.value);
                next_provenance.insert(address, CompositeProvenance::Map(cell.tag));
            }
            MapCellTag::OwnImport {
                owner,
                context,
                import,
            }
            | MapCellTag::ForeignImport {
                owner,
                context,
                import,
            } if context <= 1
                && owner as u64 == import.owner
                && address / WIDTH == owner
                && address % WIDTH >= import.local
                && address % WIDTH - import.local < import.width =>
            {
                if let Some(existing) = next_x.get(&address) {
                    let valid_alias = match next_provenance.get(&address) {
                        Some(CompositeProvenance::Base(origin)) => {
                            typed_alias_matches(cell.tag, *origin, address)
                        }
                        Some(CompositeProvenance::Map(prior)) => {
                            typed_map_alias_matches(cell.tag, *prior, address)
                        }
                        None => false,
                    };
                    if *existing != cell.value || !valid_alias {
                        return Err(format!(
                            "c145 Map typed READ alias provenance/value at {address}"
                        ));
                    }
                } else {
                    next_x.insert(address, cell.value);
                    next_provenance.insert(address, CompositeProvenance::Map(cell.tag));
                }
            }
            _ => return Err(format!("c145 invalid Map cell provenance at {address}")),
        }
    }
    for (name, terms) in roles {
        if active_addresses(terms)
            .iter()
            .any(|address| !next_x.contains_key(address))
        {
            return Err(format!(
                "c145 combined {name} selected X missing active operand"
            ));
        }
    }
    require_zero_roles(roles, &next_x)?;
    Ok((next_x, next_provenance))
}

fn stage_map_pair_x(
    x: &BTreeMap<usize, Fr>,
    provenance: &BTreeMap<usize, CompositeProvenance>,
    map0: &MapXStage<'_>,
    map1: &MapXStage<'_>,
    work: &[Term],
    max: &[Term],
    cross: &[Term],
) -> Result<(BTreeMap<usize, Fr>, BTreeMap<usize, CompositeProvenance>), String> {
    if map0.context != 0
        || map1.context != 1
        || map0.owner != map1.owner
        || map0.parent != map1.parent
    {
        return Err("c150 Map pair owner/context/parent identity".into());
    }
    let map0_roles = [
        ("Work", work),
        ("MAX", max),
        ("Map0", map0.relocated_terms),
        ("CROSS", cross),
    ];
    let (with_map0, map0_provenance) = stage_common_x(x, provenance, map0.cells, &map0_roles)?;
    let all_roles = [
        ("Work", work),
        ("MAX", max),
        ("Map0", map0.relocated_terms),
        ("Map1", map1.relocated_terms),
        ("CROSS", cross),
    ];
    stage_common_x(&with_map0, &map0_provenance, map1.cells, &all_roles)
}

impl CompositeDestination {
    fn from_base(
        candidate: &BaseCandidate,
        base: &BaseDestination,
        expected: ParentId,
    ) -> Result<Self, String> {
        if !candidate_projection_matches(candidate, base, expected) {
            return Err("c145 base destination is not parent-bound".into());
        }
        let x = base
            .x
            .cells
            .iter()
            .map(|(address, (value, _))| (*address, *value))
            .collect::<BTreeMap<_, _>>();
        let provenance = base
            .x
            .cells
            .iter()
            .map(|(address, (_, origin))| (*address, CompositeProvenance::Base(*origin)))
            .collect::<BTreeMap<_, _>>();
        if x.len() != provenance.len() {
            return Err("c145 base X provenance census".into());
        }
        Ok(Self {
            parent: Some(expected),
            base: base.clone(),
            x,
            provenance,
            map_binding: None,
            map_imports: Vec::new(),
            map_cells: BTreeMap::new(),
            map_terms: Vec::new(),
            map1_binding: None,
            map1_imports: Vec::new(),
            map1_cells: BTreeMap::new(),
            map1_terms: Vec::new(),
        })
    }

    fn snapshot(&self) -> CompositeSnapshot {
        CompositeSnapshot {
            parent: self.parent,
            base: self.base.clone(),
            x: self.x.clone(),
            provenance: self.provenance.clone(),
            map_binding: self.map_binding.clone(),
            map_imports: self.map_imports.clone(),
            map_cells: self.map_cells.clone(),
            map_terms: term_multiset(&self.map_terms),
            map1_binding: self.map1_binding.clone(),
            map1_imports: self.map1_imports.clone(),
            map1_cells: self.map1_cells.clone(),
            map1_terms: term_multiset(&self.map1_terms),
        }
    }

    pub(super) fn checked_parent(&self) -> Result<ParentId, String> {
        let parent = self.parent.ok_or("c145 composite has no parent identity")?;
        if self.base.parent != Some(parent) {
            return Err("c145 composite/base parent identity mismatch".into());
        }
        Ok(parent)
    }

    pub(super) fn map0_terms(&self) -> Result<&[Term], String> {
        if self.map_binding.is_none() {
            return Err("c145 composite has no published Map0 binding".into());
        }
        Ok(&self.map_terms)
    }

    pub(super) fn map1_terms(&self) -> Result<&[Term], String> {
        if self.map1_binding.is_none() {
            return Err("c150 composite has no published Map1 binding".into());
        }
        Ok(&self.map1_terms)
    }

    pub(super) fn selected_x_claims(&self) -> Result<Vec<SelectedXClaim>, String> {
        if self.x.len() != self.provenance.len() || self.x.keys().ne(self.provenance.keys()) {
            return Err("c145 composite X/provenance census mismatch".into());
        }
        self.x
            .iter()
            .map(|(address, value)| {
                let provenance =
                    self.provenance.get(address).copied().ok_or_else(|| {
                        format!("c145 composite X provenance missing at {address}")
                    })?;
                classify_selected_x(*address, *value, provenance)
            })
            .collect()
    }

    fn publish(
        &mut self,
        base: &BaseCandidate,
        map: &MapCandidate,
        source_loan: &MapSourceLoan,
        base_destination: &BaseDestination,
        plan: &WorkTreeHistoryPlan,
        prefix: &super::NativePrefix,
        expected: ParentId,
        sources: Sources<'_>,
    ) -> Result<(), String> {
        self.publish_pair(
            base,
            map,
            source_loan,
            None,
            base_destination,
            plan,
            prefix,
            expected,
            sources,
        )
    }

    fn publish_pair(
        &mut self,
        base: &BaseCandidate,
        map: &MapCandidate,
        source_loan: &MapSourceLoan,
        map1: Option<(&MapCandidate, &MapSourceLoan)>,
        base_destination: &BaseDestination,
        plan: &WorkTreeHistoryPlan,
        prefix: &super::NativePrefix,
        expected: ParentId,
        sources: Sources<'_>,
    ) -> Result<(), String> {
        validate_base_publication(base, base_destination, plan, prefix, expected, sources)?;
        if self.parent != Some(expected)
            || self.base != *base_destination
            || base_destination.parent != Some(expected)
        {
            return Err("c145 destination parent/source changed".into());
        }
        let base_x = base_destination
            .x
            .cells
            .iter()
            .map(|(address, (value, _))| (*address, *value))
            .collect::<BTreeMap<_, _>>();
        let base_provenance = base_destination
            .x
            .cells
            .iter()
            .map(|(address, (_, origin))| (*address, CompositeProvenance::Base(*origin)))
            .collect::<BTreeMap<_, _>>();
        if self.map_binding.is_some() || self.map1_binding.is_some() {
            return Err("c145 duplicate Map publication".into());
        }
        if self.x != base_x || self.provenance != base_provenance {
            return Err("c145 composite base X/provenance changed".into());
        }
        if self.x.keys().copied().collect::<BTreeSet<_>>()
            != self.provenance.keys().copied().collect::<BTreeSet<_>>()
        {
            return Err("c145 destination X provenance census".into());
        }
        if map.owner != OWNER || map.context != 0 {
            return Err("c145 Map owner/context identity".into());
        }
        if map.parent != expected || ParentId::from_source(plan, prefix)? != expected {
            return Err("c145 Map parent identity".into());
        }
        let expected_binding = Map::from_parent_modern_global_u(
            plan,
            55,
            LowerSelector {
                source: LowerSource::HeaderDifficulty { height: 841_729 },
                branch: LowerBranch::Pivot(54),
            },
        )?
        .binding();
        if map.binding != expected_binding || map.binding != map.map.binding() {
            return Err("c145 Map binding identity".into());
        }
        if map.cells.len() < MAP_LIVE.len()
            || map
                .cells
                .keys()
                .filter(|address| {
                    (OWNER * WIDTH + MAP_LIVE.start..OWNER * WIDTH + MAP_LIVE.end).contains(address)
                })
                .count()
                != MAP_LIVE.len()
        {
            return Err("c145 Map live cell census".into());
        }
        map.validate(plan, prefix, base, expected, source_loan)?;
        let max_terms = base
            .max
            .iter()
            .map(|(_, term)| term.clone())
            .collect::<Vec<_>>();
        let (merged_x, merged_provenance, map1_binding, map1_imports, map1_cells, map1_terms) =
            if let Some((map1, loan1)) = map1 {
                if map1.context != 1 || map1.parent != expected || map1.owner != OWNER {
                    return Err("c150 Map1 owner/context/parent identity".into());
                }
                map1.validate(plan, prefix, base, expected, loan1)?;
                let (x, provenance) = stage_map_pair_x(
                    &self.x,
                    &self.provenance,
                    &MapXStage::from(map),
                    &MapXStage::from(map1),
                    &base.work,
                    &max_terms,
                    &base.cross,
                )?;
                (
                    x,
                    provenance,
                    Some(map1.binding.clone()),
                    map1.imports.clone(),
                    map1.cells.clone(),
                    map1.relocated_terms.clone(),
                )
            } else {
                let roles = [
                    ("Work", base.work.as_slice()),
                    ("MAX", max_terms.as_slice()),
                    ("Map", map.relocated_terms.as_slice()),
                    ("CROSS", base.cross.as_slice()),
                ];
                let (x, provenance) =
                    stage_common_x(&self.x, &self.provenance, &map.cells, &roles)?;
                (x, provenance, None, Vec::new(), BTreeMap::new(), Vec::new())
            };
        let mut next = self.clone();
        next.x = merged_x;
        next.provenance = merged_provenance;
        next.map_binding = Some(map.binding.clone());
        next.map_imports = map.imports.clone();
        next.map_cells = map.cells.clone();
        next.map_terms = map.relocated_terms.clone();
        next.map1_binding = map1_binding;
        next.map1_imports = map1_imports;
        next.map1_cells = map1_cells;
        next.map1_terms = map1_terms;
        *self = next;
        Ok(())
    }
}

fn evaluate_numeric(
    terms: &[Term],
    x: &BTreeMap<usize, Fr>,
) -> Result<BTreeMap<usize, Fr>, String> {
    let value = |address: usize| -> Result<Fr, String> {
        if address == 0 {
            Ok(Fr::from(0u64))
        } else {
            x.get(&address)
                .copied()
                .ok_or_else(|| format!("c145 missing selected X address {address}"))
        }
    };
    let mut residuals = BTreeMap::<usize, Fr>::new();
    for term in terms {
        let gate = &term.gate;
        let mut residual = gate.c0;
        if !gate.c1.is_zero() {
            residual += gate.c1 * value(gate.left)?;
        }
        if !gate.c2.is_zero() {
            residual += gate.c2 * value(gate.right)?;
        }
        if !gate.c3.is_zero() {
            residual += gate.c3 * value(gate.left)? * value(gate.right)?;
        }
        *residuals.entry(term.row).or_insert(Fr::from(0u64)) += residual;
    }
    Ok(residuals)
}

fn expect_rejected_unchanged(
    destination: &mut CompositeDestination,
    base: &BaseCandidate,
    map: &MapCandidate,
    source_loan: &MapSourceLoan,
    base_destination: &BaseDestination,
    plan: &WorkTreeHistoryPlan,
    prefix: &super::NativePrefix,
    expected: ParentId,
    sources: Sources<'_>,
    needle: &str,
) -> Result<(), String> {
    let before = destination.snapshot();
    let error = destination
        .publish(
            base,
            map,
            source_loan,
            base_destination,
            plan,
            prefix,
            expected,
            sources,
        )
        .unwrap_err();
    if !error.contains(needle) || destination.snapshot() != before {
        return Err(format!(
            "c145 atomic negative did not isolate {needle}: {error}"
        ));
    }
    Ok(())
}

pub(super) fn join_and_falsify(
    plan: &WorkTreeHistoryPlan,
    prefix: &super::NativePrefix,
    base: &BaseCandidate,
    sources: Sources<'_>,
    base_destination: &BaseDestination,
    include_map1: bool,
) -> Result<CompositeDestination, String> {
    let expected = ParentId::from_source(plan, prefix)?;
    base.validate(plan, prefix, expected, sources)?;
    let stage_started = std::time::Instant::now();
    let (map, source_loan) = MapCandidate::stage(plan, prefix, base, expected, 0)?;
    if include_map1 {
        println!(
            "C150_PHASE map0_stage_s={:.3}",
            stage_started.elapsed().as_secs_f64()
        );
    }
    let map1 = if include_map1 {
        let map1_started = std::time::Instant::now();
        let candidate = MapCandidate::stage(plan, prefix, base, expected, 1)?;
        println!(
            "C150_PHASE map1_stage_s={:.3}",
            map1_started.elapsed().as_secs_f64()
        );
        Some(candidate)
    } else {
        None
    };
    let mut destination = CompositeDestination::from_base(base, base_destination, expected)?;

    if let Some((valid_map1, loan1)) = &map1 {
        let mut corrupted_map1 = valid_map1.clone();
        let (&address, cell) = corrupted_map1
            .cells
            .iter()
            .next()
            .ok_or("c150 Map1 has no cell for atomic negative")?;
        let bad_value = if cell.value.is_zero() {
            Fr::from(1u64)
        } else {
            Fr::zero()
        };
        let tag = cell.tag;
        corrupted_map1.cells.insert(
            address,
            MapCell {
                value: bad_value,
                tag,
            },
        );
        let before = destination.snapshot();
        let error = destination
            .publish_pair(
                base,
                &map,
                &source_loan,
                Some((&corrupted_map1, loan1)),
                base_destination,
                plan,
                prefix,
                expected,
                sources,
            )
            .unwrap_err();
        if !error.contains("source cell/provenance census") || destination.snapshot() != before {
            return Err(format!(
                "c150 atomic Map1 cell mutant changed destination or missed boundary: {error}"
            ));
        }
        let mut omitted_map1_row = valid_map1.clone();
        omitted_map1_row.relocated_terms.pop();
        let before = destination.snapshot();
        let error = destination
            .publish_pair(
                base,
                &map,
                &source_loan,
                Some((&omitted_map1_row, loan1)),
                base_destination,
                plan,
                prefix,
                expected,
                sources,
            )
            .unwrap_err();
        if !error.contains("Map relocated source tuple multiset")
            || destination.snapshot() != before
        {
            return Err(format!(
                "c150 atomic Map1 ROW omission changed destination or missed boundary: {error}"
            ));
        }
    }

    let mut changed_base_destination = base_destination.clone();
    let (changed_address, (changed_value, _)) = base
        .x
        .cells
        .iter()
        .next()
        .ok_or("c145 no selected base X for destination mutation")?;
    changed_base_destination
        .x
        .cells
        .get_mut(changed_address)
        .ok_or("c145 selected base X missing from destination")?
        .0 = if changed_value.is_zero() {
        Fr::from(1u64)
    } else {
        Fr::zero()
    };
    expect_rejected_unchanged(
        &mut destination,
        base,
        &map,
        &source_loan,
        &changed_base_destination,
        plan,
        prefix,
        expected,
        sources,
        "base destination/candidate projection mismatch",
    )?;

    let mut wrong_owner = map.clone();
    wrong_owner.owner += 1;
    expect_rejected_unchanged(
        &mut destination,
        base,
        &wrong_owner,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "owner/context",
    )?;
    let mut wrong_context = map.clone();
    wrong_context.context = 1;
    expect_rejected_unchanged(
        &mut destination,
        base,
        &wrong_context,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "owner/context",
    )?;
    let mut wrong_parent = map.clone();
    wrong_parent.parent.root[0] ^= 1;
    expect_rejected_unchanged(
        &mut destination,
        base,
        &wrong_parent,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "parent identity",
    )?;
    let mut wrong_binding = map.clone();
    wrong_binding.binding.parent_root = None;
    expect_rejected_unchanged(
        &mut destination,
        base,
        &wrong_binding,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "binding identity",
    )?;
    let mut missing_last = map.clone();
    missing_last
        .cells
        .remove(&(OWNER * WIDTH + MAP_LIVE.end - 1));
    expect_rejected_unchanged(
        &mut destination,
        base,
        &missing_last,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "live cell census",
    )?;

    let mut bad_helper = map.clone();
    crate::packed_owner_assembly::flip_native_row_bit_for_test(
        &mut bad_helper.row,
        MAP_LIVE.start + 672,
    )?;
    expect_rejected_unchanged(
        &mut destination,
        base,
        &bad_helper,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "source row bytes mismatch",
    )?;

    let import_address = map
        .cells
        .iter()
        .find_map(|(address, cell)| {
            matches!(
                cell.tag,
                MapCellTag::OwnImport { .. } | MapCellTag::ForeignImport { .. }
            )
            .then_some(*address)
        })
        .ok_or("c145 no active typed Map READ for isolated negative")?;
    let import_owner = import_address / WIDTH;
    let mut bad_import = map.clone();
    if import_owner == OWNER {
        crate::packed_owner_assembly::flip_native_row_bit_for_test(
            &mut bad_import.row,
            import_address % WIDTH,
        )?;
    } else {
        crate::packed_owner_assembly::flip_native_row_bit_for_test(
            bad_import
                .foreign_rows
                .get_mut(&import_owner)
                .ok_or("c145 typed Map READ foreign row missing")?,
            import_address % WIDTH,
        )?;
    }
    expect_rejected_unchanged(
        &mut destination,
        base,
        &bad_import,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "source row bytes mismatch",
    )?;

    let collision_address = OWNER * WIDTH + MAP_LIVE.end - 1;
    let collision_cell = map
        .cells
        .get(&collision_address)
        .ok_or("c145 Map last live cell missing")?;
    if !matches!(
        collision_cell.tag,
        MapCellTag::LiveWriter {
            owner: OWNER,
            context: 0,
        }
    ) {
        return Err("c145 Map last live cell is not the selected writer".into());
    }
    if destination.x.contains_key(&collision_address)
        || destination.provenance.contains_key(&collision_address)
    {
        return Err("c145 clean destination already contains Map collision address".into());
    }
    let mut collision_x = destination.x.clone();
    collision_x.insert(collision_address, collision_cell.value);
    let mut collision_provenance = destination.provenance.clone();
    collision_provenance.insert(
        collision_address,
        CompositeProvenance::Base(Origin::Native { owner: OWNER }),
    );
    let collision_x_before = collision_x.clone();
    let collision_provenance_before = collision_provenance.clone();
    let destination_before = destination.snapshot();
    let max_terms = base
        .max
        .iter()
        .map(|(_, term)| term.clone())
        .collect::<Vec<_>>();
    let roles = [
        ("Work", base.work.as_slice()),
        ("MAX", max_terms.as_slice()),
        ("Map", map.relocated_terms.as_slice()),
        ("CROSS", base.cross.as_slice()),
    ];
    let error = match stage_common_x(&collision_x, &collision_provenance, &map.cells, &roles) {
        Err(error) => error,
        Ok(_) => return Err("c145 Map live X writer collision unexpectedly staged".into()),
    };
    let expected_error = format!("c145 Map live X writer collision at {collision_address}");
    if error != expected_error
        || collision_x != collision_x_before
        || collision_provenance != collision_provenance_before
        || destination.snapshot() != destination_before
    {
        return Err(format!(
            "c145 atomic negative did not isolate Map live X writer collision at {collision_address}: {error}"
        ));
    }

    if let Some((map1, loan1)) = &map1 {
        let publish_started = std::time::Instant::now();
        destination.publish_pair(
            base,
            &map,
            &source_loan,
            Some((map1, loan1)),
            base_destination,
            plan,
            prefix,
            expected,
            sources,
        )?;
        println!(
            "C150_PHASE atomic_pair_publish_s={:.3}",
            publish_started.elapsed().as_secs_f64()
        );
    } else {
        destination.publish(
            base,
            &map,
            &source_loan,
            base_destination,
            plan,
            prefix,
            expected,
            sources,
        )?;
    }
    let base_values = base_destination
        .x
        .cells
        .iter()
        .map(|(address, (value, _))| (*address, *value))
        .collect::<BTreeMap<_, _>>();
    if destination.map_binding.as_ref() != Some(&map.binding)
        || destination.map_cells != map.cells
        || destination.map_terms.len() != map.relocated_terms.len()
        || destination.map1_binding.as_ref()
            != map1.as_ref().map(|(candidate, _)| &candidate.binding)
        || destination.map1_cells
            != map1
                .as_ref()
                .map(|(candidate, _)| candidate.cells.clone())
                .unwrap_or_default()
        || destination.map1_terms.len()
            != map1
                .as_ref()
                .map(|(candidate, _)| candidate.relocated_terms.len())
                .unwrap_or(0)
        || base_values
            .iter()
            .any(|(address, value)| destination.x.get(address) != Some(value))
    {
        return Err("c145 committed common destination census/preservation".into());
    }
    expect_rejected_unchanged(
        &mut destination,
        base,
        &map,
        &source_loan,
        base_destination,
        plan,
        prefix,
        expected,
        sources,
        "duplicate Map publication",
    )?;
    if let Some((map1, _)) = &map1 {
        println!(
            "C150_NATIVE_CARRY_COMPOSITE_PASS owner={} contexts=0,1 map0_live_x={} map1_live_x={} map0_terms={} map1_terms={} map1_imports={} common_x={} roles=Work,MAX,Map0,Map1,CROSS atomic_pair_negatives=2 atomic_publish=true map1_cut=1827775 map1_exp=55 lower_owner=841727 lower_source=HeaderDifficulty:841729/Pivot54 frame_sha256={} proof=false client=false",
            OWNER,
            MAP_LIVE.len(),
            map_live(1)?.len(),
            map.relocated_terms.len(),
            map1.relocated_terms.len(),
            map1.imports.len(),
            destination.x.len(),
            super::super::FRAME_SHA256,
        );
    } else {
        println!(
            "C145_NATIVE_MAP_MAX_PASS owner={} context=0 map_live_cells={} map_typed_reads={} map_terms={} common_x={} map_row_namespace=relocated_map0 work_max_cross_rechecked=true atomic_negatives=10 proof=false client=false",
            OWNER,
            MAP_LIVE.len(),
            map.cells.len() - MAP_LIVE.len(),
            map.relocated_terms.len(),
            destination.x.len(),
        );
    }
    Ok(destination)
}

//! Bounded native MAX -> first Cap import join and placed ROW read census.
//! The placed census covers HEADER, DAA and Scheduled ROW operands only.
//! Map, Score, Slack, point and global ROW/X sealing remain outside this test.
use super::*;
use crate::{
    h21_scheduled_family_ledger::Admission,
    h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxReplayAuthor, MaxStream, Writer},
    header_daa_row_placement::{Batch, Relation, SourceRead, UnresolvedRead},
    packed_owner_assembly::NativeHeaderSourceLease,
};
use std::io::Write as _;

const CAP_OWNER: usize = 845_759;
const MAX_OWNER: usize = 844_670;
const WIDTH: usize = 1 << 20;
const IMPORTS: usize = 448;

#[derive(Clone, Copy, Default)]
struct RelationCensus {
    occurrences: usize,
    resolved_header: usize,
    foreign: usize,
    unqualified: usize,
    unique_unresolved_wires: usize,
}

pub(super) struct PlacedReadCensus {
    pub row_terms: usize,
    pub active_occurrences: usize,
    pub unresolved_occurrences: usize,
    pub unresolved_unique_wires: usize,
}

fn relation_slot(relation: Relation) -> Result<usize, String> {
    match relation {
        Relation::Header => Ok(0),
        Relation::DaaLane(lane) if lane < 4 => Ok(1 + lane),
        Relation::Scheduled(Writer::Max { context, end })
            if context < 2 && end == CAP_OWNER + 2 => Ok(5 + context),
        Relation::Scheduled(Writer::Cap { context, origin })
            if context < 2 && origin == CAP_OWNER + 1 => Ok(7 + context),
        _ => Err("C344 placed ROW relation/owner".into()),
    }
}

/// Take compact counts while the existing C343 Batch and HEADER lease live.
/// Unresolved is classified by occurrence and by distinct physical wire.
pub(super) fn census_placed_reads(
    batch: &Batch,
    lease: &NativeHeaderSourceLease,
) -> Result<PlacedReadCensus, String> {
    let row_terms = batch.terms().len();
    let mut relations = [RelationCensus::default(); 9];
    let mut unique_by_relation: [BTreeSet<usize>; 9] =
        std::array::from_fn(|_| BTreeSet::new());
    let mut unique_global = BTreeSet::new();
    let before = lease.read_count_for_test();
    let active_occurrences = batch.visit_source_reads(lease, |read| {
        match read {
            SourceRead::Header { operand, .. } => {
                let slot = relation_slot(operand.relation)?;
                relations[slot].occurrences += 1;
                relations[slot].resolved_header += 1;
            }
            SourceRead::Unresolved { operand, reason } => {
                let slot = relation_slot(operand.relation)?;
                relations[slot].occurrences += 1;
                match reason {
                    UnresolvedRead::ForeignOwner => relations[slot].foreign += 1,
                    UnresolvedRead::UnqualifiedLocal => relations[slot].unqualified += 1,
                }
                unique_by_relation[slot].insert(operand.wire);
                unique_global.insert(operand.wire);
            }
        }
        Ok(())
    })?;
    let resolved: usize = relations.iter().map(|r| r.resolved_header).sum();
    let unresolved_occurrences: usize = relations.iter()
        .map(|r| r.foreign + r.unqualified).sum();
    if active_occurrences != resolved + unresolved_occurrences
        || lease.read_count_for_test().checked_sub(before) != Some(resolved) {
        return Err("C344 placed active-read occurrence/source census".into());
    }
    let names = [
        "HEADER", "DAA0", "DAA1", "DAA2", "DAA3",
        "SCHEDULED_MAX0", "SCHEDULED_MAX1", "SCHEDULED_CAP0", "SCHEDULED_CAP1",
    ];
    for (slot, relation) in relations.iter_mut().enumerate() {
        relation.unique_unresolved_wires = unique_by_relation[slot].len();
        if relation.occurrences != relation.resolved_header
            + relation.foreign + relation.unqualified
            || relation.unique_unresolved_wires > relation.foreign + relation.unqualified {
            return Err("C344 placed relation read census".into());
        }
        println!(
            "C344_PLACED_READ relation={} occurrences={} resolved_header={} unresolved_occurrences={} unresolved_unique_wires={} foreign={} unqualified={}",
            names[slot], relation.occurrences, relation.resolved_header,
            relation.foreign + relation.unqualified, relation.unique_unresolved_wires,
            relation.foreign, relation.unqualified,
        );
    }
    println!(
        "C344_PLACED_READ_TOTAL row_terms={row_terms} active_occurrences={active_occurrences} resolved_header={resolved} unresolved_occurrences={unresolved_occurrences} unresolved_unique_wires={} scope=placed_header_daa_scheduled",
        unique_global.len(),
    );
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(PlacedReadCensus {
        row_terms,
        active_occurrences,
        unresolved_occurrences,
        unresolved_unique_wires: unique_global.len(),
    })
}

fn compare_imports(
    expected: &[(usize, Writer, Fr)],
    actual: &[(usize, Writer, Fr)],
) -> Result<(), String> {
    if expected.len() != IMPORTS || actual.len() != IMPORTS {
        return Err("C344 MAX/Cap import count".into());
    }
    for (source, replay) in expected.iter().zip(actual) {
        if source.0 != replay.0 || replay.0 / WIDTH != MAX_OWNER {
            return Err("C344 MAX/Cap import owner/wire".into());
        }
        if source.1 != replay.1 {
            return Err("C344 MAX/Cap import context/writer".into());
        }
        if source.2 != replay.2 {
            return Err("C344 MAX/Cap import value".into());
        }
    }
    Ok(())
}

/// Reuse the one C343 frame parse, prefix, plan and native producer. Only a
/// complete native MAX calendar may be compared with first Cap's typed imports.
pub(super) fn join_closed_max_to_cap(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    producer: &NativeOwnerProducer<'_>,
) -> Result<(), String> {
    let snapshot = Eligible08NativeSnapshot::new(plan, prefix)?;
    let admission = Admission::new(plan, prefix, &snapshot)?;
    let publication = admission.first_modern_cap_publication(prefix)?;
    if publication.pending_max_read_count() != IMPORTS
        || publication.pending_max_source_owners() != vec![MAX_OWNER] {
        return Err("C344 first Cap pending MAX import census".into());
    }
    let imports = publication.checked_max_imports(plan, prefix, &snapshot)?;
    drop(publication);
    drop(admission);

    let calendar = snapshot.scheduled_plan().max_calendar();
    if calendar.len() != 7_683 || calendar.last().map(|step| step.0) != Some(MAX_OWNER) {
        return Err("C344 exact descending MAX calendar".into());
    }
    let mut stream = MaxStream::new(plan, prefix, &snapshot)?;
    if stream.remaining_owners() != calendar.len()
        || stream.retained_capacity_bytes() >= 2 * 1024 * 1024
        || stream.closed_owner_cells(MAX_OWNER).err().as_deref()
            != Some("streamed MAX incomplete closure") {
        return Err("C344 incomplete MAX calendar exported source".into());
    }
    let started = Instant::now();
    for (index, (owner, _)) in calendar.iter().enumerate() {
        if index + 1 == calendar.len()
            && (stream.remaining_owners() != 1
                || stream.closed_owner_cells(MAX_OWNER).err().as_deref()
                    != Some("streamed MAX incomplete closure")) {
            return Err("C344 partial MAX calendar exported source".into());
        }
        stream.push_native(producer, *owner)?;
        if (index + 1) % 512 == 0 || index + 1 == calendar.len() {
            println!(
                "C344_MAX_PROGRESS owners={} remaining={} elapsed_s={:.6}",
                index + 1, stream.remaining_owners(), started.elapsed().as_secs_f64(),
            );
            std::io::stdout().flush().map_err(|e| e.to_string())?;
        }
    }
    if stream.remaining_owners() != 0 {
        return Err("C344 MAX calendar incomplete".into());
    }
    let mut replay = Vec::with_capacity(IMPORTS);
    for (wire, author, value) in stream.closed_owner_cells(MAX_OWNER)? {
        if let MaxReplayAuthor::Scheduled(writer @ Writer::Max { context, end }) = author {
            let local = wire % WIDTH;
            if context < 2 && end == MAX_OWNER + 2
                && ([999_424, 1_000_097][context]..[999_648, 1_000_321][context])
                    .contains(&local) {
                replay.push((wire, writer, value));
            }
        }
    }
    compare_imports(&imports, &replay)?;

    // Each negative retains the same value and all other 447 tuples.
    let mut wrong_owner = replay.clone();
    wrong_owner[0].0 += WIDTH;
    if wrong_owner[0].2 != replay[0].2
        || compare_imports(&imports, &wrong_owner).err().as_deref()
            != Some("C344 MAX/Cap import owner/wire") {
        return Err("C344 equal-value wrong-owner negative".into());
    }
    let mut wrong_context = replay.clone();
    wrong_context[0].1 = Writer::Max { context: 1, end: MAX_OWNER + 2 };
    if wrong_context[0].2 != replay[0].2
        || compare_imports(&imports, &wrong_context).err().as_deref()
            != Some("C344 MAX/Cap import context/writer") {
        return Err("C344 equal-value wrong-context negative".into());
    }
    println!(
        "C344_MAX_CAP_JOIN max_owner={MAX_OWNER} cap_owner={CAP_OWNER} max_owners={} imports={} exact_tuples=true partial_rejected=true equal_value_wrong_owner_rejected=true equal_value_wrong_context_rejected=true global_x_row=false",
        calendar.len(), imports.len(),
    );
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

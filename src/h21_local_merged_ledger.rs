//! Test-only closed H21-local ROW/X ledger. This is a structural join only:
//! no native values, frame, transcript, proof, or client synchronization.

use ark_ff::Zero;
use std::{collections::{BTreeMap, BTreeSet}, ops::Range, sync::Arc};

use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass, WIDTH},
    h21_row_support::{
        Family, Registry as SupportRegistry, Sources, Tagged, Writer as SupportWriter,
    },
    h21_scheduled_max_cap::{Plan as Scheduled, Writer as ScheduledWriter},
    header_daa_row_placement::{DeclaredXDomain, Producer, Relation, RowPlan},
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
    x_lease_diagnostic::{Policy, Writer as LeaseWriter},
};

const ROWS: usize = 1 << 19;
const OWNERS: usize = 1 << 21;
const OWNER_SET: [usize; 3] = [845_759, 844_672, 844_670];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum RowWriter {
    Header,
    Daa(usize),
    Scheduled(ScheduledWriter),
    Relocated(Family),
}

#[cfg(test)]
#[path="h21_summary_lease_phase0_tests.rs"]
mod phase0;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum XWriter {
    WorkTree,
    Header,
    DaaRetarget,
    AssemblyInactiveZero,
    Map(usize),
    Score(usize),
    Slack(usize),
    Max(usize),
    Cap(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RowClaim {
    writer: RowWriter,
    term: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct XDomain {
    writer: XWriter,
    start: usize,
    end: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Destination {
    rows: BTreeMap<usize, RowWriter>,
    terms: Vec<RowClaim>,
    x: Vec<XDomain>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Ledger {
    owner: usize,
    class: OwnerClass,
    rows: BTreeMap<usize, RowWriter>,
    terms: Vec<RowClaim>,
    x: Vec<XDomain>,
    source_term_count: usize,
}

/// A private source-derived candidate. The ordinary path can only create it
/// from the three pinned producers below; test mutations operate on its copies.
#[derive(Clone)]
struct Candidate {
    owner: usize,
    class: OwnerClass,
    row_source: Vec<RowClaim>,
    rows: Vec<RowClaim>,
    support_source: Vec<Tagged>,
    support: Vec<Tagged>,
    reservation_source: Vec<(SupportWriter, Range<usize>)>,
    reservations: Vec<(SupportWriter, Range<usize>)>,
    declared: Vec<DeclaredXDomain>,
    policy: Arc<Policy>,
}

impl Candidate {
    fn stage(owner: usize) -> Result<Self, String> {
        if !OWNER_SET.contains(&owner) {
            return Err("candidate owner outside closed owner set".into());
        }
        let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0; 32], [0; 28])?;
        Self::stage_from_plan(&parent, owner)
    }

    pub(super) fn stage_from_plan(
        parent: &WorkTreeHistoryPlan,
        owner: usize,
    ) -> Result<Self, String> {
        if !OWNER_SET.contains(&owner) {
            return Err("candidate owner outside closed owner set".into());
        }
        Self::stage_from_sources(parent, owner, &Sources::new()?)
    }

    // This private source probe does not grant publication outside OWNER_SET.
    // Every source registry, lease and family check still runs below.
    fn stage_from_sources(
        parent: &WorkTreeHistoryPlan,
        owner: usize,
        sources: &Sources,
    ) -> Result<Self, String> {
        let roster = DaaHistoryRoster::compile(parent)?;
        let scheduled = Scheduled::new();
        let row_plan = RowPlan::new(&roster, &scheduled)?;
        let row_batch = row_plan.stage_owner(owner)?;
        let mut row_registry = row_plan.registry(owner)?;
        row_registry.commit(&row_batch)?;
        let class = roster.owner_class(owner as u64)?;
        let policy = Policy::new(parent, &roster, owner)?;
        let row_source = row_batch
            .terms()
            .map(|(relation, term)| {
                row_writer(relation).map(|writer| RowClaim {
                    writer,
                    term: term.clone(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let declared = row_batch.declared_x_domains();

        let (support_source, reservation_source) = {
            let support_batch = sources.stage_sparse_score_owner(owner)?;
            if support_batch.owner() != owner {
                return Err("c128 source owner identity".into());
            }
            let mut support_registry = SupportRegistry::new(owner)?;
            support_registry.commit(&support_batch)?;
            let terms = support_batch.terms().to_vec();
            let reservations = support_batch.reservations().collect::<Vec<_>>();
            (terms, reservations)
        };
        Ok(Self {
            owner,
            class,
            rows: row_source.clone(),
            row_source,
            support: support_source.clone(),
            support_source,
            reservations: reservation_source.clone(),
            reservation_source,
            declared,
            policy: Arc::new(policy),
        })
    }
}

fn row_writer(relation: Relation) -> Result<RowWriter, String> {
    Ok(match relation {
        Relation::Header => RowWriter::Header,
        Relation::DaaLane(lane) => RowWriter::Daa(lane),
        Relation::Scheduled(writer) => RowWriter::Scheduled(writer),
        Relation::Map(_) => return Err("paired-v2 Map relation is unsupported by the H21-local merged ledger".into()),
    })
}

fn support_row_writer(writer: SupportWriter) -> RowWriter {
    match writer {
        SupportWriter::Relocated(family) => RowWriter::Relocated(family),
        SupportWriter::Scheduled(writer) => RowWriter::Scheduled(writer),
        SupportWriter::Daa => RowWriter::Daa(usize::MAX),
    }
}

fn family_span(family: Family) -> Result<Range<usize>, String> {
    let (context, starts, lengths) = match family {
        Family::Map(c) => (c, [477_074, 492_305], [10_347, 10_347]),
        Family::Score(c) => (c, [487_421, 502_652], [4_208, 4_208]),
        Family::V(c) => (c, [491_629, 506_860], [65, 65]),
        Family::W(c) => (c, [491_694, 506_925], [224, 224]),
        Family::Slack(c) => (c, [491_918, 507_149], [387, 387]),
    };
    if context >= 2 {
        return Err("c128 family context".into());
    }
    Ok(starts[context]..starts[context] + lengths[context])
}

fn scheduled_multiset(
    rows: &[RowClaim],
) -> BTreeMap<(ScheduledWriter, usize), Vec<(crate::gkr::Gate, usize)>> {
    let mut out = BTreeMap::new();
    for claim in rows {
        let RowWriter::Scheduled(writer) = claim.writer else {
            continue;
        };
        let gates = out.entry((writer, claim.term.row)).or_insert_with(Vec::new);
        if let Some(index) = gates.iter().position(|(gate, _)| gate == &claim.term.gate) {
            gates[index].1 += 1;
        } else {
            gates.push((claim.term.gate.clone(), 1));
        }
    }
    out
}

fn support_scheduled_multiset(
    terms: &[Tagged],
) -> BTreeMap<(ScheduledWriter, usize), Vec<(crate::gkr::Gate, usize)>> {
    let mut out = BTreeMap::new();
    for tagged in terms {
        let SupportWriter::Scheduled(writer) = tagged.writer else {
            continue;
        };
        let gates = out
            .entry((writer, tagged.term.row))
            .or_insert_with(Vec::new);
        if let Some(index) = gates.iter().position(|(gate, _)| gate == &tagged.term.gate) {
            gates[index].1 += 1;
        } else {
            gates.push((tagged.term.gate.clone(), 1));
        }
    }
    out
}

fn row_claim_multiset(
    rows: &[RowClaim],
) -> BTreeMap<(RowWriter, usize), Vec<(crate::gkr::Gate, usize)>> {
    let mut out = BTreeMap::new();
    for claim in rows {
        let gates = out
            .entry((claim.writer, claim.term.row))
            .or_insert_with(Vec::new);
        if let Some(index) = gates.iter().position(|(gate, _)| gate == &claim.term.gate) {
            gates[index].1 += 1;
        } else {
            gates.push((claim.term.gate.clone(), 1));
        }
    }
    out
}

fn term_multiset(
    terms: impl Iterator<Item = Term>,
) -> BTreeMap<usize, Vec<(crate::gkr::Gate, usize)>> {
    let mut out = BTreeMap::new();
    for term in terms {
        let gates = out.entry(term.row).or_insert_with(Vec::new);
        if let Some(index) = gates.iter().position(|(gate, _)| gate == &term.gate) {
            gates[index].1 += 1;
        } else {
            gates.push((term.gate, 1));
        }
    }
    out
}

fn family_terms(
    terms: &[Tagged],
    family: Family,
) -> BTreeMap<usize, Vec<(crate::gkr::Gate, usize)>> {
    term_multiset(
        terms
            .iter()
            .filter(|tagged| tagged.writer == SupportWriter::Relocated(family))
            .map(|tagged| tagged.term.clone()),
    )
}

fn expected_family_count(terms: &[Tagged], family: Family) -> usize {
    terms
        .iter()
        .filter(|term| term.writer == SupportWriter::Relocated(family))
        .count()
}

fn gate_multisets_equal<K: Ord>(
    left: &BTreeMap<K, Vec<(crate::gkr::Gate, usize)>>,
    right: &BTreeMap<K, Vec<(crate::gkr::Gate, usize)>>,
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    left.iter().all(|(key, left_gates)| {
        let Some(right_gates) = right.get(key) else {
            return false;
        };
        left_gates.len() == right_gates.len()
            && left_gates.iter().all(|(gate, count)| {
                right_gates
                    .iter()
                    .any(|(other, other_count)| gate == other && count == other_count)
            })
    })
}

fn x_writer_for_lease(writer: LeaseWriter) -> XWriter {
    match writer {
        LeaseWriter::Header => XWriter::Header,
        LeaseWriter::DaaRetarget => XWriter::DaaRetarget,
        LeaseWriter::AssemblyInactiveZero => XWriter::AssemblyInactiveZero,
        LeaseWriter::Max0 => XWriter::Max(0),
        LeaseWriter::Max1 => XWriter::Max(1),
        LeaseWriter::Cap0 => XWriter::Cap(0),
        LeaseWriter::Cap1 => XWriter::Cap(1),
    }
}

fn expected_scheduled_lease(writer: ScheduledWriter) -> Result<LeaseWriter, String> {
    match writer {
        ScheduledWriter::Max { context: 0, .. } => Ok(LeaseWriter::Max0),
        ScheduledWriter::Max { context: 1, .. } => Ok(LeaseWriter::Max1),
        ScheduledWriter::Cap { context: 0, .. } => Ok(LeaseWriter::Cap0),
        ScheduledWriter::Cap { context: 1, .. } => Ok(LeaseWriter::Cap1),
        _ => Err("scheduled writer context".into()),
    }
}

fn header_reads_transferred_x(claim: &RowClaim, owner: usize) -> bool {
    if claim.writer != RowWriter::Header {
        return false;
    }
    let gate = &claim.term.gate;
    let base = owner * WIDTH;
    let transferred = |wire: usize| {
        wire.checked_sub(base)
            .is_some_and(|local| (671_744..688_128).contains(&local))
    };
    (!gate.c1.is_zero() || !gate.c3.is_zero()) && transferred(gate.left)
        || (!gate.c2.is_zero() || !gate.c3.is_zero()) && transferred(gate.right)
}

fn canonical_family_reservations(
    owner: usize,
) -> Result<Vec<(SupportWriter, Range<usize>)>, String> {
    let active_score = owner == 845_759;
    let mut out = Vec::new();
    for c in 0..2 {
        out.push((
            SupportWriter::Relocated(Family::Map(c)),
            671_744 + c * 8_192..677_501 + c * 8_192,
        ));
        if active_score {
            out.push((
                SupportWriter::Relocated(Family::Score(c)),
                677_501 + c * 8_192..679_549 + c * 8_192,
            ));
        }
        out.push((
            SupportWriter::Relocated(Family::Slack(c)),
            679_549 + c * 8_192..679_936 + c * 8_192,
        ));
    }
    let mut scheduled_writers = std::collections::BTreeSet::new();
    Scheduled::new().visit_owner(owner, |writer, _| {
        scheduled_writers.insert(writer);
        Ok(())
    })?;
    for writer in scheduled_writers {
        let range = match writer {
            ScheduledWriter::Max { context: 0, .. } => 999_424..1_000_097,
            ScheduledWriter::Max { context: 1, .. } => 1_000_097..1_000_770,
            ScheduledWriter::Cap { context: 0, .. } => 1_000_770..1_002_818,
            ScheduledWriter::Cap { context: 1, .. } => 1_002_818..1_004_866,
            _ => return Err("scheduled reservation context".into()),
        };
        out.push((SupportWriter::Scheduled(writer), range));
    }
    Ok(out)
}

fn closed_with(candidate: Candidate, owner: usize, class: OwnerClass) -> Result<Ledger, String> {
    if !OWNER_SET.contains(&owner) {
        return Err("candidate owner outside closed owner set".into());
    }
    close_source_candidate(candidate, owner, class)
}

// Source-only probes can diagnose an unadmitted owner without weakening the
// public staging or publication whitelist. This function cannot publish.
fn close_source_candidate(candidate: Candidate, owner: usize, class: OwnerClass) -> Result<Ledger, String> {
    // This lookup binds the immutable policy object to both explicit identity
    // arguments before comparing the staged source identity.
    candidate.policy.lease_at(owner, class, 0)?;
    if owner != candidate.owner || class != candidate.class {
        return Err("policy owner/class mismatch".into());
    }
    // Scheduled emissions must be byte-for-byte source-equivalent as a
    // multiset before either copy is deduplicated in the merged ROW ledger.
    if !gate_multisets_equal(
        &scheduled_multiset(&candidate.rows),
        &support_scheduled_multiset(&candidate.support),
    ) {
        return Err("scheduled multiset mismatch".into());
    }
    if !gate_multisets_equal(
        &scheduled_multiset(&candidate.row_source),
        &scheduled_multiset(&candidate.rows),
    ) {
        return Err("c121 source scheduled multiset mismatch".into());
    }
    if !gate_multisets_equal(
        &support_scheduled_multiset(&candidate.support_source),
        &support_scheduled_multiset(&candidate.support),
    ) {
        return Err("c128 source scheduled multiset mismatch".into());
    }
    if candidate
        .rows
        .iter()
        .any(|claim| header_reads_transferred_x(claim, owner))
    {
        return Err("HEADER active read remains in transferred X domains".into());
    }

    // Detect a real cross-writer ROW collision before source-roster/count
    // diagnostics, including a restored HEADER Cap-anchor row.
    let mut row_owners = BTreeMap::<usize, RowWriter>::new();
    for claim in &candidate.rows {
        if claim.term.row / ROWS != owner || claim.term.row >= ROWS * OWNERS {
            return Err("c121 ROW owner/extent".into());
        }
        insert_row(&mut row_owners, claim.term.row, claim.writer)?;
    }
    for tagged in &candidate.support {
        let writer = support_row_writer(tagged.writer);
        if tagged.term.row / ROWS != owner || tagged.term.row >= ROWS * OWNERS {
            return Err("c128 ROW owner/extent".into());
        }
        if let SupportWriter::Relocated(family) = tagged.writer {
            let span = family_span(family)?;
            let local = tagged.term.row - owner * ROWS;
            if !span.contains(&local) || !(477_074..507_536).contains(&local) {
                return Err(format!("c128 family ROW span {family:?}"));
            }
        }
        if let SupportWriter::Daa = tagged.writer {
            return Err("c128 DAA rows outside local merger scope".into());
        }
        insert_row(&mut row_owners, tagged.term.row, writer)?;
    }

    // Source census is checked family-by-family, then the complete tuple
    // multiset catches altered wires or coefficients within an otherwise
    // present family.
    for relation in [
        RowWriter::Header,
        RowWriter::Daa(0),
        RowWriter::Daa(1),
        RowWriter::Daa(2),
        RowWriter::Daa(3),
    ] {
        let before = candidate
            .row_source
            .iter()
            .filter(|x| x.writer == relation)
            .count();
        let after = candidate
            .rows
            .iter()
            .filter(|x| x.writer == relation)
            .count();
        if after == 0 && before > 0 {
            return Err(format!("missing active c121 family {relation:?}"));
        }
        if before != after
            || !gate_multisets_equal(
                &term_multiset(
                    candidate
                        .row_source
                        .iter()
                        .filter(|x| x.writer == relation)
                        .map(|x| x.term.clone()),
                ),
                &term_multiset(
                    candidate
                        .rows
                        .iter()
                        .filter(|x| x.writer == relation)
                        .map(|x| x.term.clone()),
                ),
            )
        {
            return Err(format!("c121 source family mismatch {relation:?}"));
        }
    }
    // The named family checks above give useful single-fault diagnostics; a
    // complete source equality also rejects unrostered writer variants.
    if !gate_multisets_equal(
        &row_claim_multiset(&candidate.row_source),
        &row_claim_multiset(&candidate.rows),
    ) {
        return Err("c121 source ROW tuple mismatch".into());
    }
    for family in [
        Family::Map(0),
        Family::Map(1),
        Family::Score(0),
        Family::Score(1),
        Family::V(0),
        Family::V(1),
        Family::W(0),
        Family::W(1),
        Family::Slack(0),
        Family::Slack(1),
    ] {
        let before = expected_family_count(&candidate.support_source, family);
        let after = expected_family_count(&candidate.support, family);
        if after == 0 && before > 0 {
            return Err(format!("missing active c128 family {family:?}"));
        }
        if before != after
            || !gate_multisets_equal(
                &family_terms(&candidate.support_source, family),
                &family_terms(&candidate.support, family),
            )
        {
            return Err(format!("c128 source family tuple mismatch {family:?}"));
        }
    }
    // Reservation policy is canonical and closed: only Map/Score/Slack write
    // through c128. W/V remain relations that read X values.
    let mut seen_ranges = BTreeMap::<(usize, usize), SupportWriter>::new();
    for (writer, range) in &candidate.reservations {
        if range.start >= range.end || range.end > WIDTH {
            return Err("X reservation extent".into());
        }
        if matches!(
            writer,
            SupportWriter::Relocated(Family::V(_) | Family::W(_))
        ) {
            return Err("V/W cannot own X".into());
        }
        if seen_ranges
            .insert((range.start, range.end), *writer)
            .is_some()
        {
            return Err("duplicate X reservation".into());
        }
    }
    for (writer, range) in &candidate.reservations {
        let SupportWriter::Relocated(family) = *writer else {
            continue;
        };
        let xwriter = match family {
            Family::Map(c) => XWriter::Map(c),
            Family::Score(c) => XWriter::Score(c),
            Family::Slack(c) => XWriter::Slack(c),
            Family::V(_) | Family::W(_) => return Err("V/W cannot own X".into()),
        };
        for cell in range.clone() {
            if candidate.policy.lease_at(owner, class, cell)? != Some(LeaseWriter::Header) {
                return Err(format!("X transfer requires Header lease at {cell}"));
            }
            let _ = xwriter;
        }
    }
    let canonical_reservations = canonical_family_reservations(owner)?;
    if candidate.reservations != canonical_reservations {
        return Err("canonical Map/Score/Slack reservation mismatch".into());
    }
    if candidate.reservation_source != canonical_reservations {
        return Err("source Map/Score/Slack reservation census".into());
    }

    let mut scheduled_domains = Vec::new();
    for (writer, range) in &candidate.reservations {
        if let SupportWriter::Scheduled(scheduled) = *writer {
            let lease = expected_scheduled_lease(scheduled)?;
            for cell in range.clone() {
                if candidate.policy.lease_at(owner, class, cell)? != Some(lease) {
                    return Err("scheduled reservation/lease mismatch".into());
                }
            }
            scheduled_domains.push((scheduled, range.clone()));
        }
    }
    let mut declared_scheduled = Vec::new();
    let base = owner * WIDTH;
    for domain in &candidate.declared {
        if let Producer::Scheduled(writer) = domain.producer {
            if domain.start < base || domain.end < domain.start || domain.end > base + WIDTH {
                return Err("c121 scheduled X declaration extent".into());
            }
            declared_scheduled.push((writer, domain.start - base..domain.end - base));
        }
    }
    if scheduled_domains != declared_scheduled {
        return Err("scheduled reservation/c121 domain mismatch".into());
    }
    let mut declared_daa = Vec::new();
    for domain in &candidate.declared {
        if let Producer::Daa = domain.producer {
            if domain.start < base || domain.end <= domain.start || domain.end > base + WIDTH {
                return Err("c121 DAA X declaration extent".into());
            }
            declared_daa.push((domain.start, domain.end));
            for cell in domain.start - base..domain.end - base {
                if candidate.policy.lease_at(owner, class, cell)? != Some(LeaseWriter::DaaRetarget)
                {
                    return Err("DAA domain/lease mismatch".into());
                }
            }
        }
    }
    let expected_daa = if matches!(
        class,
        OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_)
    ) {
        crate::daa_history_roster::BANKS
            .iter()
            .map(|&(start, end)| (base + start, base + end))
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    if declared_daa != expected_daa {
        return Err("c121 DAA declaration census".into());
    }
    let bank_lease = if matches!(
        class,
        OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_)
    ) {
        LeaseWriter::DaaRetarget
    } else {
        LeaseWriter::AssemblyInactiveZero
    };
    for (start, end) in crate::daa_history_roster::BANKS {
        for cell in start..end {
            if candidate.policy.lease_at(owner, class, cell)? != Some(bank_lease) {
                return Err("BANKS owner-class lease mismatch".into());
            }
        }
    }

    // Turn the immutable policy into compact disjoint spans. Map/Score/Slack
    // transfer only Header leases; all WorkTree reservations remain explicit.
    let mut transferred = BTreeMap::<usize, XWriter>::new();
    for (writer, range) in &candidate.reservations {
        let xwriter = match *writer {
            SupportWriter::Relocated(Family::Map(c)) => XWriter::Map(c),
            SupportWriter::Relocated(Family::Score(c)) => XWriter::Score(c),
            SupportWriter::Relocated(Family::Slack(c)) => XWriter::Slack(c),
            SupportWriter::Scheduled(_) => continue,
            _ => return Err("unsupported c128 X writer".into()),
        };
        for cell in range.clone() {
            if transferred.insert(cell, xwriter).is_some() {
                return Err("overlapping X transfer".into());
            }
        }
    }
    let mut domains = Vec::<XDomain>::new();
    let mut current: Option<(XWriter, usize)> = None;
    for cell in 0..WIDTH {
        let lease = candidate.policy.lease_at(owner, class, cell)?;
        let writer = if let Some(&moved) = transferred.get(&cell) {
            if lease != Some(LeaseWriter::Header) {
                return Err(format!("non-Header X transfer at {cell}"));
            }
            moved
        } else {
            lease.map(x_writer_for_lease).unwrap_or(XWriter::WorkTree)
        };
        match current {
            Some((active, start)) if active == writer => current = Some((active, start)),
            Some((active, start)) => {
                domains.push(XDomain {
                    writer: active,
                    start: base + start,
                    end: base + cell,
                });
                current = Some((writer, cell));
            }
            None => current = Some((writer, cell)),
        }
    }
    if let Some((writer, start)) = current {
        domains.push(XDomain {
            writer,
            start: base + start,
            end: base + WIDTH,
        });
    }

    // Keep every c121 Gate and each non-scheduled c128 Gate, including
    // multiple same-writer occurrences on one ROW. The equal c128 scheduled
    // copy was checked above and is the only copy omitted here.
    let mut terms = candidate.rows;
    terms.extend(
        candidate
            .support
            .into_iter()
            .filter_map(|tagged| match tagged.writer {
                SupportWriter::Scheduled(_) => None,
                writer => Some(RowClaim {
                    writer: support_row_writer(writer),
                    term: tagged.term,
                }),
            }),
    );
    let source_term_count = terms.len();
    Ok(Ledger {
        owner,
        class,
        rows: row_owners,
        terms,
        x: domains,
        source_term_count,
    })
}

fn close_score_cap_join(
    candidate: Candidate,
    projection: &crate::score_prefix_r_anchor::ScoreCapProjection,
) -> Result<Ledger, String> {
    use crate::score_prefix_r_anchor::ScoreCapRelation as JoinRelation;
    const OWNER: usize = 845_759;
    if candidate.owner != OWNER
        || candidate.class != OwnerClass::Carry
        || projection.owner != OWNER
    {
        return Err("c146 Score/Cap join owner/class".into());
    }

    // Compare a copy of the c146 prior-owner W polynomial in the c128 wire
    // orientation. The source equations differ only by placing the same
    // coefficient on the explicitly-zero wire; this is polynomial equivalence
    // for this structural join, not native value or frame custody.
    let mut comparison_rows = projection.rows.clone();
    for context in 0..2 {
        let row_base = OWNER * ROWS + [491_694, 506_925][context];
        let wire_base = (OWNER - 1) * WIDTH + 987_450;
        for offset in 0..224 {
            let source = Term {
                row: row_base + offset,
                gate: crate::gkr::Gate {
                    left: wire_base + offset,
                    right: 0,
                    c0: ark_bn254::Fr::zero(),
                    c1: -ark_bn254::Fr::from(1u8),
                    c2: ark_bn254::Fr::zero(),
                    c3: ark_bn254::Fr::zero(),
                },
            };
            let matches = comparison_rows.iter().filter(|claim| {
                claim.relation == JoinRelation::AliasW(context) && claim.term == source
            }).count();
            if matches != 1 {
                return Err(format!("c146 AliasW prior-owner polynomial source mismatch context={context} offset={offset}"));
            }
            let comparison = comparison_rows.iter_mut().find(|claim| {
                claim.relation == JoinRelation::AliasW(context) && claim.term == source
            }).expect("unique prior-owner W source was counted");
            comparison.term.gate.left = 0;
            comparison.term.gate.right = wire_base + offset;
            comparison.term.gate.c1 = ark_bn254::Fr::zero();
            comparison.term.gate.c2 = -ark_bn254::Fr::from(1u8);
        }
    }

    let mut row_owners = BTreeMap::new();
    for claim in &projection.rows {
        if claim.term.row / ROWS != OWNER || claim.term.row >= (OWNER + 1) * ROWS {
            return Err("c146 Score/Cap ROW owner/extent".into());
        }
        let allowed = match claim.relation {
            JoinRelation::ModernScore(context) | JoinRelation::AliasW(context) | JoinRelation::AliasV(context) => context < 2,
            JoinRelation::Cap(ScheduledWriter::Cap { context, origin }) => context < 2 && origin == OWNER + 1,
            _ => false,
        };
        if !allowed {
            return Err("c146 Score/Cap unrecognized relation".into());
        }
        if let Some(old) = row_owners.insert(claim.term.row, claim.relation) {
            if old != claim.relation {
                return Err("c146 Score/Cap semantic ROW owner collision".into());
            }
        }
    }
    for context in 0..2 {
        let relation = JoinRelation::ModernScore(context);
        let produced = term_multiset(
            projection.rows.iter().filter(|row| row.relation == relation)
                .map(|row| row.term.clone()),
        );
        let consumed = term_multiset(
            candidate.support_source.iter().filter(|tagged|
                tagged.writer == SupportWriter::Relocated(Family::Score(context)))
                .map(|tagged| tagged.term.clone()),
        );
        if produced != consumed {
            return Err(format!("c146 Score source ROW relation mismatch context={context}"));
        }
        for (relation, family) in [
            (JoinRelation::AliasW(context), Family::W(context)),
            (JoinRelation::AliasV(context), Family::V(context)),
        ] {
            let produced = term_multiset(
                comparison_rows.iter().filter(|row| row.relation == relation)
                    .map(|row| row.term.clone()),
            );
            let consumed = term_multiset(
                candidate.support_source.iter().filter(|tagged|
                    tagged.writer == SupportWriter::Relocated(family))
                    .map(|tagged| tagged.term.clone()),
            );
            if produced != consumed {
                return Err(format!("c146 Score alias ROW relation mismatch context={context}"));
            }
        }
        let writer = ScheduledWriter::Cap { context, origin: OWNER + 1 };
        let relation = JoinRelation::Cap(writer);
        let produced = term_multiset(
            projection.rows.iter().filter(|row| row.relation == relation)
                .map(|row| row.term.clone()),
        );
        let consumed = term_multiset(
            candidate.row_source.iter().filter(|claim| claim.writer == RowWriter::Scheduled(writer))
                .map(|claim| claim.term.clone()),
        );
        if produced != consumed {
            return Err(format!("c146 Cap source ROW relation mismatch context={context}"));
        }
    }

    let mut supplied_x = BTreeSet::new();
    let mut x_spans = Vec::new();
    for claim in &projection.x {
        if claim.owner != OWNER || claim.start >= claim.end
            || !supplied_x.insert((claim.relation, claim.owner, claim.start, claim.end))
        {
            return Err("c146 Score/Cap duplicate or invalid X claim".into());
        }
        if x_spans.iter().any(|(owner, start, end)|
            *owner == claim.owner && claim.start < *end && *start < claim.end)
        {
            return Err("c146 Score/Cap overlapping X claim".into());
        }
        x_spans.push((claim.owner, claim.start, claim.end));
    }
    let mut expected_x = BTreeSet::new();
    for (writer, range) in &candidate.reservation_source {
        let relation = match writer {
            SupportWriter::Relocated(Family::Score(context)) => JoinRelation::ModernScore(*context),
            SupportWriter::Scheduled(writer @ ScheduledWriter::Cap { .. }) => JoinRelation::Cap(*writer),
            _ => continue,
        };
        expected_x.insert((relation, OWNER, OWNER * WIDTH + range.start, OWNER * WIDTH + range.end));
    }
    if supplied_x != expected_x {
        return Err("c146 Score/Cap X lease source mismatch".into());
    }
    let mut declared_cap = BTreeSet::new();
    for domain in &candidate.declared {
        if let Producer::Scheduled(writer @ ScheduledWriter::Cap { .. }) = domain.producer {
            declared_cap.insert((JoinRelation::Cap(writer), OWNER, domain.start, domain.end));
        }
    }
    let expected_cap = expected_x.iter().filter(|(relation, ..)| matches!(relation, JoinRelation::Cap(_)))
        .copied().collect::<BTreeSet<_>>();
    if declared_cap != expected_cap {
        return Err("c146 Cap X declaration source mismatch".into());
    }
    close_source_candidate(candidate, OWNER, OwnerClass::Carry)
}

fn insert_row(
    rows: &mut BTreeMap<usize, RowWriter>,
    row: usize,
    writer: RowWriter,
) -> Result<(), String> {
    if let Some(previous) = rows.get(&row) {
        if *previous != writer {
            return Err(format!(
                "cross-writer ROW collision at {row}: {previous:?} vs {writer:?}"
            ));
        }
    } else {
        rows.insert(row, writer);
    }
    Ok(())
}

impl Ledger {
    fn publish(candidate: Candidate, destination: &mut Destination) -> Result<Self, String> {
        let owner = candidate.owner;
        let class = candidate.class;
        Self::publish_with(candidate, owner, class, destination)
    }

    fn publish_with(
        candidate: Candidate,
        owner: usize,
        class: OwnerClass,
        destination: &mut Destination,
    ) -> Result<Self, String> {
        let ledger = closed_with(candidate, owner, class)?;
        Self::publish_closed(ledger, destination)
    }

    fn publish_score_cap_join(
        candidate: Candidate,
        projection: &crate::score_prefix_r_anchor::ScoreCapProjection,
        destination: &mut Destination,
    ) -> Result<Self, String> {
        let ledger = close_score_cap_join(candidate, projection)?;
        Self::publish_closed(ledger, destination)
    }

    fn publish_closed(ledger: Self, destination: &mut Destination) -> Result<Self, String> {
        let mut next = destination.clone();
        for (row, writer) in &ledger.rows {
            if next.rows.contains_key(row) {
                return Err(format!("destination ROW already occupied at {row}"));
            }
            next.rows.insert(*row, *writer);
        }
        for domain in &ledger.x {
            if next
                .x
                .iter()
                .any(|existing| domain.start < existing.end && existing.start < domain.end)
            {
                return Err("destination X domain overlap".into());
            }
            next.x.push(domain.clone());
        }
        next.terms.extend(ledger.terms.iter().cloned());
        *destination = next;
        Ok(ledger)
    }
}

/// A bounded structural join of the three already admitted owners. This uses
/// the real LOCAL ledger publisher; Work and CROSS keep their own namespaces.
/// It neither assigns values nor authenticates a common X under a commitment.
struct ParentBoundMerger {
    sources: crate::h21_row_support::ParentMapSources,
    destination: Destination,
}

#[derive(Clone)]
struct ParentBoundCandidate {
    binding: crate::h21_row_support::ParentMapBinding,
    candidate: Candidate,
    // Immutable source ROW occurrences, retained separately from mutable copies.
    source_rows: Arc<Vec<RowClaim>>,
}

impl ParentBoundMerger {
    fn new(parent: &WorkTreeHistoryPlan,
        parameters: [crate::h21_row_support::MapParameters; 2]) -> Result<Self, String> {
        Ok(Self {sources: crate::h21_row_support::ParentMapSources::new(parent, parameters)?,
            destination: Destination::default()})
    }

    fn stage(&self, parent: &WorkTreeHistoryPlan, owner: usize) -> Result<ParentBoundCandidate, String> {
        self.sources.validate(parent, self.sources.binding())?;
        if !OWNER_SET.contains(&owner) {
            return Err("c141 owner outside admitted LOCAL set".into());
        }
        let candidate = Candidate::stage_from_sources(parent, owner, self.sources.sources())?;
        Ok(ParentBoundCandidate {binding: self.sources.binding().clone(),
            source_rows: Arc::new(candidate.row_source.clone()),candidate})
    }

    fn publish(&mut self, parent: &WorkTreeHistoryPlan, staged: ParentBoundCandidate) -> Result<Ledger, String> {
        self.sources.validate(parent, &staged.binding)?;
        let candidate = staged.candidate;
        if !OWNER_SET.contains(&candidate.owner) {
            return Err("c141 owner outside admitted LOCAL set".into());
        }
        if !gate_multisets_equal(&row_claim_multiset(&candidate.row_source),
            &row_claim_multiset(&staged.source_rows)) {
            return Err("c141 immutable source ROW occurrence multiset".into());
        }
        // Re-emit the actual selected Map/Score/scheduled source, rather than
        // accepting a matching binding label on stale or substituted tuples.
        let source = self.sources.sources().stage_sparse_score_owner(candidate.owner)?;
        let expected = source.terms().iter().map(|t|RowClaim {
            writer:support_row_writer(t.writer),term:t.term.clone()}).collect::<Vec<_>>();
        let claimed = candidate.support_source.iter().map(|t|RowClaim {
            writer:support_row_writer(t.writer),term:t.term.clone()}).collect::<Vec<_>>();
        if !gate_multisets_equal(&row_claim_multiset(&expected),&row_claim_multiset(&claimed))
            ||source.reservations().collect::<Vec<_>>()!=candidate.reservation_source {
            return Err("c141 emitted source tuple/reservation multiset".into());
        }
        Ledger::publish(candidate, &mut self.destination)
    }
}

/// Test-only view of the actually published mature-EIP owner. The local
/// ledger commits ROW terms and X domains, but does not retain X bit values.
#[cfg(test)]
pub(crate) fn published_mature_eip_844672_claims(
    parent: &WorkTreeHistoryPlan,
) -> Result<(Vec<Term>, Vec<Range<usize>>), String> {
    let owner = 844_672usize;
    let candidate = Candidate::stage_from_plan(parent, owner)?;
    let mut destination = Destination::default();
    let ledger = Ledger::publish(candidate, &mut destination)?;
    if ledger.owner != owner || ledger.class != OwnerClass::Mature(crate::daa_integer::Epoch::Eip)
        || destination.terms != ledger.terms
    {
        return Err("c151 mature-EIP publication receipt mismatch".into());
    }
    let row_terms = ledger
        .terms
        .iter()
        .filter(|claim| matches!(claim.writer, RowWriter::Daa(_)))
        .map(|claim| claim.term.clone())
        .collect::<Vec<_>>();
    let owner_base = owner.checked_mul(WIDTH).ok_or("c151 published owner base overflow")?;
    let domains = ledger
        .x
        .iter()
        .filter(|domain| domain.writer == XWriter::DaaRetarget)
        .map(|domain| {
            Ok(domain.start.checked_sub(owner_base).ok_or("c151 published DAA domain before owner")?
                ..domain.end.checked_sub(owner_base).ok_or("c151 published DAA domain before owner")?)
        })
        .collect::<Result<Vec<_>, String>>()?;
    if domains.len() != crate::daa_history_roster::BANKS.len() {
        return Err("c151 published DAA domain count mismatch".into());
    }
    Ok((row_terms, domains))
}

#[cfg(test)]
#[path="h21_common_writer_preflight_tests.rs"]
mod multiowner_tests;

/// A source-closed Carry ledger bound to the exact native parent inputs.
/// Its ROW19 ledger remains a separate role; this wrapper does not merge any
/// Work or CROSS row namespace into it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NativeCarryLedger {
    ledger: Ledger,
    root: [u8; 32],
    total_be28: [u8; 28],
    max_terms: Vec<(ScheduledWriter, Term)>,
}

impl NativeCarryLedger {
    pub(super) fn owner(&self) -> usize {
        self.ledger.owner
    }

    pub(super) fn class(&self) -> OwnerClass {
        self.ledger.class
    }

    pub(super) fn root(&self) -> [u8; 32] {
        self.root
    }

    pub(super) fn total(&self) -> [u8; 28] {
        self.total_be28
    }

    /// Global ROW19 claims and their source writers; consumers may inspect the
    /// set without gaining an API to publish or mutate it.
    pub(super) fn rows(&self) -> &BTreeMap<usize, RowWriter> {
        &self.ledger.rows
    }

    /// Copy of global ROW19 addresses. Callers can preflight an atomic
    /// destination without mutating this closed ledger.
    pub(super) fn row_addresses(&self) -> Vec<usize> {
        self.ledger.rows.keys().copied().collect()
    }

    /// Copy of the disjoint X lease domains and their source writers.
    pub(super) fn x_domains(&self) -> Vec<(XWriter, std::ops::Range<usize>)> {
        self.ledger
            .x
            .iter()
            .map(|domain| (domain.writer, domain.start..domain.end))
            .collect()
    }

    /// Complete c121 scheduled MAX source multiset for source comparison.
    pub(super) fn scheduled_max_terms(&self) -> &[(ScheduledWriter, Term)] {
        &self.max_terms
    }

    /// Exact source-generated occurrences for one relocated Map family.
    /// This exposes a read-only copy for combined consumers to compare against
    /// their own re-emission without widening the LOCAL publication API.
    pub(super) fn relocated_map_terms(&self, context: usize) -> Result<Vec<Term>, String> {
        if context >= 2 {
            return Err("native Carry Map context".into());
        }
        Ok(self
            .ledger
            .terms
            .iter()
            .filter(|claim| claim.writer == RowWriter::Relocated(Family::Map(context)))
            .map(|claim| claim.term.clone())
            .collect())
    }

    pub(super) fn x_writer_at(&self, address: usize) -> Option<XWriter> {
        self.ledger
            .x
            .iter()
            .find(|domain| domain.start <= address && address < domain.end)
            .map(|domain| domain.writer)
    }

    pub(super) fn is_worktree(&self, address: usize) -> bool {
        self.x_writer_at(address) == Some(XWriter::WorkTree)
    }

    pub(super) fn is_max(&self, context: usize, address: usize) -> bool {
        self.x_writer_at(address) == Some(XWriter::Max(context))
    }
}

/// Close only the owner844670 Carry structural ledger from the caller's exact
/// parent. Native values and publication remain the responsibility of the
/// separate native admission bundle.
pub(super) fn close_native_carry(plan: &WorkTreeHistoryPlan) -> Result<NativeCarryLedger, String> {
    const OWNER: usize = 844_670;
    if plan.headers() != 1_827_840 || plan.slot_log() != 21 {
        return Err("native Carry ledger requires the pinned H21 parent geometry".into());
    }
    let candidate = Candidate::stage_from_plan(plan, OWNER)?;
    if candidate.class != OwnerClass::Carry {
        return Err("native Carry ledger owner class mismatch".into());
    }
    let ledger = closed_with(candidate, OWNER, OwnerClass::Carry)?;
    let max_terms = ledger
        .terms
        .iter()
        .filter_map(|claim| match claim.writer {
            RowWriter::Scheduled(writer @ ScheduledWriter::Max { .. }) => {
                Some((writer, claim.term.clone()))
            }
            _ => None,
        })
        .collect();
    Ok(NativeCarryLedger {
        ledger,
        root: plan.descriptor().root,
        total_be28: plan.work_profile().total_be28,
        max_terms,
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        daa_history_roster::DaaHistoryRoster,
        daa_integer::Epoch,
        h21_row_support::{Family, Writer as SupportWriter},
        h21_scheduled_max_cap::{Plan as Scheduled, Writer as ScheduledWriter},
        header_daa_row_placement::{Producer, Relation, RowPlan},
        work_tree_history_plan::WorkTreeHistoryPlan,
    };
    use ark_bn254::Fr;
    use ark_ff::{One, Zero};

    use super::{Candidate, Destination, Ledger, RowWriter, XDomain, XWriter, WIDTH};

    fn rejected(candidate: Candidate, expected: &str) {
        let mut destination = Destination::default();
        let before = destination.clone();
        let error = Ledger::publish(candidate, &mut destination).unwrap_err();
        assert_eq!(error, expected);
        assert_eq!(
            destination, before,
            "failed candidate changed ROW or X destination"
        );
    }

    fn rejected_seeded(candidate: Candidate, expected: &str) {
        let mut destination = seeded_destination();
        let before = destination.clone();
        let error = Ledger::publish(candidate, &mut destination).unwrap_err();
        assert_eq!(error, expected);
        assert_eq!(
            destination, before,
            "failed candidate changed the seeded ROW or X destination"
        );
    }

    #[test]
    fn header_transfer_source_probe() {
        let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0; 32], [0; 28]).unwrap();
        let roster = DaaHistoryRoster::compile(&parent).unwrap();
        let scheduled = Scheduled::new();
        let plan = RowPlan::new(&roster, &scheduled).unwrap();
        for owner in [845_759usize, 844_672] {
            let batch = plan.stage_owner(owner).unwrap();
            let base = owner * (1 << 20);
            let mut reads = 0usize;
            let mut unary = 0usize;
            let mut examples = Vec::new();
            for (relation, term) in batch.terms() {
                if relation != Relation::Header {
                    continue;
                }
                let gate = &term.gate;
                let left_active = !gate.c1.is_zero() || !gate.c3.is_zero();
                let right_active = !gate.c2.is_zero() || !gate.c3.is_zero();
                let transfer = |global: usize| {
                    global.checked_sub(base).is_some_and(|q| {
                        (671_744..679_936).contains(&q) || (679_936..688_128).contains(&q)
                    })
                };
                if (left_active && transfer(gate.left)) || (right_active && transfer(gate.right)) {
                    reads += 1;
                    let identity = gate.c0.is_zero()
                        && gate.c1 == Fr::one()
                        && gate.c2.is_zero()
                        && gate.c3.is_zero()
                        && gate.right == base;
                    if identity {
                        unary += 1;
                    }
                    if examples.len() < 8 {
                        examples.push((
                            term.row - owner * (1 << 19),
                            gate.left.saturating_sub(base),
                            gate.right.saturating_sub(base),
                            identity,
                        ));
                    }
                }
            }
            println!("C134_HEADER_TRANSFER owner={owner} reads={reads} unary_anchors={unary} examples={examples:?}");
        }
    }

    fn published_owner(owner: usize, transferred: usize) -> (Ledger, Destination) {
        let mut destination = Destination::default();
        let candidate = Candidate::stage(owner).unwrap();
        let mut expected_terms = candidate.row_source.clone();
        expected_terms.extend(candidate.support_source.iter().filter_map(|tagged| {
            match tagged.writer {
                SupportWriter::Scheduled(_) => None,
                writer => Some(super::RowClaim {
                    writer: super::support_row_writer(writer),
                    term: tagged.term.clone(),
                }),
            }
        }));
        let ledger = Ledger::publish(candidate, &mut destination).unwrap();
        assert_eq!(ledger.owner, owner);
        assert!(!ledger.rows.is_empty());
        assert_eq!(ledger.source_term_count, ledger.terms.len());
        assert!(ledger.source_term_count > ledger.rows.len());
        assert_eq!(destination.terms, ledger.terms);
        assert!(super::gate_multisets_equal(
            &super::row_claim_multiset(&expected_terms),
            &super::row_claim_multiset(&ledger.terms),
        ));
        let moved = ledger
            .x
            .iter()
            .filter(|domain| {
                matches!(
                    domain.writer,
                    XWriter::Map(_) | XWriter::Score(_) | XWriter::Slack(_)
                )
            })
            .map(|domain| domain.end - domain.start)
            .sum::<usize>();
        assert_eq!(moved, transferred);
        assert!(ledger
            .x
            .iter()
            .any(|domain| domain.writer == XWriter::WorkTree));
        let base = owner * (1 << 20);
        for (context, start, end) in [(0, 1_000_770, 1_002_818), (1, 1_002_818, 1_004_866)] {
            if owner == 845_759 {
                assert!(ledger.x.contains(&XDomain {
                    writer: XWriter::Cap(context),
                    start: base + start,
                    end: base + end,
                }));
            } else {
                assert!(ledger.x.iter().any(|domain| {
                    domain.writer == XWriter::Header
                        && domain.start <= base + start
                        && domain.end >= base + end
                }));
            }
        }
        let bank_writer = if owner == 844_672 {
            XWriter::DaaRetarget
        } else {
            XWriter::AssemblyInactiveZero
        };
        for (start, end) in crate::daa_history_roster::BANKS {
            assert!(ledger.x.iter().any(|domain| {
                domain.writer == bank_writer
                    && domain.start <= base + start
                    && domain.end >= base + end
            }));
        }
        assert!(!destination.rows.is_empty());
        assert!(!destination.x.is_empty());
        (ledger, destination)
    }

    #[test]
    fn closes_845759_active_score_and_atomic_domains() {
        let (ledger, _) = published_owner(845_759, 16_384);
        for family in [
            Family::Map(0),
            Family::Map(1),
            Family::Score(0),
            Family::Score(1),
            Family::V(0),
            Family::V(1),
            Family::W(0),
            Family::W(1),
            Family::Slack(0),
            Family::Slack(1),
        ] {
            assert!(
                ledger
                    .rows
                    .values()
                    .any(|writer| *writer == RowWriter::Relocated(family)),
                "active source family absent from closed rows: {family:?}"
            );
        }
        assert_eq!(ledger.class, crate::daa_history_roster::OwnerClass::Carry);
    }

    #[test]
    fn closes_844672_inactive_score_and_daa_retarget() {
        let (ledger, _) = published_owner(844_672, 12_288);
        assert_eq!(
            ledger.class,
            crate::daa_history_roster::OwnerClass::Mature(Epoch::Eip)
        );
        assert!(!ledger
            .x
            .iter()
            .any(|domain| matches!(domain.writer, XWriter::Score(_))));
        assert!(ledger
            .x
            .iter()
            .any(|domain| domain.writer == XWriter::DaaRetarget));
    }

    #[test]
    fn joins_mature_eip_retarget_producer_to_ledger_with_atomic_faults() {
        let (plan, packed) =
            crate::daa_history_producer_tests::mature_eip_844672_h21_case();
        assert_eq!(
            packed.len(),
            crate::daa_history_producer::PACKED_OWNER_BYTES
        );
        assert!(
            crate::daa_history_roster::BANKS.iter().any(|&(start, end)| {
                packed[start / 8..end / 8].iter().any(|byte| *byte != 0)
            }),
            "actual retarget output must contain non-vacuous bank data"
        );

        let pristine = Candidate::stage_from_plan(&plan, 844_672).unwrap();
        let mut expected_terms = pristine.row_source.clone();
        expected_terms.extend(pristine.support_source.iter().filter_map(|tagged| {
            match tagged.writer {
                SupportWriter::Scheduled(_) => None,
                writer => Some(super::RowClaim {
                    writer: super::support_row_writer(writer),
                    term: tagged.term.clone(),
                }),
            }
        }));
        let mut destination = seeded_destination();
        let ledger = Ledger::publish(pristine.clone(), &mut destination).unwrap();
        assert_eq!(
            ledger.class,
            crate::daa_history_roster::OwnerClass::Mature(Epoch::Eip)
        );
        assert_eq!(destination.terms, ledger.terms);
        assert_eq!(ledger.source_term_count, ledger.terms.len());
        assert!(super::gate_multisets_equal(
            &super::row_claim_multiset(&expected_terms),
            &super::row_claim_multiset(&ledger.terms),
        ));
        assert!(!ledger
            .x
            .iter()
            .any(|domain| matches!(domain.writer, XWriter::Score(_))));
        let base = 844_672 * WIDTH;
        let expected_daa = crate::daa_history_roster::BANKS
            .iter()
            .map(|&(start, end)| super::XDomain {
                writer: XWriter::DaaRetarget,
                start: base + start,
                end: base + end,
            })
            .collect::<Vec<_>>();
        let actual_daa = ledger
            .x
            .iter()
            .filter(|domain| domain.writer == XWriter::DaaRetarget)
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(actual_daa, expected_daa);

        let mut premature_score = pristine.clone();
        premature_score
            .reservations
            .push((SupportWriter::Relocated(Family::Score(0)), 677_501..679_549));
        rejected_seeded(
            premature_score,
            "canonical Map/Score/Slack reservation mismatch",
        );

        let daa_index = pristine
            .declared
            .iter()
            .position(|domain| matches!(domain.producer, Producer::Daa))
            .expect("source DAA X declaration");
        let mut omitted_daa = pristine.clone();
        omitted_daa.declared.remove(daa_index);
        rejected_seeded(omitted_daa, "c121 DAA declaration census");

        let mut duplicate_daa = pristine.clone();
        duplicate_daa.declared.push(duplicate_daa.declared[daa_index]);
        rejected_seeded(duplicate_daa, "c121 DAA declaration census");

        let mut shifted_daa = pristine;
        shifted_daa.declared[daa_index].start += 1;
        rejected_seeded(shifted_daa, "c121 DAA declaration census");
    }

    #[test]
    fn closes_native_844670_carry_against_supplied_parent() {
        let root = [0x5au8; 32];
        let total = [0x31u8; 28];
        let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, root, total).unwrap();
        let ledger = super::close_native_carry(&parent).unwrap();

        assert_eq!(ledger.owner(), 844_670);
        assert_eq!(ledger.class(), crate::daa_history_roster::OwnerClass::Carry);
        assert_eq!(ledger.root(), root);
        assert_eq!(ledger.total(), total);
        assert!(ledger
            .rows()
            .values()
            .any(|writer| *writer == RowWriter::Daa(3)));
        assert!(ledger.is_worktree(844_670 * WIDTH + 987_674));
        assert!(ledger.is_max(0, 844_670 * WIDTH + 999_424));
        assert!(ledger.is_max(1, 844_670 * WIDTH + 1_000_097));
        assert!(!ledger.is_max(0, 844_670 * WIDTH + 1_000_097));
        assert_eq!(ledger.row_addresses().len(), ledger.rows().len());
        assert!(ledger
            .x_domains()
            .iter()
            .any(|(writer, range)| *writer == XWriter::WorkTree
                && range.start <= 844_670 * WIDTH + 987_674
                && 844_670 * WIDTH + 987_674 < range.end));

        for context in 0..2 {
            assert_eq!(
                ledger
                    .scheduled_max_terms()
                    .iter()
                    .filter(|(writer, _)| matches!(writer, ScheduledWriter::Max { context: c, .. } if *c == context))
                    .count(),
                2_690
            );
        }
    }

    #[test]
    fn native_carry_rejects_parent_with_wrong_height_before_staging() {
        let parent = WorkTreeHistoryPlan::compile(1_827_839, 21, [0; 32], [0; 28]).unwrap();
        assert_eq!(
            super::close_native_carry(&parent).unwrap_err(),
            "native Carry ledger requires the pinned H21 parent geometry"
        );
    }

    #[test]
    fn rejects_active_header_reads_of_transferred_x_independently() {
        let pristine = Candidate::stage(845_759).unwrap();
        let index = pristine
            .rows
            .iter()
            .position(|claim| claim.writer == RowWriter::Header)
            .expect("source HEADER gate");
        let base = 845_759usize * (1 << 20);
        for (left_transfer, c1, c2, c3) in [
            (true, 1, 0, 0),
            (false, 0, 1, 0),
            (true, 0, 0, 1),
            (false, 0, 0, 1),
        ] {
            let mut candidate = pristine.clone();
            let gate = &mut candidate.rows[index].term.gate;
            gate.c1 = Fr::from(c1);
            gate.c2 = Fr::from(c2);
            gate.c3 = Fr::from(c3);
            gate.left = base + if left_transfer { 671_744 } else { 0 };
            gate.right = base + if left_transfer { 0 } else { 671_744 };
            assert!(super::header_reads_transferred_x(
                &candidate.rows[index],
                845_759
            ));
            rejected(
                candidate,
                "HEADER active read remains in transferred X domains",
            );
        }

        let mut inactive = pristine.rows[index].clone();
        inactive.term.gate.c1 = Fr::zero();
        inactive.term.gate.c2 = Fr::zero();
        inactive.term.gate.c3 = Fr::zero();
        inactive.term.gate.left = base + 671_744;
        inactive.term.gate.right = base + 671_744;
        assert!(!super::header_reads_transferred_x(&inactive, 845_759));
        inactive.term.gate.c1 = Fr::one();
        inactive.writer = RowWriter::Daa(0);
        assert!(!super::header_reads_transferred_x(&inactive, 845_759));
    }

    #[test]
    fn rejects_independent_scheduled_x_declaration_faults() {
        let pristine = Candidate::stage(845_759).unwrap();
        let index = pristine
            .declared
            .iter()
            .position(|domain| {
                matches!(
                    domain.producer,
                    Producer::Scheduled(ScheduledWriter::Cap { context: 0, .. })
                )
            })
            .expect("source Cap0 X declaration");
        let base = 845_759usize * (1 << 20);
        let mut omitted = pristine.clone();
        omitted.declared.remove(index);
        rejected(omitted, "scheduled reservation/c121 domain mismatch");

        let mut duplicate = pristine.clone();
        duplicate.declared.push(duplicate.declared[index]);
        rejected(duplicate, "scheduled reservation/c121 domain mismatch");

        let Producer::Scheduled(ScheduledWriter::Cap { origin, .. }) =
            pristine.declared[index].producer
        else {
            unreachable!()
        };
        let mut context = pristine.clone();
        context.declared[index].producer =
            Producer::Scheduled(ScheduledWriter::Cap { context: 1, origin });
        rejected(context, "scheduled reservation/c121 domain mismatch");

        let mut changed_origin = pristine.clone();
        changed_origin.declared[index].producer = Producer::Scheduled(ScheduledWriter::Cap {
            context: 0,
            origin: origin + 1,
        });
        rejected(changed_origin, "scheduled reservation/c121 domain mismatch");

        let mut shifted = pristine.clone();
        shifted.declared[index].start += 1;
        rejected(shifted, "scheduled reservation/c121 domain mismatch");

        let mut shortened = pristine.clone();
        shortened.declared[index].end -= 1;
        rejected(shortened, "scheduled reservation/c121 domain mismatch");

        let mut outside = pristine.clone();
        outside.declared[index].start = base - 1;
        rejected(outside, "c121 scheduled X declaration extent");

        let mut inverted = pristine.clone();
        inverted.declared[index].end = inverted.declared[index].start - 1;
        rejected(inverted, "c121 scheduled X declaration extent");
    }

    #[test]
    fn rejects_wrong_policy_owner_and_class_without_publication() {
        let pristine = Candidate::stage(845_759).unwrap();
        let mut destination = Destination::default();
        let before = destination.clone();
        let error =
            Ledger::publish_with(pristine.clone(), 845_760, pristine.class, &mut destination)
                .unwrap_err();
        assert_eq!(error, "X lease owner/class");
        let error = Ledger::publish_with(
            pristine.clone(),
            845_759,
            crate::daa_history_roster::OwnerClass::Initial,
            &mut destination,
        )
        .unwrap_err();
        assert_eq!(error, "X lease owner/class");
        assert_eq!(destination, before);
    }

    #[test]
    fn rejects_preoccupied_destination_row_and_x_without_partial_publication() {
        let candidate = Candidate::stage(845_759).unwrap();
        let row = candidate.rows[0].term.row;
        let mut row_destination = Destination::default();
        row_destination.rows.insert(row, RowWriter::Header);
        let before_row = row_destination.clone();
        let error = Ledger::publish(candidate.clone(), &mut row_destination).unwrap_err();
        assert_eq!(error, format!("destination ROW already occupied at {row}"));
        assert_eq!(row_destination, before_row);

        let base = 845_759usize * (1 << 20);
        let mut x_destination = Destination::default();
        x_destination.x.push(XDomain {
            writer: XWriter::WorkTree,
            start: base,
            end: base + 1,
        });
        let before_x = x_destination.clone();
        let error = Ledger::publish(candidate, &mut x_destination).unwrap_err();
        assert_eq!(error, "destination X domain overlap");
        assert_eq!(x_destination, before_x);
    }

    #[test]
    fn rejects_premature_and_missing_score_independently() {
        let pristine = Candidate::stage(844_672).unwrap();
        let mut premature = pristine.clone();
        premature
            .reservations
            .push((SupportWriter::Relocated(Family::Score(0)), 677_501..679_549));
        rejected(premature, "canonical Map/Score/Slack reservation mismatch");

        let active = Candidate::stage(845_759).unwrap();
        let mut missing_reservation = active.clone();
        missing_reservation
            .reservations
            .retain(|(writer, _)| *writer != SupportWriter::Relocated(Family::Score(0)));
        rejected(
            missing_reservation,
            "canonical Map/Score/Slack reservation mismatch",
        );

        let mut missing_terms = active.clone();
        missing_terms
            .support
            .retain(|term| term.writer != SupportWriter::Relocated(Family::Score(0)));
        rejected(missing_terms, "missing active c128 family Score(0)");
    }

    #[test]
    fn rejects_shifted_extended_and_non_header_transfers() {
        let pristine = Candidate::stage(845_759).unwrap();
        let mut shifted = pristine.clone();
        shifted.reservations[0].1.start += 1;
        rejected(shifted, "canonical Map/Score/Slack reservation mismatch");

        let mut extended = pristine.clone();
        extended.reservations[0].1.end += 1;
        rejected(extended, "canonical Map/Score/Slack reservation mismatch");

        let mut non_header = pristine.clone();
        non_header.reservations[0].1 = 819_200..819_201;
        rejected(non_header, "X transfer requires Header lease at 819200");
    }

    #[test]
    fn rejects_duplicate_reservations_and_v_w_writer_claims() {
        let pristine = Candidate::stage(845_759).unwrap();
        let mut duplicate = pristine.clone();
        duplicate
            .reservations
            .push(duplicate.reservations[0].clone());
        rejected(duplicate, "duplicate X reservation");

        for family in [Family::V(0), Family::W(0)] {
            let mut vw = pristine.clone();
            vw.reservations
                .push((SupportWriter::Relocated(family), 600_000..600_001));
            rejected(vw, "V/W cannot own X");
        }
    }

    #[test]
    fn rejects_extra_c121_writer_and_incomplete_daa_declarations() {
        let mut extra_writer = Candidate::stage(845_759).unwrap();
        let occupied = extra_writer
            .rows
            .iter()
            .map(|claim| claim.term.row)
            .chain(extra_writer.support.iter().map(|tagged| tagged.term.row))
            .collect::<std::collections::BTreeSet<_>>();
        let owner_base = 845_759usize * (1 << 19);
        let free_row = (owner_base..owner_base + (1 << 19))
            .find(|row| !occupied.contains(row))
            .expect("free H21-local ROW");
        let mut term = extra_writer.rows[0].term.clone();
        term.row = free_row;
        extra_writer.rows.push(super::RowClaim {
            writer: RowWriter::Daa(4),
            term,
        });
        rejected(extra_writer, "c121 source ROW tuple mismatch");

        let pristine = Candidate::stage(844_672).unwrap();
        let mut omitted = pristine.clone();
        omitted
            .declared
            .retain(|domain| domain.producer != Producer::Daa);
        rejected(omitted, "c121 DAA declaration census");
        let mut duplicate = pristine.clone();
        let domain = *duplicate
            .declared
            .iter()
            .find(|domain| domain.producer == Producer::Daa)
            .expect("active DAA declaration");
        duplicate.declared.push(domain);
        rejected(duplicate, "c121 DAA declaration census");

        let mut inverted = pristine.clone();
        let domain = inverted
            .declared
            .iter_mut()
            .find(|domain| domain.producer == Producer::Daa)
            .expect("active DAA declaration");
        domain.end = domain.start - 1;
        rejected(inverted, "c121 DAA X declaration extent");
    }

    #[test]
    fn restored_header_cap_anchor_fails_on_the_actual_row_collision() {
        let mut candidate = Candidate::stage(845_759).unwrap();
        let owner = 845_759usize;
        let row = owner * (1 << 19) + 357_978;
        assert!(
            candidate.rows.iter().any(|claim| {
                claim.term.row == row
                    && matches!(
                        claim.writer,
                        RowWriter::Scheduled(ScheduledWriter::Cap { context: 0, .. })
                    )
            }),
            "the scheduled Cap source must occupy the retired HEADER anchor row"
        );
        let anchor = crate::sparse::Term {
            row,
            gate: crate::gkr::Gate {
                left: owner * (1 << 20) + 1_000_770,
                right: owner * (1 << 20),
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        };
        candidate.rows.push(super::RowClaim {
            writer: RowWriter::Header,
            term: anchor,
        });
        let mut destination = Destination::default();
        let before = destination.clone();
        let error = Ledger::publish(candidate, &mut destination).unwrap_err();
        assert!(
            error.starts_with("cross-writer ROW collision at "),
            "{error}"
        );
        assert_eq!(destination, before);
    }

    #[test]
    fn scheduled_omission_duplicate_writer_and_gate_mutants_fail_before_dedup() {
        let pristine = Candidate::stage(845_759).unwrap();
        let mut omitted = pristine.clone();
        omitted
            .support
            .retain(|term| !matches!(term.writer, SupportWriter::Scheduled(_)));
        rejected(omitted, "scheduled multiset mismatch");

        let mut duplicate = pristine.clone();
        let term = duplicate
            .support
            .iter()
            .find(|term| matches!(term.writer, SupportWriter::Scheduled(_)))
            .expect("scheduled terms")
            .clone();
        duplicate.support.push(term);
        rejected(duplicate, "scheduled multiset mismatch");

        let mut wrong_writer = pristine.clone();
        let tagged = wrong_writer
            .support
            .iter_mut()
            .find(|term| matches!(term.writer, SupportWriter::Scheduled(_)))
            .expect("scheduled terms");
        tagged.writer = SupportWriter::Scheduled(ScheduledWriter::Max { context: 0, end: 1 });
        rejected(wrong_writer, "scheduled multiset mismatch");

        let mut changed_gate = pristine.clone();
        let tagged = changed_gate
            .support
            .iter_mut()
            .find(|term| matches!(term.writer, SupportWriter::Scheduled(_)))
            .expect("scheduled terms");
        tagged.term.gate.c0 += Fr::one();
        rejected(changed_gate, "scheduled multiset mismatch");

        let mut omitted_c121 = pristine.clone();
        omitted_c121
            .rows
            .retain(|claim| !matches!(claim.writer, RowWriter::Scheduled(_)));
        rejected(omitted_c121, "scheduled multiset mismatch");

        let mut shared_corruption = pristine.clone();
        let scheduled = shared_corruption
            .support
            .iter()
            .find(|term| matches!(term.writer, SupportWriter::Scheduled(_)))
            .expect("scheduled terms")
            .clone();
        let SupportWriter::Scheduled(scheduled_writer) = scheduled.writer else {
            unreachable!()
        };
        let claim = shared_corruption
            .rows
            .iter_mut()
            .find(|claim| {
                claim.writer == RowWriter::Scheduled(scheduled_writer)
                    && claim.term.row == scheduled.term.row
                    && claim.term.gate == scheduled.term.gate
            })
            .expect("matching c121 scheduled tuple");
        claim.term.gate.c0 += Fr::one();
        let tagged = shared_corruption
            .support
            .iter_mut()
            .find(|term| {
                term.writer == SupportWriter::Scheduled(scheduled_writer)
                    && term.term.row == scheduled.term.row
                    && term.term.gate == scheduled.term.gate
            })
            .expect("matching scheduled tuple");
        tagged.term.gate.c0 += Fr::one();
        rejected(shared_corruption, "c121 source scheduled multiset mismatch");
    }

    #[test]
    fn each_active_family_omission_has_its_own_failure() {
        let baseline = Candidate::stage(845_759).unwrap();
        let active_c121 = baseline
            .row_source
            .iter()
            .map(|claim| claim.writer)
            .collect::<std::collections::BTreeSet<_>>();
        for writer in active_c121 {
            let mut candidate = baseline.clone();
            candidate.rows.retain(|claim| claim.writer != writer);
            let expected = match writer {
                RowWriter::Scheduled(_) => "scheduled multiset mismatch".to_string(),
                _ => format!("missing active c121 family {writer:?}"),
            };
            rejected(candidate, &expected);
        }
        for family in [
            Family::Map(0),
            Family::Map(1),
            Family::Score(0),
            Family::Score(1),
            Family::V(0),
            Family::V(1),
            Family::W(0),
            Family::W(1),
            Family::Slack(0),
            Family::Slack(1),
        ] {
            let mut candidate = baseline.clone();
            candidate
                .support
                .retain(|term| term.writer != SupportWriter::Relocated(family));
            rejected(candidate, &format!("missing active c128 family {family:?}"));
        }
        drop(baseline);
    }

    fn score_cap_fixture() -> (
        Candidate,
        crate::score_prefix_r_anchor::Plan,
        crate::score_prefix_r_anchor::Staged,
        crate::score_prefix_r_anchor::ScoreCapProjection,
    ) {
        let (session, caller) = crate::c146_phase1_session::Session::fixture().unwrap();
        let (plan, staged) = session.stage_for_local_ledger_join(&caller).unwrap();
        let projection = crate::score_prefix_r_anchor::project_local_score_cap(&plan, &staged).unwrap();
        (Candidate::stage(845_759).unwrap(), plan, staged, projection)
    }

    fn seeded_destination() -> Destination {
        let mut destination = Destination::default();
        destination.rows.insert(17, RowWriter::Header);
        destination.x.push(XDomain { writer: XWriter::WorkTree, start: 18, end: 19 });
        destination
    }

    fn rejects_score_cap_join(candidate: Candidate, projection: &crate::score_prefix_r_anchor::ScoreCapProjection) {
        let mut destination = seeded_destination();
        let before = destination.clone();
        assert!(Ledger::publish_score_cap_join(candidate, projection, &mut destination).is_err());
        assert_eq!(destination, before);
    }

    fn is_prior_owner_w_k0(claim: &crate::score_prefix_r_anchor::ScoreCapRow, row: usize) -> bool {
        claim.relation == crate::score_prefix_r_anchor::ScoreCapRelation::AliasW(0)
            && claim.term.row == row
            && claim.term.gate == crate::gkr::Gate {
                left: 845_758 * WIDTH + 987_450,
                right: 0,
                c0: Fr::zero(),
                c1: -Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            }
    }

    #[test]
    fn c146_modern_score_cap_projection_joins_current_carry_ledger_atomically() {
        use crate::score_prefix_r_anchor::ScoreCapRelation as JoinRelation;

        let (candidate, plan, staged, projection) = score_cap_fixture();
        assert_eq!(projection.owner, 845_759);
        let mut destination = seeded_destination();
        let ledger = Ledger::publish_score_cap_join(candidate.clone(), &projection, &mut destination).unwrap();
        assert_eq!(ledger.class, crate::daa_history_roster::OwnerClass::Carry);
        for context in 0..2 {
            assert!(ledger.rows.values().any(|writer| *writer == RowWriter::Relocated(Family::Score(context))));
            assert!(ledger.rows.values().any(|writer| *writer == RowWriter::Scheduled(ScheduledWriter::Cap { context, origin: 845_760 })));
            assert!(ledger.x.iter().any(|domain| domain.writer == XWriter::Score(context)));
            assert!(ledger.x.iter().any(|domain| domain.writer == XWriter::Cap(context)));
            assert!(projection.rows.iter().any(|row| row.relation == JoinRelation::ModernScore(context)));
            assert!(projection.rows.iter().any(|row| row.relation == JoinRelation::Cap(ScheduledWriter::Cap { context, origin: 845_760 })));
        }
        assert!(destination.rows.len() > ledger.rows.len());

        // A repeated claim is rejected even when it names the same writer and range.
        let mut duplicate_x = projection.clone();
        duplicate_x.x.push(duplicate_x.x[0].clone());
        rejects_score_cap_join(candidate.clone(), &duplicate_x);

        // The Cap and Score relations have separate semantic ROW authority.
        let mut row_collision = projection.clone();
        let score_row = row_collision.rows.iter().find(|row|
            row.relation == JoinRelation::ModernScore(0)).unwrap().term.row;
        let cap = row_collision.rows.iter_mut().find(|row|
            matches!(row.relation, JoinRelation::Cap(_))).unwrap();
        cap.term.row = score_row;
        rejects_score_cap_join(candidate.clone(), &row_collision);

        // Context is part of the Cap writer identity, even if the occupied range is unchanged.
        let mut cap_context_swap = projection.clone();
        let cap_x = cap_context_swap.x.iter_mut().find(|claim|
            matches!(claim.relation, JoinRelation::Cap(ScheduledWriter::Cap { context: 0, .. }))).unwrap();
        cap_x.relation = JoinRelation::Cap(ScheduledWriter::Cap { context: 1, origin: 845_760 });
        rejects_score_cap_join(candidate.clone(), &cap_context_swap);

        let mut alias_substitution = projection.clone();
        let alias = alias_substitution.rows.iter_mut().find(|row|
            row.relation == JoinRelation::AliasV(0)).unwrap();
        alias.term.gate.right = 845_759 * WIDTH + 1_002_818 + 740;
        rejects_score_cap_join(candidate.clone(), &alias_substitution);

        let mut rogue = projection.clone();
        let mut extra = rogue.rows.iter().find(|row|
            row.relation == JoinRelation::ModernScore(0)).unwrap().clone();
        extra.relation = JoinRelation::ModernScore(2);
        extra.term.row = 845_759 * (1 << 19) + 510_000;
        rogue.rows.push(extra);
        rejects_score_cap_join(candidate.clone(), &rogue);

        let prior_owner_w_row = 845_759 * super::ROWS + 491_694;
        let mut wrong_w_wire = projection.clone();
        let term = wrong_w_wire.rows.iter_mut().find(|row|
            is_prior_owner_w_k0(row, prior_owner_w_row)).unwrap();
        term.term.gate.left += 1;
        rejects_score_cap_join(candidate.clone(), &wrong_w_wire);

        let mut wrong_w_coefficient = projection.clone();
        let term = wrong_w_coefficient.rows.iter_mut().find(|row|
            is_prior_owner_w_k0(row, prior_owner_w_row)).unwrap();
        term.term.gate.c1 = ark_bn254::Fr::zero();
        rejects_score_cap_join(candidate.clone(), &wrong_w_coefficient);

        let mut wrong_w_sign = projection.clone();
        let term = wrong_w_sign.rows.iter_mut().find(|row|
            is_prior_owner_w_k0(row, prior_owner_w_row)).unwrap();
        term.term.gate.c1 = ark_bn254::Fr::one();
        rejects_score_cap_join(candidate.clone(), &wrong_w_sign);

        let mut wrong_w_row = projection.clone();
        let term = wrong_w_row.rows.iter_mut().find(|row|
            is_prior_owner_w_k0(row, prior_owner_w_row)).unwrap();
        term.term.row += 1;
        rejects_score_cap_join(candidate.clone(), &wrong_w_row);

        let mut wrong_w_context = projection.clone();
        let term = wrong_w_context.rows.iter_mut().find(|row|
            is_prior_owner_w_k0(row, prior_owner_w_row)).unwrap();
        term.relation = JoinRelation::AliasW(1);
        rejects_score_cap_join(candidate.clone(), &wrong_w_context);

        let mut missing_w = projection.clone();
        missing_w.rows.retain(|row| !is_prior_owner_w_k0(row, prior_owner_w_row));
        rejects_score_cap_join(candidate.clone(), &missing_w);

        let mut duplicate_w = projection.clone();
        let prior_owner_w = duplicate_w.rows.iter().find(|row|
            is_prior_owner_w_k0(row, prior_owner_w_row)).unwrap().clone();
        duplicate_w.rows.push(prior_owner_w);
        rejects_score_cap_join(candidate.clone(), &duplicate_w);

        let mut extra_w = projection.clone();
        let mut extra = extra_w.rows.iter().find(|row|
            row.relation == JoinRelation::AliasW(0)).unwrap().clone();
        extra.term.row = 845_759 * super::ROWS + 510_000;
        extra_w.rows.push(extra);
        rejects_score_cap_join(candidate.clone(), &extra_w);

        // Either active relation omitted from the projected source is fatal.
        let mut score_omitted = projection.clone();
        score_omitted.rows.retain(|row| row.relation != JoinRelation::ModernScore(0));
        rejects_score_cap_join(candidate.clone(), &score_omitted);
        let mut cap_omitted = projection.clone();
        cap_omitted.rows.retain(|row| row.relation != JoinRelation::Cap(ScheduledWriter::Cap { context: 0, origin: 845_760 }));
        rejects_score_cap_join(candidate, &cap_omitted);

        // The producer validates the actual Cap-to-V alias before it can export a join.
        let mut alias_mutant = staged;
        crate::score_prefix_r_anchor::flip_score_alias_for_test(&mut alias_mutant, 0, true, 33);
        let mut destination = seeded_destination();
        let before = destination.clone();
        assert!(crate::score_prefix_r_anchor::project_local_score_cap(&plan, &alias_mutant).is_err());
        assert_eq!(destination, before);
    }
}

//! One Eligible08 owner's source-to-sink join. External reads remain pending;
//! this module has no packed witness, completion, transcript or proof API.
use super::*;
use super::super::h21_eligible_slack::H21EligibleSlackStage;
use ark_ff::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use crate::header_daa_row_placement::{ActiveOperand, Batch as Row19Batch, OperandSide,
    Relation as Row19Relation, RowPlan};
use crate::packed_owner_assembly::{HeaderSourceBinding, NativeHeaderSourceLease};
use crate::work_tree_history_plan::WorkTreeHistoryPlan;
use blake2::{Blake2b, Digest, digest::consts::U32};

const OWNER: usize = 845_759;
const CELL_COUNT: usize = 16_384;
const CAP_MAX_OWNER: usize = 844_670;
const CAP_MAX_BASE: [usize; 2] = [999_424, 1_000_097];
const CAP_MAX_BITS: usize = 224;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Binding {
    root: [u8; 32], total: [u8; 28], profile: [u8; 32], cut: Vec<u8>,
    maps: [crate::legacy_envelope_map::Binding; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Writer { Map(usize), Score(ScoreReplayAuthor), Slack(usize), Header, Cap(usize), WorkLocal, WorkUpper, PreviousR(usize) }

/// The expected author is distinct from the relation that consumes its cell.
/// Scalar expectations do not install any of these external physical authors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RequiredAuthor {
    WorkDifficulty { owner: usize, height: usize },
    HeaderTimestamp { owner: usize, height: usize },
    PreviousR { context: usize, owner: usize },
    WorkUpper { owner: usize, height: usize },
    Cap { context: usize, origin: usize, max_owner: usize, cap_owner: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PendingRead {
    consumer: Writer, wire: usize, author: RequiredAuthor, value: bool,
}
impl PendingRead {
    pub(crate) fn wire(&self) -> usize { self.wire }
    pub(crate) fn required_author(&self) -> RequiredAuthor { self.author }
    pub(crate) fn expected_bit(&self) -> bool { self.value }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Cell { wire: usize, writer: Writer, value: bool }
#[derive(Clone, Debug, PartialEq, Eq)]
struct Row { writer: Writer, term: Term }

/// A relation occurrence and a sink occurrence are different consumers even
/// when they read the same physical wire. The ordinal includes constant terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SinkOperand { occurrence: usize, writer: Writer, row: usize,
    side: OperandSide, wire: usize }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConsumerOccurrence { Row19(ActiveOperand), Sink(SinkOperand) }

/// `SinkAdmitted` is a checked local-stage claim, not native packed authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PhysicalAuthor { NativeHeader {owner: usize}, PublishedCap {context: usize,
    origin: usize, owner: usize}, SinkAdmitted(Writer) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PhysicalClaim { owner: usize, wire: usize, author: PhysicalAuthor, bit: bool }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpenSource { ForeignOwner, UnqualifiedLocal }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OccurrenceSource {
    Resolved(PhysicalClaim),
    Pending {author: RequiredAuthor, expected_bit: bool},
    Open(OpenSource),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OccurrenceRecord { consumer: ConsumerOccurrence, wire: usize,
    source: OccurrenceSource }
#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnerOccurrenceLedger { records: Vec<OccurrenceRecord>,
    physical: BTreeMap<usize, PhysicalClaim> }

fn is_local_daa_bank_wire(wire:usize)->bool {
    wire/WIDTH==OWNER && crate::daa_history_roster::BANKS.iter()
        .any(|&(start,end)|(start..end).contains(&(wire%WIDTH)))
}

impl OwnerOccurrenceLedger {
    fn resolved_count(&self)->usize {self.records.iter().filter(|r|
        matches!(r.source,OccurrenceSource::Resolved(_))).count()}
    fn pending_count(&self)->usize {self.records.iter().filter(|r|
        matches!(r.source,OccurrenceSource::Pending{..})).count()}
    fn open_count(&self)->usize {self.records.iter().filter(|r|
        matches!(r.source,OccurrenceSource::Open(_))).count()}
    fn check_exact(&self,row19:&Row19Batch,sink:&Eligible08OwnerSink)->Result<(),String> {
        let expected=row19.active_operands().map(|op|(ConsumerOccurrence::Row19(op),op.wire))
            .chain(sink_active_operands(&sink.state).into_iter().map(|op|
                (ConsumerOccurrence::Sink(op),op.wire))).collect::<Vec<_>>();
        if self.records.len()!=expected.len() || self.records.iter().zip(expected).any(|(read,key)|
            (read.consumer,read.wire)!=key) {
            return Err("owner occurrence exact ordered consumer census".into());
        }
        for read in &self.records {
            if let OccurrenceSource::Resolved(claim)=read.source {
                if claim.wire!=read.wire || self.physical.get(&read.wire)!=Some(&claim) {
                    return Err("owner occurrence physical source projection".into());
                }
            }
        }
        Ok(())
    }
}

fn insert_physical(physical:&mut BTreeMap<usize,PhysicalClaim>,claim:PhysicalClaim)
    ->Result<(),String> {
    if claim.wire >= (1usize<<41) || claim.owner!=claim.wire/WIDTH
        || physical.insert(claim.wire,claim).is_some() {
        return Err("owner occurrence duplicate/outside physical source".into());
    }
    Ok(())
}

fn sink_active_operands(state:&State)->Vec<SinkOperand> {
    let mut out=Vec::new();
    for (occurrence,row) in state.terms.iter().enumerate() {
        let gate=&row.term.gate;
        if !gate.c1.is_zero() || !gate.c3.is_zero() {
            out.push(SinkOperand{occurrence,writer:row.writer,row:row.term.row,
                side:OperandSide::Left,wire:gate.left});
        }
        if !gate.c2.is_zero() || !gate.c3.is_zero() {
            out.push(SinkOperand{occurrence,writer:row.writer,row:row.term.row,
                side:OperandSide::Right,wire:gate.right});
        }
    }
    out
}

fn sink_read_slot(writer:Writer)->Result<usize,String> {
    match writer {
        Writer::Map(context) if context<2=>Ok(context),
        Writer::Score(author) if author.context<2=>Ok(2+author.context),
        _=>Err("owner occurrence invalid pending consumer".into()),
    }
}

fn satisfies_required(required:RequiredAuthor,claim:PhysicalClaim)->bool {
    match (required,claim.author) {
        (RequiredAuthor::WorkDifficulty{owner,height},PhysicalAuthor::SinkAdmitted(Writer::WorkLocal))=>
            owner==OWNER && height==OWNER+2 && claim.owner==owner,
        (RequiredAuthor::HeaderTimestamp{owner,height},PhysicalAuthor::NativeHeader{owner:source})=>
            source==owner && height==owner+1 && claim.owner==owner,
        (RequiredAuthor::PreviousR{context,owner},PhysicalAuthor::SinkAdmitted(Writer::PreviousR(c)))=>
            c==context && claim.owner==owner,
        (RequiredAuthor::WorkUpper{owner,height},PhysicalAuthor::SinkAdmitted(Writer::WorkUpper))=>
            owner==OWNER-1 && height==OWNER+1 && claim.owner==owner,
        (RequiredAuthor::Cap{context,origin,max_owner,cap_owner},
            PhysicalAuthor::PublishedCap{context:c,origin:o,owner})=>
            c==context && o==origin && max_owner==CAP_MAX_OWNER
                && owner==cap_owner && claim.owner==owner,
        _=>false,
    }
}

/// Only the native context can mint a production lease. The immutable stage
/// remains beside its projection to bind every bit and source term exactly.
#[derive(Clone)]
pub(crate) struct Eligible08OwnerLease {
    binding: Binding, source: H21EligibleSlackStage, map_reads: Vec<PendingRead>,
    cells: Vec<Cell>, rows: Vec<Row>, reads: Vec<PendingRead>,
}

/// A partial single-owner sink. Retained HEADER ROW ownership does not
/// authenticate its X inputs; absent HEADER/DAA sources never become zeros.
#[derive(Clone, Default, PartialEq, Eq)]
struct State {
    cells: BTreeMap<usize, (Writer, bool)>, rows: BTreeMap<usize, Writer>,
    terms: Vec<Row>, reads: Vec<PendingRead>, read_obligations: Vec<PendingRead>, published: bool,
}
/// Owned custody of the checked local source, in its own tagged namespace.
/// These terms are never installed as ROW19 terms or counted as ROW19 rows.
#[derive(Clone, PartialEq, Eq)]
struct WorkLocalPublication {
    parent: crate::h21_scheduled_max_cap::NativeParent, owner: usize, height: usize,
    terms: Vec<crate::h21_work_local_source::TaggedTerm>, operands: Vec<(usize, Fr)>,
    d: Vec<(usize, Fr)>,
}
/// Exact owner-local MAX source retained after resolving the Cap publication's
/// foreign reads. This remains separate from the Cap source custody.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CapMaxResolution {
    binding: Binding,
    owner: usize,
    cells: Vec<ResolvedCapMaxCell>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ResolvedCapMaxCell {
    wire: usize,
    author: crate::h21_scheduled_max_cap::MaxReplayAuthor,
    value: Fr,
}
/// Opaque foreign-read custody minted only after the sink has joined the
/// published Cap imports to a closed native MAX stream.
pub(crate) struct Eligible08ForeignMaxReadLease {
    destination: crate::packed_owner_assembly::HeaderSourceBinding,
    source_owner: usize,
    cells: Vec<Eligible08ForeignMaxCell>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Eligible08ForeignMaxCell {
    wire: usize,
    context: usize,
    end: usize,
    bit: usize,
    author: crate::h21_scheduled_max_cap::MaxReplayAuthor,
    value: bool,
}
impl Eligible08ForeignMaxCell {
    pub(crate) fn wire(&self) -> usize { self.wire }
    pub(crate) fn context(&self) -> usize { self.context }
    pub(crate) fn end(&self) -> usize { self.end }
    pub(crate) fn bit(&self) -> usize { self.bit }
    pub(crate) fn author(&self) -> crate::h21_scheduled_max_cap::MaxReplayAuthor { self.author }
    pub(crate) fn value(&self) -> bool { self.value }
}
impl Eligible08ForeignMaxReadLease {
    pub(crate) fn require_destination(
        &self, binding: &crate::packed_owner_assembly::HeaderSourceBinding, owner: usize,
    ) -> Result<(), String> {
        if owner != OWNER || self.destination != *binding || self.source_owner != CAP_MAX_OWNER {
            return Err("Eligible08 foreign MAX destination/source binding".into());
        }
        validate_foreign_max_cells(self.source_owner, &self.cells)
    }
    pub(crate) fn cells(&self) -> impl ExactSizeIterator<Item = &Eligible08ForeignMaxCell> {
        self.cells.iter()
    }
    pub(crate) fn cell(&self, context: usize, bit: usize)
        -> Option<crate::header_daa_row_placement::ForeignMaxCellView> {
        let index=context.checked_mul(CAP_MAX_BITS)?.checked_add(bit)?;
        self.cells.get(index).map(|cell|crate::header_daa_row_placement::ForeignMaxCellView {
            wire:cell.wire,context:cell.context,end:cell.end,bit:cell.bit,
            author:cell.author,value:cell.value,
        })
    }
    #[cfg(test)]
    pub(crate) fn mutate_source_owner_for_test(&mut self, owner: usize) { self.source_owner = owner; }
    #[cfg(test)]
    pub(crate) fn mutate_first_cell_wire_for_test(&mut self) {
        if let Some(cell) = self.cells.first_mut() { cell.wire += 1; }
    }
    #[cfg(test)]
    pub(crate) fn swap_first_two_cells_for_test(&mut self) {
        if self.cells.len() >= 2 { self.cells.swap(0, 1); }
    }
    #[cfg(test)]
    pub(crate) fn mutate_first_cell_author_for_test(&mut self) {
        if let Some(cell) = self.cells.first_mut() {
            cell.author = crate::h21_scheduled_max_cap::MaxReplayAuthor::NativeWorkD { height: CAP_MAX_OWNER + 1 };
        }
    }
    #[cfg(test)]
    pub(crate) fn truncate_cells_for_test(&mut self, len: usize) { self.cells.truncate(len); }
    #[cfg(test)]
    pub(crate) fn synthetic_for_test(
        destination: crate::packed_owner_assembly::HeaderSourceBinding,
        source_owner: usize,
        cells: Vec<Eligible08ForeignMaxCell>,
    ) -> Self { Self { destination, source_owner, cells } }
}
#[cfg(test)]
impl Eligible08ForeignMaxCell {
    pub(crate) fn synthetic_for_test(
        wire: usize, context: usize, end: usize, bit: usize,
        author: crate::h21_scheduled_max_cap::MaxReplayAuthor, value: bool,
    ) -> Self { Self { wire, context, end, bit, author, value } }
}

fn validate_foreign_max_cells(source_owner: usize, cells: &[Eligible08ForeignMaxCell])
    -> Result<(), String> {
    if source_owner != CAP_MAX_OWNER || cells.len() != 2 * CAP_MAX_BITS {
        return Err("Eligible08 foreign MAX exact source census".into());
    }
    for (index, cell) in cells.iter().enumerate() {
        let context = index / CAP_MAX_BITS;
        let bit = index % CAP_MAX_BITS;
        let author = crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
            crate::h21_scheduled_max_cap::Writer::Max { context, end: CAP_MAX_OWNER + 2 });
        if context >= 2 || cell.context != context || cell.bit != bit
            || cell.end != CAP_MAX_OWNER + 2
            || cell.wire != CAP_MAX_OWNER * WIDTH + CAP_MAX_BASE[context] + bit
            || cell.author != author || !matches!(author,
                crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
                    crate::h21_scheduled_max_cap::Writer::Max { context: c, end })
                    if c == context && end == cell.end) {
            return Err("Eligible08 foreign MAX source order/author/domain/value".into());
        }
    }
    Ok(())
}
pub(crate) struct Eligible08OwnerSink { binding: Binding, state: State,
    custody: std::sync::Arc<()>,
    source: Option<H21EligibleSlackStage>,
    cap_source: Option<crate::h21_scheduled_family_ledger::FirstModernCapPublication>,
    cap_max_resolution: Option<CapMaxResolution>,
    work_source: Option<WorkLocalPublication>,
    upper_source: Option<crate::packed_owner_assembly::WorkUpperPublication>,
    previous_r_source: Option<PremodernRPublication> }

/// Borrowed, source-retaining transport into the native owner's pre-pack
/// writer. It cannot be minted from a detached list of Boolean values.
pub(crate) struct Eligible08PackedOverlay<'s> {
    binding: HeaderSourceBinding,
    sink: &'s Eligible08OwnerSink,
}

/// A checked borrow of the completed sink's retained Map stage. The borrow
/// prevents source replacement while its terms and cells are being consumed.
/// The private custody token joins this exact sink to the physical census;
/// equal parent bindings and equal Boolean values are insufficient.
pub(crate) struct Eligible08MapSourceView<'s> {
    binding: HeaderSourceBinding,
    sink: &'s Eligible08OwnerSink,
    source: &'s H21EligibleSlackStage,
}

impl Eligible08MapSourceView<'_> {
    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.binding }

    pub(crate) fn require_typed_source(&self, lease: &Bank53TypedSourceLease)
        -> Result<(), String> {
        if lease.binding != self.binding
            || !self.sink.source.as_ref().is_some_and(|source|
                std::ptr::eq(source, self.source))
            || !lease.custody.as_ref().is_some_and(|custody|
                std::sync::Arc::ptr_eq(custody, &self.sink.custody)) {
            return Err("C453 Map view retained sink/source custody".into());
        }
        Ok(())
    }

    pub(crate) fn map_binding(&self, context: usize)
        -> Result<&crate::legacy_envelope_map::Binding, String> {
        self.source.map_stage.map_bindings.get(context)
            .ok_or_else(|| "C453 Map view context outside pair".into())
    }

    pub(crate) fn checked_terms(&self, expected: &HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass, context: usize,
    ) -> Result<&[Term], String> {
        if expected != &self.binding || owner != OWNER
            || class != crate::daa_history_roster::OwnerClass::Carry {
            return Err("C453 Map view term parent/owner/class".into());
        }
        self.source.map_stage.map_terms.get(context).map(Vec::as_slice)
            .ok_or_else(|| "C453 Map view context outside pair".into())
    }

    pub(crate) fn map_cells(&self) -> impl Iterator<Item = (usize, usize, bool)> + '_ {
        self.source.map_stage.claims.iter().filter_map(|(&local, &(author, value))|
            match author {
                H21StageAuthor::Map(context) => Some((context, OWNER * WIDTH + local, value)),
                _ => None,
            })
    }

    /// These are the same admitted obligations replayed against the retained
    /// Work-D publication: 224 ordered local bits for each Map context.
    pub(crate) fn local_imports(&self) -> impl Iterator<Item = (usize, usize, bool)> + '_ {
        self.sink.state.read_obligations.iter().filter_map(|read| match read.consumer {
            Writer::Map(context) => Some((context, read.wire, read.value)),
            _ => None,
        })
    }

    #[cfg(test)]
    pub(crate) fn typed_source_for_test(&self) -> Result<Bank53TypedSourceLease, String> {
        let d = c373_overlay_source_tests::expected_zero_d();
        self.sink.checked_overlay_map_source(&d, &self.binding)
    }
}

/// The provenance class for one ordered input to a modern Score relation.
/// These are source records, not a count of active ROW operand occurrences.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Eligible08ScoreImportKind {
    PreviousR { owner: usize },
    Cap { owner: usize, origin: usize, max_owner: usize },
    WorkUpper { owner: usize, height: usize },
}

/// Slack author surfaced without exposing the parent module's internal stage
/// author enum. Invalid internal authors remain explicit for fail-closed readers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Eligible08SlackCellAuthor {
    Slack(usize),
    Unrecognized,
}

/// One member of the retained modern Score import census.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Eligible08ScoreImport {
    context: usize,
    kind: Eligible08ScoreImportKind,
    wire: usize,
    value: Fr,
}
impl Eligible08ScoreImport {
    pub(crate) fn context(&self) -> usize { self.context }
    pub(crate) fn kind(&self) -> Eligible08ScoreImportKind { self.kind }
    pub(crate) fn wire(&self) -> usize { self.wire }
    pub(crate) fn value(&self) -> Fr { self.value }
}

/// Borrowed transport from one completed owner845759 sink into a selected
/// ROW consumer. Its foreign PreviousR and WorkUpper values are qualified by
/// their retained publications; it makes no owner845758 physical X/ROW claim.
pub(crate) struct Eligible08CompleteRowSourceView<'s> {
    binding: HeaderSourceBinding,
    sink: &'s Eligible08OwnerSink,
    source: &'s H21EligibleSlackStage,
    qualified_imports: Vec<Eligible08ScoreImport>,
}

impl<'s> Eligible08CompleteRowSourceView<'s> {
    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.binding }

    /// Recreate the Map view over these exact retained pointers and custody.
    pub(crate) fn map_view(&self) -> Eligible08MapSourceView<'s> {
        Eligible08MapSourceView {
            binding: self.binding.clone(), sink: self.sink, source: self.source,
        }
    }

    pub(crate) fn require_typed_source(&self, lease: &Bank53TypedSourceLease)
        -> Result<(), String> {
        self.map_view().require_typed_source(lease)
    }

    pub(crate) fn score_terms(&self, context: usize) -> Result<&[Term], String> {
        self.source.score_rows().get(context).map(Vec::as_slice)
            .filter(|terms| !terms.is_empty())
            .ok_or_else(|| "C455 Score terms context/source absent".into())
    }

    pub(crate) fn slack_terms(&self, context: usize) -> Result<&[Term], String> {
        let terms = self.source.slack_rows().get(context)
            .map(Vec::as_slice)
            .ok_or_else(|| "C455 Slack terms context outside pair".to_string())?;
        if terms != crate::bank53_slack::slack_zero_terms(OWNER, context)?.as_slice() {
            return Err("C455 Slack canonical zero terms".into());
        }
        Ok(terms)
    }

    /// Physical X wire, typed Score author, and exact source value.
    pub(crate) fn score_cells(&self)
        -> impl ExactSizeIterator<Item = (usize, ScoreReplayAuthor, Fr)> + '_ {
        self.source.score_cells().iter().map(|(&local, &(author, value))|
            (OWNER * WIDTH + local, author, value))
    }

    /// Physical X wire, typed Slack author, and authored Boolean.
    pub(crate) fn slack_cells(&self)
        -> impl ExactSizeIterator<Item = (usize, Eligible08SlackCellAuthor, bool)> + '_ {
        self.source.slack_cells().iter().map(|(&local, &(author, value))| {
            let author = match author {
                H21StageAuthor::Slack(context) => Eligible08SlackCellAuthor::Slack(context),
                _ => Eligible08SlackCellAuthor::Unrecognized,
            };
            (OWNER * WIDTH + local, author, value)
        })
    }

    /// Recheck the retained foreign publications and the full ordered Score
    /// import census against the original sink obligations at mint. Consumers
    /// receive only the borrowed, already-qualified ordered records.
    pub(crate) fn score_imports(&self)
        -> Result<impl ExactSizeIterator<Item = Eligible08ScoreImport> + '_, String> {
        if self.qualified_imports.len() != 1_028 {
            return Err("C455 Score imports lack completed publication qualification".into());
        }
        Ok(self.qualified_imports.iter().copied())
    }

    fn checked_score_imports(&self) -> Result<Vec<Eligible08ScoreImport>, String> {
        let sink = self.sink;
        if !sink.state.published || sink.state.cells.len() != 21_378
            || !sink.state.reads.is_empty() || sink.state.read_obligations.len() != 1_476
            || !sink.source.as_ref().is_some_and(|source| std::ptr::eq(source, self.source))
            || !self.binding.matches_sink(sink.binding.root, sink.binding.total,
                sink.binding.profile, &sink.binding.cut, OWNER)
            || sink.cap_source.is_none() || sink.work_source.is_none()
            || sink.upper_source.is_none() || sink.previous_r_source.is_none() {
            return Err("C455 complete row source sink/source closure".into());
        }

        let previous = sink.previous_r_source.as_ref().unwrap().checked_projection(
            sink.binding.root, sink.binding.total, sink.binding.profile,
            &sink.binding.cut, &sink.binding.maps)?;
        let upper = sink.upper_source.as_ref().unwrap().checked_upper(
            sink.binding.root, sink.binding.total, sink.binding.profile,
            &sink.binding.cut, OWNER - 1)?;
        let cap = sink.cap_source.as_ref().unwrap().checked_material()?;
        qualify_score_import_records(
            self.source.score_imports(), &sink.state.read_obligations,
            &previous.cells[1], &cap.q, upper, &sink.state.cells,
        )?;

        let imports = self.source.score_imports().iter().enumerate().map(
            |(index, (wire, author, value))| {
                let context = index / 514;
                let kind = match *author {
                    ScoreRelationReadAuthor::PreviousR { owner, .. } =>
                        Eligible08ScoreImportKind::PreviousR { owner },
                    ScoreRelationReadAuthor::Cap { origin, max_owner, cap_owner, .. } =>
                        Eligible08ScoreImportKind::Cap { owner: cap_owner, origin,
                            max_owner },
                    ScoreRelationReadAuthor::WorkUpper { owner, height } =>
                        Eligible08ScoreImportKind::WorkUpper { owner, height },
                };
                Eligible08ScoreImport { context, kind, wire: *wire, value: *value }
            }).collect::<Vec<_>>();
        if imports.len() != 1_028 {
            return Err("C455 qualified Score import output census".into());
        }
        Ok(imports)
    }

    #[cfg(test)]
    pub(crate) fn typed_source_for_test(&self) -> Result<Bank53TypedSourceLease, String> {
        self.map_view().typed_source_for_test()
    }
}

/// Provenance retained for one physical Bank53 cell after the sink's exact
/// source and ROW replay has closed. This is local custody metadata only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Bank53TypedAuthor {
    Map(usize),
    Score(ScoreReplayAuthor),
    Slack(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Bank53TypedSourceEntry {
    physical_wire: usize,
    author: Bank53TypedAuthor,
    value: bool,
}
impl Bank53TypedSourceEntry {
    pub(crate) fn physical_wire(&self) -> usize { self.physical_wire }
    pub(crate) fn author(&self) -> Bank53TypedAuthor { self.author }
    pub(crate) fn value(&self) -> bool { self.value }
}

/// Parent-bound transport from the admitted Eligible08 sink into Bank53.
/// Fields are private so production code cannot synthesize this lease from
/// packed bytes or a detached list of Boolean cells.
#[derive(Debug)]
pub(crate) struct Bank53TypedSourceLease {
    binding: HeaderSourceBinding,
    entries: Vec<Bank53TypedSourceEntry>,
    custody: Option<std::sync::Arc<()>>,
}

impl Bank53TypedSourceLease {
    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.binding }
    pub(crate) fn entries(&self) -> &[Bank53TypedSourceEntry] { &self.entries }

    fn expected_authors() -> Result<Vec<Option<Bank53TypedAuthor>>, String> {
        use crate::packed_owner_assembly::{BANK53_BASE, BANK53_CONTEXT_BITS, BANK53_CONTEXTS};
        let descriptor = H21EligibleMapStage::descriptor();
        let score_author = |context| ScoreReplayAuthor {
            context, origin: OWNER + 1, previous_owner: OWNER - 1,
            max_owner: descriptor.modern_start() - descriptor.offset() - 2,
            cap_owner: OWNER,
        };
        let mut authors = vec![None; BANK53_CONTEXTS * BANK53_CONTEXT_BITS];
        let mut set = |local: usize, author: Bank53TypedAuthor| -> Result<(), String> {
            let index = local.checked_sub(BANK53_BASE)
                .filter(|index| *index < authors.len())
                .ok_or("C375 Bank53 typed domain outside geometry")?;
            if authors[index].replace(author).is_some() {
                return Err("C375 Bank53 typed domain duplicate author coordinate".into());
            }
            Ok(())
        };
        for context in 0..2 {
            for local in H21EligibleMapStage::map_live(context)? {
                set(local, Bank53TypedAuthor::Map(context))?;
            }
            for local in H21EligibleMapStage::score_live(context)? {
                set(local, Bank53TypedAuthor::Score(score_author(context)))?;
            }
            for local in H21EligibleMapStage::slack_live(context)? {
                set(local, Bank53TypedAuthor::Slack(context))?;
            }
        }
        drop(set);
        if authors.iter().any(Option::is_none) {
            return Err("C375 Bank53 typed domain incomplete".into());
        }
        Ok(authors)
    }

    pub(crate) fn validate(
        &self, expected: &HeaderSourceBinding, owner: usize,
    ) -> Result<(), String> {
        use crate::packed_owner_assembly::BANK53_BASE;
        if owner != OWNER || &self.binding != expected
            || !expected.matches_sink(self.binding.root, self.binding.total,
                self.binding.profile, &self.binding.cut, owner)
            || self.entries.len() != CELL_COUNT {
            return Err("C375 Bank53 typed lease parent/owner/census".into());
        }
        let authors = Self::expected_authors()?;
        let base = OWNER.checked_mul(WIDTH).ok_or("C375 Bank53 owner base overflow")?;
        for (index, entry) in self.entries.iter().enumerate() {
            let expected_wire = base.checked_add(BANK53_BASE + index)
                .ok_or("C375 Bank53 physical wire overflow")?;
            if entry.physical_wire != expected_wire
                || authors[index] != Some(entry.author) {
                return Err(format!("C375 Bank53 exact geometry/typed domain index{index}"));
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn synthetic_for_test(binding: HeaderSourceBinding, owner: usize)
        -> Result<Self, String> {
        use crate::packed_owner_assembly::BANK53_BASE;
        if owner != OWNER { return Err("C375 Bank53 test owner".into()); }
        let authors = Self::expected_authors()?;
        let base = owner.checked_mul(WIDTH).ok_or("C375 Bank53 test owner base")?;
        let entries = authors.into_iter().enumerate().map(|(index, author)| {
            Ok(Bank53TypedSourceEntry {
                physical_wire: base.checked_add(BANK53_BASE + index)
                    .ok_or("C375 Bank53 test physical wire")?,
                author: author.ok_or("C375 Bank53 test typed domain gap")?,
                value: false,
            })
        }).collect::<Result<Vec<_>, String>>()?;
        Ok(Self { binding, entries, custody: None })
    }

    #[cfg(test)]
    pub(crate) fn mutate_entry_for_test(
        &mut self, index: usize, wire: Option<usize>, author: Option<Bank53TypedAuthor>,
        value: Option<bool>,
    ) {
        let entry = &mut self.entries[index];
        if let Some(wire) = wire { entry.physical_wire = wire; }
        if let Some(author) = author { entry.author = author; }
        if let Some(value) = value { entry.value = value; }
    }

    #[cfg(test)]
    pub(crate) fn mutate_binding_for_test(&mut self, field: usize) {
        self.binding = self.binding.mutated_field_for_test(field);
    }
}

/// The three local partitions have different physical authors. Only the
/// first partition is installed by this overlay; Cap and Work-D are checked
/// against their existing native writers before the producer returns.
#[derive(Debug)]
pub(crate) struct Eligible08CheckedLocalCells {
    pub(crate) map_score_slack: Bank53TypedSourceLease,
    pub(crate) cap: Vec<(usize, bool)>,
    pub(crate) work_d: Vec<(usize, bool)>,
}

impl Eligible08PackedOverlay<'_> {
    pub(crate) fn checked_cells(
        &self, expected: &HeaderSourceBinding, owner: usize,
    ) -> Result<Eligible08CheckedLocalCells, String> {
        if owner != OWNER || &self.binding != expected
            || !expected.matches_sink(self.sink.binding.root, self.sink.binding.total,
                self.sink.binding.profile, &self.sink.binding.cut, owner) {
            return Err("C373 overlay exact root/total/profile/cut/layout/owner binding".into());
        }
        self.sink.checked_overlay_local_cells(&self.binding)
    }
}

/// Admission reports this partial semantic join only. Pending counts cover
/// tracked Map/Score edges, excluding HEADER/DAA inputs and Cap MAX imports.
pub(crate) struct Eligible08OwnerAdmission { cells: usize, terms: usize, pending: usize }
impl Eligible08OwnerAdmission {
    pub(crate) fn cell_count(&self) -> usize { self.cells }
    pub(crate) fn term_count(&self) -> usize { self.terms }
    pub(crate) fn pending_read_count(&self) -> usize { self.pending }
}

fn context_binding(context: &H21EligibleContext<'_>) -> Result<Binding, String> {
    crate::h21_scheduled_max_cap::NativeParent::checked(
        context.producer.plan, context.producer.input)?;
    if context.descriptor != H21EligibleMapStage::descriptor()
        || context.producer.roster.owner_class(OWNER as u64)?
            != crate::daa_history_roster::OwnerClass::Carry {
        return Err("Eligible08 sink exact owner/class/cut".into());
    }
    Ok(Binding { root: context.producer.plan.descriptor().root,
        total: context.producer.plan.work_profile().total_be28,
        profile: context.producer.input.profile(), cut: context.descriptor.canonical_identity(),
        maps: [context.maps[0].binding(), context.maps[1].binding()] })
}

impl H21EligibleContext<'_> {
    pub(crate) fn owner_sink_845759(&self) -> Result<Eligible08OwnerSink, String> {
        Ok(Eligible08OwnerSink {binding: context_binding(self)?, state: State::default(),
            custody: std::sync::Arc::new(()), source: None,
            cap_source: None, cap_max_resolution: None, work_source: None, upper_source: None,
            previous_r_source: None})
    }

    /// Join the retained first Cap publication to this context's closed MAX
    /// stream. The stream itself authenticates the full native replay before
    /// any of its owner-local cells can resolve an external read.
    pub(crate) fn join_owner_cap_max_845759(&self, sink: &mut Eligible08OwnerSink,
        stream: &crate::h21_scheduled_max_cap::MaxStream<'_>) -> Result<(), String> {
        if sink.binding != context_binding(self)? {
            return Err("Eligible08 sink Cap MAX full context binding".into());
        }
        sink.resolve_first_modern_cap_max(stream, self.producer.plan, self.producer.input)
    }

    /// Mint foreign-read custody from this sink's completed native MAX join.
    /// The destination binding is generated from the same plan and fixes all
    /// HEADER-source identity fields, including layout and owner.
    pub(crate) fn foreign_max_read_lease_845759(
        &self, sink: &Eligible08OwnerSink,
    ) -> Result<Eligible08ForeignMaxReadLease, String> {
        let resolution = sink.cap_max_resolution.as_ref()
            .ok_or("Eligible08 sink foreign MAX resolution missing")?;
        let destination = crate::packed_owner_assembly::HeaderSourceBinding::for_plan(
            self.producer.plan, OWNER)?;
        let expected_cut = crate::h21_scheduled_max_cap::CutDescriptor::eligible08()
            .canonical_identity();
        if sink.binding != context_binding(self)? || resolution.binding != sink.binding
            || resolution.owner != CAP_MAX_OWNER || sink.binding.root != self.producer.plan.descriptor().root
            || sink.binding.total != self.producer.plan.work_profile().total_be28
            || sink.binding.profile != self.producer.input.profile()
            || sink.binding.cut != expected_cut {
            return Err("Eligible08 sink foreign MAX destination/full context binding".into());
        }
        let mut cells = Vec::with_capacity(2 * CAP_MAX_BITS);
        for (index, resolved) in resolution.cells.iter().enumerate() {
            let context = index / CAP_MAX_BITS;
            let bit = index % CAP_MAX_BITS;
            let author = crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
                crate::h21_scheduled_max_cap::Writer::Max { context, end: CAP_MAX_OWNER + 2 });
            if context >= 2 || resolved.author != author
                || resolved.wire != CAP_MAX_OWNER * WIDTH + CAP_MAX_BASE[context] + bit
                || (resolved.value != Fr::zero() && resolved.value != Fr::one()) {
                return Err("Eligible08 sink foreign MAX resolution order/author/value".into());
            }
            cells.push(Eligible08ForeignMaxCell { wire: resolved.wire, context,
                end: CAP_MAX_OWNER + 2, bit, author, value: resolved.value == Fr::one() });
        }
        validate_foreign_max_cells(CAP_MAX_OWNER, &cells)?;
        Ok(Eligible08ForeignMaxReadLease { destination, source_owner: CAP_MAX_OWNER, cells })
    }

    /// Mint and validate from this context's own exact producer. Callers cannot
    /// supply an independent scalar D projection or a detached local source.
    pub(crate) fn join_owner_work_local_845759(&self, sink: &mut Eligible08OwnerSink)
        -> Result<Eligible08OwnerAdmission, String> {
        let binding = context_binding(self)?;
        sink.require_work_local_destination(&binding)?;
        let parent = self.producer.work_local_native_parent()?;
        let lease = self.producer.native_work_local_lease()?;
        self.producer.require_native_work_local_lease(&parent, &lease)?;
        let local = lease.local();
        let source = WorkLocalPublication {parent: parent.clone(), owner: OWNER, height: OWNER + 2,
            terms: local.terms().to_vec(), operands: local.operands().to_vec(), d: local.d().to_vec()};
        sink.admit_work_local(&binding, &parent, source)
    }

    /// The preceding physical Work owner supplies both Score W inputs. The
    /// complete LOCAL lease is validated before minting the opaque publication.
    pub(crate) fn join_owner_work_upper_845759(&self, sink:&mut Eligible08OwnerSink)
        ->Result<Eligible08OwnerAdmission,String> {
        let binding=context_binding(self)?;
        sink.require_work_upper_destination(&binding)?;
        let parent=self.producer.work_local_native_parent()?;
        let lease=self.producer.native_work_local_lease_for_owner(OWNER-1)?;
        self.producer.require_native_work_local_lease_for_owner(&parent,OWNER-1,&lease)?;
        let source=self.producer.work_upper_publication(OWNER-1,lease.local())?;
        sink.admit_work_upper(&binding,OWNER-1,source)
    }

    pub(crate) fn join_owner_previous_r_845759(&self, sink: &mut Eligible08OwnerSink)
        -> Result<Eligible08OwnerAdmission, String> {
        let binding = context_binding(self)?;
        sink.require_previous_r_destination(&binding)?;
        let source = self.premodern_r_publication(self.premodern_score_anchors()?)?;
        sink.admit_previous_r(&binding, source)
    }

    pub(crate) fn owner_score_slack_lease(&self, stage: H21EligibleSlackStage)
        -> Result<Eligible08OwnerLease, String> {
        let binding = context_binding(self)?;
        stage.map_stage.validate_identity(self.producer.plan, self.producer.input.profile(),
            self.descriptor, &self.maps)?;
        require_canonical_map_rows(&stage, &self.maps, self.descriptor)?;
        let mut map_reads = Vec::new();
        for (context, map) in self.maps.iter().enumerate() {
            for import in map.imports(OWNER as u64)? {
                let owner = usize::try_from(import.owner).map_err(|_| "Eligible08 import owner width")?;
                let author = match import.kind {
                    Kind::Difficulty => RequiredAuthor::WorkDifficulty {owner, height: owner + 2},
                    Kind::Timestamp => RequiredAuthor::HeaderTimestamp {owner, height: owner + 1},
                };
                for bit in 0..import.width {
                    let wire = map.input_index(import, bit)?;
                    map_reads.push(PendingRead {consumer: Writer::Map(context), wire, author,
                        value: self.producer.exports.bit(wire)?});
                }
            }
        }
        let (cells, rows, reads) = material(&binding, &stage, &map_reads)?;
        Ok(Eligible08OwnerLease {binding, source: stage, map_reads, cells, rows, reads})
    }
}

fn require_canonical_map_rows(stage: &H21EligibleSlackStage, maps: &[Map; 2],
    descriptor: crate::bank53_map::CutDescriptor) -> Result<(), String> {
    for (context, map) in maps.iter().enumerate() {
        let terms = crate::bank53_map::map_owner_terms_for_descriptor(
            map, OWNER as u64, context, descriptor)?;
        if stage.map_stage.map_terms[context] != terms {
            return Err("Eligible08 sink canonical Map source rows".into());
        }
    }
    Ok(())
}

fn material(binding: &Binding, stage: &H21EligibleSlackStage, map_reads: &[PendingRead])
    -> Result<(Vec<Cell>, Vec<Row>, Vec<PendingRead>), String> {
    let map = &stage.map_stage;
    if map.owner != OWNER || map.class != crate::daa_history_roster::OwnerClass::Carry
        || map.parent_root != binding.root || map.parent_total != binding.total
        || map.parent_profile != binding.profile || map.cut_identity != binding.cut
        || binding.cut != H21EligibleMapStage::descriptor().canonical_identity()
        || map.map_bindings != binding.maps || map.map_bindings.iter().any(|b| b.parent_root.is_some())
        || map.score_terms.iter().any(|terms| !terms.is_empty())
        || map.cap_terms.iter().any(|terms| !terms.is_empty()) {
        return Err("Eligible08 sink source parent/cut/owner/binding".into());
    }
    let mut cells = Vec::with_capacity(CELL_COUNT);
    let mut rows = Vec::new();
    let mut score_authors = [None; 2];
    for context in 0..2 {
        for local in H21EligibleMapStage::map_live(context)? {
            let &(author, value) = map.claims.get(&local).ok_or("Eligible08 sink missing Map X")?;
            if author != H21StageAuthor::Map(context) { return Err("Eligible08 sink Map author".into()); }
            cells.push(Cell {wire: OWNER * WIDTH + local, writer: Writer::Map(context), value});
        }
        for local in H21EligibleMapStage::score_live(context)? {
            let &(author, value) = stage.score_cells().get(&local).ok_or("Eligible08 sink missing Score X")?;
            if author.context != context || author.origin != OWNER + 1 || author.cap_owner != OWNER
                || author.previous_owner != OWNER - 1
                || author.max_owner != H21EligibleMapStage::descriptor().modern_start()
                    - H21EligibleMapStage::descriptor().offset() - 2
                || score_authors[context].is_some_and(|prior| prior != author)
                || !(value.is_zero() || value.is_one()) {
                return Err("Eligible08 sink Score author/boolean".into());
            }
            score_authors[context] = Some(author);
            cells.push(Cell {wire: OWNER * WIDTH + local, writer: Writer::Score(author), value: value.is_one()});
        }
        for local in H21EligibleMapStage::slack_live(context)? {
            let &(author, value) = stage.slack_cells().get(&local).ok_or("Eligible08 sink missing Slack X")?;
            if author != H21StageAuthor::Slack(context) || value {
                return Err("Eligible08 sink Slack author/zero".into());
            }
            cells.push(Cell {wire: OWNER * WIDTH + local, writer: Writer::Slack(context), value});
        }
        for (writer, terms) in [(Writer::Map(context), &map.map_terms[context]),
            (Writer::Score(score_authors[context].ok_or("Eligible08 sink missing Score context")?),
                &stage.score_rows()[context]), (Writer::Slack(context), &stage.slack_rows()[context])] {
            if terms.is_empty() {return Err("Eligible08 sink missing ROW family".into());}
            rows.extend(terms.iter().cloned().map(|term| Row {writer, term}));
        }
    }
    if cells.len() != CELL_COUNT || map.claims.len() != 11_514
        || stage.score_cells().len() != 4_096 || stage.slack_cells().len() != 774 {
        return Err("Eligible08 sink exact source X census".into());
    }
    let mut reads = map_reads.to_vec();
    let layout = crate::origin_score::Layout::new();
    let mut expected_score_reads = Vec::new();
    for context in 0..2 {
        let a = score_authors[context].ok_or("Eligible08 sink Score read context")?;
        let score_base = H21EligibleMapStage::score_live(context)?.start;
        for (source, author, start, range) in [
            (ScoreRelationReadAuthor::PreviousR {context, owner: a.previous_owner},
                RequiredAuthor::PreviousR {context, owner: a.previous_owner},
                a.previous_owner * WIDTH + score_base + layout.r.start, layout.p.clone()),
            (ScoreRelationReadAuthor::Cap {context, origin: a.origin, max_owner: a.max_owner, cap_owner: a.cap_owner},
                RequiredAuthor::Cap {context, origin: a.origin, max_owner: a.max_owner, cap_owner: a.cap_owner},
                OWNER * WIDTH + H21EligibleMapStage::cap_live(context)?.start + 740, layout.sv.clone()),
            (ScoreRelationReadAuthor::WorkUpper {owner: OWNER - 1, height: OWNER + 1},
                RequiredAuthor::WorkUpper {owner: OWNER - 1, height: OWNER + 1},
                (OWNER - 1) * WIDTH + 987_450, layout.sw.clone()),
        ] {
            for (bit, local) in range.enumerate() {
                let value = stage.score_cells()[&(score_base + local)].1;
                let wire = start + bit;
                expected_score_reads.push((wire, source, value));
                reads.push(PendingRead {consumer: Writer::Score(a), wire, author, value: value.is_one()});
            }
        }
    }
    if stage.score_imports() != expected_score_reads.as_slice()
        || expected_score_reads.len() != 2 * (225 + 224 + 65) {
        return Err("Eligible08 sink exact typed Score source reads".into());
    }
    Ok((cells, rows, reads))
}

/// Join the retained Score import order to independently rechecked source
/// projections and the sink's original typed obligations. Callers must supply
/// PreviousR and Upper values from their opaque checked publications.
fn qualify_score_import_records(
    imports: &[(usize, ScoreRelationReadAuthor, Fr)],
    obligations: &[PendingRead],
    previous_r: &[(usize, usize, bool)],
    cap_q: &[Vec<(usize, bool)>; 2],
    upper: &[(usize, Fr)],
    sink_cells: &BTreeMap<usize, (Writer, bool)>,
) -> Result<(), String> {
    const PER_CONTEXT: usize = 225 + 65 + 224;
    if imports.len() != 2 * PER_CONTEXT || previous_r.len() != 450
        || cap_q.iter().any(|bits| bits.len() != 65) || upper.len() != 224 {
        return Err("C455 exact source import/projection census".into());
    }
    let layout = crate::origin_score::Layout::new();
    let mut score_obligations = obligations.iter()
        .filter(|read| matches!(read.consumer, Writer::Score(_)));
    for (index, &(wire, author, value)) in imports.iter().enumerate() {
        let context = index / PER_CONTEXT;
        let relation_offset = index % PER_CONTEXT;
        if context >= 2 || !(value.is_zero() || value.is_one()) {
            return Err("C455 typed Score import context/value".into());
        }
        let score_author = ScoreReplayAuthor { context, origin: OWNER + 1,
            previous_owner: OWNER - 1, max_owner: CAP_MAX_OWNER, cap_owner: OWNER };
        let (expected_wire, expected_author, expected_value, writer, required) =
            if relation_offset < 225 {
                let bit = relation_offset;
                let expected_wire = (OWNER - 1) * WIDTH
                    + H21EligibleMapStage::score_live(context)?.start
                    + layout.r.start + bit;
                let (source_wire, source_context, source_bit) =
                    previous_r.get(context * 225 + bit).copied()
                        .ok_or("C455 PreviousR projection index")?;
                if source_wire != expected_wire || source_context != context {
                    return Err("C455 PreviousR projection/import source qualification".into());
                }
                (expected_wire, ScoreRelationReadAuthor::PreviousR {
                    context, owner: OWNER - 1 }, Fr::from(source_bit as u64),
                    Writer::PreviousR(context), RequiredAuthor::PreviousR {
                        context, owner: OWNER - 1 })
            } else if relation_offset < 225 + 65 {
                let bit = relation_offset - 225;
                let expected_wire = OWNER * WIDTH
                    + H21EligibleMapStage::cap_live(context)?.start + 740 + bit;
                let (source_wire, source_bit) = cap_q[context].get(bit).copied()
                    .ok_or("C455 Cap q projection index")?;
                if source_wire != expected_wire {
                    return Err("C455 Cap q projection/import source qualification".into());
                }
                (expected_wire, ScoreRelationReadAuthor::Cap {
                    context, origin: OWNER + 1, max_owner: CAP_MAX_OWNER, cap_owner: OWNER },
                    Fr::from(source_bit as u64), Writer::Cap(context), RequiredAuthor::Cap {
                        context, origin: OWNER + 1, max_owner: CAP_MAX_OWNER, cap_owner: OWNER })
            } else {
                let bit = relation_offset - 225 - 65;
                let expected_wire = (OWNER - 1) * WIDTH + 987_450 + bit;
                let (source_wire, source_value) = upper.get(bit).copied()
                    .ok_or("C455 WorkUpper projection index")?;
                if source_wire != expected_wire
                    || !(source_value.is_zero() || source_value.is_one()) {
                    return Err("C455 WorkUpper projection/import source qualification".into());
                }
                (expected_wire, ScoreRelationReadAuthor::WorkUpper {
                    owner: OWNER - 1, height: OWNER + 1 }, source_value,
                    Writer::WorkUpper, RequiredAuthor::WorkUpper {
                        owner: OWNER - 1, height: OWNER + 1 })
            };
        if wire != expected_wire || author != expected_author || value != expected_value {
            return Err("C455 typed Score import order/author/value".into());
        }
        if sink_cells.get(&wire) != Some(&(writer, value.is_one())) {
            return Err("C455 qualified Score source differs from retained sink cell".into());
        }
        let read = score_obligations.next()
            .ok_or("C455 original Score read obligation missing")?;
        if read.consumer != Writer::Score(score_author) || read.wire != wire
            || read.author != required || read.value != value.is_one() {
            return Err("C455 original Score read obligation mismatch".into());
        }
    }
    if score_obligations.next().is_some() {
        return Err("C455 extra original Score read obligation".into());
    }
    Ok(())
}

type CapMaxImport = (usize, crate::h21_scheduled_max_cap::Writer, Fr);
type CapMaxReplayCell = (usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, Fr);

/// Compare the published import census with the exact typed replay values.
/// Synthetic tests exercise this pure join; only the production caller below
/// obtains `expected` and `replay` from their checked native producers.
fn prepare_cap_max_resolution(binding: &Binding, expected: &[CapMaxImport],
    replay: &[CapMaxReplayCell]) -> Result<CapMaxResolution, String> {
    let cut = crate::h21_scheduled_max_cap::CutDescriptor::eligible08().canonical_identity();
    if binding.cut != cut || expected.len() != 2 * CAP_MAX_BITS {
        return Err("Eligible08 sink exact Cap MAX replay join".into());
    }
    let in_import_lane = |wire: usize| {
        let local = wire % WIDTH;
        CAP_MAX_BASE.iter().any(|base| (*base..*base + CAP_MAX_BITS).contains(&local))
    };
    let selected: Vec<_> = replay.iter().filter(|(wire, _, _)| in_import_lane(*wire)).collect();
    if selected.len() != 2 * CAP_MAX_BITS {
        return Err("Eligible08 sink exact Cap MAX replay join".into());
    }
    let mut cells = Vec::with_capacity(2 * CAP_MAX_BITS);
    for index in 0..2 * CAP_MAX_BITS {
        let context = index / CAP_MAX_BITS;
        let bit = index % CAP_MAX_BITS;
        let wire = CAP_MAX_OWNER * WIDTH + CAP_MAX_BASE[context] + bit;
        let author = crate::h21_scheduled_max_cap::Writer::Max {context, end: CAP_MAX_OWNER + 2};
        let (expected_wire, expected_author, expected_value) = expected[index];
        let (replay_wire, replay_author, replay_value) = *selected[index];
        if (expected_wire, expected_author, expected_value)
                != (wire, author, replay_value)
            || replay_wire != wire
            || replay_author != crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(author)
            || (expected_value != Fr::zero() && expected_value != Fr::one()) {
            return Err("Eligible08 sink exact Cap MAX replay join".into());
        }
        cells.push(ResolvedCapMaxCell {wire: replay_wire, author: replay_author, value: replay_value});
    }
    Ok(CapMaxResolution {binding: binding.clone(), owner: CAP_MAX_OWNER, cells})
}

impl Eligible08OwnerSink {
    /// Mint from the completed sink and its exact native context. No Map
    /// lease, source values, or ordered terms are accepted from the caller.
    pub(crate) fn map_source_view_845759<'s>(&'s self, context: &H21EligibleContext<'_>)
        -> Result<Eligible08MapSourceView<'s>, String> {
        let overlay = self.packed_overlay_845759(context)?;
        let source = self.source.as_ref().ok_or("C453 Map view retained source absent")?;
        source.map_stage.validate_identity(context.producer.plan,
            context.producer.input.profile(), context.descriptor, &context.maps)?;
        require_canonical_map_rows(source, &context.maps, context.descriptor)?;
        Ok(Eligible08MapSourceView { binding: overlay.binding, sink: self, source })
    }

    /// Mint the Score/Slack reader view only after the same completed sink,
    /// source identity, typed X census, ordered imports, and foreign
    /// publications have all been rechecked against this exact context.
    pub(crate) fn complete_row_source_view_845759<'s>(
        &'s self, context: &H21EligibleContext<'_>,
    ) -> Result<Eligible08CompleteRowSourceView<'s>, String> {
        let map = self.map_source_view_845759(context)?;
        let mut view = Eligible08CompleteRowSourceView {
            binding: map.binding.clone(), sink: self, source: map.source,
            qualified_imports: Vec::new(),
        };
        view.qualified_imports = view.checked_score_imports()?;
        if view.score_cells().len() != 4_096 || view.slack_cells().len() != 774 {
            return Err("C455 complete row source typed X census".into());
        }
        for context in 0..2 {
            view.score_terms(context)?;
            view.slack_terms(context)?;
        }
        if view.score_imports()?.len() != 1_028 {
            return Err("C455 complete row source import census".into());
        }
        Ok(view)
    }

    /// Isolate one retained Upper publication fault through the same complete
    /// Score/Slack mint used by the authentic selector. The original token is
    /// restored before returning, and no destination sink state is changed.
    #[cfg(test)]
    pub(crate) fn c455_retained_upper_fault_rejects_complete_view_for_test(
        &mut self, context: &H21EligibleContext<'_>,
    ) -> Result<(), String> {
        let original_upper = self.upper_source.clone()
            .ok_or("C455 test retained Upper publication absent")?;
        let before_binding = self.binding.clone();
        let before_state = self.state.clone();
        let before_custody = std::sync::Arc::clone(&self.custody);
        let before_source = self.source.clone();
        let before_work = self.work_source.clone();
        let before_cap = self.cap_source.as_ref().map(|source| source as *const _);
        let before_cap_max = self.cap_max_resolution.as_ref().map(|source| source as *const _);
        let before_previous_r = self.previous_r_source.as_ref().map(|source| source as *const _);
        let unchanged = |sink: &Eligible08OwnerSink| {
            sink.binding == before_binding && sink.state == before_state
                && std::sync::Arc::ptr_eq(&sink.custody, &before_custody)
                && sink.source == before_source && sink.work_source == before_work
                && sink.cap_source.as_ref().map(|source| source as *const _) == before_cap
                && sink.cap_max_resolution.as_ref().map(|source| source as *const _) == before_cap_max
                && sink.previous_r_source.as_ref().map(|source| source as *const _) == before_previous_r
                && sink.upper_source.as_ref() == Some(&original_upper)
        };

        let mutation = self.upper_source.as_mut()
            .ok_or("C455 test retained Upper publication absent")?
            .c455_flip_upper_value_for_test();
        if let Err(error) = mutation {
            self.upper_source = Some(original_upper.clone());
            if !unchanged(self) {
                return Err("C455 retained Upper mutation error changed sink custody/state".into());
            }
            return Err(error);
        }

        let mint_error = match self.complete_row_source_view_845759(context) {
            Err(error) => Some(error),
            Ok(view) => {
                drop(view);
                None
            }
        };
        self.upper_source = Some(original_upper.clone());

        if !unchanged(self) {
            return Err("C455 retained Upper fault probe changed sink custody/state".into());
        }
        match mint_error {
            Some(error) if error == "Work Upper exact physical operand projection" => {}
            Some(error) => return Err(format!(
                "C455 retained Upper fault reached unexpected mint rejection: {error}")),
            None => return Err("C455 complete row mint accepted retained Upper publication fault".into()),
        }
        Ok(())
    }

    /// Bounded zero source fixture. This does not satisfy the production
    /// completed-sink gate or establish native history/packed authority.
    #[cfg(test)]
    pub(crate) fn synthetic_map_source_for_test() -> Self {
        c373_overlay_source_tests::admitted_synthetic_source()
    }

    /// Test-only modern ROW geometry; it has no foreign publications.
    #[cfg(test)]
    pub(crate) fn synthetic_complete_row_source_for_test() -> Self {
        c373_overlay_source_tests::admitted_synthetic_source_for_c455()
    }

    #[cfg(test)]
    pub(crate) fn map_source_view_for_test(&self) -> Result<Eligible08MapSourceView<'_>, String> {
        let binding = c373_overlay_source_tests::packed_binding_for_test(self);
        self.checked_overlay_map_source(&c373_overlay_source_tests::expected_zero_d(), &binding)?;
        let source = self.source.as_ref().ok_or("C453 test Map source absent")?;
        let maps = H21EligibleMapStage::source_maps()?;
        if source.map_stage.map_bindings != [maps[0].binding(), maps[1].binding()] {
            return Err("C453 test Map source binding".into());
        }
        require_canonical_map_rows(source, &maps, H21EligibleMapStage::descriptor())?;
        Ok(Eligible08MapSourceView { binding, sink: self, source })
    }

    /// Local source mechanics only. This synthetic view has no retained
    /// PreviousR/WorkUpper publications and can never pass score_imports().
    #[cfg(test)]
    pub(crate) fn local_source_view_for_test(
        &self,
    ) -> Result<Eligible08CompleteRowSourceView<'_>, String> {
        let map = self.map_source_view_for_test()?;
        Ok(Eligible08CompleteRowSourceView {
            binding: map.binding.clone(), sink: self, source: map.source,
            qualified_imports: Vec::new(),
        })
    }

    /// Export only a completed, same-parent sink. The returned borrow keeps
    /// the checked source stage and all admitted publications alive during
    /// the native pre-pack claim and final value comparison.
    pub(crate) fn packed_overlay_845759<'s>(
        &'s self, context: &H21EligibleContext<'_>,
    ) -> Result<Eligible08PackedOverlay<'s>, String> {
        if self.binding != context_binding(context)? {
            return Err("C373 overlay exact Eligible08 context binding".into());
        }
        let binding = HeaderSourceBinding::for_plan(context.producer.plan, OWNER)?;
        if binding.profile() != context.producer.input.profile() {
            return Err("C373 overlay native profile drift".into());
        }
        let overlay = Eligible08PackedOverlay { binding, sink: self };
        overlay.checked_cells(&overlay.binding, OWNER)?;
        Ok(overlay)
    }

    fn checked_overlay_local_cells(
        &self, binding: &HeaderSourceBinding,
    ) -> Result<Eligible08CheckedLocalCells, String> {
        if !self.state.published || self.state.cells.len() != 21_378
            || !self.state.reads.is_empty() || self.cap_max_resolution.is_none()
            || self.upper_source.is_none() || self.previous_r_source.is_none() {
            return Err("C373 overlay completed sink/read/source census".into());
        }
        let cap_source = self.cap_source.as_ref().ok_or("C373 overlay Cap source absent")?;
        let work_source = self.work_source.as_ref().ok_or("C373 overlay Work-D source absent")?;
        let map_score_slack = self.checked_overlay_map_source(&work_source.d, binding)?;
        cap_source.require_binding(self.binding.root, self.binding.total,
            self.binding.profile, &self.binding.cut)?;
        let cap_material = cap_source.checked_material()?;
        if cap_material.cells.len() != 4_096 {
            return Err("C373 overlay exact Cap cell census".into());
        }
        let mut cap = Vec::with_capacity(4_096);
        for (wire, context, value) in cap_material.cells {
            if context >= 2 || wire / WIDTH != OWNER
                || self.state.cells.get(&wire) != Some(&(Writer::Cap(context), value)) {
                return Err("C373 overlay Cap author/value replay".into());
            }
            cap.push((wire % WIDTH, value));
        }
        if work_source.owner != OWNER || work_source.height != OWNER + 2
            || work_source.d.len() != 224 {
            return Err("C373 overlay exact Work-D owner/height/census".into());
        }
        let mut work_d = Vec::with_capacity(224);
        for (bit, &(wire, value)) in work_source.d.iter().enumerate() {
            if wire != OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL + bit
                || (value != Fr::zero() && value != Fr::one())
                || self.state.cells.get(&wire) != Some(&(Writer::WorkLocal, value.is_one())) {
                return Err("C373 overlay Work-D author/value replay".into());
            }
            work_d.push((wire % WIDTH, value.is_one()));
        }
        if map_score_slack.entries().len() != 16_384 || cap.len() != 4_096 || work_d.len() != 224 {
            return Err("C373 overlay exact 20,704 local cell census".into());
        }
        Ok(Eligible08CheckedLocalCells { map_score_slack, cap, work_d })
    }

    fn checked_overlay_map_source(
        &self, expected_d: &[(usize, Fr)], binding: &HeaderSourceBinding,
    ) -> Result<Bank53TypedSourceLease, String> {
        let source = self.source.as_ref().ok_or("C373 overlay Map/Score/Slack source absent")?;
        if expected_d.len() != 224 {
            return Err("C373 overlay exact independent Work-D census".into());
        }
        for (bit, &(wire, value)) in expected_d.iter().enumerate() {
            if wire != OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL + bit
                || (value != Fr::zero() && value != Fr::one()) {
                return Err("C373 overlay independent Work-D wire/value order".into());
            }
        }
        let mut expected_map_reads = Vec::with_capacity(448);
        for context in 0..2 {
            for &(wire, value) in expected_d {
                expected_map_reads.push(PendingRead {
                    consumer: Writer::Map(context), wire,
                    author: RequiredAuthor::WorkDifficulty {owner: OWNER, height: OWNER + 2},
                    value: value.is_one(),
                });
            }
        }
        let map_reads = self.state.read_obligations.iter()
            .filter(|read| matches!(read.consumer, Writer::Map(_)))
            .cloned().collect::<Vec<_>>();
        if map_reads != expected_map_reads {
            return Err("C373 overlay exact independent Map read obligation replay".into());
        }
        let (cells, rows, reads) = material(&self.binding, source, &expected_map_reads)?;
        if cells.len() != CELL_COUNT || self.state.read_obligations != reads
            || self.state.terms.get(..rows.len()) != Some(rows.as_slice()) {
            return Err("C373 overlay exact admitted source/ROW/read replay".into());
        }
        let mut entries = Vec::with_capacity(CELL_COUNT);
        for cell in cells {
            if self.state.cells.get(&cell.wire) != Some(&(cell.writer, cell.value))
                || cell.wire / WIDTH != OWNER {
                return Err("C373 overlay Map/Score/Slack author/value replay".into());
            }
            let author = match cell.writer {
                Writer::Map(context) => Bank53TypedAuthor::Map(context),
                Writer::Score(author) => Bank53TypedAuthor::Score(author),
                Writer::Slack(context) => Bank53TypedAuthor::Slack(context),
                _ => return Err("C375 Bank53 source has non-Map/Score/Slack author".into()),
            };
            entries.push(Bank53TypedSourceEntry {
                physical_wire: cell.wire, author, value: cell.value,
            });
        }
        let lease = Bank53TypedSourceLease { binding: binding.clone(), entries,
            custody: Some(std::sync::Arc::clone(&self.custody)) };
        lease.validate(binding, OWNER)?;
        Ok(lease)
    }

    /// Source-only projection for the first modern Carry owner. Each row
    /// occurrence retains its own consumer identity. Pending sink reads are
    /// expanded only over active terms of that same sink writer and wire.
    /// A missing native HEADER lease stays open; this is not a packed witness.
    fn occurrence_ledger_845759(&self,row_plan:&RowPlan<'_, '_>,row19:&Row19Batch,
        plan:&WorkTreeHistoryPlan,header:Option<&NativeHeaderSourceLease>)
        ->Result<OwnerOccurrenceLedger,String> {
        if !self.state.published || self.source.is_none() {
            return Err("owner occurrence sink not admitted".into());
        }
        row19.require_owner_parent(plan,OWNER)?;
        let mut profile_bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let expected_profile:[u8;32]=Blake2b::<U32>::digest(profile_bytes).into();
        if self.binding.root!=plan.descriptor().root
            || self.binding.total!=plan.work_profile().total_be28
            || self.binding.profile!=expected_profile
            || self.binding.cut!=crate::bank53_map::CutDescriptor::eligible08().canonical_identity() {
            return Err("owner occurrence sink/ROW parent cut profile".into());
        }
        let cap_source=self.cap_source.as_ref()
            .ok_or("owner occurrence first Cap publication missing")?;
        cap_source.require_binding(self.binding.root,self.binding.total,self.binding.profile,
            &self.binding.cut)?;
        let material=cap_source.checked_material()?;
        let suffix=self.state.terms.len().checked_sub(material.rows.len())
            .ok_or("owner occurrence Cap/HEADER ROW suffix")?;
        if self.state.terms[..suffix].iter().any(|r|matches!(r.writer,Writer::Header|Writer::Cap(_)))
            || self.state.terms[suffix..]!=material.rows.iter().map(|(context,term)|Row{
                writer:context.map_or(Writer::Header,Writer::Cap),term:term.clone()})
                .collect::<Vec<_>>() {
            return Err("owner occurrence exact retained Cap/HEADER ROW source".into());
        }
        let raw_header=material.rows.iter().filter_map(|(context,term)|
            context.is_none().then(||term.clone())).collect::<Vec<_>>();
        let placed_header=row_plan.check_raw_header_placement(OWNER,&raw_header,row19)?;
        let mut header_index=0usize;
        let placed_partition=material.rows.iter().map(|(context,term)|match context {
            None=>{let placed=placed_header[header_index].clone();header_index+=1;
                (Row19Relation::Header,placed)},
            Some(context)=>(Row19Relation::Scheduled(
                crate::h21_scheduled_max_cap::Writer::Cap{context:*context,origin:OWNER+1}),
                term.clone()),
        }).collect::<Vec<_>>();
        let row_partition=row19.terms().filter_map(|(relation,term)|match relation {
            Row19Relation::Header | Row19Relation::Scheduled(
                crate::h21_scheduled_max_cap::Writer::Cap{..})=>Some((relation,term.clone())),
            _=>None,
        }).collect::<Vec<_>>();
        if header_index!=placed_header.len() || placed_partition!=row_partition {
            return Err("owner occurrence exact placed Header/Cap partition".into());
        }

        let mut physical=BTreeMap::new();
        let mut cap_cells=0usize;
        for (&wire,&(writer,bit)) in &self.state.cells {
            match writer {
                Writer::Header=>return Err("owner occurrence HEADER sink cell without native source".into()),
                Writer::Cap(_)=>{cap_cells+=1;},
                Writer::WorkLocal if self.work_source.is_none()=>
                    return Err("owner occurrence Work LOCAL source absent".into()),
                Writer::WorkUpper if self.upper_source.is_none()=>
                    return Err("owner occurrence Work Upper source absent".into()),
                Writer::PreviousR(_) if self.previous_r_source.is_none()=>
                    return Err("owner occurrence Previous R source absent".into()),
                _=>insert_physical(&mut physical,PhysicalClaim{owner:wire/WIDTH,wire,
                    author:PhysicalAuthor::SinkAdmitted(writer),bit})?,
            }
        }
        if cap_cells!=material.cells.len() {return Err("owner occurrence Cap cell census".into());}
        for &(wire,context,bit) in &material.cells {
            if self.state.cells.get(&wire)!=Some(&(Writer::Cap(context),bit)) {
                return Err("owner occurrence exact published Cap cell".into());
            }
            insert_physical(&mut physical,PhysicalClaim{owner:OWNER,wire,
                author:PhysicalAuthor::PublishedCap{context,origin:OWNER+1,owner:OWNER},bit})?;
        }

        let sink_operands=sink_active_operands(&self.state);
        let row_operands=row19.active_operands().collect::<Vec<_>>();
        if let Some(lease)=header {
            let wires=row_operands.iter().map(|op|op.wire)
                .chain(sink_operands.iter().map(|op|op.wire)).collect::<BTreeSet<_>>();
            for wire in wires {
                if let Some(bit)=row19.header_bit(lease,wire)? {
                    insert_physical(&mut physical,PhysicalClaim{owner:OWNER,wire,
                        author:PhysicalAuthor::NativeHeader{owner:OWNER},bit})?;
                }
            }
        }
        if physical.values().any(|claim|is_local_daa_bank_wire(claim.wire)) {
            return Err("owner occurrence local DAA bank claim lacks native source".into());
        }

        let mut obligations=BTreeMap::new();
        for read in &self.state.read_obligations {
            let key=(sink_read_slot(read.consumer)?,read.wire);
            if obligations.insert(key,read).is_some() {
                return Err("owner occurrence duplicate original sink edge".into());
            }
        }
        let mut pending=BTreeMap::new();
        for read in &self.state.reads {
            let key=(sink_read_slot(read.consumer)?,read.wire);
            if pending.insert(key,read).is_some() || obligations.get(&key)!=Some(&read) {
                return Err("owner occurrence pending edge not original".into());
            }
        }
        let mut used=BTreeMap::<(usize,usize),usize>::new();
        let mut records=Vec::with_capacity(row_operands.len()+sink_operands.len());
        for operand in row_operands {
            let source=physical.get(&operand.wire).copied().map(OccurrenceSource::Resolved)
                .unwrap_or_else(||OccurrenceSource::Open(if operand.wire/WIDTH==OWNER {
                    OpenSource::UnqualifiedLocal } else {OpenSource::ForeignOwner}));
            records.push(OccurrenceRecord{consumer:ConsumerOccurrence::Row19(operand),
                wire:operand.wire,source});
        }
        for operand in sink_operands {
            let slot=match operand.writer {Writer::Map(_)|Writer::Score(_)=>
                Some(sink_read_slot(operand.writer)?),_=>None};
            let key=slot.map(|slot|(slot,operand.wire));
            let expected=key.and_then(|key|obligations.get(&key).copied());
            if let Some(read)=expected {
                if read.consumer!=operand.writer {
                    return Err("owner occurrence pending consumer family".into());
                }
                *used.entry(key.unwrap()).or_insert(0)+=1;
            }
            let claim=physical.get(&operand.wire).copied();
            let still_pending=key.is_some_and(|key|pending.contains_key(&key));
            let source=match (expected,claim,still_pending) {
                (Some(read),Some(claim),false)=>{
                    if claim.bit!=read.value || !satisfies_required(read.author,claim) {
                        return Err("owner occurrence typed source author/value".into());
                    }
                    OccurrenceSource::Resolved(claim)
                },
                (Some(_),Some(_),true)=>return Err("owner occurrence claimed source still pending".into()),
                (Some(read),None,true)=>OccurrenceSource::Pending{
                    author:read.author,expected_bit:read.value},
                (Some(_),None,false)=>return Err("owner occurrence resolved edge lacks source".into()),
                (None,Some(claim),_)=>OccurrenceSource::Resolved(claim),
                (None,None,_) if matches!(operand.writer,Writer::Header|Writer::Cap(_))=>
                    OccurrenceSource::Open(if operand.wire/WIDTH==OWNER {
                        OpenSource::UnqualifiedLocal } else {OpenSource::ForeignOwner}),
                (None,None,_)=>return Err("owner occurrence unclassified active sink read".into()),
            };
            records.push(OccurrenceRecord{consumer:ConsumerOccurrence::Sink(operand),
                wire:operand.wire,source});
        }
        if obligations.keys().any(|key|!used.contains_key(key)) {
            return Err("owner occurrence orphan original sink edge".into());
        }
        let ledger=OwnerOccurrenceLedger{records,physical};
        ledger.check_exact(row19,self)?;
        Ok(ledger)
    }
    fn require_previous_r_destination(&self, binding: &Binding) -> Result<(), String> {
        if self.binding != *binding { return Err("R450 sink exact destination binding".into()); }
        if !self.state.published || self.source.is_none() || self.work_source.is_none()
            || self.previous_r_source.is_some() {
            return Err("R450 sink order/duplicate".into());
        }
        Ok(())
    }

    /// Shared projection checker. Its conditional tests confer no native token
    /// authority; production reaches it only after checked_projection above.
    fn prepare_previous_r(&self, binding: &Binding, projection: &R450Projection) -> Result<State, String> {
        self.require_previous_r_destination(binding)?;
        let cells = &projection.cells[1];
        if cells.len() != 450 { return Err("R450 sink source census".into()); }
        let mut next = self.state.clone();
        for context in 0..2 {
            for bit in 0..225 {
                let expected = (OWNER - 1) * WIDTH + [677_501, 685_693][context] + 1318 + bit;
                let (wire, actual_context, value) = cells[context * 225 + bit];
                if wire != expected || actual_context != context {
                    return Err("R450 sink exact physical source/order".into());
                }
                if next.cells.insert(wire, (Writer::PreviousR(context), value)).is_some() {
                    return Err("R450 sink duplicate X including equal".into());
                }
            }
        }
        let mut matched = [[false; 225]; 2];
        let mut remaining = Vec::with_capacity(next.reads.len());
        for read in &next.reads {
            if let RequiredAuthor::PreviousR { context, owner } = read.author {
                let author = match read.consumer { Writer::Score(author) => author,
                    _ => return Err("R450 sink exact Score consumer".into()) };
                if context >= 2 || owner != OWNER - 1 || author.context != context
                    || author.previous_owner != owner || author.origin != OWNER + 1
                    || author.max_owner != 844_670 || author.cap_owner != OWNER {
                    return Err("R450 sink exact typed source/consumer".into());
                }
                let bit = read.wire.checked_sub(owner * WIDTH + [677_501, 685_693][context] + 1318)
                    .filter(|bit| *bit < 225).ok_or("R450 sink exact read domain")?;
                if matched[context][bit]
                    || cells[context * 225 + bit] != (read.wire, context, read.value)
                    || next.cells.get(&read.wire) != Some(&(Writer::PreviousR(context), read.value)) {
                    return Err("R450 sink source bit/duplicate read".into());
                }
                matched[context][bit] = true;
            } else { remaining.push(read.clone()); }
        }
        if matched.iter().flatten().any(|bit| !*bit) { return Err("R450 sink exact 450-read census".into()); }
        next.reads = remaining;
        Ok(next)
    }

    fn admit_previous_r(&mut self, binding: &Binding, source: PremodernRPublication)
        -> Result<Eligible08OwnerAdmission, String> {
        self.require_previous_r_destination(binding)?;
        let projection = source.checked_projection(binding.root, binding.total, binding.profile,
            &binding.cut, &binding.maps)?;
        let next = self.prepare_previous_r(binding, &projection)?;
        let admission = Eligible08OwnerAdmission { cells: next.cells.len(), terms: next.terms.len(), pending: next.reads.len() };
        self.previous_r_source = Some(source);
        self.state = next;
        Ok(admission)
    }

    /// Selected Map/Score obligations only, not a complete active-X census.
    pub(crate) fn pending_sources(&self) -> &[PendingRead] { &self.state.reads }

    /// Compare the checked sink's own local Boolean values with one native row.
    /// This is a semantic diagnostic for selected authors, not a complete X
    /// writer census or a proof of all ROW/PCS obligations. In particular,
    /// WorkLocal is the sink's semantic label; it does not transfer the
    /// packed Work-D cells' physical HEADER authorship.
    #[cfg(test)]
    pub(crate) fn reconcile_local_packed_bits_845759(
        &self, context: &H21EligibleContext<'_>,
        packed: &crate::packed_owner_assembly::NativePackedRow,
    ) -> Result<(usize, usize), String> {
        if self.binding != context_binding(context)? || !self.state.published
            || self.source.is_none() || self.cap_source.is_none()
            || self.cap_max_resolution.is_none() || self.work_source.is_none()
            || self.upper_source.is_none() || self.previous_r_source.is_none()
            || !self.state.reads.is_empty() {
            return Err("C372 sink exact context/source/read closure".into());
        }
        let expected = crate::packed_owner_assembly::HeaderSourceBinding::for_plan(
            context.producer.plan, OWNER)?;
        packed.require_header_source_binding(
            &expected, OWNER, crate::daa_history_roster::OwnerClass::Carry)?;
        reconcile_local_cells_with_bytes_845759(&self.state.cells, packed.packed_bytes())
    }

    pub(crate) fn retained_work_local_counts(&self) -> (usize, usize) {
        self.work_source.as_ref().map_or((0, 0), |source| (source.terms.len(), source.operands.len()))
    }

    pub(crate) fn retained_work_upper_counts(&self)->(usize,usize) {
        self.upper_source.as_ref().map_or((0,0),|source|source.retained_counts())
    }
    fn require_work_upper_destination(&self,binding:&Binding)->Result<(),String> {
        if self.binding!=*binding {return Err("Eligible08 sink Upper full context binding".into());}
        if !self.state.published || self.source.is_none() || self.work_source.is_none()
            || self.upper_source.is_some() {
            return Err("Eligible08 sink Upper order/duplicate".into());
        }
        Ok(())
    }
    // Production calls this only with OWNER-1 and a token minted from that
    // context's checked native lease. The owner argument also permits a bounded
    // real packed-source fixture without manufacturing native H21 authority.
    fn admit_work_upper(&mut self,binding:&Binding,source_owner:usize,
        source:crate::packed_owner_assembly::WorkUpperPublication)
        ->Result<Eligible08OwnerAdmission,String> {
        self.require_work_upper_destination(binding)?;
        let upper=source.checked_upper(binding.root,binding.total,binding.profile,&binding.cut,source_owner)?;
        let mut next=self.state.clone();
        for &(wire,value) in upper {
            if next.cells.insert(wire,(Writer::WorkUpper,value.is_one())).is_some() {
                return Err("Eligible08 sink Upper duplicate X".into());
            }
        }
        let mut matched=[[false;224];2];
        let mut remaining=Vec::with_capacity(next.reads.len());
        for read in &next.reads {
            if let RequiredAuthor::WorkUpper{owner,height}=read.author {
                let context=match read.consumer {Writer::Score(author) if author.context<2
                    && author.origin==OWNER+1 && author.previous_owner==OWNER-1
                    && author.max_owner==844_670 && author.cap_owner==OWNER=>author.context,
                    _=>return Err("Eligible08 sink Upper exact Score consumer".into())};
                if owner!=source_owner || height!=source_owner+2 {
                    return Err("Eligible08 sink Upper exact typed source".into());
                }
                let bit=read.wire.checked_sub(source_owner*WIDTH+987450).filter(|bit|*bit<224)
                    .ok_or("Eligible08 sink Upper exact read domain")?;
                if matched[context][bit] || upper[bit]!=(read.wire,Fr::from(read.value as u64))
                    || next.cells.get(&read.wire)!=Some(&(Writer::WorkUpper,read.value)) {
                    return Err("Eligible08 sink Upper source bit/duplicate read".into());
                }
                matched[context][bit]=true;
            } else {remaining.push(read.clone());}
        }
        if matched.iter().flatten().any(|bit|!*bit) {
            return Err("Eligible08 sink Upper exact 448-read census".into());
        }
        next.reads=remaining;
        let admission=Eligible08OwnerAdmission{cells:next.cells.len(),terms:next.terms.len(),pending:next.reads.len()};
        self.upper_source=Some(source);self.state=next;
        Ok(admission)
    }

    fn require_work_local_destination(&self, binding: &Binding) -> Result<(), String> {
        if self.binding != *binding {return Err("Eligible08 sink Work full context binding".into());}
        if !self.state.published || self.source.is_none() || self.work_source.is_some() {
            return Err("Eligible08 sink Work order/duplicate".into());
        }
        Ok(())
    }

    fn admit_work_local(&mut self, binding: &Binding,
        parent: &crate::h21_scheduled_max_cap::NativeParent, source: WorkLocalPublication)
        -> Result<Eligible08OwnerAdmission, String> {
        self.require_work_local_destination(binding)?;
        if source.parent != *parent || source.owner != OWNER || source.height != OWNER + 2
            || source.terms.len() != 3265 || source.operands.len() != 1184 {
            return Err("Eligible08 sink Work native parent/owner/height/material".into());
        }
        if source.d.len() != 224 {return Err("Eligible08 sink Work exact D census".into());}
        let mut next = self.state.clone();
        for (bit, &(wire, value)) in source.d.iter().enumerate() {
            if wire != OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL + bit
                || !(value.is_zero() || value.is_one())
                || !source.operands.iter().any(|&(w, v)| w == wire && v == value) {
                return Err("Eligible08 sink Work exact D wire/value/operand".into());
            }
            if next.cells.insert(wire, (Writer::WorkLocal, value.is_one())).is_some() {
                return Err("Eligible08 sink Work duplicate X".into());
            }
        }
        let mut matched = [[false; 224]; 2];
        let mut remaining = Vec::with_capacity(next.reads.len());
        for read in &next.reads {
            if let RequiredAuthor::WorkDifficulty {owner, height} = read.author {
                let context = match read.consumer {Writer::Map(context) if context < 2 => context,
                    _ => return Err("Eligible08 sink Work Map consumer context".into())};
                if owner != OWNER || height != OWNER + 2 {
                    return Err("Eligible08 sink Work exact typed source".into());
                }
                let bit = read.wire.checked_sub(OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL)
                    .filter(|bit| *bit < 224).ok_or("Eligible08 sink Work exact read domain")?;
                if matched[context][bit] || source.d[bit] != (read.wire, Fr::from(read.value as u64))
                    || next.cells.get(&read.wire) != Some(&(Writer::WorkLocal, read.value)) {
                    return Err("Eligible08 sink Work source bit/duplicate read".into());
                }
                matched[context][bit] = true;
            } else {remaining.push(read.clone());}
        }
        if matched.iter().flatten().any(|bit| !*bit) {
            return Err("Eligible08 sink Work exact 448-read census".into());
        }
        next.reads = remaining;
        let admitted = Eligible08OwnerAdmission {cells: next.cells.len(), terms: next.terms.len(),
            pending: next.reads.len()};
        // Checked local custody and all 448 read edges publish together. Every
        // failure above leaves ROW19, siblings and pending obligations intact.
        self.work_source = Some(source); self.state = next;
        Ok(admitted)
    }

    /// These are the new Cap authors' own unresolved MAX inputs. They remain
    /// distinct from Map/Score edges. Retained HEADER/DAA input authentication
    /// remains open and is not included in either count.
    pub(crate) fn pending_cap_max_read_count(&self)->usize {
        if self.cap_max_resolution.is_some() { 0 }
        else { self.cap_source.as_ref().map_or(0,|source|source.pending_max_read_count()) }
    }

    /// Resolve the first Cap's 448 MAX imports from the same fully closed
    /// native stream and snapshot that validate its retained publication.
    pub(crate) fn resolve_first_modern_cap_max(
        &mut self,
        stream: &crate::h21_scheduled_max_cap::MaxStream<'_>,
        plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix: &crate::packed_owner_assembly::NativePrefix,
    ) -> Result<(), String> {
        if !self.state.published || self.source.is_none()
            || self.cap_source.is_none() || self.cap_max_resolution.is_some() {
            return Err("Eligible08 sink Cap MAX order/duplicate".into());
        }
        let snapshot = stream.closed_native_snapshot(plan, prefix)?;
        let expected_cut = crate::h21_scheduled_max_cap::CutDescriptor::eligible08()
            .canonical_identity();
        if plan.descriptor().root != self.binding.root
            || plan.work_profile().total_be28 != self.binding.total
            || prefix.profile() != self.binding.profile
            || self.binding.cut != expected_cut {
            return Err("Eligible08 sink Cap MAX destination binding".into());
        }
        let replay = stream.closed_owner_cells(CAP_MAX_OWNER)?;
        let expected = self.cap_source.as_ref().unwrap().checked_max_imports(plan, prefix, snapshot)?;
        let resolution = prepare_cap_max_resolution(&self.binding, &expected, &replay)?;
        self.commit_cap_max_resolution(resolution)
    }

    fn commit_cap_max_resolution(&mut self, resolution: CapMaxResolution) -> Result<(), String> {
        if !self.state.published || self.source.is_none()
            || self.cap_source.is_none() || self.cap_max_resolution.is_some()
            || resolution.binding != self.binding || resolution.owner != CAP_MAX_OWNER
            || resolution.cells.len() != 2 * CAP_MAX_BITS {
            return Err("Eligible08 sink Cap MAX order/duplicate".into());
        }
        self.cap_max_resolution = Some(resolution);
        Ok(())
    }

    pub(crate) fn admit_first_modern_cap(&mut self,
        source:crate::h21_scheduled_family_ledger::FirstModernCapPublication)
        ->Result<Eligible08OwnerAdmission,String> {
        if !self.state.published || self.source.is_none() || self.cap_source.is_some() {
            return Err("Eligible08 sink Cap order/duplicate".into());
        }
        source.require_binding(self.binding.root,self.binding.total,self.binding.profile,&self.binding.cut)?;
        let material=source.checked_material()?;
        self.admit_first_modern_cap_material(source,material)
    }

    /// Commit material already returned by `checked_material`. Kept private so
    /// production callers cannot detach material from its checked publisher;
    /// the unit diagnostic uses it to avoid replaying the large Cap source.
    fn admit_first_modern_cap_material(&mut self,
        source:crate::h21_scheduled_family_ledger::FirstModernCapPublication,
        material:crate::h21_scheduled_family_ledger::CapJoinMaterial)
        ->Result<Eligible08OwnerAdmission,String> {
        if !self.state.published || self.source.is_none() || self.cap_source.is_some() {
            return Err("Eligible08 sink Cap order/duplicate".into());
        }
        source.require_binding(self.binding.root,self.binding.total,self.binding.profile,&self.binding.cut)?;
        let mut next=self.state.clone();
        let mut added_rows=BTreeMap::new();
        for (context,term) in material.rows {
            let writer=context.map_or(Writer::Header,Writer::Cap);
            if term.row/crate::bank53_map::ROW_STRIDE!=OWNER
                || self.state.rows.contains_key(&term.row)
                || added_rows.insert(term.row,writer).is_some_and(|prior|prior!=writer) {
                return Err("Eligible08 sink Cap/HEADER ROW overlap/owner".into());
            }
            next.terms.push(Row{writer,term});
        }
        next.rows.extend(added_rows);
        for (wire,context,value) in material.cells {
            if wire/WIDTH!=OWNER || context>=2
                || next.cells.insert(wire,(Writer::Cap(context),value)).is_some() {
                return Err("Eligible08 sink Cap duplicate X/owner".into());
            }
        }
        let mut matched=[vec![false;65],vec![false;65]];
        let mut remaining=Vec::with_capacity(next.reads.len());
        for read in &next.reads {
            if let RequiredAuthor::Cap{context,origin,max_owner,cap_owner}=read.author {
                let score_context=match read.consumer {Writer::Score(author)=>author.context,
                    _=>return Err("Eligible08 sink Cap consumer author".into())};
                if context>=2 || score_context!=context || origin!=OWNER+1
                    || max_owner!=844_670 || cap_owner!=OWNER {
                    return Err("Eligible08 sink Cap exact typed source".into());
                }
                let bit=read.wire.checked_sub(OWNER*WIDTH+[1_000_770,1_002_818][context]+740)
                    .filter(|bit|*bit<65).ok_or("Eligible08 sink Cap exact q domain")?;
                if matched[context][bit] || material.q[context][bit]!=(read.wire,read.value)
                    || next.cells.get(&read.wire)!=Some(&(Writer::Cap(context),read.value)) {
                    return Err("Eligible08 sink Cap source bit/duplicate read".into());
                }
                matched[context][bit]=true;
            } else {remaining.push(read.clone());}
        }
        if matched.iter().flatten().any(|bit|!*bit) {
            return Err("Eligible08 sink Cap exact 130-read census".into());
        }
        next.reads=remaining;
        let admitted=Eligible08OwnerAdmission{cells:next.cells.len(),terms:next.terms.len(),pending:next.reads.len()};
        // Every source, ownership and cross-context read check precedes both
        // publications. Failed Cap admission preserves the original sink.
        self.cap_source=Some(source);self.state=next;
        Ok(admitted)
    }

    pub(crate) fn admit(&mut self, lease: Eligible08OwnerLease)
        -> Result<Eligible08OwnerAdmission, String> {
        if self.binding != lease.binding || self.state.published || self.source.is_some() {
            return Err("Eligible08 sink destination binding/duplicate".into());
        }
        let mut next = State::default();
        for cell in &lease.cells {
            if cell.wire / WIDTH != OWNER
                || next.cells.insert(cell.wire, (cell.writer, cell.value)).is_some() {
                return Err("Eligible08 sink duplicate/outside X author".into());
            }
        }
        for row in &lease.rows {
            if row.term.row / crate::bank53_map::ROW_STRIDE != OWNER {
                return Err("Eligible08 sink physical ROW owner".into());
            }
            if next.rows.insert(row.term.row, row.writer).is_some_and(|prior| prior != row.writer) {
                return Err("Eligible08 sink cross-writer ROW collision".into());
            }
        }
        let (cells, rows, reads) = material(&lease.binding, &lease.source, &lease.map_reads)?;
        if lease.cells != cells || lease.rows != rows || lease.reads != reads {
            return Err("Eligible08 sink exact source projection".into());
        }
        let mut by_wire = BTreeMap::new();
        let mut by_consumer = BTreeMap::new();
        for read in &reads {
            if read.wire >= (1usize << 41)
                || by_wire.insert(read.wire, (read.author, read.value))
                    .is_some_and(|prior| prior != (read.author, read.value)) {
                return Err("Eligible08 sink typed read disagreement/extent".into());
            }
            // Writer is not an Ord key; source order preserves the three
            // family contexts in a small integer consumer slot.
            let slot = match read.consumer {Writer::Map(c) => c, Writer::Score(a) => 2 + a.context,
                Writer::Slack(c) => 4 + c,
                Writer::Header|Writer::Cap(_)|Writer::WorkLocal|Writer::WorkUpper|Writer::PreviousR(_)=>return Err("Eligible08 sink invalid initial consumer".into())};
            if by_consumer.insert((slot, read.wire), ()).is_some() {
                return Err("Eligible08 sink duplicate read edge".into());
            }
        }
        for row in &rows {
            let g = &row.term.gate;
            let slot = match row.writer {Writer::Map(c) => c, Writer::Score(a) => 2 + a.context,
                Writer::Slack(c) => 4 + c,
                Writer::Header|Writer::Cap(_)|Writer::WorkLocal|Writer::WorkUpper|Writer::PreviousR(_)=>return Err("Eligible08 sink invalid initial ROW writer".into())};
            for (wire, active) in [(g.left, !g.c1.is_zero() || !g.c3.is_zero()),
                (g.right, !g.c2.is_zero() || !g.c3.is_zero())] {
                // Gate::evaluate treats coordinate zero like every other
                // input: an active operand needs its own classified author.
                if active && !next.cells.contains_key(&wire)
                    && !by_consumer.contains_key(&(slot, wire)) {
                    return Err("Eligible08 sink unclassified active read".into());
                }
            }
        }
        let admitted = Eligible08OwnerAdmission {cells: cells.len(), terms: rows.len(), pending: reads.len()};
        next.terms = rows; next.read_obligations=reads.clone();
        next.reads = reads; next.published = true;
        // Every fallible check precedes publication, including read coverage.
        self.source = Some(lease.source); self.state = next;
        Ok(admitted)
    }
}

/// All selected local cells are compared individually. The foreign cells have
/// their own exact typed-domain census but are never read from this owner's row.
#[cfg(test)]
fn reconcile_local_cells_with_bytes_845759(
    cells: &BTreeMap<usize, (Writer, bool)>, packed: &[u8],
) -> Result<(usize, usize), String> {
    if packed.len() != WIDTH / 8 {
        return Err("C372 packed owner byte width".into());
    }
    let mut local_count = 0usize;
    let mut mismatches = [0usize; 9];
    let mut first_mismatch = None;
    let mut compare = |local: usize, writer: Writer, domain: usize| -> Result<(), String> {
        let wire = OWNER * WIDTH + local;
        let &(actual_writer, value) = cells.get(&wire)
            .ok_or_else(|| format!("C372 missing local cell domain={domain} local={local}"))?;
        if actual_writer != writer {
            return Err(format!("C372 wrong local writer domain={domain} local={local}"));
        }
        if matches!(writer, Writer::Slack(_)) && value {
            return Err(format!("C372 nonzero Slack domain={domain} local={local}"));
        }
        let packed_value = ((packed[local / 8] >> (local % 8)) & 1) != 0;
        if value != packed_value {
            mismatches[domain] += 1;
            first_mismatch.get_or_insert((domain, local));
        }
        local_count += 1;
        Ok(())
    };
    for context in 0..2 {
        let score_author = ScoreReplayAuthor {context, origin: OWNER + 1,
            previous_owner: OWNER - 1, max_owner: CAP_MAX_OWNER, cap_owner: OWNER};
        for local in H21EligibleMapStage::map_live(context)? {
            compare(local, Writer::Map(context), context)?;
        }
        for local in H21EligibleMapStage::score_live(context)? {
            compare(local, Writer::Score(score_author), 2 + context)?;
        }
        for local in H21EligibleMapStage::slack_live(context)? {
            compare(local, Writer::Slack(context), 4 + context)?;
        }
        for local in H21EligibleMapStage::cap_live(context)? {
            compare(local, Writer::Cap(context), 6 + context)?;
        }
    }
    for bit in 0..224 {
        compare(crate::legacy_envelope_map::D_LOCAL + bit, Writer::WorkLocal, 8)?;
    }
    if local_count != 20_704 {
        return Err("C372 local cell domain census".into());
    }
    let mut foreign_count = 0usize;
    for bit in 0..224 {
        let wire = (OWNER - 1) * WIDTH + 987_450 + bit;
        if !matches!(cells.get(&wire), Some((Writer::WorkUpper, _))) {
            return Err(format!("C372 foreign WorkUpper domain/writer bit={bit}"));
        }
        foreign_count += 1;
    }
    for context in 0..2 {
        for bit in 0..225 {
            let wire = (OWNER - 1) * WIDTH + [677_501, 685_693][context] + 1_318 + bit;
            if !matches!(cells.get(&wire), Some((Writer::PreviousR(c), _)) if *c == context) {
                return Err(format!("C372 foreign PreviousR domain/writer context={context} bit={bit}"));
            }
            foreign_count += 1;
        }
    }
    if foreign_count != 674 || cells.len() != local_count + foreign_count {
        return Err("C372 exact local/foreign cell partition".into());
    }
    if mismatches.iter().any(|&count| count != 0) {
        return Err(format!("C372 local semantic X/packed mismatch Map={:?} Score={:?} Slack={:?} Cap={:?} WorkLocal={} first={first_mismatch:?}",
            &mismatches[0..2], &mismatches[2..4], &mismatches[4..6],
            &mismatches[6..8], mismatches[8]));
    }
    Ok((local_count, foreign_count))
}

#[cfg(test)]
mod c373_overlay_source_tests {
    use super::*;

    #[test]
    fn c453_map_view_retains_exact_source_custody_and_imports() {
        let sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let detached = Eligible08OwnerSink::synthetic_map_source_for_test();
        let view = sink.map_source_view_for_test().unwrap();
        let own = view.typed_source_for_test().unwrap();
        let detached_view = detached.map_source_view_for_test().unwrap();
        let detached_lease = detached_view.typed_source_for_test().unwrap();
        assert_eq!(own.binding(), detached_lease.binding());
        assert_eq!(own.entries(), detached_lease.entries());
        view.require_typed_source(&own).unwrap();
        assert!(view.require_typed_source(&detached_lease).unwrap_err().contains("custody"));
        assert!(detached_view.require_typed_source(&own).is_err());
        let unretained = Bank53TypedSourceLease::synthetic_for_test(
            view.binding().clone(), OWNER).unwrap();
        assert!(view.require_typed_source(&unretained).is_err());
        assert_eq!(view.map_cells().count(), 11_514);
        let imports = view.local_imports().collect::<Vec<_>>();
        assert_eq!(imports.len(), 448);
        for (index, &(context, wire, value)) in imports.iter().enumerate() {
            assert_eq!(context, index / 224);
            assert_eq!(wire, OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL + index % 224);
            assert!(!value);
        }
        for context in 0..2 {
            assert_eq!(view.map_binding(context).unwrap(), &sink.binding.maps[context]);
            assert!(std::ptr::eq(view.checked_terms(view.binding(), OWNER,
                crate::daa_history_roster::OwnerClass::Carry, context).unwrap(),
                sink.source.as_ref().unwrap().map_stage.map_terms[context].as_slice()));
        }
        assert!(view.map_binding(2).is_err());
        assert!(view.checked_terms(&view.binding().mutated_field_for_test(0), OWNER,
            crate::daa_history_roster::OwnerClass::Carry, 0).is_err());
    }

    #[test]
    fn c453_map_view_rejects_coordinated_noncanonical_terms() {
        let mut sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        // Mutate both retained source and admitted ROW projection together.
        // Their equality alone cannot authorize caller-reordered Map terms.
        sink.source.as_mut().unwrap().map_stage.map_terms[0].swap(0, 1);
        sink.state.terms.swap(0, 1);
        assert!(sink.map_source_view_for_test().err().unwrap().contains("canonical Map"));
    }

    pub(super) fn admitted_synthetic_source() -> Eligible08OwnerSink {
        admitted_synthetic_source_with(H21EligibleSlackStage::synthetic_owner_sink_source())
    }

    pub(super) fn admitted_synthetic_source_for_c455() -> Eligible08OwnerSink {
        admitted_synthetic_source_with(
            H21EligibleSlackStage::synthetic_owner_sink_source_for_c455())
    }

    fn admitted_synthetic_source_with(mut source: H21EligibleSlackStage) -> Eligible08OwnerSink {
        let maps = H21EligibleMapStage::source_maps().unwrap();
        let descriptor = H21EligibleMapStage::descriptor();
        let mut map_reads = Vec::new();
        for (context, map) in maps.iter().enumerate() {
            source.map_stage.map_terms[context] =
                crate::bank53_map::map_owner_terms_for_descriptor(
                    map, OWNER as u64, context, descriptor).unwrap();
            for import in map.imports(OWNER as u64).unwrap() {
                let author = match import.kind {
                    Kind::Difficulty => RequiredAuthor::WorkDifficulty {
                        owner: import.owner as usize, height: import.owner as usize + 2,
                    },
                    Kind::Timestamp => RequiredAuthor::HeaderTimestamp {
                        owner: import.owner as usize, height: import.owner as usize + 1,
                    },
                };
                for bit in 0..import.width {
                    map_reads.push(PendingRead {consumer: Writer::Map(context),
                        wire: map.input_index(import, bit).unwrap(), author, value: false});
                }
            }
        }
        let map = &source.map_stage;
        let binding = Binding {root: map.parent_root, total: map.parent_total,
            profile: map.parent_profile, cut: map.cut_identity.clone(),
            maps: map.map_bindings.clone()};
        let (cells, rows, reads) = material(&binding, &source, &map_reads).unwrap();
        let lease = Eligible08OwnerLease {binding: binding.clone(), source,
            map_reads, cells, rows, reads};
        let mut sink = Eligible08OwnerSink {binding, state: State::default(),
            custody: std::sync::Arc::new(()), source: None,
            cap_source: None, cap_max_resolution: None, work_source: None,
            upper_source: None, previous_r_source: None};
        sink.admit(lease).unwrap();
        sink
    }

    pub(super) fn expected_zero_d() -> Vec<(usize, Fr)> {
        (0..224).map(|bit| (
            OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL + bit, Fr::zero(),
        )).collect()
    }

    pub(super) fn packed_binding_for_test(sink: &Eligible08OwnerSink) -> HeaderSourceBinding {
        HeaderSourceBinding::from_sink_for_test(sink.binding.root, sink.binding.total,
            sink.binding.profile, sink.binding.cut.clone(), OWNER)
    }

    fn assert_overlay_rejects(sink: &Eligible08OwnerSink, expected_d: &[(usize, Fr)], needle: &str) {
        let binding = packed_binding_for_test(sink);
        match sink.checked_overlay_map_source(expected_d, &binding) {
            Err(error) => assert!(error.contains(needle), "unexpected bounded error: {error}"),
            Ok(_) => panic!("overlay accepted isolated mutant: {needle}"),
        }
    }

    #[test]
    fn c373_source_replay_rejects_independent_cell_and_read_mutants() {
        let mut sink = admitted_synthetic_source();
        let expected_d = expected_zero_d();
        let binding = packed_binding_for_test(&sink);
        assert_eq!(sink.checked_overlay_map_source(&expected_d, &binding).unwrap()
            .entries().len(), CELL_COUNT);
        let first = OWNER * WIDTH + H21EligibleMapStage::map_live(0).unwrap().start;
        let saved = sink.state.cells[&first];
        sink.state.cells.insert(first, (saved.0, !saved.1));
        assert_overlay_rejects(&sink, &expected_d, "author/value replay");
        sink.state.cells.insert(first, (Writer::Header, saved.1));
        assert_overlay_rejects(&sink, &expected_d, "author/value replay");
        sink.state.cells.remove(&first);
        assert_overlay_rejects(&sink, &expected_d, "author/value replay");
        sink.state.cells.insert(first, saved);
        let slack = OWNER * WIDTH + H21EligibleMapStage::slack_live(0).unwrap().start;
        let saved_slack = sink.state.cells[&slack];
        sink.state.cells.insert(slack, (saved_slack.0, true));
        assert_overlay_rejects(&sink, &expected_d, "author/value replay");
        sink.state.cells.insert(slack, saved_slack);
        let mut value = admitted_synthetic_source();
        value.state.read_obligations[0].value ^= true;
        assert_overlay_rejects(&value, &expected_d, "Map read obligation replay");
        let mut wire = admitted_synthetic_source();
        wire.state.read_obligations[0].wire += 1;
        assert_overlay_rejects(&wire, &expected_d, "Map read obligation replay");
        let mut author = admitted_synthetic_source();
        author.state.read_obligations[0].author = RequiredAuthor::WorkDifficulty {
            owner: OWNER + 1, height: OWNER + 3,
        };
        assert_overlay_rejects(&author, &expected_d, "Map read obligation replay");
        let mut consumer = admitted_synthetic_source();
        consumer.state.read_obligations[0].consumer = Writer::Slack(0);
        assert_overlay_rejects(&consumer, &expected_d, "Map read obligation replay");
        let mut context = admitted_synthetic_source();
        context.state.read_obligations[0].consumer = Writer::Map(1);
        assert_overlay_rejects(&context, &expected_d, "Map read obligation replay");
        let mut wrong_d = expected_d.clone();
        wrong_d[0].1 = Fr::one();
        let fresh = admitted_synthetic_source();
        assert_overlay_rejects(&fresh, &wrong_d, "Map read obligation replay");
    }

    #[test]
    fn c373_overlay_binding_rejects_every_field_and_foreign_owner() {
        let sink = admitted_synthetic_source();
        let binding = HeaderSourceBinding::from_sink_for_test(sink.binding.root,
            sink.binding.total, sink.binding.profile, sink.binding.cut.clone(), OWNER);
        let overlay = Eligible08PackedOverlay {binding: binding.clone(), sink: &sink};
        assert!(overlay.checked_cells(&binding, OWNER).unwrap_err()
            .contains("completed sink"));
        for field in 0..6 {
            let wrong = binding.mutated_field_for_test(field);
            assert!(overlay.checked_cells(&wrong, OWNER).unwrap_err().contains("binding"),
                "field {field} escaped overlay binding");
        }
        assert!(overlay.checked_cells(&binding, OWNER + 1).unwrap_err().contains("binding"));
    }
}

#[cfg(test)]
#[path = "h21_eligible_owner_sink_tests.rs"]
mod tests;

#[cfg(test)]
mod c365_foreign_max_tests {
    use super::*;

    fn fixture()->(Eligible08ForeignMaxReadLease,
        crate::packed_owner_assembly::HeaderSourceBinding) {
        let binding=crate::packed_owner_assembly::HeaderSourceBinding::diagnostic_for_test(OWNER);
        let cells=(0..2*CAP_MAX_BITS).map(|index| {
            let context=index/CAP_MAX_BITS;let bit=index%CAP_MAX_BITS;
            Eligible08ForeignMaxCell {wire:CAP_MAX_OWNER*WIDTH+CAP_MAX_BASE[context]+bit,
                context,end:CAP_MAX_OWNER+2,bit,
                author:crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
                    crate::h21_scheduled_max_cap::Writer::Max{context,end:CAP_MAX_OWNER+2}),
                value:bit%2==0}
        }).collect();
        (Eligible08ForeignMaxReadLease{destination:binding.clone(),source_owner:CAP_MAX_OWNER,cells},binding)
    }

    #[test]
    fn c365_synthetic_foreign_max_lease_checks_destination_and_exact_source_order() {
        let (lease,binding)=fixture();
        assert!(lease.require_destination(&binding,OWNER).is_ok());
        for field in 0..6 {
            let wrong_binding=binding.mutated_field_for_test(field);
            assert!(lease.require_destination(&wrong_binding,OWNER).is_err(),
                "destination field mutation {field} accepted");
        }
        assert!(lease.require_destination(&binding,OWNER+1).is_err());

        let mut wrong_owner=fixture().0;wrong_owner.mutate_source_owner_for_test(844_671);
        assert!(wrong_owner.require_destination(&binding,OWNER).is_err());
        let mut wrong_wire=fixture().0;wrong_wire.mutate_first_cell_wire_for_test();
        assert!(wrong_wire.require_destination(&binding,OWNER).is_err());
        let mut wrong_author=fixture().0;wrong_author.mutate_first_cell_author_for_test();
        assert!(wrong_author.require_destination(&binding,OWNER).is_err());
        let mut wrong_order=fixture().0;wrong_order.cells.swap(0,1);
        assert!(wrong_order.require_destination(&binding,OWNER).is_err());
    }
}

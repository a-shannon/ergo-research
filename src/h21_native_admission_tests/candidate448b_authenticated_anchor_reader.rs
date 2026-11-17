//! One authentic owner417790 first-anchor physical producer-to-ROW/X read join.
//! Local and foreign open reads remain obligations; no proof or client is run.

use std::{collections::{BTreeMap, BTreeSet}, io::Write};
use ark_ff::Zero;
use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS},
    header_daa_row_placement::{
        AnchorActiveOperand, AnchorCellAuthor, AnchorLayout, AnchorLocalDomain,
        AnchorRead, AnchorRelation, AnchorSourceKind, OperandSide, Relation, RowPlan,
    },
    h21_scheduled_max_cap::{Plan as Scheduled, Writer},
    packed_owner_assembly::{
        HeaderSourceBinding, MapPairSourceAuthor, NativeHeaderSourceLease,
        NativeOwnerProducer, NativePackedRow, NativePrefix, validate_native_plan_input,
    },
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const N: usize = 1_827_840;
const OWNER: usize = 417_790;
const WIDTH: usize = 1 << 20;
const ROWS: usize = 1 << 19;
const BANK53_BASE: usize = 671_744;
const BANK53_BITS: usize = 16_384;
const CONTEXT_BITS: usize = 8_192;
const MAP_BITS: usize = 5_757;
const SCORE_BITS: usize = 2_048;
const SLACK_BITS: usize = 387;

fn packed_bit(row: &NativePackedRow, wire: usize) -> Result<bool, String> {
    let local = wire.checked_sub(OWNER * WIDTH).filter(|local| *local < WIDTH)
        .ok_or("C448b packed read owner")?;
    if row.owner() != OWNER || row.packed_bytes().len() != WIDTH / 8 {
        return Err("C448b packed row identity/width".into());
    }
    Ok((row.packed_bytes()[local / 8] >> (local % 8)) & 1 != 0)
}

fn relation_slot(relation: AnchorRelation) -> Result<usize, String> {
    match relation {
        AnchorRelation::Ordinary(Relation::Header) => Ok(0),
        AnchorRelation::Ordinary(Relation::DaaLane(lane)) if lane < 4 => Ok(1 + lane),
        AnchorRelation::Ordinary(Relation::Scheduled(Writer::Max {context, end}))
            if context < 2 && end == OWNER + 2 => Ok(5 + context),
        AnchorRelation::Ordinary(Relation::Scheduled(Writer::Cap {context, origin}))
            if context < 2 && origin == OWNER + 1 => Ok(7 + context),
        AnchorRelation::Map(context) if context < 2 => Ok(9 + context),
        AnchorRelation::ScoreAnchor(context) if context < 2 => Ok(11 + context),
        AnchorRelation::Slack(context) if context < 2 => Ok(13 + context),
        _ => Err("C448b unexpected relation in 15-slot census".into()),
    }
}

fn source_kind_index(kind: AnchorSourceKind) -> usize {
    match kind {
        AnchorSourceKind::Header => 0, AnchorSourceKind::Tree => 1,
        AnchorSourceKind::Daa => 2, AnchorSourceKind::WorkUpper => 3,
        AnchorSourceKind::WorkD => 4, AnchorSourceKind::Unqualified => 5,
    }
}

fn expected_source(operand: AnchorActiveOperand, imports: &BTreeMap<usize, AnchorSourceKind>)
    -> AnchorSourceKind
{
    let wire = operand.wire;
    if operand.relation == AnchorRelation::Ordinary(Relation::DaaLane(2))
        && [OWNER - 1, OWNER - 2].contains(&(wire / WIDTH))
        && (987_674..987_898).contains(&(wire % WIDTH))
    {
        return AnchorSourceKind::WorkD;
    }
    imports.get(&wire).copied().unwrap_or_else(|| {
        if wire / WIDTH == OWNER - 1 && (987_450..987_674).contains(&(wire % WIDTH)) {
            AnchorSourceKind::WorkUpper
        } else { AnchorSourceKind::Unqualified }
    })
}

#[derive(Default)]
struct ReadCensus {
    bank53: [usize; 6], header: usize, open_local: [usize; 3], open_foreign: [usize; 6],
}
impl ReadCensus {
    fn total(&self) -> usize {
        self.bank53.iter().sum::<usize>() + self.header
            + self.open_local.iter().sum::<usize>() + self.open_foreign.iter().sum::<usize>()
    }
    fn check(&mut self, read: &AnchorRead, operand: AnchorActiveOperand,
        row: &NativePackedRow, binding: &HeaderSourceBinding, header: &NativeHeaderSourceLease,
        cells: &BTreeMap<usize, (AnchorCellAuthor, bool)>,
        imports: &BTreeMap<usize, AnchorSourceKind>,
    ) -> Result<(), String> {
        if read.operand() != operand {
            return Err("C448b exact canonical occurrence/relation/ROW/side/wire/flags".into());
        }
        match *read {
            AnchorRead::Bank53 {author, value, ..} => {
                if cells.get(&operand.wire) != Some(&(author, value))
                    || packed_bit(row, operand.wire)? != value
                    || header.read_header_bit(binding, operand.wire)?.is_some()
                {
                    return Err("C448b typed Bank53 source/author/packed equality".into());
                }
                let index = match author {
                    AnchorCellAuthor::Map(c) if c < 2 => c,
                    AnchorCellAuthor::ScoreAnchor(c) if c < 2 => 2 + c,
                    AnchorCellAuthor::Slack(c) if c < 2 => 4 + c,
                    _ => return Err("C448b Bank53 read context".into()),
                };
                self.bank53[index] += 1;
            },
            AnchorRead::Header {value, ..} => {
                if cells.contains_key(&operand.wire)
                    || header.read_header_bit(binding, operand.wire)? != Some(value)
                    || packed_bit(row, operand.wire)? != value
                {
                    return Err("C448b native HEADER source/author/packed equality".into());
                }
                self.header += 1;
            },
            AnchorRead::OpenLocal {domain, expected, ..} => {
                if operand.wire / WIDTH != OWNER || cells.contains_key(&operand.wire)
                    || header.read_header_bit(binding, operand.wire)?.is_some()
                {
                    return Err("C448b open local read gained a resolved local source".into());
                }
                let imported = expected_source(operand, imports);
                let (wanted_domain, wanted_kind, index) =
                    if BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&(operand.wire % WIDTH))) {
                        (AnchorLocalDomain::Daa, AnchorSourceKind::Daa, 0)
                    } else if imported == AnchorSourceKind::Tree {
                        (AnchorLocalDomain::Tree, AnchorSourceKind::Tree, 1)
                    } else { (AnchorLocalDomain::Unqualified, imported, 2) };
                if domain != wanted_domain || expected != wanted_kind {
                    return Err("C448b open local domain/expected source".into());
                }
                self.open_local[index] += 1;
            },
            AnchorRead::OpenForeign {source_owner, expected, ..} => {
                if source_owner == OWNER || source_owner != operand.wire / WIDTH
                    || expected != expected_source(operand, imports)
                {
                    return Err("C448b foreign owner/relation/expected source".into());
                }
                self.open_foreign[source_kind_index(expected)] += 1;
            },
        }
        Ok(())
    }
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed single-process bounded Job required"]
fn c448_authenticated_owner417790_anchor_row_x() -> Result<(), String> {
    let path = std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path = std::path::Path::new(&path);
    if !path.is_absolute() { return Err("C448b H21 frame path must be absolute".into()); }
    let before = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != super::FRAME_BYTES {
        return Err("C448b pinned H21 frame regular-file/length preflight".into());
    }
    let file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    if file.metadata().map_err(|e| e.to_string())?.len() != super::FRAME_BYTES {
        return Err("C448b opened H21 frame length".into());
    }
    let mut frame = super::FrameReader::new(
        std::io::BufReader::with_capacity(super::CHUNK, file), super::FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 { return Err("C448b H21 frame RAW records incomplete".into()); }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != super::PREFIX_BYTES
        || extensions != super::EXTENSIONS
    {
        return Err("C448b H21 frame prefix/extension census".into());
    }
    // This completes the one frame parse and hashes every retained frame byte.
    frame.finish(super::PREFIX_BYTES, super::TAIL_BYTES, super::FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(N as u64, 21, prefix.root(), prefix.total_be28())?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    let scheduled = Scheduled::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let context = crate::packed_owner_assembly::H21EligibleContext::new(&plan, &prefix)?;
    let class = roster.owner_class(OWNER as u64)?;
    if class != OwnerClass::Carry { return Err("C448b owner417790 is not Carry".into()); }
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER)?;

    // Build once. Its existing checked predecessor owner417789 LOCAL is retained.
    let bundle = context.map_pair_slack_anchor_bundle(OWNER)?;
    let map = bundle.map_slack().map_lease().checked_cells(&binding, OWNER, class)?;
    let score = bundle.checked_score_cells(&binding, OWNER, class)?;
    let slack = bundle.map_slack().checked_slack_cells(&binding, OWNER, class)?;
    if map.len() != 2 * MAP_BITS || score.len() != 2 * SCORE_BITS
        || slack.len() != 2 * SLACK_BITS
    {
        return Err("C448b complete typed two-context source census".into());
    }
    let mut bank_terms = [0usize; 6];
    for c in 0..2 {
        bank_terms[c] = bundle.map_slack().map_lease().terms(c)?.len();
        bank_terms[2 + c] = bundle.checked_score_terms(&binding, OWNER, class, c)?.len();
        bank_terms[4 + c] = bundle.map_slack().checked_slack_terms(&binding, OWNER, class, c)?.len();
    }
    if bank_terms[..2] != [7_579, 7_579] || bank_terms[2..4].contains(&0)
        || bank_terms[4..] != [SLACK_BITS, SLACK_BITS]
    {
        return Err("C448b exact Map/ScoreAnchor/Slack term census".into());
    }
    let mut cells = BTreeMap::new();
    for (index, cell) in map.iter().enumerate() {
        if cell.context() != index / MAP_BITS || cell.offset() != index % MAP_BITS {
            return Err("C448b checked Map context/offset".into());
        }
        if cells.insert(cell.physical_wire(), (AnchorCellAuthor::Map(cell.context()), cell.value())).is_some() {
            return Err("C448b duplicate typed Map physical cell".into());
        }
    }
    for (index, cell) in score.iter().enumerate() {
        if cell.context() != index / SCORE_BITS
            || cells.insert(cell.physical_wire(), (AnchorCellAuthor::ScoreAnchor(cell.context()), cell.value())).is_some()
        {
            return Err("C448b typed ScoreAnchor context/duplicate".into());
        }
    }
    for (index, cell) in slack.iter().enumerate() {
        if cell.context() != index / SLACK_BITS || cell.value()
            || cells.insert(cell.physical_wire(), (AnchorCellAuthor::Slack(cell.context()), cell.value())).is_some()
        {
            return Err("C448b typed Slack context/zero/duplicate".into());
        }
    }
    let mut imports = BTreeMap::new();
    for import in bundle.map_slack().map_lease().imports() {
        let kind = match import.author() {
            MapPairSourceAuthor::Header => AnchorSourceKind::Header,
            MapPairSourceAuthor::Tree => AnchorSourceKind::Tree,
        };
        if imports.insert(import.physical_wire(), kind).is_some_and(|old| old != kind) {
            return Err("C448b conflicting checked imported source authors".into());
        }
    }

    // Exactly one destination packed production; HEADER is a lease from this producer.
    let packed = producer.produce_first_anchor_packed_receipt(OWNER, &bundle)?;
    let header = producer.header_source_lease(OWNER)?;
    header.check_binding(&binding)?;
    header.check_author()?;
    if packed.binding() != &binding || !std::ptr::eq(packed.bundle(), &bundle)
        || packed.row().class() != class || cells.len() != BANK53_BITS
    {
        return Err("C448b native receipt exact source/owner/class/partition".into());
    }
    for (index, (&wire, &(author, value))) in cells.iter().enumerate() {
        let c = index / CONTEXT_BITS;
        let offset = index % CONTEXT_BITS;
        let wanted_author = if offset < MAP_BITS { AnchorCellAuthor::Map(c) }
            else if offset < MAP_BITS + SCORE_BITS { AnchorCellAuthor::ScoreAnchor(c) }
            else { AnchorCellAuthor::Slack(c) };
        if wire != OWNER * WIDTH + BANK53_BASE + index || author != wanted_author
            || packed_bit(packed.row(), wire)? != value
            || header.read_header_bit(&binding, wire)?.is_some()
        {
            return Err("C448b complete typed physical source/author/packed partition".into());
        }
    }
    let stage = row_plan.stage_owner_with_anchor_reads(OWNER, &packed, Some(&header))?;
    if !std::ptr::eq(stage.packed(), packed.row()) || stage.batch().owner() != OWNER
        || stage.batch().class() != class || stage.batch().source_binding() != &binding
        || stage.batch().layout_digest() != AnchorLayout::digest()
    {
        return Err("C448b native read stage exact retained receipt/ROW identity".into());
    }

    // Independently enumerate gates before operand filtering: constants advance
    // ordinals, repeated operands remain occurrences, and c3 emits left then right.
    let read_count = stage.reads().len();
    let mut reads = stage.reads();
    let mut census = ReadCensus::default();
    let mut terms = [0usize; 15];
    let mut placed_rows = BTreeSet::new();
    let mut bank_slot = 0;
    for (occurrence, (relation, term)) in stage.batch().terms().enumerate() {
        let slot = relation_slot(relation)?;
        if slot >= 9 {
            if slot < bank_slot { return Err("C448b canonical Bank53 family traversal".into()); }
            bank_slot = slot;
        } else if bank_slot != 0 { return Err("C448b ordinary terms after Bank53".into()); }
        terms[slot] += 1;
        if !(OWNER * ROWS..(OWNER + 1) * ROWS).contains(&term.row) {
            return Err("C448b canonical placed ROW owner".into());
        }
        placed_rows.insert(term.row);
        let gate = &term.gate;
        let c1 = !gate.c1.is_zero();
        let c2 = !gate.c2.is_zero();
        let c3 = !gate.c3.is_zero();
        for (active, side, wire, c1_active, c2_active) in [
            (c1 || c3, OperandSide::Left, gate.left, c1, false),
            (c2 || c3, OperandSide::Right, gate.right, false, c2),
        ] {
            if !active { continue; }
            let operand = AnchorActiveOperand {occurrence, relation, row: term.row, side, wire,
                c1_active, c2_active, c3_active: c3};
            let read = reads.next().ok_or("C448b omitted canonical active read")?;
            census.check(read, operand, stage.packed(), &binding, &header, &cells, &imports)?;
        }
    }
    if reads.next().is_some() || census.total() != read_count || read_count == 0
        || terms[5..9] != [0; 4] || terms[9..] != bank_terms || census.open_foreign[4] == 0
        || stage.registry().distinct_rows() != placed_rows.len() || placed_rows.is_empty()
    {
        return Err("C448b exact canonical read/15-slot/atomic registry census".into());
    }

    let after = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !after.is_file() || after.file_type().is_symlink() || after.len() != super::FRAME_BYTES {
        return Err("C448b pinned H21 frame post-read regular-file/length".into());
    }
    let after_file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    if after_file.metadata().map_err(|e| e.to_string())?.len() != super::FRAME_BYTES {
        return Err("C448b opened post-read H21 frame length".into());
    }
    // Hash-only identity check; this does not parse a second frame.
    let after_frame = super::FrameReader::new(
        std::io::BufReader::with_capacity(super::CHUNK, after_file), super::FRAME_BYTES,
    )?;
    after_frame.finish(0, super::FRAME_BYTES, super::FRAME_SHA256)?;
    println!("C448B_AUTHENTIC_READ_CENSUS owner=417790 terms={} rows={} reads={} bank53_map0={} bank53_map1={} bank53_score0={} bank53_score1={} bank53_slack0={} bank53_slack1={} header={} open_local={} open_local_daa={} open_local_tree={} open_local_unqualified={} open_foreign={} foreign_header={} foreign_tree={} foreign_daa={} foreign_work_upper={} foreign_work_d={} foreign_unqualified={} frame_bytes_before={} frame_sha256_before={} frame_bytes_after={} frame_sha256_after={}",
        terms.iter().sum::<usize>(), placed_rows.len(), read_count,
        census.bank53[0], census.bank53[1], census.bank53[2], census.bank53[3],
        census.bank53[4], census.bank53[5], census.header, census.open_local.iter().sum::<usize>(),
        census.open_local[0], census.open_local[1], census.open_local[2],
        census.open_foreign.iter().sum::<usize>(), census.open_foreign[0], census.open_foreign[1],
        census.open_foreign[2], census.open_foreign[3], census.open_foreign[4], census.open_foreign[5],
        before.len(), super::FRAME_SHA256, after.len(), super::FRAME_SHA256);
    println!("C448B_AUTHENTIC_FIRST_ANCHOR_ROW_X_PASS owner=417790 relations=15 bank53_cells=16384 source_author_packed_equal=true open_reads_recorded=true proof=false client=false");
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

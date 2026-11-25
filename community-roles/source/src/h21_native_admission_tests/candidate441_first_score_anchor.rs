//! C441 authentic first premodern Score anchor on the selected Bank53 path.
//! One retained H21 context authenticates owner0 C440 and owner417790 C441.

use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    packed_owner_assembly::{
        HeaderSourceBinding, NativeOwnerProducer, NativePackedRow, NativePrefix,
        validate_native_plan_input,
    },
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const N: usize = 1_827_840;
const OWNER_BITS: usize = 1 << 20;
const OWNER_BYTES: usize = OWNER_BITS / 8;
const BANK53_BASE: usize = 671_744;
const BANK53_BITS: usize = 16_384;
const MAP_LIVE_BITS: usize = 5_757;
const SCORE_BITS_PER_CONTEXT: usize = 2_048;
const SLACK_BITS_PER_CONTEXT: usize = 387;

fn packed_bit(row: &NativePackedRow, local: usize) -> bool {
    row.packed_bytes()[local / 8] & (1 << (local % 8)) != 0
}

fn compare_typed_cells(
    row: &NativePackedRow,
    owner: usize,
    cells: impl IntoIterator<Item = (usize, bool)>,
    expected_count: usize,
    label: &str,
) -> Result<std::collections::BTreeSet<usize>, String> {
    if row.owner() != owner || row.packed_bytes().len() != OWNER_BYTES {
        return Err(format!("{label} packed row identity/size"));
    }
    let base = owner.checked_mul(OWNER_BITS).ok_or("C441 physical owner base overflow")?;
    let mut seen = std::collections::BTreeSet::new();
    for (wire, value) in cells {
        let local = wire.checked_sub(base).ok_or_else(|| format!("{label} source wire before owner"))?;
        if local >= OWNER_BITS || !seen.insert(local) || packed_bit(row, local) != value {
            return Err(format!("{label} typed source/packed mismatch local={local}"));
        }
    }
    if seen.len() != expected_count {
        return Err(format!("{label} typed cell census {} != {expected_count}", seen.len()));
    }
    Ok(seen)
}

fn require_continuity(
    ordinary: &NativePackedRow,
    admitted: &NativePackedRow,
    owner: usize,
    admitted_cells: &std::collections::BTreeSet<usize>,
    label: &str,
) -> Result<(), String> {
    for local in 0..OWNER_BITS {
        if !admitted_cells.contains(&local)
            && packed_bit(ordinary, local) != packed_bit(admitted, local)
        {
            return Err(format!("{label} changed outside typed source local={local}"));
        }
    }
    if ordinary.owner() != owner || admitted.owner() != owner {
        return Err(format!("{label} ordinary/admitted owner mismatch"));
    }
    Ok(())
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed single-process bounded Job required"]
fn c441_authenticated_owner417790_first_score_anchor() -> Result<(), String> {
    let path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("pinned H21 frame path required")?;
    let path = std::path::Path::new(&path);
    if !path.is_absolute() {
        return Err("C441 H21 frame path must be absolute".into());
    }
    let before = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != super::FRAME_BYTES {
        return Err("C441 pinned H21 frame regular-file/length preflight".into());
    }
    let file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    if file.metadata().map_err(|e| e.to_string())?.len() != super::FRAME_BYTES {
        return Err("C441 opened H21 frame length".into());
    }
    let mut frame = super::FrameReader::new(
        std::io::BufReader::with_capacity(super::CHUNK, file), super::FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C441 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != super::PREFIX_BYTES
        || extensions != super::EXTENSIONS
    {
        return Err("C441 H21 frame prefix/extension census".into());
    }
    frame.finish(super::PREFIX_BYTES, super::TAIL_BYTES, super::FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, 21, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let context = crate::packed_owner_assembly::H21EligibleContext::new(&plan, &prefix)?;

    // C440 owner0: one exact Map+Slack bundle and packed producer.
    let owner0 = 0usize;
    let class0 = roster.owner_class(owner0 as u64)?;
    let binding0 = HeaderSourceBinding::for_plan(&plan, owner0)?;
    let c440 = context.map_pair_slack_bundle(owner0)?;
    let map0 = c440.map_lease().checked_cells(&binding0, owner0, class0)?;
    let slack0 = c440.checked_slack_cells(&binding0, owner0, class0)?;
    if map0.len() != 2 * MAP_LIVE_BITS || slack0.len() != 2 * SLACK_BITS_PER_CONTEXT {
        return Err("C441 C440 owner0 Map/Slack typed source census".into());
    }
    for context_index in 0..2 {
        let _ = c440.map_lease().terms(context_index)?;
        let _ = c440.checked_slack_terms(&binding0, owner0, class0, context_index)?;
    }
    if c440.checked_slack_cells(&binding0, owner0 + 1, class0).is_ok()
        || c440.checked_slack_cells(&binding0, owner0, OwnerClass::Carry).is_ok()
    {
        return Err("C441 C440 owner0 accepted wrong owner/class".into());
    }
    let c440_row = producer.produce_with_map_slack_bundle(owner0, &c440)?;
    let c440_ordinary = producer.produce(owner0)?;
    let c440_seen = compare_typed_cells(
        &c440_row,
        owner0,
        map0.iter().map(|cell| (cell.physical_wire(), cell.value()))
            .chain(slack0.iter().map(|cell| (cell.physical_wire(), cell.value()))),
        2 * (MAP_LIVE_BITS + SLACK_BITS_PER_CONTEXT),
        "C440 owner0 Map+Slack",
    )?;
    require_continuity(&c440_ordinary, &c440_row, owner0, &c440_seen, "C440 owner0")?;

    // C441 owner417790: both Score anchors consume the same retained Map stage.
    let owner = 417_790usize;
    let class = roster.owner_class(owner as u64)?;
    if class != OwnerClass::Carry {
        return Err("C441 owner417790 is not Carry".into());
    }
    let binding = HeaderSourceBinding::for_plan(&plan, owner)?;
    let c441 = context.map_pair_slack_anchor_bundle(owner)?;
    let map = c441.map_slack().map_lease().checked_cells(&binding, owner, class)?;
    let slack = c441.map_slack().checked_slack_cells(&binding, owner, class)?;
    let score = c441.checked_score_cells(&binding, owner, class)?;
    if map.len() != 2 * MAP_LIVE_BITS
        || slack.len() != 2 * SLACK_BITS_PER_CONTEXT
        || score.len() != 2 * SCORE_BITS_PER_CONTEXT
    {
        return Err("C441 owner417790 Map/Score/Slack source census".into());
    }
    for context_index in 0..2 {
        let _ = c441.map_slack().map_lease().terms(context_index)?;
        let _ = c441.map_slack().checked_slack_terms(&binding, owner, class, context_index)?;
        let score_terms = c441.checked_score_terms(&binding, owner, class, context_index)?;
        if score_terms.is_empty() {
            return Err(format!("C441 Score{context_index} ordered terms empty"));
        }
    }
    if c441.checked_score_cells(&binding, owner + 1, class).is_ok()
        || c441.checked_score_cells(&binding, owner, OwnerClass::M1).is_ok()
    {
        return Err("C441 owner417790 accepted wrong owner/class".into());
    }
    let c441_row = producer.produce_with_map_slack_anchor_bundle(owner, &c441)?;
    let c441_ordinary = producer.produce(owner)?;
    let cells = map.iter().map(|cell| (cell.physical_wire(), cell.value()))
        .chain(score.iter().map(|cell| (cell.physical_wire(), cell.value())))
        .chain(slack.iter().map(|cell| (cell.physical_wire(), cell.value())));
    let c441_seen = compare_typed_cells(
        &c441_row, owner, cells,
        2 * (MAP_LIVE_BITS + SCORE_BITS_PER_CONTEXT + SLACK_BITS_PER_CONTEXT),
        "C441 owner417790 Map+Score+Slack",
    )?;
    if c441_seen.len() != BANK53_BITS
        || c441_seen.iter().copied().ne(BANK53_BASE..BANK53_BASE + BANK53_BITS)
    {
        return Err("C441 owner417790 typed cells do not exactly cover Bank53".into());
    }
    require_continuity(&c441_ordinary, &c441_row, owner, &c441_seen, "C441 owner417790")?;

    let after = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !after.is_file() || after.file_type().is_symlink() || after.len() != super::FRAME_BYTES {
        return Err("C441 pinned H21 frame post-production file preflight".into());
    }
    let after_file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    if after_file.metadata().map_err(|e| e.to_string())?.len() != super::FRAME_BYTES {
        return Err("C441 opened post-production H21 frame length".into());
    }
    let after_frame = super::FrameReader::new(
        std::io::BufReader::with_capacity(super::CHUNK, after_file), super::FRAME_BYTES,
    )?;
    after_frame.finish(0, super::FRAME_BYTES, super::FRAME_SHA256)?;
    println!("C441_AUTHENTIC_FIRST_SCORE_ANCHOR_PASS c440_owner=0 c441_owner=417790 contexts=2 anchor_bits=4096 bank53_cells=16384 source_cells_match=true proof=false client=false");
    Ok(())
}

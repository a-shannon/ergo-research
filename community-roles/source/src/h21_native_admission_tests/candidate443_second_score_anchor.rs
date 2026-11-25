//! C443 authentic second premodern Score anchor on the selected Bank53 path.
//! One parsed H21 prefix and retained context produce both physical anchors.

use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    packed_owner_assembly::{
        Eligible08MapSlackSecondAnchorBundle, HeaderSourceBinding,
        NativeOwnerProducer, NativePackedRow, NativePrefix,
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
    let base = owner.checked_mul(OWNER_BITS).ok_or("C443 physical owner base overflow")?;
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

fn reject_second_source(
    bundle: &Eligible08MapSlackSecondAnchorBundle,
    binding: &HeaderSourceBinding, owner: usize, class: OwnerClass,
    expected_error: &str, label: &str,
) -> Result<(), String> {
    match bundle.checked_score_cells(binding, owner, class) {
        Ok(_) => Err(format!("C443 {label} unexpectedly accepted")),
        Err(error) if error.contains(expected_error) => Ok(()),
        Err(error) => Err(format!("C443 {label} rejected at wrong gate: {error}")),
    }
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed single-process bounded Job required"]
fn c443_authenticated_owner845758_second_score_anchor() -> Result<(), String> {
    let path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("pinned H21 frame path required")?;
    let path = std::path::Path::new(&path);
    if !path.is_absolute() {
        return Err("C443 H21 frame path must be absolute".into());
    }
    let before = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != super::FRAME_BYTES {
        return Err("C443 pinned H21 frame regular-file/length preflight".into());
    }
    let file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    if file.metadata().map_err(|e| e.to_string())?.len() != super::FRAME_BYTES {
        return Err("C443 opened H21 frame length".into());
    }
    let mut frame = super::FrameReader::new(
        std::io::BufReader::with_capacity(super::CHUNK, file), super::FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C443 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != super::PREFIX_BYTES
        || extensions != super::EXTENSIONS
    {
        return Err("C443 H21 frame prefix/extension census".into());
    }
    frame.finish(super::PREFIX_BYTES, super::TAIL_BYTES, super::FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, 21, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let context = crate::packed_owner_assembly::H21EligibleContext::new(&plan, &prefix)?;
    let premodern = context.premodern_r_publication(context.premodern_score_anchors()?)?;

    // C441 owner417790: produce the authenticated first anchor from the same
    // retained context and preserve its packed row for C443 predecessor checks.
    let first_owner = 417_790usize;
    let first_class = roster.owner_class(first_owner as u64)?;
    if first_class != OwnerClass::Carry {
        return Err("C443 first owner417790 is not Carry".into());
    }
    let first_binding = HeaderSourceBinding::for_plan(&plan, first_owner)?;
    let first_bundle = context.map_pair_slack_anchor_bundle(first_owner)?;
    let first_map = first_bundle.map_slack().map_lease()
        .checked_cells(&first_binding, first_owner, first_class)?;
    let first_slack = first_bundle.map_slack()
        .checked_slack_cells(&first_binding, first_owner, first_class)?;
    let first_score = first_bundle.checked_score_cells(&first_binding, first_owner, first_class)?;
    if first_map.len() != 2 * MAP_LIVE_BITS
        || first_slack.len() != 2 * SLACK_BITS_PER_CONTEXT
        || first_score.len() != 2 * SCORE_BITS_PER_CONTEXT
    {
        return Err("C443 first owner417790 Map/Score/Slack source census".into());
    }
    for context_index in 0..2 {
        let _ = first_bundle.map_slack().map_lease().terms(context_index)?;
        let _ = first_bundle.map_slack()
            .checked_slack_terms(&first_binding, first_owner, first_class, context_index)?;
        if first_bundle.checked_score_terms(&first_binding, first_owner, first_class, context_index)?.is_empty() {
            return Err(format!("C443 first Score{context_index} ordered terms empty"));
        }
    }
    let first_row = producer.produce_with_map_slack_anchor_bundle(first_owner, &first_bundle)?;
    let first_ordinary = producer.produce(first_owner)?;
    let first_cells = first_map.iter().map(|cell| (cell.physical_wire(), cell.value()))
        .chain(first_score.iter().map(|cell| (cell.physical_wire(), cell.value())))
        .chain(first_slack.iter().map(|cell| (cell.physical_wire(), cell.value())));
    let first_seen = compare_typed_cells(
        &first_row, first_owner, first_cells,
        2 * (MAP_LIVE_BITS + SCORE_BITS_PER_CONTEXT + SLACK_BITS_PER_CONTEXT),
        "C443 first owner417790 Map+Score+Slack",
    )?;
    if first_seen.len() != BANK53_BITS
        || first_seen.iter().copied().ne(BANK53_BASE..BANK53_BASE + BANK53_BITS)
    {
        return Err("C443 first owner417790 typed cells do not exactly cover Bank53".into());
    }
    require_continuity(&first_ordinary, &first_row, first_owner, &first_seen, "C443 first owner")?;

    // C443 owner845758: the second bundle consumes the first packed owner and
    // the exact premodern R publication retained by this context.
    let owner = 845_758usize;
    let class = roster.owner_class(owner as u64)?;
    if class != OwnerClass::Carry {
        return Err("C443 owner845758 is not Carry".into());
    }
    let binding = HeaderSourceBinding::for_plan(&plan, owner)?;
    let second_bundle = context.map_pair_slack_second_anchor_bundle(
        owner, &first_bundle, &premodern,
    )?;
    let map = second_bundle.map_slack().map_lease().checked_cells(&binding, owner, class)?;
    let slack = second_bundle.map_slack().checked_slack_cells(&binding, owner, class)?;
    let score = second_bundle.checked_score_cells(&binding, owner, class)?;
    if map.len() != 2 * MAP_LIVE_BITS
        || slack.len() != 2 * SLACK_BITS_PER_CONTEXT
        || score.len() != 2 * SCORE_BITS_PER_CONTEXT
    {
        return Err("C443 owner845758 Map/Score/Slack source census".into());
    }
    for context_index in 0..2 {
        let _ = second_bundle.map_slack().map_lease().terms(context_index)?;
        let _ = second_bundle.map_slack()
            .checked_slack_terms(&binding, owner, class, context_index)?;
        if second_bundle.checked_score_terms(&binding, owner, class, context_index)?.is_empty() {
            return Err(format!("C443 second Score{context_index} ordered terms empty"));
        }
    }
    second_bundle.checked_predecessor_packed(&first_row)?;

    // A one-bit corruption of the first packed Score/R source is rejected
    // before the second physical producer is entered.
    let mut mutated_bytes = first_row.packed_bytes().to_vec();
    let changed_local = BANK53_BASE + MAP_LIVE_BITS
        + crate::origin_score::Layout::new().r.start;
    if !first_score.iter().any(|cell|
        cell.physical_wire() == first_owner * OWNER_BITS + changed_local) {
        return Err("C443 predecessor mutation target is not first R".into());
    }
    mutated_bytes[changed_local / 8] ^= 1 << (changed_local % 8);
    let mutated_first = first_row.with_packed_bytes_for_test(&mutated_bytes)?;
    if second_bundle.checked_predecessor_packed(&mutated_first).is_ok() {
        return Err("C443 first packed R bit mutation unexpectedly admitted".into());
    }
    match producer.produce_with_map_slack_second_anchor_bundle(
        owner, &second_bundle, &mutated_first,
    ) {
        Ok(_) => return Err("C443 physical second writer accepted changed first packed R".into()),
        Err(error) if error.contains("predecessor packed Score mismatch") => (),
        Err(error) => return Err(format!("C443 predecessor bit rejected at wrong gate: {error}")),
    }

    // Each native-source mutant changes one obligation while the valid
    // publication, first row and other source fields stay fixed.
    let mut bad = second_bundle.clone();
    bad.flip_first_r_lease_for_test(0)?;
    reject_second_source(&bad, &binding, owner, class, "R450", "first R lease bit")?;

    for kind in 0..2 {
        let mut bad = second_bundle.clone();
        bad.mutate_second_upper_for_test(kind)?;
        let gate = if kind == 0 { "R450" } else { "Work Upper" };
        reject_second_source(&bad, &binding, owner, class, gate,
            if kind == 0 { "second Upper bit" } else { "second Upper owner" })?;
    }

    let mut bad = second_bundle.clone();
    let missing_local = bad.remove_zero_second_score_for_test(0)?;
    if !(BANK53_BASE + MAP_LIVE_BITS..BANK53_BASE + MAP_LIVE_BITS + SCORE_BITS_PER_CONTEXT)
        .contains(&missing_local) {
        return Err("C443 removed zero is outside Score0".into());
    }
    reject_second_source(&bad, &binding, owner, class, "R450", "missing zero Score claim")?;

    let mut bad = second_bundle.clone();
    bad.swap_second_score_terms_for_test(1)?;
    reject_second_source(&bad, &binding, owner, class, "R450", "second Score term order")?;

    for kind in 0..3 {
        let mut bad = second_bundle.clone();
        bad.mutate_second_binding_for_test(kind)?;
        reject_second_source(&bad, &binding, owner, class, "R450",
            ["second R profile", "second R context", "second R Map binding"][kind])?;
    }
    if second_bundle.checked_score_cells(&binding, owner - 1, class).is_ok()
        || second_bundle.checked_score_cells(&binding, owner + 1, class).is_ok()
        || second_bundle.checked_score_cells(&binding, owner, OwnerClass::M1).is_ok() {
        return Err("C443 second source accepted wrong owner/class".into());
    }
    match producer.produce_with_map_slack_second_anchor_bundle(
        owner - 1, &second_bundle, &first_row,
    ) {
        Ok(_) => return Err("C443 physical second writer accepted owner845757".into()),
        Err(error) if error.contains("requires Carry owner845758") => (),
        Err(error) => return Err(format!("C443 owner845757 rejected at wrong gate: {error}")),
    }

    let second_row = producer.produce_with_map_slack_second_anchor_bundle(
        owner, &second_bundle, &first_row,
    )?;
    let ordinary = producer.produce(owner)?;
    let cells = map.iter().map(|cell| (cell.physical_wire(), cell.value()))
        .chain(score.iter().map(|cell| (cell.physical_wire(), cell.value())))
        .chain(slack.iter().map(|cell| (cell.physical_wire(), cell.value())));
    let seen = compare_typed_cells(
        &second_row, owner, cells,
        2 * (MAP_LIVE_BITS + SCORE_BITS_PER_CONTEXT + SLACK_BITS_PER_CONTEXT),
        "C443 owner845758 Map+Score+Slack",
    )?;
    if seen.len() != BANK53_BITS || seen.iter().copied().ne(BANK53_BASE..BANK53_BASE + BANK53_BITS) {
        return Err("C443 owner845758 typed cells do not exactly cover Bank53".into());
    }
    require_continuity(&ordinary, &second_row, owner, &seen, "C443 owner845758")?;

    println!("C443_AUTHENTIC_SECOND_ANCHOR_PASS first_owner=417790 second_owner=845758 contexts=2 anchor_bits=4096 bank53_cells=16384 source_cells_match=true first_r_flip_rejected_before_second=true native_source_mutants=8 frame_parsed_once=true proof=false client=false");
    Ok(())
}

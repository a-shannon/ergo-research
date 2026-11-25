//! Selected-owner Map/HEADER-zero and multi-class FullZero DAA source/ROW tests.

use super::*;
use std::{
    fs::{self, File, OpenOptions},
    io::{BufReader, Read, Seek, SeekFrom},
    os::windows::fs::OpenOptionsExt,
};
use crate::{
    bank53_required_writer::{required_bank53_writer, RequiredWriter},
    daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS, WIDTH},
    header_daa_row_placement::{
        ActiveOperand, C503Bank53Author, C503EarlyCarryMapHeaderRow, OperandSide, Producer,
        Relation, RowPlan,
    },
    packed_owner_assembly::{
        HeaderSourceBinding, H21EligibleContext, NativeMixedMapHeaderRow, NativeOwnerProducer,
    },
};

const OWNER: usize = 845_760;
const CONTEXTS: usize = 2;
const CONTEXT_BITS: usize = 8_192;
const MAP_BITS: usize = 5_757;
const BANK53_BASE: usize = 671_744;
const EXPECTED_CELLS: usize = CONTEXTS * CONTEXT_BITS;
const EXPECTED_MAP: usize = CONTEXTS * MAP_BITS;
const EXPECTED_HEADER_ZERO: usize = CONTEXTS * (CONTEXT_BITS - MAP_BITS);

fn hash_same_handle(file: &mut File) -> Result<(u64, String), String> {
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
    let mut hash = super::Sha256Stream::new()?;
    let mut buffer = vec![0u8; CHUNK];
    let mut bytes = 0u64;
    loop {
        let count = file.read(&mut buffer).map_err(|error| error.to_string())?;
        if count == 0 { break; }
        hash.update(&buffer[..count])?;
        bytes += count as u64;
    }
    Ok((bytes, super::hex(&hash.finish()?)))
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed bounded Job; selected-owner structural ROW only"]
fn c452_mixed_map_header_zero_authentic_selected_owner_structural_row() -> Result<(), String> {
    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("pinned H21 frame path required")?;
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C450 H21 frame path must be absolute".into());
    }
    let before = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != FRAME_BYTES {
        return Err("C450 pinned H21 frame regular-file/length preflight".into());
    }

    // Keep one read-only handle open for prehash, parse and posthash.
    // FILE_SHARE_READ excludes concurrent writers and deletion on Windows.
    let mut file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if file.metadata().map_err(|error| error.to_string())?.len() != FRAME_BYTES {
        return Err("C450 opened H21 frame length".into());
    }
    let prehash = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    prehash.finish(0, FRAME_BYTES, FRAME_SHA256)?;
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;

    let mut frame = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C450 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C450 H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    if OWNER >= N || roster.owner_class(OWNER as u64)? != OwnerClass::Carry {
        return Err("C450 owner845760 must be genuine Carry".into());
    }

    // The H21 context creates only the typed Map lease; one separate producer
    // call below writes the destination row from this exact same plan/prefix.
    let context = H21EligibleContext::new(&plan, &prefix)?;
    let map_lease = context.map_pair_lease(OWNER)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER)?;
    if map_lease.binding() != &binding {
        return Err("C450 generated Map lease parent binding".into());
    }

    // This is the sole destination production call. The opaque token retains
    // this exact Map lease, its actual HEADER capture, and the final packed row.
    let mixed: NativeMixedMapHeaderRow<'_> =
        producer.produce_mixed_map_header_row(OWNER, &map_lease)?;
    if mixed.row().owner() != OWNER || mixed.row().class() != OwnerClass::Carry
        || mixed.binding() != &binding || mixed.map_lease().binding() != &binding {
        return Err("C450 mixed row identity/class/parent binding".into());
    }

    let mut seen = vec![false; EXPECTED_CELLS];
    let mut map_author = 0usize;
    let mut map_value_match = 0usize;
    let mut header_claims = 0usize;
    let mut header_source_zero = 0usize;
    let mut packed_zero = 0usize;
    let packed = mixed.row().packed_bytes();
    for context_index in 0..CONTEXTS {
        for offset in 0..CONTEXT_BITS {
            let index = context_index * CONTEXT_BITS + offset;
            if std::mem::replace(&mut seen[index], true) {
                return Err("C450 duplicate context/offset coverage".into());
            }
            let required = required_bank53_writer(OWNER, context_index, offset)?;
            let local = BANK53_BASE + index;
            match required {
                RequiredWriter::Map { context } if context == context_index && offset < MAP_BITS => {
                    let value = mixed.read_map(&binding, context_index, offset)?;
                    if ((packed[local / 8] >> (local % 8)) & 1 != 0) != value {
                        return Err("C450 Map value differs from packed row".into());
                    }
                    map_author += 1;
                    map_value_match += 1;
                }
                RequiredWriter::HeaderZero if offset >= MAP_BITS => {
                    if mixed.read_header_zero(&binding, context_index, offset)? {
                        return Err("C450 HEADER-zero source is nonzero".into());
                    }
                    header_claims += 1;
                    header_source_zero += 1;
                    if (packed[local / 8] >> (local % 8)) & 1 != 0 {
                        return Err("C450 final HEADER-zero packed bit is nonzero".into());
                    }
                    packed_zero += 1;
                }
                _ => return Err(format!("C450 unexpected required author context={context_index} offset={offset}")),
            }
        }
    }
    if seen.iter().any(|covered| !covered) || map_author != EXPECTED_MAP
        || map_value_match != EXPECTED_MAP || header_claims != EXPECTED_HEADER_ZERO
        || header_source_zero != EXPECTED_HEADER_ZERO || packed_zero != EXPECTED_HEADER_ZERO {
        return Err("C450 incomplete mixed two-context Bank53 census".into());
    }

    // Join structural ROW admission to the same opaque physical row token and
    // its retained lease. This stages equations only; it adds no operand reader.
    let scheduled = crate::h21_scheduled_max_cap::Plan::eligible08();
    let row_plan = crate::header_daa_row_placement::RowPlan::new(&roster, &scheduled)?;
    let row_batch = row_plan.stage_owner_with_map_pair_general(OWNER, mixed.map_lease())?;
    if row_batch.owner() != mixed.row().owner() || row_batch.class() != mixed.row().class()
        || row_batch.source_binding() != mixed.binding()
        || row_batch.source_binding() != mixed.map_lease().binding()
        || row_batch.layout_digest()
            != crate::header_daa_row_placement::Layout::paired_map_general().digest() {
        return Err("C452 selected-owner structural ROW identity/class/parent/v4 layout".into());
    }
    let row_counts = row_batch.counts();
    let mut row_map_terms = [0usize; CONTEXTS];
    for context_index in 0..CONTEXTS {
        let source_terms = mixed.map_lease().terms(context_index)?;
        let placed_terms = row_batch.map_terms(context_index)?;
        if placed_terms.len() != source_terms.len()
            || row_counts[9 + context_index] != source_terms.len() {
            return Err(format!(
                "C452 selected-owner structural ROW ordered Map term census context={context_index}"
            ));
        }
        row_map_terms[context_index] = source_terms.len();
    }
    let mut row_registry = row_plan.registry_with_map_pair_general(OWNER)?;
    let row_registry_before = row_registry.clone();
    row_registry.commit_map_pair(&row_batch)?;
    if row_registry == row_registry_before {
        return Err("C452 selected-owner structural ROW commit made no transition".into());
    }
    drop(row_registry);
    drop(row_batch);
    drop(row_plan);
    drop(scheduled);

    drop(mixed);
    drop(map_lease);
    drop(context);
    drop(producer);
    drop(roster);
    drop(plan);
    drop(prefix);

    let after_handle = file.metadata().map_err(|error| error.to_string())?;
    if after_handle.len() != FRAME_BYTES {
        return Err("C450 frame length changed on retained handle".into());
    }
    let (after_bytes, after_sha) = hash_same_handle(&mut file)?;
    if after_bytes != FRAME_BYTES || after_sha != FRAME_SHA256 {
        return Err("C450 frame posthash changed on retained handle".into());
    }
    let after_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !after_path.is_file() || after_path.file_type().is_symlink()
        || after_path.len() != FRAME_BYTES
        || after_path.modified().map_err(|error| error.to_string())?
            != before.modified().map_err(|error| error.to_string())? {
        return Err("C450 frame path changed during authentic test".into());
    }

    println!(
        "C452_MIXED_MAP_HEADER_SELECTED_OWNER_STRUCTURAL_ROW_AUTHENTIC_PASS owner={OWNER} class=Carry producer_calls=1 frame_parses=1 contexts={CONTEXTS} bank53_cells={EXPECTED_CELLS} required_map={EXPECTED_MAP} map_author={map_author} map_value_match={map_value_match} header_zero_required={EXPECTED_HEADER_ZERO} header_claims={header_claims} header_source_zero={header_source_zero} packed_zero={packed_zero} parent_bound=true row_layout=v4 row_map0_terms={} row_map1_terms={} row_commits=1 scope=selected_owner_structural_row operand_reader=false global_proof=false frame_bytes_before={FRAME_BYTES} frame_sha256_before={} frame_bytes_after={after_bytes} frame_sha256_after={}",
        row_map_terms[0], row_map_terms[1],
        FRAME_SHA256.to_ascii_uppercase(), after_sha.to_ascii_uppercase(),
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed bounded Job; authentic owner2 native C503 join"]
fn c522_native_owner2_map_header_c503_join_from_pinned_frame() -> Result<(), String> {
    const OWNER: usize = 2;
    const EXPECTED_MAP: usize = 5_757;
    const EXPECTED_HEADER_ZERO: usize = 2_435;
    const BANK53_START: usize = 671_744;
    const BANK53_END: usize = BANK53_START + CONTEXTS * CONTEXT_BITS;
    const FRAME_SHA: &str = "a68d86562a56c5b71cf2180e4762bf8775b1061b6953bff7281ec50b7ee52c5e";

    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("C522 pinned H21 frame path required")?;
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C522 H21 frame path must be absolute".into());
    }
    let before = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != FRAME_BYTES {
        return Err("C522 pinned H21 frame regular-file/length preflight".into());
    }

    // One read-only handle spans prehash, the sole NativePrefix parse and posthash.
    let mut file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if file.metadata().map_err(|error| error.to_string())?.len() != FRAME_BYTES {
        return Err("C522 opened H21 frame length".into());
    }
    let prehash = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    prehash.finish(0, FRAME_BYTES, FRAME_SHA)?;
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
    let mut frame = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C522 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C522 H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    if roster.owner_class(OWNER as u64)? != OwnerClass::Carry {
        return Err("C522 owner2 must be genuine Carry".into());
    }
    let context = H21EligibleContext::new(&plan, &prefix)?;
    let map_lease = context.map_pair_lease(OWNER)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER)?;
    if map_lease.binding() != &binding {
        return Err("C522 generated Map lease parent binding".into());
    }
    let mixed: NativeMixedMapHeaderRow<'_> =
        producer.produce_mixed_map_header_row(OWNER, &map_lease)?;
    if mixed.row().owner() != OWNER || mixed.row().class() != OwnerClass::Carry
        || mixed.binding() != &binding || mixed.map_lease().binding() != &binding {
        return Err("C522 native mixed row identity/class/parent binding".into());
    }

    let packed = mixed.row().packed_bytes().to_vec();
    let mut map_reads = 0usize;
    let mut map_matches = 0usize;
    let mut header_reads = 0usize;
    let mut header_source_zero = 0usize;
    let mut header_packed_zero = 0usize;
    for context_index in 0..CONTEXTS {
        for offset in 0..CONTEXT_BITS {
            let local = BANK53_START + context_index * CONTEXT_BITS + offset;
            match required_bank53_writer(OWNER, context_index, offset)? {
                RequiredWriter::Map { context } if context == context_index && offset < MAP_BITS => {
                    let value = mixed.read_map(&binding, context_index, offset)?;
                    if ((packed[local / 8] >> (local % 8)) & 1 != 0) != value {
                        return Err("C522 native Map source/packed bit mismatch".into());
                    }
                    map_reads += 1;
                    map_matches += 1;
                }
                RequiredWriter::HeaderZero if offset >= MAP_BITS => {
                    if mixed.read_header_zero(&binding, context_index, offset)?
                        || (packed[local / 8] >> (local % 8)) & 1 != 0 {
                        return Err("C522 native HEADER-zero source/packed bit mismatch".into());
                    }
                    header_reads += 1;
                    header_source_zero += 1;
                    header_packed_zero += 1;
                }
                _ => return Err(format!(
                    "C522 unexpected Bank53 author context={context_index} offset={offset}"
                )),
            }
        }
    }
    if map_reads != CONTEXTS * EXPECTED_MAP || map_matches != map_reads
        || header_reads != CONTEXTS * EXPECTED_HEADER_ZERO
        || header_source_zero != header_reads || header_packed_zero != header_reads {
        return Err("C522 native mixed Bank53 source census".into());
    }

    let scheduled = crate::h21_scheduled_max_cap::Plan::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled)?;
    let joined = C503EarlyCarryMapHeaderRow::from_producer(&row_plan, mixed)?;
    joined.validate()?;
    let batch = joined.batch();
    if batch.owner() != OWNER || batch.class() != OwnerClass::Carry
        || batch.source_binding() != &binding
        || batch.layout_digest()
            != crate::header_daa_row_placement::Layout::paired_map_general().digest() {
        return Err("C522 C503 owner/class/binding/paired-layout mismatch".into());
    }

    let owner_base = OWNER.checked_mul(WIDTH).ok_or("C522 owner wire base overflow")?;
    let operands: Vec<ActiveOperand> = batch.active_operands().collect();
    let mut expected_map = [0usize; CONTEXTS];
    let mut expected_header_zero = 0usize;
    for operand in &operands {
        let Some(local) = operand.wire.checked_sub(owner_base)
            .filter(|local| (BANK53_START..BANK53_END).contains(local)) else { continue; };
        let context_index = (local - BANK53_START) / CONTEXT_BITS;
        let offset = (local - BANK53_START) % CONTEXT_BITS;
        if offset < MAP_BITS {
            expected_map[context_index] += 1;
        } else {
            expected_header_zero += 1;
        }
    }
    let mut joined_map = [0usize; CONTEXTS];
    let mut joined_header_zero = 0usize;
    for read in joined.bank53_reads() {
        let local = read.operand.wire.checked_sub(owner_base)
            .filter(|local| (BANK53_START..BANK53_END).contains(local))
            .ok_or("C522 C503 read is outside owner-local Bank53")?;
        let context_index = (local - BANK53_START) / CONTEXT_BITS;
        let offset = (local - BANK53_START) % CONTEXT_BITS;
        let packed_value = packed[local / 8] & (1 << (local % 8)) != 0;
        if read.value != packed_value {
            return Err("C522 C503 ordered read value differs from packed row".into());
        }
        match read.author {
            C503Bank53Author::Map(author_context) => {
                if author_context != context_index || offset >= MAP_BITS
                    || !matches!(required_bank53_writer(OWNER, context_index, offset)?,
                        RequiredWriter::Map { context } if context == author_context) {
                    return Err("C522 C503 Map read author mismatch".into());
                }
                joined_map[author_context] += 1;
            }
            C503Bank53Author::HeaderZero => {
                if offset < MAP_BITS || read.value
                    || !matches!(required_bank53_writer(OWNER, context_index, offset)?,
                        RequiredWriter::HeaderZero) {
                    return Err("C522 C503 HEADER-zero read author/value mismatch".into());
                }
                joined_header_zero += 1;
            }
        }
    }
    if expected_map.iter().any(|count| *count < EXPECTED_MAP)
        || joined_map != expected_map || joined_header_zero != expected_header_zero {
        return Err("C522 C503 ordered Bank53 author/value census".into());
    }

    // Independently derive the open complement in occurrence order, in O(n).
    let expected_open: Vec<ActiveOperand> = operands.iter().copied().filter(|operand| {
        !operand.wire.checked_sub(owner_base)
            .is_some_and(|local| (BANK53_START..BANK53_END).contains(&local))
    }).collect();
    let reads = joined.bank53_reads();
    let mut open_complement = Vec::new();
    let mut read_index = 0usize;
    for operand in &operands {
        let Some(read) = reads.get(read_index) else {
            open_complement.push(*operand);
            continue;
        };
        let claimed = read.operand;
        let precedes = claimed.occurrence < operand.occurrence
            || (claimed.occurrence == operand.occurrence
                && matches!((claimed.side, operand.side),
                    (OperandSide::Left, OperandSide::Right)));
        let same_position = claimed.occurrence == operand.occurrence
            && claimed.side == operand.side;
        if same_position {
            if claimed != *operand { return Err("C522 C503 read identity mismatch".into()); }
            read_index += 1;
        } else {
            if precedes { return Err("C522 C503 read ordering mismatch".into()); }
            open_complement.push(*operand);
        }
    }
    if read_index != reads.len() || open_complement != expected_open
        || expected_open.is_empty() || joined.open_read_count() != expected_open.len() {
        return Err("C522 independent ordered open-read complement mismatch".into());
    }

    let open_reads = joined.open_read_count();
    let bank53_reads = reads.len();
    drop(joined);
    drop(row_plan);
    drop(scheduled);
    drop(map_lease);
    drop(context);
    drop(producer);
    drop(roster);
    drop(plan);
    drop(prefix);

    let after_handle = file.metadata().map_err(|error| error.to_string())?;
    if after_handle.len() != FRAME_BYTES { return Err("C522 frame length changed on handle".into()); }
    let (after_bytes, after_sha) = hash_same_handle(&mut file)?;
    if after_bytes != FRAME_BYTES || after_sha != FRAME_SHA {
        return Err("C522 frame posthash changed on retained handle".into());
    }
    let after_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !after_path.is_file() || after_path.file_type().is_symlink()
        || after_path.len() != FRAME_BYTES
        || after_path.modified().map_err(|error| error.to_string())?
            != before.modified().map_err(|error| error.to_string())? {
        return Err("C522 frame path changed during authentic test".into());
    }

    println!(
        "C522_OWNER2_MAP_HEADER_C503_NATIVE_JOIN_PASS owner={OWNER} class=Carry producer_calls=1 frame_parses=1 bank53_map_source_reads={map_reads} bank53_map_packed_matches={map_matches} bank53_header_zero_source_reads={header_reads} bank53_header_zero_packed_zero={header_packed_zero} c503_bank53_reads={bank53_reads} c503_open_reads={open_reads} frame_bytes_before={FRAME_BYTES} frame_sha256_before={} frame_bytes_after={after_bytes} frame_sha256_after={} source=true partialROW=true commonX=false fullRow=false globalRow=false GKR=false PCS=false proof=false client=false production=false",
        FRAME_SHA.to_ascii_uppercase(), after_sha.to_ascii_uppercase(),
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}

#[test]
#[ignore = "exact pinned H21 frame; selected full-zero DAA owners and lane3 reads only"]
fn c520_native_full_zero_multi_class_h21_source_row() -> Result<(), String> {
    const FULL_ZERO_BITS_PER_OWNER: usize = 81_920;
    const OWNERS: [(usize, OwnerClass); 6] = [
        (0, OwnerClass::Genesis),
        (1, OwnerClass::Initial),
        (1_024, OwnerClass::Singleton),
        (417_791, OwnerClass::FixedV2),
        (417_792, OwnerClass::FixedV2),
        (1_827_840, OwnerClass::Padding),
    ];

    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("C520 pinned H21 frame path required")?;
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C520 H21 frame path must be absolute".into());
    }
    let before = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != FRAME_BYTES {
        return Err("C520 pinned H21 frame regular-file/length preflight".into());
    }

    // Hold one read-only handle for prehash, a single canonical parse, and posthash.
    let mut file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if file.metadata().map_err(|error| error.to_string())?.len() != FRAME_BYTES {
        return Err("C520 opened H21 frame length".into());
    }
    let prehash = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    prehash.finish(0, FRAME_BYTES, FRAME_SHA256)?;
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;

    let mut frame = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C520 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C520 H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    let scheduled = crate::h21_scheduled_max_cap::Plan::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;

    let mut producer_calls = 0usize;
    let mut full_zero_claimed_bits = 0usize;
    let mut packed_zero_bits = 0usize;
    let mut lane3_terms = 0usize;
    let mut lane3_reads = 0usize;
    let mut daa_domains = 0usize;

    for &(owner, expected_class) in &OWNERS {
        let class = roster.owner_class(owner as u64)
            .map_err(|error| format!("C520 owner{owner} roster: {error}"))?;
        if class != expected_class {
            return Err(format!("C520 owner{owner} class {class:?}, expected {expected_class:?}"));
        }
        let binding = HeaderSourceBinding::for_plan(&plan, owner)?;
        let (row, lease) = producer
            .produce_with_full_zero_daa_source_lease(owner)
            .map_err(|error| format!("C520 owner{owner}/{class:?} production: {error}"))?;
        row.require_header_source_binding(&binding, owner, class)
            .map_err(|error| format!("C520 owner{owner}/{class:?} row binding: {error}"))?;
        lease.check_full_zero_source(&binding)
            .map_err(|error| format!("C520 owner{owner}/{class:?} DAA author: {error}"))?;

        let base = owner.checked_mul(WIDTH).ok_or("C520 DAA owner base overflow")?;
        let packed = row.packed_bytes();
        let mut owner_claimed_bits = 0usize;
        let mut owner_packed_zero_bits = 0usize;
        for &(start, end) in &BANKS {
            for local in start..end {
                let physical_wire = base.checked_add(local).ok_or("C520 DAA wire overflow")?;
                let source_value = lease.read_daa_bit(&binding, physical_wire)?
                    .ok_or_else(|| format!("C520 owner{owner} missing FullZero claim wire{physical_wire}"))?;
                let packed_value = packed[local / 8] & (1 << (local % 8)) != 0;
                if source_value || packed_value || source_value != packed_value {
                    return Err(format!("C520 owner{owner} FullZero source/packed mismatch wire{local}"));
                }
                owner_claimed_bits += 1;
                owner_packed_zero_bits += 1;
            }
        }
        if owner_claimed_bits != FULL_ZERO_BITS_PER_OWNER
            || owner_packed_zero_bits != FULL_ZERO_BITS_PER_OWNER {
            return Err(format!("C520 owner{owner} FullZero bit census"));
        }

        let joined = row_plan.stage_owner_with_daa_reads(owner, &lease)
            .map_err(|error| format!("C520 owner{owner}/{class:?} ROW DAA join: {error}"))?;
        let batch = joined.batch();
        batch.require_owner_parent(&plan, owner)
            .map_err(|error| format!("C520 owner{owner}/{class:?} ROW parent: {error}"))?;
        if batch.terms().any(|(relation, _)| matches!(relation,
            Relation::Scheduled(_) | Relation::Map(_))) {
            return Err(format!("C520 owner{owner}/{class:?} unexpected scheduled/Map terms"));
        }

        let owner_lane3_terms = batch.terms()
            .filter(|(relation, _)| *relation == Relation::DaaLane(3))
            .count();
        let expected_lane3_operands = batch.active_operands()
            .filter(|operand| operand.relation == Relation::DaaLane(3))
            .collect::<Vec<_>>();
        let actual_lane3_reads = joined.daa_reads()
            .filter(|read| read.operand.relation == Relation::DaaLane(3))
            .collect::<Vec<_>>();
        if owner_lane3_terms != FULL_ZERO_BITS_PER_OWNER
            || expected_lane3_operands.len() != FULL_ZERO_BITS_PER_OWNER
            || actual_lane3_reads.len() != FULL_ZERO_BITS_PER_OWNER {
            return Err(format!(
                "C520 owner{owner}/{class:?} lane3 census terms={owner_lane3_terms} operands={} reads={}",
                expected_lane3_operands.len(), actual_lane3_reads.len(),
            ));
        }
        // With the exact count and bank envelope, uniqueness implies full coverage.
        let mut seen_lane3 = vec![false; WIDTH];
        for (index, (operand, read)) in expected_lane3_operands.iter()
            .zip(actual_lane3_reads.iter()).enumerate() {
            let local = operand.wire.checked_sub(base)
                .filter(|local| *local < WIDTH)
                .ok_or_else(|| format!("C520 owner{owner} lane3 foreign wire at occurrence{}", operand.occurrence))?;
            if read.operand != *operand || read.value || operand.side != OperandSide::Left
                || !operand.c1_active || operand.c2_active || operand.c3_active
                || !BANKS.iter().any(|&(start, end)| (start..end).contains(&local))
                || (packed[local / 8] & (1 << (local % 8)) != 0) {
                return Err(format!("C520 owner{owner} lane3 occurrence/read mismatch index={index}"));
            }
            if seen_lane3[local] {
                return Err(format!("C520 owner{owner} duplicate lane3 bank wire{local}"));
            }
            seen_lane3[local] = true;
        }

        let domains = batch.declared_x_domains_with_daa_source(&lease)
            .map_err(|error| format!("C520 owner{owner}/{class:?} DAA domains: {error}"))?;
        if domains.len() != BANKS.len() {
            return Err(format!("C520 owner{owner}/{class:?} DAA domain count {}", domains.len()));
        }
        for (domain, &(start, end)) in domains.iter().zip(BANKS.iter()) {
            if domain.producer != Producer::Daa
                || domain.start != base + start || domain.end != base + end {
                return Err(format!("C520 owner{owner}/{class:?} DAA domain mismatch"));
            }
        }

        producer_calls += 1;
        full_zero_claimed_bits += owner_claimed_bits;
        packed_zero_bits += owner_packed_zero_bits;
        lane3_terms += owner_lane3_terms;
        lane3_reads += actual_lane3_reads.len();
        daa_domains += domains.len();
        drop(joined);
        drop(lease);
        drop(row);
    }

    const EXPECTED_TOTAL_BITS: usize = OWNERS.len() * FULL_ZERO_BITS_PER_OWNER;
    if producer_calls != OWNERS.len() || full_zero_claimed_bits != EXPECTED_TOTAL_BITS
        || packed_zero_bits != EXPECTED_TOTAL_BITS || lane3_terms != EXPECTED_TOTAL_BITS
        || lane3_reads != EXPECTED_TOTAL_BITS || daa_domains != OWNERS.len() * BANKS.len() {
        return Err("C520 multi-class FullZero aggregate census".into());
    }

    drop(row_plan);
    drop(producer);
    drop(scheduled);
    drop(roster);
    drop(plan);
    drop(prefix);

    let after_handle = file.metadata().map_err(|error| error.to_string())?;
    if after_handle.len() != FRAME_BYTES {
        return Err("C520 frame length changed on retained handle".into());
    }
    let (after_bytes, after_sha) = hash_same_handle(&mut file)?;
    if after_bytes != FRAME_BYTES || after_sha != FRAME_SHA256 {
        return Err("C520 frame posthash changed on retained handle".into());
    }
    let after_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !after_path.is_file() || after_path.file_type().is_symlink()
        || after_path.len() != FRAME_BYTES
        || after_path.modified().map_err(|error| error.to_string())?
            != before.modified().map_err(|error| error.to_string())? {
        return Err("C520 frame path changed during authentic test".into());
    }

    println!(
        "C520_H21_FULL_ZERO_MULTI_CLASS_SOURCE_ROW_PASS owners=[0,1,1024,417791,417792,1827840] producer_calls={producer_calls} frame_parses=1 full_zero_claimed_bits={full_zero_claimed_bits} packed_zero_bits={packed_zero_bits} lane3_terms={lane3_terms} lane3_reads={lane3_reads} daa_domains={daa_domains} late_generic_claim_guard=passed max_stream=false score_stream=false common_x=false full_row=false global_row=false proof=false client=false frame_bytes_before={FRAME_BYTES} frame_sha256_before={} frame_bytes_after={after_bytes} frame_sha256_after={}",
        FRAME_SHA256.to_ascii_uppercase(), after_sha.to_ascii_uppercase(),
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}

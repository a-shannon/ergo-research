//! One authentic Padding owner HEADER-zero source/packed equality check.

use super::*;
use std::{
    fs::{self, File, OpenOptions},
    io::{BufReader, Read, Seek, SeekFrom},
    os::windows::fs::OpenOptionsExt,
};
use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    bank53_required_writer::{required_bank53_writer, RequiredWriter},
    packed_owner_assembly::NativePaddingHeaderZeroRow,
};

const BANK53_BASE: usize = 671_744;
const CONTEXTS: usize = 2;
const CONTEXT_BITS: usize = 8_192;
const EXPECTED_CELLS: usize = CONTEXTS * CONTEXT_BITS;
const OWNER: usize = 1_827_840;

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
#[ignore = "exact pinned H21 frame; reviewed single-process bounded Job required"]
fn c449b_authentic_padding_header_zero_source_and_packed_row() -> Result<(), String> {
    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("pinned H21 frame path required")?;
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C449b H21 frame path must be absolute".into());
    }
    let before = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != FRAME_BYTES {
        return Err("C449b pinned H21 frame regular-file/length preflight".into());
    }

    // Keep one read-only handle open for the prehash, parse and posthash.
    // FILE_SHARE_READ excludes concurrent writers and deletion on Windows.
    let mut file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if file.metadata().map_err(|error| error.to_string())?.len() != FRAME_BYTES {
        return Err("C449b opened H21 frame length".into());
    }

    // Prehash the exact retained handle, then parse the frame exactly once.
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
            return Err("C449b H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C449b H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    if roster.owner_class(OWNER as u64)? != OwnerClass::Padding {
        return Err("C449b owner N is not Padding".into());
    }
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER)?;

    // This is the sole destination production call. The returned opaque token
    // owns the exact native row and the actual HEADER-seed capture together.
    let native: NativePaddingHeaderZeroRow = producer.produce_padding_header_zero_row()?;
    if native.row().owner() != OWNER || native.row().class() != OwnerClass::Padding {
        return Err("C449b native padding row identity/class".into());
    }
    native.row().require_header_source_binding(&binding, OWNER, OwnerClass::Padding)?;

    let mut seen = vec![false; EXPECTED_CELLS];
    let mut source_zero = 0usize;
    let mut packed_zero = 0usize;
    for context in 0..CONTEXTS {
        for offset in 0..CONTEXT_BITS {
            if required_bank53_writer(OWNER, context, offset)? != RequiredWriter::HeaderZero {
                return Err("C449b required-writer oracle did not require HEADER-zero".into());
            }
            let index = context * CONTEXT_BITS + offset;
            if std::mem::replace(&mut seen[index], true) {
                return Err("C449b duplicate context/offset coverage".into());
            }
            // The wrapper rejects an absent/non-HEADER claim and checks source
            // zero against the exact packed bit while enforcing this binding.
            if native.read_header_zero(&binding, context, offset)? {
                return Err("C449b captured HEADER source is nonzero".into());
            }
            source_zero += 1;
            let local = BANK53_BASE + index;
            let packed = native.row().packed_bytes();
            if ((packed[local / 8] >> (local % 8)) & 1) != 0 {
                return Err("C449b final packed Bank53 bit is nonzero".into());
            }
            packed_zero += 1;
        }
    }
    if seen.iter().any(|covered| !covered) || source_zero != EXPECTED_CELLS
        || packed_zero != EXPECTED_CELLS
    {
        return Err("C449b incomplete two-context Bank53 census".into());
    }

    drop(native);
    drop(binding);
    drop(producer);
    drop(roster);
    drop(plan);
    drop(prefix);

    let after_handle = file.metadata().map_err(|error| error.to_string())?;
    if after_handle.len() != FRAME_BYTES {
        return Err("C449b frame length changed on retained handle".into());
    }
    let (after_bytes, after_sha) = hash_same_handle(&mut file)?;
    if after_bytes != FRAME_BYTES || after_sha != FRAME_SHA256 {
        return Err("C449b frame posthash changed on retained handle".into());
    }
    let after_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if !after_path.is_file() || after_path.file_type().is_symlink()
        || after_path.len() != FRAME_BYTES
        || after_path.modified().map_err(|error| error.to_string())?
            != before.modified().map_err(|error| error.to_string())?
    {
        return Err("C449b frame path changed during authentic test".into());
    }

    println!(
        "C449B_PADDING_HEADER_ZERO_AUTHENTIC_PASS owner={OWNER} class=Padding producer_calls=1 frame_parses=1 contexts={CONTEXTS} bank53_cells={EXPECTED_CELLS} header_claims={EXPECTED_CELLS} source_zero={source_zero} packed_zero={packed_zero} parent_bound=true frame_bytes_before={FRAME_BYTES} frame_sha256_before={} frame_bytes_after={after_bytes} frame_sha256_after={}",
        FRAME_SHA256.to_ascii_uppercase(),
        after_sha.to_ascii_uppercase(),
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}

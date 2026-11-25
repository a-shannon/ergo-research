//! Distinct owner0 Genesis HeaderZero native selector.
//! This proves only source-owned HeaderZero custody for the two Bank53 contexts.

use super::*;
use std::{
    collections::BTreeSet,
    fs::{Metadata, OpenOptions},
    io::{Seek, SeekFrom},
    os::windows::{fs::{MetadataExt, OpenOptionsExt}, io::AsRawHandle},
    time::SystemTime,
};
use crate::daa_history_roster::{DaaHistoryRoster, OwnerClass};

const OWNER: usize = 0;
const OWNER_BITS: usize = 1 << 20;
const OWNER_BYTES: usize = OWNER_BITS / 8;
const CONTEXTS: usize = 2;
const CONTEXT_BITS: usize = 8_192;
const MAP_LIVE_BITS: usize = 5_757;
const SCORE_BITS_PER_CONTEXT: usize = 2_048;
const SLACK_BITS_PER_CONTEXT: usize = 387;
const HEADER_ZERO_FIRST_OFFSET: usize = 5_757;
const HEADER_ZERO_LAST_OFFSET: usize = 7_804;
const HEADER_ZERO_CELLS: usize = CONTEXTS * 2_048;
const MAP_CELLS: usize = CONTEXTS * MAP_LIVE_BITS;
const SLACK_CELLS: usize = CONTEXTS * SLACK_BITS_PER_CONTEXT;
const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0400;
const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;
const FRAME_SHA256_UPPER: &str =
    "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E";

// Stable Windows BY_HANDLE_FILE_INFORMATION layout. Last-access time is
// deliberately excluded from identity because reads may update it.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct HandleIdentity {
    attributes: u32,
    created: [u32; 2],
    accessed: [u32; 2],
    written: [u32; 2],
    volume: u32,
    size_high: u32,
    size_low: u32,
    links: u32,
    index_high: u32,
    index_low: u32,
}

fn handle_identity(file: &File, label: &str) -> Result<HandleIdentity, String> {
    #[link(name = "kernel32")]
    extern "system" {
        fn GetFileInformationByHandle(
            handle: *mut std::ffi::c_void,
            information: *mut HandleIdentity,
        ) -> i32;
    }
    let mut identity = HandleIdentity::default();
    // The repr(C) result is writable, and File outlives this borrowed call.
    if unsafe { GetFileInformationByHandle(file.as_raw_handle(), &mut identity) } == 0 {
        return Err(format!(
            "C491 {label} handle identity: {}",
            std::io::Error::last_os_error(),
        ));
    }
    if identity.attributes & 0x410 != 0 || identity.links != 1
        || ((u64::from(identity.size_high) << 32) | u64::from(identity.size_low)) != FRAME_BYTES
    {
        return Err(format!(
            "C491 {label} is not a regular non-reparse single-link pinned-size file",
        ));
    }
    identity.accessed = [0; 2];
    Ok(identity)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PathStamp {
    size: u64,
    attributes: u32,
    modified: SystemTime,
}

fn path_stamp(metadata: &Metadata, label: &str) -> Result<PathStamp, String> {
    let attributes = metadata.file_attributes();
    if !metadata.is_file() || metadata.file_type().is_symlink()
        || attributes & FILE_ATTRIBUTE_REPARSE_POINT != 0
    {
        return Err(format!("C491 {label} is not a regular non-reparse file"));
    }
    Ok(PathStamp {
        size: metadata.len(),
        attributes,
        modified: metadata.modified().map_err(|error| error.to_string())?,
    })
}

fn hash_retained_frame(file: &mut File) -> Result<(), String> {
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
    let frame = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut *file), FRAME_BYTES,
    )?;
    frame.finish(0, FRAME_BYTES, FRAME_SHA256)
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed single-process bounded Job required"]
fn c491_genesis_header_zero_native_selector() -> Result<(), String> {
    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("pinned H21 frame path required")?;
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C491 H21 frame path must be absolute".into());
    }
    let before_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    let before_path_stamp = path_stamp(&before_path, "pre-open path")?;
    if before_path_stamp.size != FRAME_BYTES {
        return Err("C491 pinned H21 frame length".into());
    }

    // Keep one handle open for prehash, the sole parse, and posthash. On
    // Windows, share_mode(1) denies concurrent writes/deletes; OPEN_REPARSE_POINT
    // lets the handle itself fail closed if the path changes to a reparse point.
    let mut file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .custom_flags(FILE_FLAG_OPEN_REPARSE_POINT)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    let before_identity = handle_identity(&file, "opened frame")?;
    let opened_size = (u64::from(before_identity.size_high) << 32)
        | u64::from(before_identity.size_low);
    if opened_size != before_path_stamp.size {
        return Err("C491 path/handle length mismatch".into());
    }
    let opened_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if path_stamp(&opened_path, "opened path")? != before_path_stamp {
        return Err("C491 frame path metadata changed during open".into());
    }
    let named_file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .custom_flags(FILE_FLAG_OPEN_REPARSE_POINT)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if handle_identity(&named_file, "opened named path")? != before_identity {
        return Err("C491 opened path/held handle identity mismatch".into());
    }
    drop(named_file);

    hash_retained_frame(&mut file)?;
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
    let mut frame = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C491 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N
        || frame.offset != PREFIX_BYTES
        || extensions != EXTENSIONS
    {
        return Err("C491 H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    if roster.owner_class(OWNER as u64)? != OwnerClass::Genesis {
        return Err("C491 owner0 is not Genesis".into());
    }
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let context = crate::packed_owner_assembly::H21EligibleContext::new(&plan, &prefix)?;
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER)?;

    // Mint one exact owner0 Map+Slack bundle and validate its typed cells.
    let bundle = context.map_pair_slack_bundle(OWNER)?;
    let map = bundle.map_lease().checked_cells(&binding, OWNER, OwnerClass::Genesis)?;
    let slack = bundle.checked_slack_cells(&binding, OWNER, OwnerClass::Genesis)?;
    if map.len() != MAP_CELLS || slack.len() != SLACK_CELLS {
        return Err("C491 owner0 Map/Slack typed source census".into());
    }
    let mut typed_wires = BTreeSet::new();
    for (index, cell) in map.iter().enumerate() {
        let context_index = index / MAP_LIVE_BITS;
        let offset = index % MAP_LIVE_BITS;
        let expected_wire = OWNER * OWNER_BITS + BANK53_BASE
            + context_index * CONTEXT_BITS + offset;
        if cell.context() != context_index || cell.offset() != offset
            || cell.physical_wire() != expected_wire
            || !typed_wires.insert(expected_wire)
        {
            return Err("C491 owner0 ordered typed Map source identity".into());
        }
    }
    for (index, cell) in slack.iter().enumerate() {
        let context_index = index / SLACK_BITS_PER_CONTEXT;
        let offset = index % SLACK_BITS_PER_CONTEXT;
        let expected_wire = OWNER * OWNER_BITS + BANK53_BASE
            + context_index * CONTEXT_BITS + MAP_LIVE_BITS
            + SCORE_BITS_PER_CONTEXT + offset;
        if cell.context() != context_index || cell.physical_wire() != expected_wire
            || !typed_wires.insert(expected_wire)
        {
            return Err("C491 owner0 ordered typed Slack source identity".into());
        }
    }
    if typed_wires.len() != MAP_CELLS + SLACK_CELLS {
        return Err("C491 owner0 typed Map/Slack physical partition".into());
    }

    // This is the sole owner0 destination production. The opaque validation
    // authenticates all source claims and the exact borrowed bundle identity.
    let native = producer.produce_genesis_header_zero_with_map_slack_bundle(OWNER, &bundle)?;
    native.validate_for(&binding, &bundle)?;
    if native.row().owner() != OWNER
        || native.row().class() != OwnerClass::Genesis
        || native.row().packed_bytes().len() != OWNER_BYTES
    {
        return Err("C491 native owner0 Genesis row identity/size".into());
    }
    let packed = native.row().packed_bytes();
    let mut packed_zero = 0usize;
    for context_index in 0..CONTEXTS {
        for offset in HEADER_ZERO_FIRST_OFFSET..=HEADER_ZERO_LAST_OFFSET {
            let local = BANK53_BASE + context_index * CONTEXT_BITS + offset;
            if local >= OWNER_BITS || ((packed[local / 8] >> (local % 8)) & 1) != 0 {
                return Err("C491 final packed HeaderZero bit is nonzero".into());
            }
            packed_zero += 1;
        }
    }
    if packed_zero != HEADER_ZERO_CELLS {
        return Err("C491 final packed HeaderZero census".into());
    }

    drop(native);
    drop(bundle);
    drop(context);
    drop(producer);
    drop(roster);
    drop(plan);
    drop(prefix);

    // Hash the retained handle again without parsing another frame, then bind
    // its identity and metadata to both path observations.
    hash_retained_frame(&mut file)?;
    let after_handle = handle_identity(&file, "postflight handle")?;
    let after_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    let after_path_stamp = path_stamp(&after_path, "postflight path")?;
    let named_after = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .custom_flags(FILE_FLAG_OPEN_REPARSE_POINT)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    let named_after_identity = handle_identity(&named_after, "postflight named path")?;
    if after_handle != before_identity || named_after_identity != before_identity
        || after_path_stamp != before_path_stamp
    {
        return Err("C491 H21 frame identity/metadata changed during selector".into());
    }
    drop(named_after);

    println!(
        "C491_GENESIS_HEADER_ZERO_NATIVE_PASS owner=0 class=Genesis producer_calls=1 frame_parses=1 contexts=2 header_claims=4096 packed_zero=4096 parent_bound=true frame_bytes_before=1321781831 frame_sha256_before={FRAME_SHA256_UPPER} frame_bytes_after=1321781831 frame_sha256_after={FRAME_SHA256_UPPER} proof=false client=false full_history=false full_x=false global_row=false production=false"
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}

//! One pinned-frame common-parent observation with distinct owner bindings.

use super::*;
use crate::daa_history_roster::{DaaHistoryRoster, OwnerClass};
use std::{
    fs::{Metadata, OpenOptions},
    io::{Seek, SeekFrom},
    os::windows::{fs::{MetadataExt, OpenOptionsExt}, io::AsRawHandle},
    time::SystemTime,
};

const FRAME_SHA256_UPPER: &str =
    "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E";
const GENESIS_OWNER: usize = 0;
const SCORE_OWNER: usize = 845_887;
const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0400;
const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;

// Stable Windows BY_HANDLE_FILE_INFORMATION layout. Reading may update the
// last-access time, so that field is excluded from retained-file identity.
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
            "C494 {label} handle identity: {}",
            std::io::Error::last_os_error(),
        ));
    }
    if identity.attributes & 0x410 != 0 || identity.links != 1
        || ((u64::from(identity.size_high) << 32) | u64::from(identity.size_low)) != FRAME_BYTES
    {
        return Err(format!(
            "C494 {label} is not a regular non-reparse single-link pinned-size file",
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
        return Err(format!("C494 {label} is not a regular non-reparse file"));
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

fn lower_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed single-process bounded Job required"]
fn c494_common_parent_native_selector() -> Result<(), String> {
    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("C494 pinned H21 frame path required")?;
    if !crate::preview_test_paths::absolute_outside_source(Path::new(&frame_path)) {
        return Err("C494 H21 frame path must be absolute and outside source".into());
    }
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C494 H21 frame path must be absolute".into());
    }
    let before_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    let before_path_stamp = path_stamp(&before_path, "pre-open path")?;
    if before_path_stamp.size != FRAME_BYTES {
        return Err("C494 pinned H21 frame length".into());
    }

    // One held handle denies write/delete sharing for both hashes and the
    // sole parse. Ancestor reparse rejection remains a runner obligation.
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
        return Err("C494 path/handle length mismatch".into());
    }
    let opened_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if path_stamp(&opened_path, "opened path")? != before_path_stamp {
        return Err("C494 frame path metadata changed during open".into());
    }
    let named_file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .custom_flags(FILE_FLAG_OPEN_REPARSE_POINT)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if handle_identity(&named_file, "opened named path")? != before_identity {
        return Err("C494 opened path/held handle identity mismatch".into());
    }
    drop(named_file);

    hash_retained_frame(&mut file)?;
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
    let mut frame = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        // The shared iterator emits exactly the thirteen pinned progress
        // heights for N headers; no separate progress parse occurs here.
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C494 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C494 H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    if roster.owner_class(GENESIS_OWNER as u64)? != OwnerClass::Genesis {
        return Err("C494 owner0 is not Genesis".into());
    }
    let context = crate::packed_owner_assembly::H21EligibleContext::new(&plan, &prefix)?;
    let genesis_binding = HeaderSourceBinding::for_plan(&plan, GENESIS_OWNER)?;
    let score_binding = HeaderSourceBinding::for_plan(&plan, SCORE_OWNER)?;
    let cut = crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
    let layout = crate::header_daa_row_placement::Layout::fixed().digest();
    if genesis_binding == score_binding {
        return Err("C494 distinct owner bindings unexpectedly equal".into());
    }
    for (binding, owner) in [(&genesis_binding, GENESIS_OWNER), (&score_binding, SCORE_OWNER)] {
        if !binding.matches_sink(prefix.root(), prefix.total_be28(), prefix.profile(), &cut, owner) {
            return Err("C494 separate common-parent binding validation".into());
        }
    }

    // This checked success retains and revalidates the exact owner0 result
    // and bundle alongside the installed Score carrier. It authenticates all
    // 4096 false claims/final packed bits and the five installed counts below.
    // The helper makes exactly one owner0 destination production call.
    super::candidate494_combined_owner0_score::c494_combined_owner0_score_compile_only(
        &plan, &prefix, &context,
    )?;
    let root_hex = lower_hex(&prefix.root());
    let total_hex = lower_hex(&prefix.total_be28());
    let profile_hex = lower_hex(&prefix.profile());
    let cut_hex = lower_hex(&cut);
    let layout_hex = lower_hex(&layout);
    drop(context);
    drop(roster);
    drop(plan);
    drop(prefix);

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
        return Err("C494 H21 frame identity/metadata changed during selector".into());
    }
    drop(named_after);

    println!(
        "C494_COMMON_PARENT_NATIVE_PASS selector=c494_common_parent_native_selector version=1 frame_parses=1 frame_bytes_before=1321781831 frame_sha256_before={FRAME_SHA256_UPPER} frame_bytes_after=1321781831 frame_sha256_after={FRAME_SHA256_UPPER} parent_root={root_hex} parent_total={total_hex} profile={profile_hex} cut={cut_hex} layout={layout_hex} owner0=0 owner845887=845887 owner0_binding_valid=true owner845887_binding_valid=true owner_bindings_equal=false common_parent=true owner0_class=Genesis owner0_destination_production_calls=1 header_claims=4096 packed_zero=4096 terms=17864 row_leases=7516 assignments=4870 reservations=4870 score_reads=1028 full_owner_row=false full_x=false common_x=false global_row=false eq26=false full_eq26=false g_final_x=false pcs=false proof=false client=false production=false"
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}

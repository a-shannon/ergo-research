//! One pinned-frame observation of both clipped owners' HeaderZero custody.

use super::*;
use crate::daa_history_roster::{DaaHistoryRoster, OwnerClass};
use crate::packed_owner_assembly::H21EligibleContext;
use std::{
    fs::{Metadata, OpenOptions},
    io::{Seek, SeekFrom},
    os::windows::{fs::{MetadataExt, OpenOptionsExt}, io::AsRawHandle},
    time::SystemTime,
};

const FRAME_SHA256_UPPER: &str =
    "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E";
const CONTEXT0_OWNER: usize = 1_810_904;
const CONTEXT1_OWNER: usize = 1_810_841;
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
            "C497 {label} handle identity: {}",
            std::io::Error::last_os_error(),
        ));
    }
    if identity.attributes & 0x410 != 0 || identity.links != 1
        || ((u64::from(identity.size_high) << 32) | u64::from(identity.size_low)) != FRAME_BYTES
    {
        return Err(format!(
            "C497 {label} is not a regular non-reparse single-link pinned-size file",
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
        return Err(format!("C497 {label} is not a regular non-reparse file"));
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
fn c497_clipped_header_zero_native_selector() -> Result<(), String> {
    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("C497 pinned H21 frame path required")?;
    if !crate::preview_test_paths::absolute_outside_source(Path::new(&frame_path)) {
        return Err("C497 H21 frame path must be absolute and outside source".into());
    }
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C497 H21 frame path must be absolute".into());
    }
    let before_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    let before_path_stamp = path_stamp(&before_path, "pre-open path")?;
    if before_path_stamp.size != FRAME_BYTES {
        return Err("C497 pinned H21 frame length".into());
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
        return Err("C497 path/handle length mismatch".into());
    }
    let opened_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if path_stamp(&opened_path, "opened path")? != before_path_stamp {
        return Err("C497 frame path metadata changed during open".into());
    }
    let named_file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .custom_flags(FILE_FLAG_OPEN_REPARSE_POINT)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if handle_identity(&named_file, "opened named path")? != before_identity {
        return Err("C497 opened path/held handle identity mismatch".into());
    }
    drop(named_file);

    hash_retained_frame(&mut file)?;
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
    let mut frame = super::FrameReader::new(
        BufReader::with_capacity(CHUNK, &mut file), FRAME_BYTES,
    )?;
    super::preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        // The shared iterator emits the thirteen pinned H21 progress heights.
        let mut headers = super::HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C497 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C497 H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    for owner in [CONTEXT0_OWNER, CONTEXT1_OWNER] {
        if roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("C497 clipped owner is not Carry".into());
        }
    }
    let context = H21EligibleContext::new(&plan, &prefix)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let binding0 = HeaderSourceBinding::for_plan(&plan, CONTEXT0_OWNER)?;
    let binding1 = HeaderSourceBinding::for_plan(&plan, CONTEXT1_OWNER)?;
    let cut = crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
    let layout = crate::header_daa_row_placement::Layout::fixed().digest();
    if binding0 == binding1 {
        return Err("C497 distinct owner bindings unexpectedly equal".into());
    }
    for (binding, owner) in [(&binding0, CONTEXT0_OWNER), (&binding1, CONTEXT1_OWNER)] {
        if !binding.matches_sink(prefix.root(), prefix.total_be28(), prefix.profile(), &cut, owner) {
            return Err("C497 separate common-parent binding validation".into());
        }
    }

    // Both leases come from this context's generated Maps and native imports.
    // The producer derives the fixed active context from each exact owner.
    let lease0 = context.map_pair_lease(CONTEXT0_OWNER)?;
    let lease1 = context.map_pair_lease(CONTEXT1_OWNER)?;
    if lease0.binding() != &binding0 || lease1.binding() != &binding1 {
        return Err("C497 exact owner Map pair bindings".into());
    }
    lease0.checked_cells(&binding0, CONTEXT0_OWNER, OwnerClass::Carry)?;
    lease1.checked_cells(&binding1, CONTEXT1_OWNER, OwnerClass::Carry)?;
    let retained0 = producer.produce_clipped_header_zero_with_map_pair(CONTEXT0_OWNER, &lease0)?;
    let retained1 = producer.produce_clipped_header_zero_with_map_pair(CONTEXT1_OWNER, &lease1)?;

    // Each opaque result checks the complete 2,822-cell exclusive capture,
    // final packed zeros, full binding and the original borrowed lease object.
    // Retain and revalidate both after the second destination production.
    retained0.validate_for(&binding0, &lease0)?;
    retained1.validate_for(&binding1, &lease1)?;
    let root_hex = lower_hex(&prefix.root());
    let total_hex = lower_hex(&prefix.total_be28());
    let profile_hex = lower_hex(&prefix.profile());
    let cut_hex = lower_hex(&cut);
    let layout_hex = lower_hex(&layout);
    drop(retained1);
    drop(retained0);
    drop(lease1);
    drop(lease0);
    drop(producer);
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
        return Err("C497 H21 frame identity/metadata changed during selector".into());
    }
    drop(named_after);

    println!(
        "C497_CLIPPED_HEADER_ZERO_NATIVE_PASS selector=c497_clipped_header_zero_native_selector version=1 frame_parses=1 frame_bytes_before=1321781831 frame_sha256_before={FRAME_SHA256_UPPER} frame_bytes_after=1321781831 frame_sha256_after={FRAME_SHA256_UPPER} parent_root={root_hex} parent_total={total_hex} profile={profile_hex} cut={cut_hex} layout={layout_hex} owner0=1810904 active_context0=0 owner1=1810841 active_context1=1 owner0_class=Carry owner1_class=Carry owner0_binding_valid=true owner1_binding_valid=true owner_bindings_equal=false common_parent=true map_pair_leases=2 destination_production_calls=2 validated_header_zero_cells0=2822 validated_header_zero_cells1=2822 validated_packed_zero0=2822 validated_packed_zero1=2822 exact_lease_identity=true clipped_score=false full_owner_row=false full_x=false common_x=false global_row=false eq26=false full_eq26=false g_final_x=false pcs=false proof=false client=false production=false"
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}

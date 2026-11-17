//! One pinned-frame join of both clipped Score relations to physical authors.

use super::*;
use crate::daa_history_roster::{DaaHistoryRoster, OwnerClass};
use crate::h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxStream, Plan as MaxPlan};
use crate::h21_scheduled_family_ledger::Admission;
use crate::packed_owner_assembly::{
    ClippedScoreReadAuthorBundle, H21EligibleContext, ScoredOwnerPackingView,
};
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
const CONTEXT0_PREDECESSOR: usize = 1_810_879;
const CONTEXT1_PREDECESSOR: usize = 1_810_751;
const MAX_OWNERS: usize = 7_683;
const SCORE_PUSHES: usize = 7_542;
const SCORE_RECORDS: usize = 7_543;
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
            "C501 {label} handle identity: {}",
            std::io::Error::last_os_error(),
        ));
    }
    if identity.attributes & 0x410 != 0 || identity.links != 1
        || ((u64::from(identity.size_high) << 32) | u64::from(identity.size_low)) != FRAME_BYTES
    {
        return Err(format!(
            "C501 {label} is not a regular non-reparse single-link pinned-size file",
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
        return Err(format!("C501 {label} is not a regular non-reparse file"));
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
fn c501_clipped_score_read_authors_native_selector() -> Result<(), String> {
    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("C501 pinned H21 frame path required")?;
    if !crate::preview_test_paths::absolute_outside_source(Path::new(&frame_path)) {
        return Err("C501 H21 frame path must be absolute and outside source".into());
    }
    let frame_path = Path::new(&frame_path);
    if !frame_path.is_absolute() {
        return Err("C501 H21 frame path must be absolute".into());
    }
    let before_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    let before_path_stamp = path_stamp(&before_path, "pre-open path")?;
    if before_path_stamp.size != FRAME_BYTES {
        return Err("C501 pinned H21 frame length".into());
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
        return Err("C501 path/handle length mismatch".into());
    }
    let opened_path = fs::symlink_metadata(frame_path).map_err(|error| error.to_string())?;
    if path_stamp(&opened_path, "opened path")? != before_path_stamp {
        return Err("C501 frame path metadata changed during open".into());
    }
    let named_file = OpenOptions::new()
        .read(true)
        .share_mode(1)
        .custom_flags(FILE_FLAG_OPEN_REPARSE_POINT)
        .open(frame_path)
        .map_err(|error| error.to_string())?;
    if handle_identity(&named_file, "opened named path")? != before_identity {
        return Err("C501 opened path/held handle identity mismatch".into());
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
            return Err("C501 H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C501 H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    )?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    for owner in [CONTEXT0_OWNER, CONTEXT1_OWNER] {
        if roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("C501 clipped owner is not Carry".into());
        }
    }
    let context = H21EligibleContext::new(&plan, &prefix)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let binding0 = HeaderSourceBinding::for_plan(&plan, CONTEXT0_OWNER)?;
    let binding1 = HeaderSourceBinding::for_plan(&plan, CONTEXT1_OWNER)?;
    let cut = crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
    let layout = crate::header_daa_row_placement::Layout::fixed().digest();
    if binding0 == binding1 {
        return Err("C501 distinct owner bindings unexpectedly equal".into());
    }
    for (binding, owner) in [(&binding0, CONTEXT0_OWNER), (&binding1, CONTEXT1_OWNER)] {
        if !binding.matches_sink(prefix.root(), prefix.total_be28(), prefix.profile(), &cut, owner) {
            return Err("C501 separate common-parent binding validation".into());
        }
    }

    // Close MAX and Score from this same parsed prefix. No fixture or imported
    // relation can enter either stream.
    let snapshot = Eligible08NativeSnapshot::new(&plan, &prefix)?;
    let mut closed_max = MaxStream::new(&plan, &prefix, &snapshot)?;
    let max_calendar = MaxPlan::eligible08().max_calendar();
    if max_calendar.len() != MAX_OWNERS || closed_max.remaining_owners() != MAX_OWNERS {
        return Err("C501 MAX source calendar census".into());
    }
    for (owner, _) in max_calendar {
        closed_max.push_native(&producer, owner)?;
    }
    closed_max.closed_native_snapshot(&plan, &prefix)?;

    let mut closed_score = context.score_endpoint_stream(&closed_max)?;
    let mut score_pushes = 0usize;
    while let Some(owner) = closed_score.next_owner() {
        if score_pushes >= SCORE_PUSHES {
            return Err("C501 Score source calendar bound".into());
        }
        closed_score.push_native(owner)?;
        score_pushes += 1;
    }
    if score_pushes != SCORE_PUSHES || !closed_score.is_closed()
        || closed_score.remaining_owners() != 0
    {
        return Err("C501 terminal Score source closure".into());
    }
    closed_score.terminal_r()?;

    // Destination relations and both predecessor candidates are minted from
    // the same closed native MAX/Score streams and remain alive together.
    let relation0 = closed_score.closed_owner_relation(CONTEXT0_OWNER)?;
    let relation1 = closed_score.closed_owner_relation(CONTEXT1_OWNER)?;
    for (relation, binding, owner) in [
        (&relation0, &binding0, CONTEXT0_OWNER),
        (&relation1, &binding1, CONTEXT1_OWNER),
    ] {
        if relation.owner() != owner || relation.parent_root() != prefix.root()
            || relation.parent_total() != prefix.total_be28()
            || relation.parent_profile() != prefix.profile() || relation.cut_identity() != cut
            || binding.owner() != owner
        {
            return Err("C501 terminal Score common-parent identity".into());
        }
    }

    let predecessor_relation0 = closed_score.closed_owner_relation(CONTEXT0_PREDECESSOR)?;
    let predecessor_relation1 = closed_score.closed_owner_relation(CONTEXT1_PREDECESSOR)?;
    let predecessor_join0 = context.join_scored_owner_source(
        CONTEXT0_PREDECESSOR, predecessor_relation0, &closed_max)?;
    let predecessor_join1 = context.join_scored_owner_source(
        CONTEXT1_PREDECESSOR, predecessor_relation1, &closed_max)?;
    let predecessor0 = producer.produce_scored_owner_packed_source_lease(
        ScoredOwnerPackingView::from_checked_join(predecessor_join0)?)?;
    let predecessor1 = producer.produce_scored_owner_packed_source_lease(
        ScoredOwnerPackingView::from_checked_join(predecessor_join1)?)?;
    if predecessor0.owner() != CONTEXT0_PREDECESSOR
        || predecessor1.owner() != CONTEXT1_PREDECESSOR
    {
        return Err("C501 predecessor owner identity".into());
    }

    let lease0 = context.map_pair_lease(CONTEXT0_OWNER)?;
    let lease1 = context.map_pair_lease(CONTEXT1_OWNER)?;
    if lease0.binding() != &binding0 || lease1.binding() != &binding1 {
        return Err("C501 exact owner Map pair bindings".into());
    }
    lease0.checked_cells(&binding0, CONTEXT0_OWNER, OwnerClass::Carry)?;
    lease1.checked_cells(&binding1, CONTEXT1_OWNER, OwnerClass::Carry)?;
    relation0.require_original_map_bindings([
        lease0.map_binding(0)?, lease0.map_binding(1)?,
    ])?;
    relation1.require_original_map_bindings([
        lease1.map_binding(0)?, lease1.map_binding(1)?,
    ])?;

    let closed_snapshot = closed_max.closed_native_snapshot(&plan, &prefix)?;
    let admission = Admission::new(&plan, &prefix, closed_snapshot)?;
    if ClippedScoreReadAuthorBundle::new(
        &relation0, &predecessor1,
        admission.scored_owner_cap_publication(CONTEXT0_OWNER)?, &producer, 0,
    ).is_ok() {
        return Err("C501 accepted cross-context predecessor candidate 1->0".into());
    }
    if ClippedScoreReadAuthorBundle::new(
        &relation1, &predecessor0,
        admission.scored_owner_cap_publication(CONTEXT1_OWNER)?, &producer, 1,
    ).is_ok() {
        return Err("C501 accepted cross-context predecessor candidate 0->1".into());
    }
    if ClippedScoreReadAuthorBundle::new(
        &relation0, &predecessor0,
        admission.scored_owner_cap_publication(CONTEXT1_OWNER)?, &producer, 0,
    ).is_ok() {
        return Err("C501 accepted cross-context Cap publication 1->0".into());
    }
    if ClippedScoreReadAuthorBundle::new(
        &relation1, &predecessor1,
        admission.scored_owner_cap_publication(CONTEXT0_OWNER)?, &producer, 1,
    ).is_ok() {
        return Err("C501 accepted cross-context Cap publication 0->1".into());
    }

    let retained0 = producer.produce_clipped_score_with_map_pair(&relation0, &lease0, 0)?;
    let retained1 = producer.produce_clipped_score_with_map_pair(&relation1, &lease1, 1)?;
    let bundle0 = ClippedScoreReadAuthorBundle::new(
        &relation0, &predecessor0,
        admission.scored_owner_cap_publication(CONTEXT0_OWNER)?, &producer, 0)?;
    let bundle1 = ClippedScoreReadAuthorBundle::new(
        &relation1, &predecessor1,
        admission.scored_owner_cap_publication(CONTEXT1_OWNER)?, &producer, 1)?;
    if retained0.census() != (2_048, 8_545, 514, 2_822)
        || retained1.census() != (2_048, 8_545, 514, 2_822)
        || bundle0.census()? != (225, 65, 224, 514)
        || bundle1.census()? != (225, 65, 224, 514)
    {
        return Err("C501 clipped destination/author census".into());
    }
    bundle0.validate()?;
    bundle1.validate()?;
    retained0.validate_for(&binding0, &lease0)?;
    retained1.validate_for(&binding1, &lease1)?;

    let root_hex = lower_hex(&prefix.root());
    let total_hex = lower_hex(&prefix.total_be28());
    let profile_hex = lower_hex(&prefix.profile());
    let cut_hex = lower_hex(&cut);
    let layout_hex = lower_hex(&layout);
    drop(bundle1);
    drop(bundle0);
    drop(retained1);
    drop(retained0);
    drop(predecessor1);
    drop(predecessor0);
    drop(admission);
    drop(lease1);
    drop(lease0);
    drop(relation1);
    drop(relation0);
    drop(closed_score);
    drop(closed_max);
    drop(snapshot);
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
        return Err("C501 H21 frame identity/metadata changed during selector".into());
    }
    drop(named_after);

    println!(
        "C501_CLIPPED_SCORE_NATIVE_PASS selector=c501_clipped_score_read_authors_native_selector version=1 frame_parses=1 frame_bytes_before=1321781831 frame_sha256_before={FRAME_SHA256_UPPER} frame_bytes_after=1321781831 frame_sha256_after={FRAME_SHA256_UPPER} parent_root={root_hex} parent_total={total_hex} profile={profile_hex} cut={cut_hex} layout={layout_hex} owner0=1810904 active_context0=0 owner1=1810841 active_context1=1 owner0_class=Carry owner1_class=Carry owner0_binding_valid=true owner1_binding_valid=true owner_bindings_equal=false common_parent=true max_owners=7683 score_owners={SCORE_RECORDS} score_relations=2 map_pair_leases=2 destination_production_calls=2 validated_score_cells0=2048 validated_score_cells1=2048 validated_score_terms0=8545 validated_score_terms1=8545 validated_score_reads0=514 validated_score_reads1=514 validated_header_zero_cells0=2822 validated_header_zero_cells1=2822 validated_packed_score0=2048 validated_packed_score1=2048 validated_packed_header_zero0=2822 validated_packed_header_zero1=2822 exact_relation_borrows=true exact_lease_identity=true clipped_score_native=true predecessor_candidates=2 cap_publications=2 author_bundles=2 previous_reads_each=225 cap_reads_each=65 work_upper_reads_each=224 foreign_reads_physically_authenticated=true cross_predecessor_rejected=true cross_cap_rejected=true full_owner_row=false full_x=false common_x=false global_row=false eq26=false full_eq26=false g_final_x=false pcs=false proof=false client=false production=false upstream_acceptance=false"
    );
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    Ok(())
}


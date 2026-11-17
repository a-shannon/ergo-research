//! Test-only H21 admission and physical Bank53 Map component join from a pinned
//! ERFV frame. This does not build a complete shared witness or proof.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    io::{BufReader, Read, Write},
    path::Path,
    time::Instant,
};

use ark_bn254::Fr;
use ark_ff::Zero;
use num_bigint::{BigInt, BigUint};
use serde_json::Value;

use crate::{
    legacy_envelope_map::{Import, Inputs, Kind, LowerBranch, LowerSelector, LowerSource, Map},
    native_owner_exports::NativeExports,
    native_prefix_auth_plan::role0_sha256,
    packed_owner_assembly::{
        flip_native_row_bit_for_test, mutate_native_row_parent_for_test,
        truncate_native_row_for_test, validate_h21_bank53_map_lane_for_test,
        validate_native_bank53_map_consumer, validate_native_plan_input, HeaderSourceBinding,
        MatureEipResolvedCell, MatureEipSourceCell, NativeMatureEipResolvedSource,
        NativeMatureEipSourceMatrix, NativeOwnerProducer, NativePackedRow, NativePrefix,
    },
    work_tree_history_plan::WorkTreeHistoryPlan,
};

#[path = "h21_native_admission_tests/candidate319_ab_extract.rs"]
mod candidate319_ab_extract;

#[path = "h21_native_admission_tests/candidate320_field_consumer.rs"]
mod candidate320_field_consumer;

#[path = "h21_native_admission_tests/candidate330_role3_projection.rs"]
mod candidate330_role3_projection;

#[path = "h21_native_admission_tests/candidate339_point_window.rs"]
mod candidate339_point_window;

#[path = "h21_native_admission_tests/candidate344_closed_max_cap_census.rs"]
mod candidate344_closed_max_cap_census;

#[path = "h21_native_admission_tests/candidate350_native_owner_u0.rs"]
mod candidate350_native_owner_u0;

#[path = "h21_native_admission_tests/candidate391_ab_typed_role4.rs"]
mod candidate391_ab_typed_role4;

#[path = "h21_native_admission_tests/candidate95_map_packed_join.rs"]
mod candidate95_map_packed_join;

#[path = "h21_native_admission_tests/candidate126_d_max.rs"]
mod candidate126_d_max;

#[path = "h21_native_admission_tests/candidate131_native_q9.rs"]
mod candidate131_native_q9;

#[path = "h21_native_admission_tests/candidate135_native_work_max.rs"]
mod candidate135_native_work_max;

#[path = "h21_native_admission_tests/candidate135_native_values.rs"]
mod candidate135_native_values;

#[path = "h21_native_admission_tests/candidate136_native_bundle.rs"]
mod candidate136_native_bundle;

#[path = "h21_native_admission_tests/candidate138_native_global_u.rs"]
mod candidate138_native_global_u;

#[path = "h21_native_admission_tests/candidate146_native_session.rs"]
mod candidate146_native_session;

#[path = "h21_native_admission_tests/candidate151_native_daa.rs"]
mod candidate151_native_daa;

#[path = "h21_native_admission_tests/candidate154_common_roster.rs"]
mod candidate154_common_roster;

#[path = "h21_native_admission_tests/candidate155_two_domain_common_x.rs"]
mod candidate155_two_domain_common_x;

#[path = "h21_native_admission_tests/candidate435_factorized_global_x_toy.rs"]
mod candidate435_factorized_global_x_toy;

#[path = "h21_native_admission_tests/candidate436_genesis_map_coordinates.rs"]
mod candidate436_genesis_map_coordinates;

#[path = "h21_native_admission_tests/candidate438_map_pair_source.rs"]
mod candidate438_map_pair_source;

#[path = "h21_native_admission_tests/candidate441_first_score_anchor.rs"]
mod candidate441_first_score_anchor;

#[path = "h21_native_admission_tests/candidate491_genesis_header_zero.rs"]
mod candidate491_genesis_header_zero;

#[path = "h21_native_admission_tests/candidate494_combined_owner0_score.rs"]
mod candidate494_combined_owner0_score;

#[path = "h21_native_admission_tests/candidate494_common_parent_native_gate.rs"]
mod candidate494_common_parent_native_gate;

#[path = "h21_native_admission_tests/candidate495_common_parent_native_gate.rs"]
mod candidate495_common_parent_native_gate;

#[path = "h21_native_admission_tests/candidate497_clipped_header_zero_native_gate.rs"]
mod candidate497_clipped_header_zero_native_gate;

#[path = "h21_native_admission_tests/candidate499_clipped_score_native_gate.rs"]
mod candidate499_clipped_score_native_gate;

#[path = "h21_native_admission_tests/candidate501_clipped_score_read_authors_native.rs"]
mod candidate501_clipped_score_read_authors_native;

#[path = "h21_native_admission_tests/candidate443_second_score_anchor.rs"]
mod candidate443_second_score_anchor;

#[path = "h21_native_admission_tests/candidate448b_authenticated_anchor_reader.rs"]
mod candidate448b_authenticated_anchor_reader;

#[path = "h21_native_admission_tests/candidate449b_authentic_padding.rs"]
mod candidate449b_authentic_padding;

#[path = "h21_native_admission_tests/candidate450_mixed_map_header.rs"]
mod candidate450_mixed_map_header;

#[path = "h21_native_admission_tests/candidate186_native_full_max.rs"]
mod candidate186_native_full_max;

#[path = "h21_native_admission_tests/candidate187_native_score.rs"]
mod candidate187_native_score;

#[path = "h21_native_admission_tests/candidate206_native_r450.rs"]
mod candidate206_native_r450;

#[path = "h21_native_admission_tests/candidate587_native_owner_values.rs"]
mod candidate587_native_owner_values;

const N: usize = 1_827_840;
const H: usize = 21;
const CHUNK: usize = 65_536;
const FRAME_BYTES: u64 = 1_321_781_831;
const FRAME_SHA256: &str = "a68d86562a56c5b71cf2180e4762bf8775b1061b6953bff7281ec50b7ee52c5e";
const PREFIX_BYTES: u64 = 436_881_872;
const TAIL_BYTES: u64 = 884_899_959;
const EXTENSIONS: u64 = 1_785;
const D_BYTES: u64 = 131_501;
const D_SHA256: &str = "97541ee3cdc7fc12942e6904f277241d2ac74edbf4794a1f477f9b1bae1424e9";
const B_BYTES: u64 = 68_166;
const B_SHA256: &str = "f840b3a55c7187f69a8b5fc939da1aaaaedac59e9984cdc3b1be1c5366561edd";
const D_MAX_HEIGHT: u64 = 841_729;
const D_MAX: &str = "21673152299925504";
const B_MAX_Q: u64 = 821;
const B_MAX: &str = "22610951816408797";
const E: usize = 55;
const LOWER_PIVOT: usize = 54;
const BANK53_BASE: usize = 671_744;
const BANK53_CONTEXT_BITS: usize = 8_192;
const BANK53_MAP_LIVE_BITS: usize = 5_757;
const OWNER_ROW_BITS: usize = 1 << 20;
const OWNER_ROW_BYTES: usize = OWNER_ROW_BITS / 8;
const REAL_PCS_LOG_N: usize = 41;
const REAL_SIGMA_BITS: usize = 1 << 21;
const REAL_SIGMA_ROW_BYTES: usize = REAL_SIGMA_BITS / 8;
const REAL_FIRST_OWNER: usize = 841_726;
const REAL_SECOND_OWNER: usize = 841_727;
const REAL_EXPECTED_ROW: usize = 420_863;

// This producer is deliberately isolated from the PCS consumer. Returning
// only the canonical row drops the parsed frame/prefix and owner intermediates
// before the caller constructs log41 Dory setup and vectors.
fn produce_real_sigma21_row_from_pinned_frame() -> Vec<u8> {
    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = File::open(path).expect("open pinned H21 frame");
    assert_eq!(
        file.metadata().unwrap().len(),
        FRAME_BYTES,
        "opened frame length"
    );
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact ERFV header prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact ERFV extension count");
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(
        after.len(),
        FRAME_BYTES,
        "frame length after complete SHA256"
    );

    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    ).expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("source-owned producer bound to admitted prefix");
    let even = producer.produce(REAL_FIRST_OWNER).expect("real even owner row");
    let odd = producer.produce(REAL_SECOND_OWNER).expect("real odd owner row");
    assert_eq!(even.owner(), REAL_FIRST_OWNER);
    assert_eq!(odd.owner(), REAL_SECOND_OWNER);
    assert_eq!(even.packed_bytes().len(), OWNER_ROW_BYTES);
    assert_eq!(odd.packed_bytes().len(), OWNER_ROW_BYTES);
    assert_eq!(REAL_FIRST_OWNER & 1, 0);
    assert_eq!(REAL_SECOND_OWNER, REAL_FIRST_OWNER + 1);
    assert_eq!(REAL_FIRST_OWNER / 2, REAL_EXPECTED_ROW);
    assert_eq!(REAL_FIRST_OWNER / 2, REAL_SECOND_OWNER / 2);
    assert_ne!(H, REAL_PCS_LOG_N, "history log must remain distinct from PCS log");
    assert_eq!(1usize << (REAL_PCS_LOG_N / 2), OWNER_ROW_BITS);
    assert_eq!(1usize << REAL_PCS_LOG_N.div_ceil(2), REAL_SIGMA_BITS);

    let mut joined = Vec::with_capacity(REAL_SIGMA_ROW_BYTES);
    joined.extend_from_slice(even.packed_bytes());
    joined.extend_from_slice(odd.packed_bytes());
    assert_eq!(joined.len(), REAL_SIGMA_ROW_BYTES);

    // Explicitly end every producer-side owner before the consumer is called.
    drop(even);
    drop(odd);
    drop(producer);
    drop(plan);
    drop(prefix);
    let row_sha256 = hex(&role0_sha256(&joined).expect("joined row SHA-256"));
    println!("CANDIDATE85_OWNER_ROW_RECONSTRUCTED owners={REAL_FIRST_OWNER},{REAL_SECOND_OWNER} row={REAL_EXPECTED_ROW} bytes={} sha256={row_sha256} prior_candidate83_row_sha256=unavailable full_h21_witness=false", joined.len());
    std::io::stdout().flush().expect("row reconstruction marker flush");
    joined
}

#[test]
#[ignore = "pinned full H21 frame; bounded runner and source review required"]
fn c342_native_header_q14908_source_to_row_read() -> Result<(), String> {
    use crate::header_daa_row_placement::{Relation,RowPlan,SourceRead};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    const OWNER:usize=845_759;
    const ROWS:usize=1<<19;
    const WIDTH:usize=1<<20;
    let path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path=Path::new(&path);
    if !path.is_absolute(){return Err("H21 frame path must be absolute".into());}
    let before=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len()!=FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file=File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0{return Err("H21 frame RAW records incomplete".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N || frame.offset!=PREFIX_BYTES || extensions!=EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if after.len()!=before.len() || after.modified().map_err(|e|e.to_string())?
        !=before.modified().map_err(|e|e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    validate_native_plan_input(&plan,&prefix)?;
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix)?;
    let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&plan)?;
    let scheduled=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&scheduled)?;
    let batch=row_plan.stage_owner(OWNER)?;
    let target=batch.active_operands().find(|operand|
        operand.relation==Relation::Header && operand.row==OWNER*ROWS+14_908
            && operand.wire==OWNER*WIDTH+526_330)
        .ok_or("retained native HEADER NOT q14908/X526330")?;
    let mut lease=producer.header_source_lease(OWNER)?;
    let value=match batch.resolve_one(target.occurrence,target.side,&lease)? {
        SourceRead::Header{operand,value} if operand==target=>value,
        _=>return Err("native HEADER source read unresolved or changed".into()),
    };
    let row=producer.produce(OWNER)?;
    row.validate_identity_for_history_test(&plan,&prefix,OWNER)?;
    let local=target.wire-OWNER*WIDTH;
    let packed=row.packed_bytes()[local/8]&(1<<(local%8))!=0;
    if value!=packed{return Err("native HEADER lease/packed owner bit mismatch".into());}
    let admitted=lease.read_count_for_test();
    lease.wrong_author_mutant_for_test();
    let error=batch.resolve_one(target.occurrence,target.side,&lease).err()
        .ok_or("wrong native HEADER author admitted")?;
    if !error.contains("author mismatch before read admission")
        || lease.read_count_for_test()!=admitted {
        return Err("wrong native HEADER author reached value read".into());
    }
    Ok(())
}

#[test]
#[ignore = "pinned full H21 frame; bounded native HEADER/DAA ROW runner required"]
fn c347_native_header_daa_active_union_from_pinned_frame() -> Result<(), String> {
    use crate::daa_history_roster::{DaaHistoryRoster,BANKS};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::{NativeRead,RowPlan,UnresolvedRead};
    use crate::packed_owner_assembly::{HeaderSourceBinding,NativeHeaderSourceLease};
    const OWNER:usize=844_672;
    const WIDTH:usize=1<<20;
    let path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path=Path::new(&path);
    if !path.is_absolute(){return Err("H21 frame path must be absolute".into());}
    let before=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len()!=FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file=File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0{return Err("H21 frame RAW records incomplete".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N || frame.offset!=PREFIX_BYTES || extensions!=EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if after.len()!=before.len() || after.modified().map_err(|e|e.to_string())?
        !=before.modified().map_err(|e|e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    validate_native_plan_input(&plan,&prefix)?;
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix)?;
    let (row,mut lease)=producer.produce_with_daa_source_lease(OWNER)?;
    row.validate_identity_for_history_test(&plan,&prefix,OWNER)?;
    let roster=DaaHistoryRoster::compile(&plan)?;
    let scheduled=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&scheduled)?;
    let joined=row_plan.stage_owner_with_daa_reads(OWNER,&lease)?;
    let mut source_reads=joined.daa_reads();
    let mut active=0usize;
    for operand in joined.batch().active_operands() {
        let Some(local)=operand.wire.checked_sub(OWNER*WIDTH).filter(|local|*local<WIDTH) else {continue;};
        if !BANKS.iter().any(|&(start,end)|(start..end).contains(&local)){continue;}
        let read=source_reads.next().ok_or("missing active DAA bank read")?;
        let packed=row.packed_bytes()[local/8]&(1<<(local%8))!=0;
        if read.operand!=operand || read.value!=packed {
            return Err("native DAA author/active ROW/packed value mismatch".into());
        }
        active+=1;
    }
    if source_reads.next().is_some() || active==0 || joined.daa_reads().len()!=active
        || lease.read_count_for_test()!=active {
        return Err("native DAA active read occurrence census".into());
    }
    let binding=HeaderSourceBinding::for_plan(&plan,OWNER)?;
    let mut bank_bits=0usize;
    for (start,end) in BANKS {
        for local in start..end {
            let value=lease.read_daa_bit(&binding,OWNER*WIDTH+local)?
                .ok_or("native DAA bank bit missing")?;
            let packed=row.packed_bytes()[local/8]&(1<<(local%8))!=0;
            if value!=packed{return Err("native DAA full bank/packed value mismatch".into());}
            bank_bits+=1;
        }
    }
    if bank_bits!=81_920 || lease.read_count_for_test()!=active+bank_bits {
        return Err("native DAA full bank census".into());
    }
    let admitted=lease.read_count_for_test();
    if lease.read_daa_bit(&binding,OWNER*WIDTH)?.is_some()
        || lease.read_count_for_test()!=admitted {
        return Err("native DAA non-bank read admitted".into());
    }
    let foreign=lease.read_daa_bit(&binding,(OWNER+1)*WIDTH+BANKS[0].0).err()
        .ok_or("foreign DAA owner admitted")?;
    if !foreign.contains("physical owner") || lease.read_count_for_test()!=admitted {
        return Err("foreign DAA owner reached value read".into());
    }
    let wrong_owner=row_plan.stage_owner_with_daa_reads(OWNER+1,&lease).err()
        .ok_or("foreign DAA owner admitted by ROW join")?;
    if !wrong_owner.contains("root/total/profile/cut/layout/owner")
        || lease.read_count_for_test()!=admitted {
        return Err("foreign DAA owner reached ROW join value read".into());
    }
    let wrong_binding=HeaderSourceBinding::for_plan(&plan,OWNER+1)?;
    let wrong=lease.read_daa_bit(&wrong_binding,OWNER*WIDTH+BANKS[0].0).err()
        .ok_or("wrong DAA binding admitted")?;
    if !wrong.contains("root/total/profile/cut/layout/owner")
        || lease.read_count_for_test()!=admitted {
        return Err("wrong DAA binding reached value read".into());
    }
    let mut header=producer.header_source_lease(OWNER)?;
    let header_before=header.read_count_for_test();
    let daa_before=lease.read_count_for_test();
    let union=row_plan.stage_owner_with_native_reads(OWNER,&header,&lease)?;
    let mut reads=union.reads();
    let(mut header_reads,mut daa_reads,mut foreign_open,mut local_open)=(0usize,0usize,0usize,0usize);
    let mut first_bank=None;
    for operand in union.batch().active_operands() {
        let read=*reads.next().ok_or("missing active native read")?;
        let local=operand.wire.checked_sub(OWNER*WIDTH).filter(|local|*local<WIDTH);
        match read {
            NativeRead::Header{operand:actual,value} => {
                let local=local.ok_or("foreign wire resolved by HEADER")?;
                if actual!=operand || BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0) {
                    return Err("HEADER active read order/domain/value mismatch".into());
                }
                header_reads+=1;
            }
            NativeRead::Daa{operand:actual,value} => {
                let local=local.ok_or("foreign wire resolved by DAA")?;
                if actual!=operand || !BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0) {
                    return Err("DAA active read order/domain/value mismatch".into());
                }
                first_bank.get_or_insert((operand.wire,value));
                daa_reads+=1;
            }
            NativeRead::Cap0{..}|NativeRead::Cap1{..} =>
                return Err("native pre-Cap read join resolved Cap".into()),
            NativeRead::ForeignMax{..} =>
                return Err("native pre-C365 read join resolved foreign MAX".into()),
            NativeRead::PointMembership{..} =>
                return Err("native pre-C369 read join resolved point membership".into()),
            NativeRead::ForeignDaaLane2{..} =>
                return Err("native pre-C366 read join resolved foreign DAA".into()),
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::ForeignOwner} => {
                if actual!=operand || local.is_some() {
                    return Err("foreign open active read order/domain mismatch".into());
                }
                foreign_open+=1;
            }
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::UnqualifiedLocal} => {
                let local=local.ok_or("unqualified local read is foreign")?;
                if actual!=operand || BANKS.iter().any(|&(start,end)|(start..end).contains(&local)) {
                    return Err("unqualified local active read order/domain mismatch".into());
                }
                local_open+=1;
            }
        }
    }
    if reads.next().is_some() || header_reads==0 || daa_reads!=active
        || foreign_open==0 || local_open==0
        || union.reads().len()!=header_reads+daa_reads+foreign_open+local_open
        || header.read_count_for_test()!=header_before+header_reads
        || lease.read_count_for_test()!=daa_before+daa_reads {
        return Err("native HEADER/DAA active read occurrence census".into());
    }
    let(header_admitted,daa_admitted)=(header.read_count_for_test(),lease.read_count_for_test());
    let wrong=row_plan.stage_owner_with_native_reads(OWNER+1,&header,&lease).err()
        .ok_or("foreign owner admitted by native union")?;
    if !wrong.contains("root/total/profile/cut/layout/owner")
        || header.read_count_for_test()!=header_admitted
        || lease.read_count_for_test()!=daa_admitted {
        return Err("foreign owner reached native union value read".into());
    }
    let foreign_header=producer.header_source_lease(OWNER+1)?;
    let wrong=union.batch().checked_native_reads(&foreign_header,&lease).err()
        .ok_or("wrong HEADER binding admitted by native union")?;
    if !wrong.contains("HEADER source root/total/profile/cut/layout/owner")
        || foreign_header.read_count_for_test()!=0
        || lease.read_count_for_test()!=daa_admitted {
        return Err("wrong HEADER binding reached native union value read".into());
    }
    // A test-only author-shaped HEADER claim on a DAA bank must fail closed.
    let(bank_wire,bank_value)=first_bank.ok_or("no active DAA bank operand")?;
    let overlapping=NativeHeaderSourceLease::wrong_author_for_test(
        binding.clone(),bank_wire,bank_value).native_author_shape_for_test();
    let wrong=union.batch().checked_native_reads(&overlapping,&lease).err()
        .ok_or("concurrent HEADER/DAA bank claim admitted")?;
    if !wrong.contains("concurrent HEADER claim")
        || overlapping.read_count_for_test()!=1 {
        return Err("concurrent HEADER/DAA bank claim not isolated".into());
    }
    let daa_after_overlap=lease.read_count_for_test();
    header.wrong_author_mutant_for_test();
    let wrong=union.batch().checked_native_reads(&header,&lease).err()
        .ok_or("equal-value wrong HEADER author admitted by native union")?;
    if !wrong.contains("HEADER source author mismatch before read admission")
        || header.read_count_for_test()!=header_admitted
        || lease.read_count_for_test()!=daa_after_overlap {
        return Err("equal-value wrong HEADER author reached native union value read".into());
    }
    let good_header=producer.header_source_lease(OWNER)?;
    lease.wrong_author_mutant_for_test();
    let wrong=row_plan.stage_owner_with_daa_reads(OWNER,&lease).err()
        .ok_or("equal-value wrong DAA author admitted")?;
    if !wrong.contains("author mismatch before read admission")
        || lease.read_count_for_test()!=daa_after_overlap {
        return Err("equal-value wrong DAA author reached value read".into());
    }
    let wrong=union.batch().checked_native_reads(&good_header,&lease).err()
        .ok_or("equal-value wrong DAA author admitted by native union")?;
    if !wrong.contains("DAA source author mismatch before read admission")
        || good_header.read_count_for_test()!=0
        || lease.read_count_for_test()!=daa_after_overlap {
        return Err("equal-value wrong DAA author reached native union value read".into());
    }
    println!("C347_NATIVE_HEADER_DAA_ROW owner={OWNER} header_reads={header_reads} daa_reads={daa_reads} foreign_open={foreign_open} local_open={local_open} bank_bits={bank_bits} overlap_rejected=true wrong_authors_rejected=true global_x_row=false pcs_proof_client=false");
    Ok(())
}

#[test]
#[ignore = "pinned H21 frame; bounded native partial X/ROW owner runner required"]
fn c359_native_m1_partial_x_row_from_pinned_frame() -> Result<(), String> {
    use crate::daa_history_roster::{DaaHistoryRoster,BANKS,OwnerClass};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::{NativeRead,NativeXAuthor,RowPlan,UnresolvedRead};
    const OWNER:usize=2048;
    const WIDTH:usize=1<<20;
    let path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path=Path::new(&path);
    if !path.is_absolute(){return Err("H21 frame path must be absolute".into());}
    let before=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len()!=FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file=File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0{return Err("H21 frame RAW records incomplete".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N || frame.offset!=PREFIX_BYTES || extensions!=EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if after.len()!=before.len() || after.modified().map_err(|e|e.to_string())?
        !=before.modified().map_err(|e|e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    validate_native_plan_input(&plan,&prefix)?;
    let roster=DaaHistoryRoster::compile(&plan)?;
    if roster.owner_class(OWNER as u64)?!=OwnerClass::M1 {
        return Err("C359 pinned owner is not M1".into());
    }
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix)?;
    let (row,mut daa)=producer.produce_with_daa_source_lease(OWNER)?;
    let header=producer.header_source_lease(OWNER)?;
    let scheduled=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&scheduled)?;
    let stage=row_plan.stage_owner_partial_x_row(OWNER,&row,&header,&daa)?;
    if stage.row_owner()!=OWNER
        || stage.batch().terms().count()==0
        || stage.reads().len()!=stage.batch().active_operands().count() {
        return Err("C359 partial stage ROW/active occurrence custody".into());
    }
    let(mut header_occ,mut daa_occ,mut foreign_open,mut local_open)=(0,0,0,0);
    for read in stage.reads() {match read {
        NativeRead::Header{..}=>header_occ+=1,
        NativeRead::Daa{..}=>daa_occ+=1,
        NativeRead::Cap0{..}|NativeRead::Cap1{..}=>
            return Err("C359 legacy partial X/ROW unexpectedly resolved Cap".into()),
        NativeRead::ForeignMax{..}=>
            return Err("C359 legacy partial X/ROW unexpectedly resolved foreign MAX".into()),
        NativeRead::PointMembership{..}=>
            return Err("C359 legacy partial X/ROW unexpectedly resolved point membership".into()),
        NativeRead::ForeignDaaLane2{..}=>
            return Err("C359 legacy partial X/ROW unexpectedly resolved foreign DAA".into()),
        NativeRead::Unresolved{reason:UnresolvedRead::ForeignOwner,..}=>foreign_open+=1,
        NativeRead::Unresolved{reason:UnresolvedRead::UnqualifiedLocal,..}=>local_open+=1,
    }}
    let claims=stage.claims().copied().collect::<Vec<_>>();
    if header_occ==0 || daa_occ==0 || claims.is_empty()
        || claims.len()>header_occ+daa_occ
        || foreign_open+local_open==0
        || header.read_count_for_test()!=header_occ
        || daa.read_count_for_test()!=daa_occ
        || claims.windows(2).any(|pair|pair[0].wire>=pair[1].wire) {
        return Err("C359 partial X claim and typed open census".into());
    }
    for claim in &claims {
        let local=claim.wire.checked_sub(OWNER*WIDTH).filter(|local|*local<WIDTH)
            .ok_or("C359 claim outside selected owner")?;
        let bank=BANKS.iter().any(|&(start,end)|(start..end).contains(&local));
        if bank!=(claim.author==NativeXAuthor::Daa)
            || claim.value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0) {
            return Err("C359 deduplicated claim author/value/packed mismatch".into());
        }
    }
    let before_reads=(header.read_count_for_test(),daa.read_count_for_test());
    let mut wrong_parent=row.clone();
    mutate_native_row_parent_for_test(&mut wrong_parent);
    let wrong=row_plan.stage_owner_partial_x_row(OWNER,&wrong_parent,&header,&daa).err()
        .ok_or("C359 wrong row parent admitted")?;
    if !wrong.contains("native packed ROW source")
        || (header.read_count_for_test(),daa.read_count_for_test())!=before_reads {
        return Err("C359 wrong row parent reached value read".into());
    }
    let mut wrong_header=producer.header_source_lease(OWNER)?;
    wrong_header.wrong_author_mutant_for_test();
    let wrong=row_plan.stage_owner_partial_x_row(OWNER,&row,&wrong_header,&daa).err()
        .ok_or("C359 wrong HEADER author admitted")?;
    if !wrong.contains("HEADER source author mismatch before read admission")
        || wrong_header.read_count_for_test()!=0 || daa.read_count_for_test()!=before_reads.1 {
        return Err("C359 wrong HEADER author reached value read".into());
    }
    let first=claims[0];
    let mut wrong_bit=row.clone();
    flip_native_row_bit_for_test(&mut wrong_bit,first.wire-OWNER*WIDTH)?;
    let wrong=row_plan.stage_owner_partial_x_row(OWNER,&wrong_bit,&header,&daa).err()
        .ok_or("C359 flipped resolved packed bit admitted")?;
    if !wrong.contains("native packed value mismatch") {
        return Err("C359 flipped resolved bit missed exact source comparison".into());
    }
    let good_header=producer.header_source_lease(OWNER)?;
    daa.wrong_author_mutant_for_test();
    let admitted=daa.read_count_for_test();
    let wrong=row_plan.stage_owner_partial_x_row(OWNER,&row,&good_header,&daa).err()
        .ok_or("C359 wrong DAA author admitted")?;
    if !wrong.contains("DAA source author mismatch before read admission")
        || good_header.read_count_for_test()!=0 || daa.read_count_for_test()!=admitted {
        return Err("C359 wrong DAA author reached value read".into());
    }
    println!("C359_PARTIAL_X_ROW owner={OWNER} header_occ={header_occ} daa_occ={daa_occ} foreign_open={foreign_open} local_open={local_open} unique_claims={} wrong_parent_author_bit_rejected=true full_x_row=false proof=false",claims.len());
    Ok(())
}

#[test]
#[ignore = "pinned H21 frame; bounded CarryZero partial X/ROW owner runner required"]
fn c362_native_carry_zero_partial_x_row_from_pinned_frame() -> Result<(), String> {
    use crate::daa_history_roster::{DaaHistoryRoster,BANKS,OwnerClass};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::{NativeRead,NativeXAuthor,Producer,Relation,RowPlan,UnresolvedRead};
    use crate::packed_owner_assembly::CarryZeroLeaseFault;
    const OWNER:usize=845_759;
    const ROWS:usize=1<<19;
    const WIDTH:usize=1<<20;
    if std::env::var("NIPOPOW_C362_CARRY_ZERO_ROW_ACTUAL").as_deref()!=Ok("1") {
        return Err("explicit C362 CarryZero ROW mode required".into());
    }
    let path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path=Path::new(&path);
    if !path.is_absolute(){return Err("H21 frame path must be absolute".into());}
    let before=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len()!=FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file=File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0{return Err("H21 frame RAW records incomplete".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N || frame.offset!=PREFIX_BYTES || extensions!=EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if after.len()!=before.len() || after.modified().map_err(|e|e.to_string())?
        !=before.modified().map_err(|e|e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    validate_native_plan_input(&plan,&prefix)?;
    let roster=DaaHistoryRoster::compile(&plan)?;
    if roster.owner_class(OWNER as u64)?!=OwnerClass::Carry {
        return Err("C362 pinned owner is not Carry".into());
    }
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix)?;
    let (row,daa)=producer.produce_with_carry_zero_daa_source_lease(OWNER)?;
    let header=producer.header_source_lease(OWNER)?;
    let scheduled=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&scheduled)?;
    if row.owner()!=OWNER || row.packed_bytes().len()!=WIDTH/8
        || BANKS.iter().any(|&(start,end)|row.packed_bytes()[start/8..end/8].iter().any(|byte|*byte!=0)) {
        return Err("C362 explicit CarryZero bank bytes/row identity".into());
    }
    let batch=row_plan.stage_owner(OWNER)?;
    if batch.declared_x_domains().iter().any(|domain|domain.producer==Producer::Daa) {
        return Err("C362 Carry DAA domains appeared without a source writer".into());
    }
    let domains=batch.declared_x_domains_with_daa_source(&daa)?
        .into_iter().filter(|domain|domain.producer==Producer::Daa).collect::<Vec<_>>();
    let base=OWNER.checked_mul(WIDTH).ok_or("C362 owner wire overflow")?;
    let expected_domains=BANKS.iter().map(|&(start,end)|
        crate::header_daa_row_placement::DeclaredXDomain{producer:Producer::Daa,start:base+start,end:base+end})
        .collect::<Vec<_>>();
    if domains!=expected_domains || domains.iter().map(|domain|domain.end-domain.start).sum::<usize>()!=81_920 {
        return Err("C362 exact four-bank DAA declaration geometry".into());
    }

    let stage=row_plan.stage_owner_partial_x_row(OWNER,&row,&header,&daa)?;
    if stage.row_owner()!=OWNER || stage.batch().terms().count()==0
        || stage.reads().len()!=stage.batch().active_operands().count() {
        return Err("C362 partial stage ROW/active occurrence custody".into());
    }
    let(mut header_occ,mut daa_occ,mut lane3_occ,mut lane2_foreign,mut foreign_open,mut local_open)=(0usize,0usize,0usize,0usize,0usize,0usize);
    let mut daa_wires=BTreeSet::new();
    let mut lane3_wires=BTreeSet::new();
    for (operand,read) in stage.batch().active_operands().zip(stage.reads()) {
        match *read {
            NativeRead::Header{operand:actual,value} => {
                let local=operand.wire.checked_sub(base).filter(|local|*local<WIDTH)
                    .ok_or("C362 foreign operand resolved by HEADER")?;
                if actual!=operand || BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0) {
                    return Err("C362 HEADER active read author/value/packed mismatch".into());
                }
                header_occ+=1;
            }
            NativeRead::Daa{operand:actual,value} => {
                let local=operand.wire.checked_sub(base).filter(|local|*local<WIDTH)
                    .ok_or("C362 foreign operand resolved by DAA")?;
                if actual!=operand
                    || !BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || value || row.packed_bytes()[local/8]&(1<<(local%8))!=0 {
                    return Err("C362 DAA source bank/zero/packed mismatch".into());
                }
                if operand.relation==Relation::DaaLane(3) {
                    let q=operand.row.checked_sub(OWNER*ROWS).filter(|q|*q<ROWS)
                        .ok_or("C362 DAA ROW outside owner")?;
                    if !(393_216..475_136).contains(&q) {
                        return Err("C362 lane-3 zero ROW extent mismatch".into());
                    }
                    lane3_wires.insert(operand.wire);
                    lane3_occ+=1;
                }
                daa_wires.insert(operand.wire);
                daa_occ+=1;
            }
            NativeRead::Cap0{..}|NativeRead::Cap1{..} =>
                return Err("C362 legacy partial X/ROW unexpectedly resolved Cap".into()),
            NativeRead::ForeignMax{..} =>
                return Err("C362 legacy partial X/ROW unexpectedly resolved foreign MAX".into()),
            NativeRead::PointMembership{..} =>
                return Err("C362 legacy partial X/ROW unexpectedly resolved point membership".into()),
            NativeRead::ForeignDaaLane2{..} =>
                return Err("C362 legacy partial X/ROW unexpectedly resolved foreign DAA".into()),
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::ForeignOwner} => {
                if actual!=operand || operand.wire/ WIDTH==OWNER {
                    return Err("C362 foreign open occurrence identity".into());
                }
                if operand.relation==Relation::DaaLane(2) {
                    let physical_owner=operand.wire/WIDTH;
                    if physical_owner!=OWNER-1 && physical_owner!=OWNER-2 {
                        return Err("C362 lane-2 foreign owner is outside EqualParent".into());
                    }
                    lane2_foreign+=1;
                }
                foreign_open+=1;
            }
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::UnqualifiedLocal} => {
                if actual!=operand || operand.wire/WIDTH!=OWNER {
                    return Err("C362 local open occurrence identity".into());
                }
                local_open+=1;
            }
        }
    }
    let expected_bank_wires=BANKS.iter().flat_map(|&(start,end)|
        (start..end).map(|local|base+local)).collect::<BTreeSet<_>>();
    if header_occ==0 || daa_occ<lane3_occ || lane3_occ!=81_920
        || lane3_wires.len()!=81_920 || lane3_wires!=expected_bank_wires
        || daa_wires!=expected_bank_wires || lane2_foreign!=448
        || foreign_open<lane2_foreign || local_open==0
        || daa.read_count_for_test()!=daa_occ || header.read_count_for_test()!=header_occ {
        return Err("C362 CarryZero active lane/read census".into());
    }
    let claims=stage.claims().copied().collect::<Vec<_>>();
    let claim_daa_wires=claims.iter().filter(|claim|claim.author==NativeXAuthor::Daa)
        .map(|claim|claim.wire).collect::<BTreeSet<_>>();
    if claims.is_empty() || claims.windows(2).any(|pair|pair[0].wire>=pair[1].wire)
        || claim_daa_wires!=expected_bank_wires || claim_daa_wires!=daa_wires
        || claims.iter().any(|claim|{
            let local=claim.wire.checked_sub(base).filter(|local|*local<WIDTH);
            match (claim.author,local) {
                (NativeXAuthor::Daa,Some(local))=>!BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || claim.value,
                (NativeXAuthor::Header,Some(local))=>BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || claim.value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0),
                _=>true,
            }
        }) {
        return Err("C362 deduplicated X claim author/value/packed census".into());
    }

    let faults=[CarryZeroLeaseFault::WrongBindingOwner,CarryZeroLeaseFault::WrongRoot,
        CarryZeroLeaseFault::WrongTotal,CarryZeroLeaseFault::WrongProfile,
        CarryZeroLeaseFault::WrongCut,CarryZeroLeaseFault::WrongLayout,
        CarryZeroLeaseFault::WrongPayloadOwner,CarryZeroLeaseFault::WrongClass,
        CarryZeroLeaseFault::WrongAuthor,CarryZeroLeaseFault::WrongSourceVariant,
        CarryZeroLeaseFault::IncompleteDomain,CarryZeroLeaseFault::DuplicateDomain,
        CarryZeroLeaseFault::ExtendedDomain,CarryZeroLeaseFault::OverlappingDomain,
        CarryZeroLeaseFault::WrongClaimCount,
        CarryZeroLeaseFault::ShiftedDomainStart];
    for fault in faults {
        let wrong=daa.with_carry_zero_fault_for_test(fault)?;
        let header_before=header.read_count_for_test();
        if batch.declared_x_domains_with_daa_source(&wrong).is_ok()
            || header.read_count_for_test()!=header_before || wrong.read_count_for_test()!=0 {
            return Err(format!("C362 malformed CarryZero author/domain reached declaration/read: {fault:?}"));
        }
        if row_plan.stage_owner_partial_x_row(OWNER,&row,&header,&wrong).is_ok()
            || header.read_count_for_test()!=header_before || wrong.read_count_for_test()!=0 {
            return Err(format!("C362 malformed CarryZero author/domain reached value read: {fault:?}"));
        }
    }
    let first_daa=claims.iter().find(|claim|claim.author==NativeXAuthor::Daa)
        .ok_or("C362 missing deduplicated DAA claim")?;
    let mut wrong_bit=row.clone();
    flip_native_row_bit_for_test(&mut wrong_bit,first_daa.wire-base)?;
    let mismatch=row_plan.stage_owner_partial_x_row(OWNER,&wrong_bit,&header,&daa).err()
        .ok_or("C362 flipped CarryZero packed bit admitted")?;
    if !mismatch.contains("native packed value mismatch") {
        return Err("C362 flipped packed bit missed atomic source comparison".into());
    }
    println!("C362_CARRYZERO_PARTIAL_X_ROW owner={OWNER} daa_lane3_active={lane3_occ} daa_unique={} lane2_foreign_open={lane2_foreign} header_occ={header_occ} local_open={local_open} exact_bank_domains=4 malformed_author_domains_rejected=true flipped_packed_bit_rejected=true full_x_row=false proof=false",
        daa_wires.len());
    Ok(())
}

#[test]
#[ignore = "pinned H21 frame; bounded native Cap0-to-ROW source join required"]
fn c360_native_cap0_active_row_overlay_from_pinned_frame() -> Result<(), String> {
    use crate::{
        daa_history_roster::DaaHistoryRoster,
        h21_scheduled_max_cap::{Eligible08NativeSnapshot,Plan as Scheduled,Writer},
        header_daa_row_placement::{Relation,RowPlan},
    };
    const OWNER:usize=845_759;
    if std::env::var("NIPOPOW_C360_CAP0_ROW_ACTUAL").as_deref()!=Ok("1") {
        return Err("explicit C360 Cap0 ROW mode required".into());
    }
    let path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path=Path::new(&path);
    if !path.is_absolute(){return Err("H21 frame path must be absolute".into());}
    let before=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len()!=FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file=File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0{return Err("H21 frame RAW records incomplete".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N || frame.offset!=PREFIX_BYTES || extensions!=EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if after.len()!=before.len() || after.modified().map_err(|e|e.to_string())?
        !=before.modified().map_err(|e|e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    validate_native_plan_input(&plan,&prefix)?;
    let snapshot=Eligible08NativeSnapshot::new(&plan,&prefix)?;
    let cap=snapshot.first_modern_cap_lease(&plan,&prefix)?;
    let roster=DaaHistoryRoster::compile(&plan)?;
    let scheduled=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&scheduled)?;
    let overlay=row_plan.stage_owner_cap0_overlay(OWNER,&plan,&prefix,&cap)?;
    let claim_count=overlay.claims().len();
    let cell_count=overlay.source_cells().len();
    if overlay.owner()!=OWNER || overlay.source_row_count()!=6_419 || cell_count!=2_048
        || overlay.cap0_relation_active_occurrences()==0 || claim_count==0
        || claim_count+overlay.open_cap0_relation_occurrences()
            !=overlay.cap0_relation_active_occurrences() {
        return Err("C360 non-vacuous Cap0 source/active ROW census".into());
    }
    let cap0_writer=Writer::Cap{context:0,origin:OWNER+1};
    for claim in overlay.claims() {
        let operand=claim.operand();
        let local=operand.wire.checked_sub(OWNER*OWNER_ROW_BITS)
            .filter(|local|(1_000_770..1_002_818).contains(local))
            .ok_or("C360 claim outside Cap0 owner-local domain")?;
        if operand.relation!=Relation::Scheduled(cap0_writer) || claim.author()!=cap0_writer
            || overlay.source_cells().nth(local-1_000_770)
                .map(|(wire,value)|(*wire,*value))!=Some((local,claim.value())) {
            return Err(format!("C360 typed Cap0 claim/source-cell mismatch at {local}"));
        }
    }

    let mut wrong_root=prefix.root();wrong_root[0]^=1;
    let wrong_plan=WorkTreeHistoryPlan::compile(N as u64,H,wrong_root,prefix.total_be28())?;
    if row_plan.stage_owner_cap0_overlay(OWNER,&wrong_plan,&prefix,&cap).is_ok() {
        return Err("C360 wrong native parent binding admitted".into());
    }
    let mut wrong_context=overlay.clone();
    wrong_context.change_first_author_for_test(Writer::Cap{context:1,origin:OWNER+1});
    if wrong_context.validate().is_ok() {return Err("C360 wrong Cap context admitted".into());}
    let mut wrong_author=overlay.clone();
    wrong_author.change_first_author_for_test(Writer::Max{context:0,end:OWNER+2});
    if wrong_author.validate().is_ok() {return Err("C360 wrong source author admitted".into());}
    let mut missing=overlay.clone();missing.remove_first_claim_for_test();
    if missing.validate().is_ok() {return Err("C360 missing active Cap0 claim admitted".into());}
    let mut duplicated=overlay.clone();duplicated.duplicate_first_claim_for_test();
    if duplicated.validate().is_ok() {return Err("C360 duplicate active Cap0 claim admitted".into());}
    let mut flipped=overlay.clone();flipped.flip_first_claim_for_test();
    if flipped.validate().is_ok() {return Err("C360 flipped Cap0 claim value admitted".into());}
    println!("C360_CAP0_ACTIVE_ROW_OVERLAY_PASS owner={OWNER} source_rows={} source_cells={cell_count} cap0_relation_active_occurrences={} cap0_claims={claim_count} open_cap0_relation_occurrences={} nonvacuous_source=true wrong_binding_author_context_missing_duplicate_bitflip_rejected=true full_x_row=false proof=false client=false",
        overlay.source_row_count(),overlay.cap0_relation_active_occurrences(),
        overlay.open_cap0_relation_occurrences());
    Ok(())
}

#[test]
#[ignore = "pinned H21 frame; bounded C363 Cap0-to-partial-X/ROW join required"]
fn c363_native_cap0_partial_x_row_join_from_pinned_frame() -> Result<(), String> {
    use crate::{
        daa_history_roster::{DaaHistoryRoster,BANKS},
        h21_scheduled_max_cap::{Eligible08NativeSnapshot,Plan as Scheduled,Writer},
        header_daa_row_placement::{NativeRead,NativeXAuthor,Relation,RowPlan,UnresolvedRead},
        packed_owner_assembly::{HeaderSourceBinding,NativeHeaderSourceLease,NativeOwnerProducer},
    };
    const OWNER:usize=845_759;
    const WIDTH:usize=1<<20;
    const CAP0_START:usize=1_000_770;
    const CAP0_END:usize=1_002_818;
    const CAP1_END:usize=1_004_866;
    if std::env::var("NIPOPOW_C363_CAP0_ROW_ACTUAL").as_deref()!=Ok("1") {
        return Err("explicit C363 Cap0 ROW mode required".into());
    }
    let path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path=Path::new(&path);
    if !path.is_absolute(){return Err("H21 frame path must be absolute".into());}
    let before=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len()!=FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file=File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0{return Err("H21 frame RAW records incomplete".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N || frame.offset!=PREFIX_BYTES || extensions!=EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if after.len()!=before.len() || after.modified().map_err(|e|e.to_string())?
        !=before.modified().map_err(|e|e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    validate_native_plan_input(&plan,&prefix)?;
    let snapshot=Eligible08NativeSnapshot::new(&plan,&prefix)?;
    let cap=snapshot.first_modern_cap_lease(&plan,&prefix)?;
    let roster=DaaHistoryRoster::compile(&plan)?;
    let scheduled=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&scheduled)?;
    let overlay=row_plan.stage_owner_cap0_overlay(OWNER,&plan,&prefix,&cap)?;
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix)?;
    let mut forged_cap=snapshot.first_modern_cap_lease(&plan,&prefix)?;
    forged_cap.flip_cap_q_bit_for_test(0,0)?;
    if producer.produce_with_carry_zero_daa_cap0_source_lease(OWNER,&snapshot,&forged_cap)
        .err().is_none_or(|error|!error.contains("Eligible08 MAX/Cap owner patch parent/source")) {
        return Err("C363 same-parent forged Cap lease passed exact source replay".into());
    }
    let (row,daa)=producer.produce_with_carry_zero_daa_cap0_source_lease(OWNER,&snapshot,&cap)?;
    let header=producer.header_source_lease(OWNER)?;
    let source_claims=overlay.claims().len();
    let source_cells=overlay.source_cells().len();
    let cap0_writer=Writer::Cap{context:0,origin:OWNER+1};
    if overlay.owner()!=OWNER || overlay.source_row_count()!=6_419
        || source_claims!=7_574 || source_cells!=2_048
        || overlay.open_cap0_relation_occurrences()!=224
        || source_claims+overlay.open_cap0_relation_occurrences()
            !=overlay.cap0_relation_active_occurrences() {
        return Err("C363 exact Cap0 source/active occurrence census".into());
    }
    if !overlay.claims().any(|claim| claim.value()) {
        return Err("C363 pinned fixture has no active true Cap0 claim for packed-bit regression".into());
    }
    for (index,(wire,_)) in overlay.source_cells().enumerate() {
        if *wire!=CAP0_START+index {return Err("C363 Cap0 source-cell domain/order".into());}
    }

    let c362=row_plan.stage_owner_partial_x_row(OWNER,&row,&header,&daa)?;
    let joined=row_plan.stage_owner_partial_x_row_with_cap0(OWNER,&row,&header,&daa,&overlay)?;
    let prior_claims=c362.claims().copied().collect::<Vec<_>>();
    let retained_claims=joined.claims().filter(|claim|
        matches!(claim.author,NativeXAuthor::Header|NativeXAuthor::Daa))
        .copied().collect::<Vec<_>>();
    if prior_claims!=retained_claims {
        return Err("C363 changed the C362 HEADER/DAA claim ledger".into());
    }
    let expected_bank_wires=BANKS.iter().flat_map(|&(start,end)|
        (start..end).map(|local|OWNER*WIDTH+local)).collect::<BTreeSet<_>>();
    let daa_wires=joined.claims().filter(|claim|claim.author==NativeXAuthor::Daa)
        .map(|claim|claim.wire).collect::<BTreeSet<_>>();
    if daa_wires!=expected_bank_wires {return Err("C363 lost C362 bank-zero claims".into());}

    let(mut header_reads,mut daa_reads,mut daa_lane3_occ,mut cap0_reads,mut cap0_true_reads,
        mut cap0_false_reads,mut cap0_open,mut header_cap_anchor_open,mut other_open)=
        (0usize,0usize,0usize,0usize,0usize,0usize,0usize,0usize,0usize);
    let(mut cap0_wires,mut daa_lane3_wires)=(BTreeSet::new(),BTreeSet::new());
    for (operand,read) in joined.batch().active_operands().zip(joined.reads()) {
        match *read {
            NativeRead::Header{operand:actual,value} => {
                let local=operand.wire.checked_sub(OWNER*WIDTH).filter(|l|*l<WIDTH)
                    .ok_or("C363 foreign HEADER read")?;
                if actual!=operand || operand.relation==Relation::Scheduled(cap0_writer)
                    || BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || (operand.relation==Relation::Header && (CAP0_START..CAP1_END).contains(&local))
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0) {
                    return Err("C363 HEADER read author/value/packed mismatch".into());
                }
                header_reads+=1;
            }
            NativeRead::Daa{operand:actual,value} => {
                let local=operand.wire.checked_sub(OWNER*WIDTH).filter(|l|*l<WIDTH)
                    .ok_or("C363 foreign DAA read")?;
                if actual!=operand || !BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || value || row.packed_bytes()[local/8]&(1<<(local%8))!=0 {
                    return Err("C363 DAA read author/value/packed mismatch".into());
                }
                if operand.relation==Relation::DaaLane(3) {
                    let q=operand.row.checked_sub(OWNER*(1<<19)).filter(|q|*q<(1<<19))
                        .ok_or("C363 lane-3 DAA row outside owner")?;
                    if !(393_216..475_136).contains(&q) {
                        return Err("C363 lane-3 DAA row extent mismatch".into());
                    }
                    daa_lane3_occ+=1;
                    daa_lane3_wires.insert(operand.wire);
                }
                daa_reads+=1;
            }
            NativeRead::Cap0{operand:actual,author,value} => {
                let local=operand.wire.checked_sub(OWNER*WIDTH)
                    .filter(|local|(CAP0_START..CAP0_END).contains(local))
                    .ok_or("C363 Cap0 read outside exact source domain")?;
                let source=overlay.source_cells().nth(local-CAP0_START)
                    .map(|(wire,value)|(*wire,*value));
                if actual!=operand || author!=cap0_writer
                    || operand.relation!=Relation::Scheduled(cap0_writer)
                    || source!=Some((local,value))
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0)
                    || overlay.claims().find(|claim|claim.operand()==operand)
                        .map(|claim|(claim.author(),claim.value()))!=Some((author,value)) {
                    return Err("C363 Cap0 read source/wire/author/value/packed mismatch".into());
                }
                cap0_reads+=1;
                if value {cap0_true_reads+=1;} else {cap0_false_reads+=1;}
                cap0_wires.insert(operand.wire);
            }
            NativeRead::Cap1{..} =>
                return Err("C363 Cap0 partial X/ROW unexpectedly resolved Cap1".into()),
            NativeRead::ForeignMax{..} =>
                return Err("C363 Cap0 partial X/ROW unexpectedly resolved foreign MAX".into()),
            NativeRead::PointMembership{..} =>
                return Err("C363 Cap0 partial X/ROW unexpectedly resolved point membership".into()),
            NativeRead::ForeignDaaLane2{..} =>
                return Err("C363 Cap0 partial X/ROW unexpectedly resolved foreign DAA".into()),
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::UnqualifiedLocal} => {
                if actual!=operand || operand.wire/ WIDTH!=OWNER {
                    return Err("C363 local unresolved occurrence identity".into());
                }
                if operand.relation==Relation::Scheduled(cap0_writer) {
                    let local=operand.wire%WIDTH;
                    if (CAP0_START..CAP0_END).contains(&local) {
                        return Err("C363 in-domain Cap0 read remained open".into());
                    }
                    cap0_open+=1;
                } else {
                    let local=operand.wire%WIDTH;
                    if operand.relation==Relation::Header && (CAP0_START..CAP1_END).contains(&local) {
                        header_cap_anchor_open+=1;
                    } else {other_open+=1;}
                }
            }
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::ForeignOwner} => {
                if actual!=operand || operand.wire/ WIDTH==OWNER {
                    return Err("C363 foreign unresolved occurrence identity".into());
                }
                if operand.relation==Relation::Scheduled(cap0_writer) {
                    cap0_open+=1;
                } else {other_open+=1;}
            }
        }
    }
    let staged_cap0=joined.claims().filter(|claim|claim.author==NativeXAuthor::Cap0(cap0_writer))
        .map(|claim|claim.wire).collect::<BTreeSet<_>>();
    let source_cap0=overlay.claims().map(|claim|claim.operand().wire).collect::<BTreeSet<_>>();
    if header_reads==0 || daa_reads<daa_lane3_occ || daa_lane3_occ!=81_920
        || daa_lane3_wires!=expected_bank_wires || daa_reads<81_920 || cap0_reads!=source_claims
        || cap0_true_reads==0 || cap0_false_reads==0
        || cap0_open!=224 || cap0_open!=overlay.open_cap0_relation_occurrences()
        || header_cap_anchor_open!=0 || other_open==0
        || staged_cap0!=source_cap0 || cap0_wires!=source_cap0 || cap0_wires.len()>source_cells
        || joined.reads().len()!=joined.batch().active_operands().count()
        || joined.claims().len()>joined.reads().len()
        || joined.claims().map(|claim|claim.wire).collect::<Vec<_>>().windows(2)
            .any(|pair|pair[0]>=pair[1]) {
        return Err("C363 partial X/ROW read and deduplicated claim census".into());
    }

    let mut wrong_root=prefix.root();wrong_root[0]^=1;
    let wrong_plan=WorkTreeHistoryPlan::compile(N as u64,H,wrong_root,prefix.total_be28())?;
    let mut wrong_binding=overlay.clone();wrong_binding.change_binding_for_test(&wrong_plan,OWNER)?;
    let mut self_consistent_wrong_binding=overlay.clone();
    self_consistent_wrong_binding.change_self_consistent_binding_for_test(&wrong_plan,OWNER)?;
    if self_consistent_wrong_binding.validate().is_err() {
        return Err("C363 self-consistent wrong-root overlay fixture is malformed".into());
    }
    let mut wrong_author=overlay.clone();
    wrong_author.change_first_author_for_test(Writer::Max{context:0,end:OWNER+2});
    let mut wrong_context=overlay.clone();
    wrong_context.change_first_author_for_test(Writer::Cap{context:1,origin:OWNER+1});
    let mut wrong_domain=overlay.clone();wrong_domain.change_first_domain_for_test();
    let mut wrong_value=overlay.clone();wrong_value.flip_first_claim_for_test();
    let mut missing=overlay.clone();missing.remove_first_claim_for_test();
    let mut duplicate=overlay.clone();duplicate.duplicate_first_claim_for_test();
    let mut duplicate_conflict=overlay.clone();
    duplicate_conflict.duplicate_first_claim_with_conflicting_value_for_test();
    let header_before=header.read_count_for_test();let daa_before=daa.read_count_for_test();
    let wrong_consumer_binding=row_plan.stage_owner_partial_x_row_with_cap0(
        OWNER,&row,&header,&daa,&self_consistent_wrong_binding).err()
        .ok_or("C363 consumer accepted self-consistent wrong-root overlay")?;
    if !wrong_consumer_binding.contains("Cap0 binding/batch mismatch")
        || header.read_count_for_test()!=header_before || daa.read_count_for_test()!=daa_before {
        return Err("C363 self-consistent wrong-root overlay reached source reads".into());
    }
    for (name,mutant) in [
        ("binding",wrong_binding),("author",wrong_author),("context",wrong_context),
        ("domain",wrong_domain),("value",wrong_value),("missing",missing),
        ("duplicate",duplicate),("duplicate_value",duplicate_conflict),
    ] {
        if row_plan.stage_owner_partial_x_row_with_cap0(OWNER,&row,&header,&daa,&mutant).is_ok()
            || header.read_count_for_test()!=header_before || daa.read_count_for_test()!=daa_before {
            return Err(format!("C363 Cap0 {name} mutant admitted or reached source reads"));
        }
    }
    let first_cap0=joined.claims().find(|claim|
        claim.author==NativeXAuthor::Cap0(cap0_writer) && claim.value)
        .ok_or("C363 missing true Cap0 X claim")?;
    let overlap_operand=overlay.claims().next().ok_or("C363 missing Cap0 overlap fixture")?;
    let overlap_header=NativeHeaderSourceLease::wrong_author_for_test(
        HeaderSourceBinding::for_plan(&plan,OWNER)?,overlap_operand.operand().wire,
        overlap_operand.value()).native_author_shape_for_test();
    let overlap_error=row_plan.stage_owner_partial_x_row_with_cap0(
        OWNER,&row,&overlap_header,&daa,&overlay).err()
        .ok_or("C363 admitted overlapping native HEADER/Cap0 read")?;
    if !overlap_error.contains("Cap0 overlaps another native author")
        || overlap_header.read_count_for_test()==0 {
        return Err("C363 overlap mutant missed the Cap0 author-conflict boundary".into());
    }
    let local=first_cap0.wire-OWNER*WIDTH;
    let mut wrong_bit=row.clone();
    crate::packed_owner_assembly::flip_native_row_bit_for_test(&mut wrong_bit,local)?;
    if !row_plan.stage_owner_partial_x_row_with_cap0(OWNER,&wrong_bit,&header,&daa,&overlay)
        .err().is_some_and(|err|err.contains("Cap0 source/packed mismatch")) {
        return Err("C363 flipped packed Cap0 bit admitted".into());
    }
    println!("C363_CAP0_PARTIAL_X_ROW_PASS owner={OWNER} source_claims={source_claims} source_cells={source_cells} out_of_domain_open={cap0_open} header_cap_anchor_open={header_cap_anchor_open} header_cap_anchor_rows_retired=true header_reads={header_reads} daa_reads={daa_reads} daa_lane3_reads={daa_lane3_occ} cap0_reads={cap0_reads} cap0_true_reads={cap0_true_reads} cap0_false_reads={cap0_false_reads} unique_cap0_wires={} binding_author_context_domain_value_missing_duplicate_duplicate_value_packed_bit_rejected=true c362_claims_preserved=true full_x_row=false proof=false",
        cap0_wires.len());
    Ok(())
}

#[test]
#[ignore = "pinned H21 frame; explicit C364 Cap01 partial-X/ROW source join"]
fn c364_native_cap01_partial_x_row_join_from_pinned_frame() -> Result<(), String> {
    use crate::{
        daa_history_roster::{DaaHistoryRoster,BANKS},
        h21_scheduled_max_cap::{Eligible08NativeSnapshot,Plan as Scheduled,Writer},
        header_daa_row_placement::{NativeRead,NativeXAuthor,Relation,RowPlan,UnresolvedRead},
        packed_owner_assembly::{HeaderSourceBinding,NativeHeaderSourceLease,NativeOwnerProducer},
    };
    const OWNER:usize=845_759;
    const WIDTH:usize=1<<20;
    const CAP0_START:usize=1_000_770;
    const CAP0_END:usize=1_002_818;
    const CAP1_END:usize=1_004_866;
    if std::env::var("NIPOPOW_C364_CAP01_ROW_ACTUAL").as_deref()!=Ok("1") {
        return Err("explicit C364 Cap01 ROW mode required".into());
    }
    let path=std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path=Path::new(&path);
    if !path.is_absolute(){return Err("H21 frame path must be absolute".into());}
    let before=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len()!=FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file=File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len()!=FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining!=0{return Err("H21 frame RAW records incomplete".into());}
        (prefix,headers.extensions)
    };
    if prefix.header_count()!=N || frame.offset!=PREFIX_BYTES || extensions!=EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if after.len()!=before.len() || after.modified().map_err(|e|e.to_string())?
        !=before.modified().map_err(|e|e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28())?;
    validate_native_plan_input(&plan,&prefix)?;
    let snapshot=Eligible08NativeSnapshot::new(&plan,&prefix)?;
    let cap=snapshot.first_modern_cap_lease(&plan,&prefix)?;
    let roster=DaaHistoryRoster::compile(&plan)?;
    let scheduled=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&scheduled)?;
    let cap0=row_plan.stage_owner_cap0_overlay(OWNER,&plan,&prefix,&cap)?;
    let cap1=row_plan.stage_owner_cap1_overlay(OWNER,&plan,&prefix,&cap)?;
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix)?;
    let mut forged_cap=snapshot.first_modern_cap_lease(&plan,&prefix)?;
    forged_cap.flip_cap_q_bit_for_test(0,0)?;
    if producer.produce_with_carry_zero_daa_cap01_source_lease(OWNER,&snapshot,&forged_cap)
        .err().is_none_or(|error|!error.contains("Eligible08 MAX/Cap owner patch parent/source")) {
        return Err("C364 same-parent forged Cap lease passed exact source replay".into());
    }
    let (row,daa)=producer.produce_with_carry_zero_daa_cap01_source_lease(OWNER,&snapshot,&cap)?;
    let header=producer.header_source_lease(OWNER)?;
    let cap0_writer=Writer::Cap{context:0,origin:OWNER+1};
    let cap1_writer=Writer::Cap{context:1,origin:OWNER+1};
    let cap1_claims=cap1.claims().len();
    let cap1_cells=cap1.source_cells().len();
    if cap1.owner()!=OWNER || cap1.source_row_count()!=6_419
        || cap1_claims!=7_574 || cap1_cells!=2_048
        || cap1.open_cap1_relation_occurrences()!=224
        || cap1_claims+cap1.open_cap1_relation_occurrences()
            !=cap1.cap1_relation_active_occurrences() {
        return Err("C364 exact Cap1 source/active occurrence census".into());
    }
    if !cap1.claims().any(|claim|claim.value())
        || !cap1.claims().any(|claim|!claim.value()) {
        return Err("C364 Cap1 claims lack true/false source values".into());
    }
    for (index,(wire,_)) in cap1.source_cells().enumerate() {
        if *wire!=CAP0_END+index {return Err("C364 Cap1 source-cell domain/order".into());}
    }

    let c362=row_plan.stage_owner_partial_x_row(OWNER,&row,&header,&daa)?;
    let c363=row_plan.stage_owner_partial_x_row_with_cap0(OWNER,&row,&header,&daa,&cap0)?;
    let joined=row_plan.stage_owner_partial_x_row_with_cap01(
        OWNER,&row,&header,&daa,&cap0,&cap1)?;
    let legacy_claims=c362.claims().copied().collect::<Vec<_>>();
    let joined_legacy=joined.claims().filter(|claim|
        matches!(claim.author,NativeXAuthor::Header|NativeXAuthor::Daa))
        .copied().collect::<Vec<_>>();
    let c363_cap0=c363.claims().filter(|claim|
        matches!(claim.author,NativeXAuthor::Cap0(_))).copied().collect::<Vec<_>>();
    let joined_cap0=joined.claims().filter(|claim|
        matches!(claim.author,NativeXAuthor::Cap0(_))).copied().collect::<Vec<_>>();
    if legacy_claims!=joined_legacy || c363_cap0!=joined_cap0 {
        return Err("C364 changed C362 HEADER/DAA or C363 Cap0 claim ledger".into());
    }
    let expected_bank_wires=BANKS.iter().flat_map(|&(start,end)|
        (start..end).map(|local|OWNER*WIDTH+local)).collect::<BTreeSet<_>>();
    let daa_wires=joined.claims().filter(|claim|claim.author==NativeXAuthor::Daa)
        .map(|claim|claim.wire).collect::<BTreeSet<_>>();
    if daa_wires!=expected_bank_wires {return Err("C364 lost C362 bank-zero claims".into());}

    let (mut header_reads,mut daa_reads,mut daa_lane3_occ,mut cap0_reads,mut cap1_reads,
        mut cap1_true,mut cap1_false,mut cap0_open,mut cap0_foreign_open,mut cap1_open,
        mut cap1_foreign_open,mut header_cap_anchor_open,mut other_open,mut other_local_open,
        mut other_foreign_open)=(0usize,0usize,0usize,0usize,0usize,0usize,0usize,0usize,
        0usize,0usize,0usize,0usize,0usize,0usize,0usize);
    let (mut cap0_wires,mut cap1_wires,mut daa_lane3_wires)=(BTreeSet::new(),BTreeSet::new(),BTreeSet::new());
    for (operand,read) in joined.batch().active_operands().zip(joined.reads()) {
        match *read {
            NativeRead::Header{operand:actual,value} => {
                let local=operand.wire.checked_sub(OWNER*WIDTH).filter(|l|*l<WIDTH)
                    .ok_or("C364 foreign HEADER read")?;
                if actual!=operand || operand.relation==Relation::Scheduled(cap0_writer)
                    || operand.relation==Relation::Scheduled(cap1_writer)
                    || BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || (operand.relation==Relation::Header && (CAP0_START..CAP1_END).contains(&local))
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0) {
                    return Err("C364 HEADER read author/value/packed mismatch".into());
                }
                header_reads+=1;
            }
            NativeRead::Daa{operand:actual,value} => {
                let local=operand.wire.checked_sub(OWNER*WIDTH).filter(|l|*l<WIDTH)
                    .ok_or("C364 foreign DAA read")?;
                if actual!=operand || !BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    || value || row.packed_bytes()[local/8]&(1<<(local%8))!=0 {
                    return Err("C364 DAA read author/value/packed mismatch".into());
                }
                if operand.relation==Relation::DaaLane(3) {
                    let q=operand.row.checked_sub(OWNER*(1<<19)).filter(|q|*q<(1<<19))
                        .ok_or("C364 lane-3 DAA row outside owner")?;
                    if !(393_216..475_136).contains(&q) {
                        return Err("C364 lane-3 DAA row extent mismatch".into());
                    }
                    daa_lane3_occ+=1;
                    daa_lane3_wires.insert(operand.wire);
                }
                daa_reads+=1;
            }
            NativeRead::Cap0{operand:actual,author,value} => {
                let local=operand.wire.checked_sub(OWNER*WIDTH)
                    .filter(|l|(CAP0_START..CAP0_END).contains(l)).ok_or("C364 Cap0 read outside source domain")?;
                if actual!=operand || author!=cap0_writer
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0)
                    || cap0.claims().find(|claim|claim.operand()==operand)
                        .map(|claim|(claim.author(),claim.value()))!=Some((author,value)) {
                    return Err("C364 Cap0 source/wire/author/value/packed mismatch".into());
                }
                cap0_reads+=1;
                cap0_wires.insert(operand.wire);
            }
            NativeRead::Cap1{operand:actual,author,value} => {
                let local=operand.wire.checked_sub(OWNER*WIDTH)
                    .filter(|l|(CAP0_END..CAP1_END).contains(l)).ok_or("C364 Cap1 read outside exact source domain")?;
                let source=cap1.source_cells().nth(local-CAP0_END).map(|(wire,value)|(*wire,*value));
                if actual!=operand || author!=cap1_writer
                    || operand.relation!=Relation::Scheduled(cap1_writer)
                    || source!=Some((local,value))
                    || value!=(row.packed_bytes()[local/8]&(1<<(local%8))!=0)
                    || cap1.claims().find(|claim|claim.operand()==operand)
                        .map(|claim|(claim.author(),claim.value()))!=Some((author,value)) {
                    return Err("C364 Cap1 read source/wire/author/value/packed mismatch".into());
                }
                cap1_reads+=1;
                if value {cap1_true+=1;} else {cap1_false+=1;}
                cap1_wires.insert(operand.wire);
            }
            NativeRead::ForeignMax{..} => {
                return Err("C364 unexpected foreign MAX read without sink lease".into());
            }
            NativeRead::PointMembership{..} => {
                return Err("C364 unexpected point-membership read without point lease".into());
            }
            NativeRead::ForeignDaaLane2{..} => {
                return Err("C364 unexpected foreign DAA read without lane2 leases".into());
            }
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::ForeignOwner} => {
                if actual!=operand || operand.wire/WIDTH==OWNER {
                    return Err("C364 foreign unresolved occurrence identity".into());
                }
                if operand.relation==Relation::Scheduled(cap0_writer) {
                    cap0_foreign_open+=1;
                } else if operand.relation==Relation::Scheduled(cap1_writer) {
                    cap1_foreign_open+=1;
                } else {other_open+=1;other_foreign_open+=1;}
            }
            NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::UnqualifiedLocal} => {
                if actual!=operand || operand.wire/WIDTH!=OWNER {
                    return Err("C364 local unresolved occurrence identity".into());
                }
                let local=operand.wire%WIDTH;
                if operand.relation==Relation::Scheduled(cap0_writer) {
                    if (CAP0_START..CAP0_END).contains(&local) {return Err("C364 in-domain Cap0 read remained open".into());}
                    cap0_open+=1;
                } else if operand.relation==Relation::Scheduled(cap1_writer) {
                    if (CAP0_END..CAP1_END).contains(&local) {return Err("C364 in-domain Cap1 read remained open".into());}
                    cap1_open+=1;
                } else if operand.relation==Relation::Header && (CAP0_START..CAP1_END).contains(&local) {
                    header_cap_anchor_open+=1;
                } else {other_open+=1;other_local_open+=1;}
            }
        }
    }
    let source_cap1=cap1.claims().map(|claim|claim.operand().wire).collect::<BTreeSet<_>>();
    let staged_cap1=joined.claims().filter(|claim|claim.author==NativeXAuthor::Cap1(cap1_writer))
        .map(|claim|claim.wire).collect::<BTreeSet<_>>();
    if header_reads==0 || daa_lane3_occ!=81_920 || daa_lane3_wires!=expected_bank_wires
        || cap0_reads!=cap0.claims().len() || cap1_reads!=cap1_claims || cap1_true==0 || cap1_false==0
        || cap1_foreign_open!=224 || cap1_foreign_open+cap1_open!=cap1.open_cap1_relation_occurrences()
        || cap0_foreign_open!=224 || cap0_foreign_open+cap0_open!=cap0.open_cap0_relation_occurrences()
        || header_cap_anchor_open!=0 || other_open!=2_322
        || other_open+cap1_foreign_open!=2_546
        || other_local_open+other_foreign_open!=other_open
        || staged_cap1!=source_cap1 || cap1_wires!=source_cap1 || cap1_wires.len()!=2_048
        || joined.reads().len()!=joined.batch().active_operands().count()
        || joined.claims().len()>joined.reads().len()
        || joined.claims().map(|claim|claim.wire).collect::<Vec<_>>().windows(2).any(|pair|pair[0]>=pair[1]) {
        return Err(format!("C364 partial X/ROW read census cap0_foreign_open={cap0_foreign_open} cap0_local_open={cap0_open} cap1_foreign_open={cap1_foreign_open} cap1_local_open={cap1_open} other_local_open={other_local_open} other_foreign_open={other_foreign_open} other_open={other_open} cap1_residual_open={}" ,other_open+cap1_foreign_open));
    }

    let mut wrong_root=prefix.root();wrong_root[0]^=1;
    let wrong_plan=WorkTreeHistoryPlan::compile(N as u64,H,wrong_root,prefix.total_be28())?;
    let mut wrong_binding=cap1.clone();wrong_binding.change_binding_for_test(&wrong_plan,OWNER)?;
    let mut self_consistent_wrong_binding=cap1.clone();
    self_consistent_wrong_binding.change_self_consistent_binding_for_test(&wrong_plan,OWNER)?;
    if self_consistent_wrong_binding.validate().is_err() {return Err("C364 malformed self-consistent binding mutant".into());}
    let mut wrong_author=cap1.clone();wrong_author.change_first_author_for_test(Writer::Max{context:0,end:OWNER+2});
    let mut wrong_context=cap1.clone();wrong_context.change_first_author_for_test(Writer::Cap{context:0,origin:OWNER+1});
    let mut wrong_domain=cap1.clone();wrong_domain.change_first_domain_for_test();
    let mut wrong_value=cap1.clone();wrong_value.flip_first_claim_for_test();
    let mut missing=cap1.clone();missing.remove_first_claim_for_test();
    let mut duplicate=cap1.clone();duplicate.duplicate_first_claim_for_test();
    let mut duplicate_value=cap1.clone();duplicate_value.duplicate_first_claim_with_conflicting_value_for_test();
    let mut forged_source=cap1.clone();forged_source.flip_first_source_cell_for_test();
    let header_before=header.read_count_for_test();let daa_before=daa.read_count_for_test();
    if row_plan.stage_owner_partial_x_row_with_cap01(OWNER,&row,&header,&daa,&cap0,&self_consistent_wrong_binding)
        .err().is_none_or(|err|!err.contains("Cap1 binding/batch mismatch"))
        || header.read_count_for_test()!=header_before || daa.read_count_for_test()!=daa_before {
        return Err("C364 self-consistent wrong-root overlay reached source reads".into());
    }
    for (name,mutant) in [("binding",wrong_binding),("author",wrong_author),("context",wrong_context),
        ("domain",wrong_domain),("value",wrong_value),("missing",missing),("duplicate",duplicate),
        ("duplicate_value",duplicate_value),("source_cell",forged_source)] {
        if row_plan.stage_owner_partial_x_row_with_cap01(OWNER,&row,&header,&daa,&cap0,&mutant).is_ok()
            || header.read_count_for_test()!=header_before || daa.read_count_for_test()!=daa_before {
            return Err(format!("C364 Cap1 {name} mutant admitted or reached source reads"));
        }
    }
    let first_cap1=joined.claims().find(|claim|claim.author==NativeXAuthor::Cap1(cap1_writer) && claim.value)
        .ok_or("C364 missing true Cap1 X claim")?;
    let mut wrong_bit=row.clone();
    flip_native_row_bit_for_test(&mut wrong_bit,first_cap1.wire-OWNER*WIDTH)?;
    if !row_plan.stage_owner_partial_x_row_with_cap01(OWNER,&wrong_bit,&header,&daa,&cap0,&cap1)
        .err().is_some_and(|err|err.contains("Cap1 source/packed mismatch"))
        || header.read_count_for_test()!=header_before || daa.read_count_for_test()!=daa_before {
        return Err("C364 flipped packed Cap1 bit admitted or reached source reads".into());
    }
    println!("C364_CAP01_PARTIAL_X_ROW_PASS owner={OWNER} cap0_reads={cap0_reads} cap0_foreign_open={cap0_foreign_open} cap1_reads={cap1_reads} cap1_true={cap1_true} cap1_false={cap1_false} unique_cap1_wires={} cap1_foreign_open={cap1_foreign_open} cap1_local_open={cap1_open} other_local_open={other_local_open} other_foreign_open={other_foreign_open} other_open={other_open} cap1_residual_open={} header_reads={header_reads} daa_reads={daa_reads} c362_c363_claims_preserved=true mutants_rejected=true full_x_row=false proof=false client=false",
        cap1_wires.len(),other_open+cap1_foreign_open);
    Ok(())
}

#[test]
#[ignore = "pinned H21 frame and real-row PCS boundary preproof; bounded runner required"]
fn h21_real_owner_pair_sparse_pcs_boundary_preproof() {
    let row = produce_real_sigma21_row_from_pinned_frame();
    crate::sparse_log41_full_opening_tests::real_row_boundary_preproof(
        REAL_EXPECTED_ROW, &row,
    );
}

#[test]
#[ignore = "pinned H21 frame to sparse log41 Dory opening; bounded 4 GiB/1200 s runner required"]
fn h21_real_owner_pair_sparse_log41_full_opening() {
    let row = produce_real_sigma21_row_from_pinned_frame();
    crate::sparse_log41_full_opening_tests::real_row_full_opening(
        REAL_EXPECTED_ROW, row,
    );
}

#[test]
#[ignore = "pinned full ERFV identity, native H20 prefix and local Score join; reviewed 2GiB/240s Job required"]
fn native_upper_two_modern_score_owners_same_x_window() -> Result<(), String> {
    const PREFIX_N: usize = 845_761;
    const PREFIX_H: usize = 20;
    let started = Instant::now();
    let path = std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned frame environment variable")?;
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned full frame length");
    let file = File::open(path).map_err(|e| e.to_string())?;
    assert_eq!(file.metadata().map_err(|e| e.to_string())?.len(), FRAME_BYTES);
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
    preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        // HeaderIter must retain the FULL record count: extension framing uses
        // absolute heights even after only the linked NativePrefix is retained.
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(PREFIX_N, (&mut headers).take(PREFIX_N))?;
        assert_eq!(headers.remaining, 982_079, "remaining full-frame records after prefix");
        for raw in headers.by_ref() {
            raw?; // Every drained record error propagates; never discard Result.
        }
        assert_eq!(headers.remaining, 0, "all full-frame records drained");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), PREFIX_N);
    assert_eq!(frame.offset, 436_881_872, "exact full ERFV header prefix bytes");
    assert_eq!(extensions, 1_785, "exact full-frame extension count");
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES, "frame restat after full SHA256");
    assert_eq!(after.modified().map_err(|e| e.to_string())?, before.modified().map_err(|e| e.to_string())?);
    println!("C125A_FRAME linked_headers={PREFIX_N} drained_records=982079 remaining=0 extensions={extensions} full_sha256_verified=true frame_s={:.6}", started.elapsed().as_secs_f64());
    std::io::stdout().flush().map_err(|e| e.to_string())?;

    let plan = WorkTreeHistoryPlan::compile(PREFIX_N as u64, PREFIX_H, prefix.root(), prefix.total_be28())?;
    validate_native_plan_input(&plan, &prefix)?;
    assert_eq!((plan.headers(), plan.slot_log(), plan.slots()), (PREFIX_N as u64, PREFIX_H, 1 << 20));
    let exports = NativeExports::new_for_history(&plan, &prefix)?;
    let word = |owner: usize, local: usize| -> Result<(BigUint, Vec<bool>), String> {
        let mut n = BigUint::from(0u8);
        let mut bits = Vec::with_capacity(224);
        for k in 0..224 {
            let bit = exports.bit(owner * 1_048_576 + local + k)?;
            bits.push(bit);
            if bit { n |= BigUint::from(1u8) << k; }
        }
        Ok((n, bits))
    };
    let mut upper = Vec::with_capacity(2);
    for (score_owner, source_owner, height) in [(845_759, 845_758, 845_760), (845_760, 845_759, 845_761)] {
        let (lower_be, upper_be) = prefix.interval(height)?;
        // Independent BE integer/bit oracle; do not reuse NativeExports'
        // private be224_bit helper or infer upper from lower/work coordinates.
        let expected = BigUint::from_bytes_be(&upper_be);
        let (actual, bits) = word(source_owner, 987_450)?;
        for k in 0..224 { assert_eq!(bits[k], expected.bit(k as u64), "upper source{source_owner} bit{k}"); }
        assert_eq!(actual, expected);
        assert!(!actual.is_zero());
        let wrong_owner = if source_owner == 845_758 { 845_759 } else { 845_758 };
        assert_ne!(word(wrong_owner, 987_450)?.0, actual, "isolated shifted owner");
        let lower = word(source_owner, 987_226)?.0;
        assert_eq!(lower, BigUint::from_bytes_be(&lower_be));
        assert_ne!(lower, actual, "isolated lower local instead of Upper");
        let work = word(source_owner, 987_674)?.0;
        assert_ne!(work, actual, "isolated individual-work local instead of Upper");
        println!("C125A_UPPER score_owner={score_owner} source_owner={source_owner} height={height} width=224 bits_equal=true owner_lower_work_negatives=true");
        upper.push(actual);
    }
    assert!(upper[1] > upper[0], "real cumulative Upper must strictly increase");
    let input = crate::score_window_join::Inputs {
        upper: [upper[0].clone(), upper[1].clone()],
        // This lot authenticates Upper only. MAX.R and the first predecessor
        // remain explicit conditional inputs, as in the reviewed c124 window.
        max: [[BigUint::from(5u8), BigUint::from(6u8)], [BigUint::from(5u8), BigUint::from(6u8)]],
        previous: [BigUint::from(100u8), BigUint::from(100u8)],
    };
    let mut destination = crate::score_window_join::Destination::default();
    let empty = destination.clone();
    crate::score_window_join::join(&mut destination, &input)?;
    assert_ne!(destination, empty, "one local window published after census and residuals");
    let published = destination.clone();
    assert!(crate::score_window_join::join(&mut destination, &input).unwrap_err().contains("duplicate window publish"));
    assert_eq!(destination, published, "second publish leaves destination unchanged");
    // Keep production-facing modern admission closed, including both contexts.
    for c in 0..2 {
        use crate::origin_score_map::{Plan, Profile, Mode, GuardPolicy};
        let count = [1_827_838, 1_827_775][c];
        let score_plan = Plan::new(1, count, vec![Profile {
            mode: if c == 0 { Mode::Sampled } else { Mode::Exact }, prefix: count,
            expected: BigUint::from(0u8), guard: GuardPolicy::Disabled,
        }])?;
        for owner in [845_759, 845_760] {
            assert!(crate::bank53_map_score::score_owner_terms(&score_plan, owner, c)
                .unwrap_err().contains("active modern Score"));
        }
    }
    println!("C125A_JOIN native_upper_ports=2 contexts=2 score_owners=2 local_residuals=zero published_once=true max_and_initial_r=conditional full_witness=false proof=false elapsed_s={:.6}", started.elapsed().as_secs_f64());
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

/// A fixed spread through the full PCS row domain, with both already observed
/// Bank53-adjacent rows included. These remain base-native rows, not a full
/// H21 Map/Score/U/V witness.
fn candidate94_row_ids() -> Vec<usize> {
    const PCS_ROWS: usize = 1 << 20;
    let mut ids: Vec<usize> = (0..62).map(|i| i * (PCS_ROWS - 1) / 61).collect();
    ids.extend([420_831, REAL_EXPECTED_ROW]);
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), 64, "candidate94 row selection must be unique");
    assert_eq!((ids[0], ids[63]), (0, PCS_ROWS - 1));
    ids
}

#[test]
#[ignore = "pinned H21 frame to bounded real-row seven-claim projection; independent Job review required"]
fn h21_c312_real_rows_seven_claim_projection() {
    if let (Some(fixture), Some(expected_sha)) = (
        std::env::var_os("C312_SELECTED_FIXTURE"),
        std::env::var("C312_SELECTED_SHA256").ok(),
    ) {
        let bytes = fs::read(Path::new(&fixture)).expect("read extracted C312 selected fixture");
        assert_eq!(bytes.len(), 8_388_608, "selected fixture exact length");
        assert!(expected_sha.len() == 64 && expected_sha.bytes().all(|byte| byte.is_ascii_hexdigit()),
                "selected fixture receipt hash must be 64 hex digits");
        assert!(hex(&role0_sha256(&bytes).expect("selected fixture SHA-256")).eq_ignore_ascii_case(&expected_sha),
                "selected fixture receipt hash");
        let indices = [0usize,34379,68759,103138,137518,171897,206277,240656,275036,309415,343795,378174,412554,420863,446933,481313,515692,550072,584451,618831,653210,687590,721969,756349,790728,825108,859487,893867,928246,962626,997005,1031385];
        let rows = indices.iter().enumerate().map(|(slot, index)| {
            (*index, bytes[slot * REAL_SIGMA_ROW_BYTES..(slot + 1) * REAL_SIGMA_ROW_BYTES].to_vec())
        }).collect();
        crate::packed::c312_projection_tests::run(rows);
        return;
    }
    let started = Instant::now();
    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = File::open(path).expect("open pinned H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES, "opened frame length");
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact ERFV header prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact ERFV extension count");
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES, "frame length after complete SHA256");
    let frame_seconds = started.elapsed().as_secs_f64();

    let plan_started = Instant::now();
    let plan = WorkTreeHistoryPlan::compile(
        N as u64, H, prefix.root(), prefix.total_be28(),
    ).expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("source-owned producer bound to admitted prefix");
    let plan_seconds = plan_started.elapsed().as_secs_f64();
    let rows_started = Instant::now();
    let mut rows = Vec::with_capacity(64);
    for row_index in candidate94_row_ids() {
        let even_owner = row_index.checked_mul(2).expect("even owner index");
        let odd_owner = even_owner + 1;
        let even = producer.produce(even_owner).expect("real even owner row");
        let odd = producer.produce(odd_owner).expect("real odd owner row");
        assert_eq!((even.owner(), odd.owner()), (even_owner, odd_owner));
        assert_eq!((even.packed_bytes().len(), odd.packed_bytes().len()),
                   (OWNER_ROW_BYTES, OWNER_ROW_BYTES));
        let mut joined = Vec::with_capacity(REAL_SIGMA_ROW_BYTES);
        joined.extend_from_slice(even.packed_bytes());
        joined.extend_from_slice(odd.packed_bytes());
        assert_eq!(joined.len(), REAL_SIGMA_ROW_BYTES);
        if row_index == REAL_EXPECTED_ROW {
            assert_eq!(hex(&role0_sha256(&joined).expect("observed row digest")),
                       "629f65d24d6a770830dee8cf7069e0aea02d7d67bf47ff1b2821576f6e49a9da");
        }
        rows.push((row_index, joined));
    }
    drop(producer);
    drop(plan);
    drop(prefix);
    let rows_seconds = rows_started.elapsed().as_secs_f64();
    println!("CANDIDATE94_REAL_ROWS_RECONSTRUCTED rows={} first={} last={} observed_d_row={} frame_s={frame_seconds:.6} plan_s={plan_seconds:.6} rows_s={rows_seconds:.6} full_h21_witness=false",
             rows.len(), rows.first().unwrap().0, rows.last().unwrap().0, REAL_EXPECTED_ROW);
    std::io::stdout().flush().expect("row reconstruction marker flush");
    crate::packed::c312_projection_tests::run(rows);
}

#[link(name = "advapi32")]
extern "system" {
    fn CryptAcquireContextW(
        provider: *mut usize,
        container: *const u16,
        provider_name: *const u16,
        provider_type: u32,
        flags: u32,
    ) -> i32;
    fn CryptCreateHash(
        provider: usize,
        algorithm: u32,
        key: usize,
        flags: u32,
        hash: *mut usize,
    ) -> i32;
    fn CryptHashData(hash: usize, bytes: *const u8, len: u32, flags: u32) -> i32;
    fn CryptGetHashParam(
        hash: usize,
        parameter: u32,
        data: *mut u8,
        len: *mut u32,
        flags: u32,
    ) -> i32;
    fn CryptDestroyHash(hash: usize) -> i32;
    fn CryptReleaseContext(provider: usize, flags: u32) -> i32;
}

struct Sha256Stream {
    provider: usize,
    hash: usize,
}

impl Sha256Stream {
    fn new() -> Result<Self, String> {
        let mut provider = 0;
        // PROV_RSA_AES / CRYPT_VERIFYCONTEXT: no persisted key container.
        let ok = unsafe {
            CryptAcquireContextW(
                &mut provider,
                std::ptr::null(),
                std::ptr::null(),
                24,
                0xf000_0000,
            )
        };
        if ok == 0 {
            return Err(format!(
                "CryptAcquireContextW: {}",
                std::io::Error::last_os_error()
            ));
        }
        let mut hash = 0;
        // CALG_SHA_256; this stays test-only and adds no Cargo dependency.
        let ok = unsafe { CryptCreateHash(provider, 0x800c, 0, 0, &mut hash) };
        if ok == 0 {
            unsafe { CryptReleaseContext(provider, 0) };
            return Err(format!(
                "CryptCreateHash: {}",
                std::io::Error::last_os_error()
            ));
        }
        Ok(Self { provider, hash })
    }

    fn update(&mut self, bytes: &[u8]) -> Result<(), String> {
        if bytes.len() > CHUNK {
            return Err("SHA256 update exceeds 64 KiB".into());
        }
        let ok = unsafe { CryptHashData(self.hash, bytes.as_ptr(), bytes.len() as u32, 0) };
        if ok == 0 {
            return Err(format!(
                "CryptHashData: {}",
                std::io::Error::last_os_error()
            ));
        }
        Ok(())
    }

    fn finish(self) -> Result<[u8; 32], String> {
        let mut digest = [0u8; 32];
        let mut len = digest.len() as u32;
        // HP_HASHVAL returns the completed SHA256 digest.
        let ok = unsafe { CryptGetHashParam(self.hash, 2, digest.as_mut_ptr(), &mut len, 0) };
        if ok == 0 || len != 32 {
            return Err(format!(
                "CryptGetHashParam: {}",
                std::io::Error::last_os_error()
            ));
        }
        Ok(digest)
    }
}

impl Drop for Sha256Stream {
    fn drop(&mut self) {
        unsafe {
            CryptDestroyHash(self.hash);
            CryptReleaseContext(self.provider, 0);
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

struct FrameReader<R: Read> {
    stream: R,
    hash: Sha256Stream,
    offset: u64,
    total: u64,
}

impl<R: Read> FrameReader<R> {
    fn new(stream: R, total: u64) -> Result<Self, String> {
        Ok(Self {
            stream,
            hash: Sha256Stream::new()?,
            offset: 0,
            total,
        })
    }

    fn exact(&mut self, target: &mut [u8]) -> Result<(), String> {
        if target.len() > CHUNK || target.len() as u64 > self.total - self.offset {
            return Err(format!("ERFV read length at offset {}", self.offset));
        }
        self.stream
            .read_exact(target)
            .map_err(|error| format!("ERFV truncated at offset {}: {error}", self.offset))?;
        self.hash.update(target)?;
        self.offset += target.len() as u64;
        Ok(())
    }

    fn byte(&mut self) -> Result<u8, String> {
        let mut bytes = [0u8; 1];
        self.exact(&mut bytes)?;
        Ok(bytes[0])
    }

    fn u32(&mut self) -> Result<u32, String> {
        let mut bytes = [0u8; 4];
        self.exact(&mut bytes)?;
        Ok(u32::from_be_bytes(bytes))
    }

    fn discard(&mut self, mut bytes: u64) -> Result<(), String> {
        let mut scratch = [0u8; CHUNK];
        while bytes != 0 {
            let take = bytes.min(CHUNK as u64) as usize;
            self.exact(&mut scratch[..take])?;
            bytes -= take as u64;
        }
        Ok(())
    }

    fn finish(mut self, prefix: u64, tail: u64, expected_sha: &str) -> Result<(), String> {
        if self.offset != prefix || self.total - self.offset != tail {
            return Err(format!(
                "ERFV prefix/tail mismatch at offset {}",
                self.offset
            ));
        }
        self.discard(tail)?;
        let mut extra = [0u8; 1];
        if self
            .stream
            .read(&mut extra)
            .map_err(|error| error.to_string())?
            != 0
        {
            return Err("ERFV bytes after fixed file length".into());
        }
        if hex(&self.hash.finish()?) != expected_sha {
            return Err("ERFV full-file SHA256 mismatch".into());
        }
        Ok(())
    }
}

fn preamble<R: Read>(frame: &mut FrameReader<R>, anchor: u32, tip: u32) -> Result<(), String> {
    let mut magic = [0u8; 8];
    frame.exact(&mut magic)?;
    if &magic != b"ERFV0001" || frame.u32()? != anchor || frame.u32()? != tip {
        return Err("ERFV magic/anchor/tip mismatch".into());
    }
    Ok(())
}

struct HeaderIter<'a, R: Read> {
    frame: &'a mut FrameReader<R>,
    remaining: usize,
    count: usize,
    extensions: u64,
}

impl<'a, R: Read> HeaderIter<'a, R> {
    fn new(frame: &'a mut FrameReader<R>, count: usize) -> Self {
        Self {
            frame,
            remaining: count,
            count,
            extensions: 0,
        }
    }

    fn one(&mut self, height: usize) -> Result<Vec<u8>, String> {
        let start = self.frame.offset;
        let size = self.frame.u32()? as usize;
        if !(1..=514).contains(&size) {
            return Err("ERFV RAW length outside 1..514".into());
        }
        let mut raw = vec![0u8; size];
        self.frame.exact(&mut raw)?;
        match self.frame.byte()? {
            0 => {}
            1 => {
                let extension_size = self.frame.u32()? as u64;
                if extension_size > 1_048_575 {
                    return Err("ERFV extension length exceeds cap".into());
                }
                self.frame.discard(extension_size)?;
                self.extensions += 1;
            }
            _ => return Err("ERFV extension flag".into()),
        }
        if height & 131_071 == 0 {
            println!(
                "H21_FRAME_HEADERS height={height} offset={}",
                self.frame.offset
            );
            std::io::stdout()
                .flush()
                .map_err(|error| error.to_string())?;
        }
        if self.frame.offset <= start {
            return Err("ERFV record failed to advance".into());
        }
        Ok(raw)
    }
}

impl<R: Read> Iterator for HeaderIter<'_, R> {
    type Item = Result<Vec<u8>, String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let height = self.count - self.remaining + 1;
        self.remaining -= 1;
        let offset = self.frame.offset;
        Some(
            self.one(height)
                .map_err(|error| format!("{error} at height={height} frame_offset={offset}")),
        )
    }
}

fn phase(label: &str) {
    println!("H21_NATIVE_ADMISSION phase={label}");
    std::io::stdout().flush().expect("phase marker flush");
}

fn pinned_json(name: &str, bytes: u64, sha: &str) -> Value {
    let path = std::env::var_os(name).expect("pinned receipt environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "receipt path must be absolute");
    let before = fs::symlink_metadata(path).expect("receipt metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), bytes, "pinned receipt length");
    let data = fs::read(path).expect("pinned receipt read");
    assert_eq!(data.len() as u64, bytes, "pinned receipt length after read");
    assert_eq!(
        hex(&role0_sha256(&data).unwrap()),
        sha,
        "pinned receipt SHA256"
    );
    let after = fs::symlink_metadata(path).expect("receipt restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), bytes, "pinned receipt length after read");
    serde_json::from_slice(&data).expect("pinned receipt JSON")
}

fn member<'a>(value: &'a Value, name: &str) -> &'a Value {
    value.get(name).unwrap_or_else(|| panic!("missing {name}"))
}

fn unsigned(value: &Value) -> u64 {
    value.as_u64().expect("receipt unsigned integer")
}

fn decimal(value: &Value) -> BigUint {
    let text = value.as_str().expect("receipt decimal string");
    assert!(!text.is_empty() && (text == "0" || !text.starts_with('0')));
    assert!(text.bytes().all(|byte| byte.is_ascii_digit()));
    text.parse().expect("receipt decimal")
}

fn typed_inputs(map: &Map, owner: u64, exports: &NativeExports<'_>) -> (Inputs, Vec<Import>) {
    let imports = map.imports(owner).expect("typed H21 imports");
    let mut inputs = Inputs::default();
    for import in &imports {
        let mut word = BigUint::from(0u8);
        for bit in 0..import.width {
            let index = map
                .input_index(*import, bit)
                .expect("typed parent coordinate");
            if exports.bit(index).expect("native parent export") {
                word |= BigUint::from(1u8) << bit;
            }
        }
        inputs
            .put(map, *import, &BigInt::from(word))
            .expect("typed native import");
    }
    (inputs, imports)
}

fn packed_bit(bytes: &[u8], index: usize) -> bool {
    ((bytes[index / 8] >> (index % 8)) & 1) != 0
}

fn point(length: usize, seed: u64) -> Vec<Fr> {
    (0..length)
        .map(|i| Fr::from(seed + 3 * i as u64 + 2) / Fr::from(seed + 11 * i as u64 + 19))
        .collect()
}

fn boolean_point(length: usize, value: u64) -> Vec<Fr> {
    (0..length).map(|bit| Fr::from((value >> bit) & 1)).collect()
}

fn eq_point(point: &[Fr], index: u64) -> Fr {
    point.iter().enumerate().fold(Fr::from(1u64), |acc, (bit, value)| {
        acc * if (index >> bit) & 1 == 1 { *value } else { Fr::from(1u64) - *value }
    })
}

fn direct_physical_coefficients(
    terms: &[crate::sparse::Term],
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> [Fr; 4] {
    let mut result = [Fr::zero(); 4];
    for term in terms {
        let weight = eq_point(r, term.row as u64)
            * eq_point(u, term.gate.left as u64)
            * eq_point(v, term.gate.right as u64);
        for (slot, coefficient) in result.iter_mut().zip([
            term.gate.c0,
            term.gate.c1,
            term.gate.c2,
            term.gate.c3,
        ]) {
            *slot += weight * coefficient;
        }
    }
    result
}

fn map_import_signature(map: &Map, owner: usize) -> BTreeSet<(u64, Kind)> {
    map.imports(owner as u64)
        .expect("typed import census")
        .into_iter()
        .map(|import| (import.owner, import.kind))
        .collect()
}

fn expected_q821_imports(owner: usize) -> BTreeSet<(u64, Kind)> {
    let mut expected = BTreeSet::from([
        (owner as u64, Kind::Difficulty),
        (owner as u64, Kind::Timestamp),
        (821 * 1024 + 958, Kind::Difficulty),
    ]);
    for q in 814..=820 {
        expected.insert((q * 1024 + 1022, Kind::Difficulty));
    }
    for q in 813..=820 {
        expected.insert((q * 1024 + 1023, Kind::Timestamp));
    }
    expected
}

fn import_rows_for(
    map: &Map,
    owner: usize,
    candidates: &BTreeMap<usize, NativePackedRow>,
) -> BTreeMap<usize, NativePackedRow> {
    map.imports(owner as u64)
        .expect("consumer import census")
        .into_iter()
        .filter(|import| import.owner != owner as u64)
        .map(|import| {
            let source = import.owner as usize;
            (source, candidates.get(&source).expect("produced typed source row").clone())
        })
        .collect()
}

#[test]
#[ignore = "full pinned H21 frame, resource-bounded runner and independent source/runner review required"]
fn h21_pinned_frame_native_parent_imports_and_bank53_physical_map_join() {
    let d = pinned_json("NIPOPOW_H21_D_CENSUS", D_BYTES, D_SHA256);
    let b = pinned_json("NIPOPOW_H21_B_DIAGNOSTIC", B_BYTES, B_SHA256);
    assert_eq!(member(&d, "format").as_str(), Some("H21-D-CENSUS-1"));
    assert_eq!(
        member(&b, "format").as_str(),
        Some("H21-B-ENVELOPE-DIAGNOSTIC-1")
    );
    assert_eq!(member(&d, "frame"), member(&b, "frame"));
    assert_eq!(unsigned(member(member(&d, "frame"), "bytes")), FRAME_BYTES);
    assert_eq!(
        member(member(&d, "frame"), "sha256").as_str(),
        Some(FRAME_SHA256)
    );
    assert_eq!(unsigned(member(&d, "header_count")), N as u64);
    assert_eq!(unsigned(member(&d, "header_prefix_bytes")), PREFIX_BYTES);
    assert_eq!(unsigned(member(&d, "opaque_tail_bytes")), TAIL_BYTES);
    assert_eq!(unsigned(member(&d, "extension_flags_present")), EXTENSIONS);
    assert_eq!(member(&b, "source_receipt_sha256").as_str(), Some(D_SHA256));
    assert_eq!(
        unsigned(member(member(&d, "difficulty_max"), "height")),
        D_MAX_HEIGHT
    );
    assert_eq!(
        decimal(member(member(&d, "difficulty_max"), "difficulty")).to_string(),
        D_MAX
    );
    assert_eq!(
        unsigned(member(member(&b, "max_legacy_bound"), "q")),
        B_MAX_Q
    );
    assert_eq!(
        decimal(member(member(&b, "max_legacy_bound"), "bound")).to_string(),
        B_MAX
    );
    assert_eq!(
        unsigned(member(member(&b, "global_u"), "exponent")),
        E as u64
    );
    let lower = member(member(&b, "global_u"), "selected_lower_candidate");
    assert_eq!(unsigned(member(lower, "height")), D_MAX_HEIGHT);
    assert_eq!(
        unsigned(member(member(lower, "branch"), "bit")),
        LOWER_PIVOT as u64
    );

    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = File::open(path).expect("open H21 frame");
    assert_eq!(
        file.metadata().unwrap().len(),
        FRAME_BYTES,
        "opened frame length"
    );
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    phase("NATIVE_PREFIX_START");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    phase("NATIVE_PREFIX_READY");
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact ERFV header prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact ERFV extension count");
    frame
        .finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(
        after.len(),
        FRAME_BYTES,
        "frame length after complete SHA256"
    );
    phase("FRAME_SHA256_OK");

    let root = prefix.root();
    let total = prefix.total_be28();
    {
        phase("PARENT_COMPILE_START");
        let plan = WorkTreeHistoryPlan::compile(N as u64, H, root, total)
            .expect("same-root/total H21 parent plan");
        phase("PARENT_READY");
        validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
        let exports = NativeExports::new_for_history(&plan, &prefix)
            .expect("H21 native exports bound to parent");
        phase("EXPORTS_READY");
        let map = Map::from_parent_modern_global_u(
            &plan,
            E,
            LowerSelector {
                source: LowerSource::HeaderDifficulty {
                    height: D_MAX_HEIGHT,
                },
                branch: LowerBranch::Pivot(LOWER_PIVOT),
            },
        )
        .expect("same-parent selected H21 Map");
        assert_eq!(map.binding().parent_root, Some(root));

        let d_owner = D_MAX_HEIGHT - 2;
        let b_owner = B_MAX_Q * 1024 + 959;
        // Check both complete reserved contexts before generating either
        // symbolic or packed owner Map row.
        for owner in [d_owner as usize, b_owner as usize] {
            validate_h21_bank53_map_lane_for_test(&plan, owner, 0)
                .expect("H21 context 0/1 remain HEADER-owned for selected owner");
            let parent_mask = plan.physical_assignment_replacement_mask(owner as u64)
                .expect("parent replacement mask");
            assert!(parent_mask[BANK53_BASE..BANK53_BASE + 2 * BANK53_CONTEXT_BITS]
                .iter().all(|replaced| !replaced), "owner{owner} Bank53 context overlaps parent data");
        }
        let (d_inputs, d_imports) = typed_inputs(&map, d_owner, &exports);
        assert_eq!(d_imports.len(), 1, "selected D has one native import");
        assert_eq!(d_imports[0].kind, Kind::Difficulty);
        assert_eq!(d_imports[0].owner, d_owner);
        assert_eq!(d_inputs.get(d_imports[0]).unwrap().to_string(), D_MAX);
        let d_row = map
            .generate(d_owner, &d_inputs)
            .expect("native selected D row");
        assert!(map.failures(&d_row, &d_inputs).unwrap().is_empty());
        phase("D_SELECTED_READY");
        let mut d_mutant = d_inputs.clone();
        d_mutant.flip(d_imports[0], LOWER_PIVOT).unwrap();
        let selected_f = d_owner as usize * (1 << 14) + 10_123;
        assert!(
            map.failures(&d_row, &d_mutant)
                .unwrap()
                .iter()
                .any(|(index, _)| *index == selected_f),
            "selected D pivot mutant"
        );

        let (b_inputs, b_imports) = typed_inputs(&map, b_owner, &exports);
        assert!(b_imports
            .iter()
            .any(|import| import.kind == Kind::Timestamp));
        assert!(b_imports
            .iter()
            .any(|import| import.kind == Kind::Difficulty && import.owner != b_owner));
        let b_row = map.generate(b_owner, &b_inputs).expect("native q821 B row");
        assert!(map.failures(&b_row, &b_inputs).unwrap().is_empty());
        assert_eq!(b_row.bound(&map).unwrap().to_string(), B_MAX);
        phase("B_MAX_READY");
        for kind in [Kind::Difficulty, Kind::Timestamp] {
            let import = *b_imports
                .iter()
                .find(|import| import.kind == kind && import.owner != b_owner)
                .expect("foreign q821 native import");
            let mut mutant = b_inputs.clone();
            mutant.flip(import, 0).unwrap();
            assert!(
                !map.failures(&b_row, &mutant).unwrap().is_empty(),
                "foreign D/T bit mutant must break the same-parent row"
            );
        }
        phase("IMPORT_NEGATIVES_READY");

        assert_eq!(map_import_signature(&map, d_owner as usize), BTreeSet::from([
            (d_owner, Kind::Difficulty),
        ]), "D owner canonical import census");
        assert_eq!(map_import_signature(&map, b_owner as usize),
            expected_q821_imports(b_owner as usize), "q821 B canonical import census");
        let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
            .expect("unadapted H21 physical Map producer");

        let map_produce_started = Instant::now();
        let d_map_row = producer.produce_bank53_map_h21_for_test(
            d_owner as usize, &map, 0,
        ).expect("source-owned D841727 Map in context 0");
        let b_map_row = producer.produce_bank53_map_h21_for_test(
            b_owner as usize, &map, 0,
        ).expect("source-owned q821 B841663 Map in context 0");
        let map_produce_seconds = map_produce_started.elapsed().as_secs_f64();
        assert_eq!(d_map_row.owner(), d_owner as usize);
        assert_eq!(b_map_row.owner(), b_owner as usize);
        assert_eq!(d_map_row.packed_bytes().len(), 1 << 17, "native owner row bytes");
        assert_eq!(b_map_row.packed_bytes().len(), 1 << 17, "native owner row bytes");
        let lane = BANK53_BASE;
        for (owner_row, symbolic_row, owner) in [
            (&d_map_row, &d_row, d_owner as usize),
            (&b_map_row, &b_row, b_owner as usize),
        ] {
            for offset in 0..BANK53_MAP_LIVE_BITS {
                assert_eq!(
                    packed_bit(owner_row.packed_bytes(), lane + offset),
                    symbolic_row.bits[offset],
                    "owner{owner} physical Map bit{offset}",
                );
            }
            assert!((BANK53_MAP_LIVE_BITS..BANK53_CONTEXT_BITS)
                .all(|offset| !packed_bit(owner_row.packed_bytes(), lane + offset)),
                "owner{owner} context tail/slack must be zero");
        }

        let b_foreign_owners: BTreeSet<usize> = b_imports.iter()
            .filter(|import| import.owner != b_owner)
            .map(|import| import.owner as usize)
            .collect();
        assert_eq!(b_foreign_owners.len(), 16, "q821 B foreign owner count");
        let foreign_started = Instant::now();
        let mut foreign_candidates = BTreeMap::new();
        for owner in &b_foreign_owners {
            foreign_candidates.insert(*owner, producer.produce(*owner)
                .expect("base native typed source owner row"));
        }
        let foreign_produce_seconds = foreign_started.elapsed().as_secs_f64();
        let d_foreign = import_rows_for(&map, d_owner as usize, &foreign_candidates);
        let b_foreign = import_rows_for(&map, b_owner as usize, &foreign_candidates);
        assert!(d_foreign.is_empty(), "D selected row has only its own D import");
        assert_eq!(b_foreign.len(), 16, "all q821 typed foreign imports supplied");

        let consumer_started = Instant::now();
        validate_native_bank53_map_consumer(
            &plan, &prefix, &map, d_owner as usize, 0, &d_map_row, &d_foreign,
        ).expect("D packed imports and literal physical Map residual");
        validate_native_bank53_map_consumer(
            &plan, &prefix, &map, b_owner as usize, 0, &b_map_row, &b_foreign,
        ).expect("q821 packed imports and literal physical Map residual");
        let consumer_seconds = consumer_started.elapsed().as_secs_f64();

        let pivot_threshold = ((BigUint::from(1u8) << E) + BigUint::from(4u8))
            / BigUint::from(3u8);
        let other_pivot = (0..224).find(|bit| {
            *bit != LOWER_PIVOT && !pivot_threshold.bit(*bit as u64)
        }).expect("a second canonical zero pivot bit");
        let wrong_pivot = Map::from_parent_modern_global_u(
            &plan,
            E,
            LowerSelector {
                source: LowerSource::HeaderDifficulty { height: D_MAX_HEIGHT },
                branch: LowerBranch::Pivot(other_pivot),
            },
        ).expect("different valid same-parent pivot binding");
        assert!(validate_native_bank53_map_consumer(
            &plan, &prefix, &wrong_pivot, d_owner as usize, 0, &d_map_row, &d_foreign,
        ).unwrap_err().contains("binding/context"), "pivot mutant isolated");
        assert!(validate_native_bank53_map_consumer(
            &plan, &prefix, &map, b_owner as usize, 1, &b_map_row, &b_foreign,
        ).unwrap_err().contains("binding/context"), "context mutant isolated");

        for kind in [Kind::Difficulty, Kind::Timestamp] {
            let import = *b_imports.iter()
                .find(|import| import.kind == kind && import.owner != b_owner)
                .expect("foreign q821 D/T import");
            let mut mutated = b_foreign.clone();
            flip_native_row_bit_for_test(
                mutated.get_mut(&(import.owner as usize)).expect("foreign packed row"),
                import.local,
            ).expect("isolated imported-coordinate mutation");
            assert!(validate_native_bank53_map_consumer(
                &plan, &prefix, &map, b_owner as usize, 0, &b_map_row, &mutated,
            ).unwrap_err().contains("typed import differs"), "foreign {kind:?} mutant");
        }
        let mut wrong_parent = b_map_row.clone();
        mutate_native_row_parent_for_test(&mut wrong_parent);
        assert!(validate_native_bank53_map_consumer(
            &plan, &prefix, &map, b_owner as usize, 0, &wrong_parent, &b_foreign,
        ).unwrap_err().contains("parent binding"), "parent mutant isolated");
        let mut nonzero_tail = b_map_row.clone();
        flip_native_row_bit_for_test(&mut nonzero_tail, lane + BANK53_MAP_LIVE_BITS)
            .expect("tail mutation coordinate");
        assert!(validate_native_bank53_map_consumer(
            &plan, &prefix, &map, b_owner as usize, 0, &nonzero_tail, &b_foreign,
        ).unwrap_err().contains("tail/Score slack"), "physical tail mutant isolated");
        let mut short_row = b_map_row.clone();
        truncate_native_row_for_test(&mut short_row);
        assert!(validate_native_bank53_map_consumer(
            &plan, &prefix, &map, b_owner as usize, 0, &short_row, &b_foreign,
        ).unwrap_err().contains("row length"), "short native row rejected");
        let mut missing_foreign = b_foreign.clone();
        missing_foreign.pop_first();
        assert!(validate_native_bank53_map_consumer(
            &plan, &prefix, &map, b_owner as usize, 0, &b_map_row, &missing_foreign,
        ).unwrap_err().contains("census"), "missing foreign owner rejected");

        let analytic_started = Instant::now();
        let mut physical_terms = 0usize;
        for owner in [d_owner as usize, b_owner as usize] {
            let terms = crate::bank53_map::map_owner_terms(&map, owner as u64, 0)
                .expect("literal physical Map terms");
            physical_terms += terms.len();
            let mut r = point(19, 311 + owner as u64);
            r.extend(boolean_point(H, owner as u64));
            let mut u = point(20, 401 + owner as u64);
            u.extend(point(H, 503 + owner as u64));
            let mut v = point(20, 601 + owner as u64);
            v.extend(point(H, 701 + owner as u64));
            assert!(r[19..].iter().all(|value| *value == Fr::zero() || *value == Fr::from(1u64)));
            assert!(u[..20].iter().any(|value| *value != Fr::zero() && *value != Fr::from(1u64)));
            assert!(v[..20].iter().any(|value| *value != Fr::zero() && *value != Fr::from(1u64)));
            assert_eq!(
                map.bank53_coefficients(0, &r, &u, &v).expect("analytic Bank53 coefficients"),
                direct_physical_coefficients(&terms, &r, &u, &v),
                "owner{owner} analytic coefficients equal direct physical-term oracle",
            );
        }
        let analytic_seconds = analytic_started.elapsed().as_secs_f64();
        let d_live_bits = (0..BANK53_MAP_LIVE_BITS)
            .filter(|offset| packed_bit(d_map_row.packed_bytes(), lane + offset))
            .count();
        let b_live_bits = (0..BANK53_MAP_LIVE_BITS)
            .filter(|offset| packed_bit(b_map_row.packed_bytes(), lane + offset))
            .count();
        println!(
            "H21_BANK53_PHYSICAL_MAP_PASS scope=base-native-map-component-only full_h21=false owners={d_owner},{b_owner} context=0 d_imports={} b_imports={} b_foreign_owners={} d_live_bits={d_live_bits} b_live_bits={b_live_bits} physical_terms={physical_terms} map_rows_s={map_produce_seconds:.6} foreign_base_rows_s={foreign_produce_seconds:.6} literal_consumer_s={consumer_seconds:.6} analytic_direct_s={analytic_seconds:.6} frame_sha256={FRAME_SHA256} score_v=none same_x=none",
            d_imports.len(), b_imports.len(), b_foreign.len(),
        );
    }
    println!("H21_NATIVE_ADMISSION_PASS headers={N} e={E} d_owner={} b_q={B_MAX_Q} b_owner={} frame_sha256={FRAME_SHA256} proof=none", D_MAX_HEIGHT - 2, B_MAX_Q * 1024 + 959);
}

fn tiny_frame() -> Vec<u8> {
    let mut bytes = b"ERFV0001".to_vec();
    bytes.extend_from_slice(&1u32.to_be_bytes());
    bytes.extend_from_slice(&2u32.to_be_bytes());
    for raw in [b'x', b'y'] {
        bytes.extend_from_slice(&1u32.to_be_bytes());
        bytes.push(raw);
        bytes.push(0);
    }
    bytes.extend_from_slice(b"TAIL");
    bytes
}

#[test]
fn h21_ervf_streaming_parser_and_isolated_negatives() {
    let bytes = tiny_frame();
    let expected = hex(&role0_sha256(&bytes).unwrap());
    let mut frame = FrameReader::new(bytes.as_slice(), bytes.len() as u64).unwrap();
    preamble(&mut frame, 1, 2).unwrap();
    let mut headers = HeaderIter::new(&mut frame, 2);
    assert_eq!(headers.next().unwrap().unwrap(), b"x");
    assert_eq!(headers.next().unwrap().unwrap(), b"y");
    assert!(headers.next().is_none());
    drop(headers);
    frame
        .finish((bytes.len() - 4) as u64, 4, &expected)
        .unwrap();

    let mut wrong_magic = bytes.clone();
    wrong_magic[0] ^= 1;
    let mut frame = FrameReader::new(wrong_magic.as_slice(), wrong_magic.len() as u64).unwrap();
    assert!(preamble(&mut frame, 1, 2).unwrap_err().contains("magic"));

    let mut wrong_length = bytes.clone();
    wrong_length[16..20].copy_from_slice(&515u32.to_be_bytes());
    let mut frame = FrameReader::new(wrong_length.as_slice(), wrong_length.len() as u64).unwrap();
    preamble(&mut frame, 1, 2).unwrap();
    assert!(HeaderIter::new(&mut frame, 2)
        .next()
        .unwrap()
        .unwrap_err()
        .contains("RAW length"));

    let mut wrong_flag = bytes.clone();
    wrong_flag[21] = 2;
    let mut frame = FrameReader::new(wrong_flag.as_slice(), wrong_flag.len() as u64).unwrap();
    preamble(&mut frame, 1, 2).unwrap();
    assert!(HeaderIter::new(&mut frame, 2)
        .next()
        .unwrap()
        .unwrap_err()
        .contains("extension flag"));

    let mut oversized_extension = bytes[..22].to_vec();
    oversized_extension[21] = 1;
    oversized_extension.extend_from_slice(&1_048_576u32.to_be_bytes());
    oversized_extension.extend_from_slice(&bytes[22..]);
    let mut frame = FrameReader::new(
        oversized_extension.as_slice(),
        oversized_extension.len() as u64,
    )
    .unwrap();
    preamble(&mut frame, 1, 2).unwrap();
    assert!(HeaderIter::new(&mut frame, 2)
        .next()
        .unwrap()
        .unwrap_err()
        .contains("extension length exceeds cap"));

    let truncated_record = &bytes[..20];
    let mut frame = FrameReader::new(truncated_record, bytes.len() as u64).unwrap();
    preamble(&mut frame, 1, 2).unwrap();
    assert!(HeaderIter::new(&mut frame, 2)
        .next()
        .unwrap()
        .unwrap_err()
        .contains("truncated"));

    let truncated_tail = &bytes[..bytes.len() - 1];
    let mut frame = FrameReader::new(truncated_tail, bytes.len() as u64).unwrap();
    preamble(&mut frame, 1, 2).unwrap();
    let mut headers = HeaderIter::new(&mut frame, 2);
    assert!(headers.next().unwrap().is_ok());
    assert!(headers.next().unwrap().is_ok());
    drop(headers);
    assert!(frame
        .finish((bytes.len() - 4) as u64, 4, &expected)
        .unwrap_err()
        .contains("truncated"));

    let mut wrong_tail = bytes.clone();
    *wrong_tail.last_mut().unwrap() ^= 1;
    let mut frame = FrameReader::new(wrong_tail.as_slice(), wrong_tail.len() as u64).unwrap();
    preamble(&mut frame, 1, 2).unwrap();
    let mut headers = HeaderIter::new(&mut frame, 2);
    assert!(headers.next().unwrap().is_ok());
    assert!(headers.next().unwrap().is_ok());
    drop(headers);
    assert!(frame
        .finish((bytes.len() - 4) as u64, 4, &expected)
        .unwrap_err()
        .contains("SHA256 mismatch"));
}

#[test]
#[ignore = "full pinned H21 frame; bounded source-matrix runner and independent review required"]
fn c377_authentic_mature_eip_source_matrix_from_producer() {
    const OWNER: usize = 844_672;
    const OWNER_BITS: usize = 1 << 20;
    const BANK53_BASE: usize = 671_744;
    const BANK53_BITS: usize = 2 * 8_192;

    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = File::open(path).expect("open H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES, "opened frame length");
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact ERFV header prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact ERFV extension count");
    frame
        .finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES, "frame length after complete SHA256");

    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())
        .expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("source-owned producer bound to admitted prefix");
    let matrix = NativeMatureEipSourceMatrix::from_producer(&producer)
        .expect("authentic Mature(Eip) prefix source matrix");
    assert_eq!(
        matrix.check_complete(&plan).unwrap(),
        [565_294, 401_362, 81_920]
    );

    let binding = HeaderSourceBinding::for_plan(&plan, OWNER).expect("fixed H21 owner binding");
    let physical = |local: usize| OWNER * OWNER_BITS + local;
    // These reserved Bank53 cells are HEADER-owned zeroes, not DAA cells.
    for local in [BANK53_BASE, BANK53_BASE + BANK53_BITS - 1] {
        assert_eq!(
            matrix.source_cell(&binding, physical(local)).unwrap(),
            MatureEipSourceCell::Header(false),
        );
    }
    // Only the four DAA banks are unresolved; check both ends of each range.
    for (start, end) in crate::daa_history_roster::BANKS {
        for local in [start, end - 1] {
            assert_eq!(
                matrix.source_cell(&binding, physical(local)).unwrap(),
                MatureEipSourceCell::DaaUnresolved,
            );
        }
    }
    let wrong_binding =
        HeaderSourceBinding::for_plan(&plan, OWNER + 1).expect("neighboring H21 owner binding");
    assert!(matrix
        .source_cell(&wrong_binding, physical(BANK53_BASE))
        .is_err());
}

#[test]
#[ignore = "full pinned H21 frame and ROW; bounded C378 runner plus independent review required"]
fn c378_authentic_mature_eip_resolved_matches_native_row() {
    const OWNER: usize = 844_672;
    const OWNER_BITS: usize = 1 << 20;

    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = File::open(path).expect("open H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES, "opened frame length");
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact ERFV header prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact ERFV extension count");
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES, "frame length after complete SHA256");

    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())
        .expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("source-owned producer bound to admitted prefix");
    let resolved = NativeMatureEipResolvedSource::from_producer(&producer)
        .expect("authentic Mature(Eip) DAA source from Header/Tree shadow");
    resolved.check_complete(&plan).expect("complete three-author source image");
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER).unwrap();
    let physical = |local: usize| OWNER * OWNER_BITS + local;
    assert_eq!(resolved.source_cell(&binding, physical(BANK53_BASE)).unwrap(),
        MatureEipResolvedCell::Header(false));
    for (start, end) in crate::daa_history_roster::BANKS {
        assert!(matches!(resolved.source_cell(&binding, physical(start)).unwrap(),
            MatureEipResolvedCell::Daa(_)));
        assert!(matches!(resolved.source_cell(&binding, physical(end - 1)).unwrap(),
            MatureEipResolvedCell::Daa(_)));
    }
    let row = producer.produce(OWNER).expect("independent ordinary native ROW");
    assert_eq!(row.packed_bytes().len(), 1 << 17);
    let mismatch = resolved.packed_bytes().iter().zip(row.packed_bytes())
        .position(|(source, row)| source != row);
    assert!(mismatch.is_none(), "C378 source/ROW first differing byte {mismatch:?}");
}

#[test]
#[ignore = "full pinned H21 frame and dense owner ROW; bounded C379 runner required"]
fn c379_authentic_mature_eip_dense_owner_residuals() {
    use crate::daa_history_roster::{DaaHistoryRoster, BANKS};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::{ActiveOperand, NativeTypedAuthorRead,
        OperandSide, Relation, RowPlan, TypedAuthorJoinPlan};
    use crate::packed_owner_assembly::NativeTypedAuthor;

    const OWNER: usize = 844_672;
    const WIDTH: usize = 1 << 20;
    const ROWS: usize = 1 << 19;
    const EXPECTED_TERMS: usize = 821_307;
    const EXPECTED_ACTIVE: usize = 1_289_184;
    const EXPECTED_FOREIGN: usize = 864;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Author { Header, Tree, Daa }

    // The expected tag comes from physical ownership, never from the source cell.
    // A matching bit with a different author must be rejected before evaluation.
    fn admit(expected: Author, cell: MatureEipResolvedCell) -> Result<bool, &'static str> {
        match (expected, cell) {
            (Author::Header, MatureEipResolvedCell::Header(value))
            | (Author::Tree, MatureEipResolvedCell::Tree(value))
            | (Author::Daa, MatureEipResolvedCell::Daa(value)) => Ok(value),
            _ => Err("physical source author tag mismatch"),
        }
    }

    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = File::open(path).expect("open H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES, "opened frame length");
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact ERFV header prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact ERFV extension count");
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES, "frame length after complete SHA256");
    assert_eq!(after.modified().unwrap(), before.modified().unwrap(),
        "frame changed during complete SHA256");

    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())
        .expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("source-owned producer bound to admitted prefix");
    let resolved = NativeMatureEipResolvedSource::from_producer(&producer)
        .expect("authentic three-author Mature(Eip) source");
    resolved.check_complete(&plan).expect("complete three-author source image");
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER).unwrap();
    let tree_mask = plan.physical_assignment_replacement_mask(OWNER as u64)
        .expect("independent Tree physical ownership mask");
    assert_eq!(tree_mask.len(), WIDTH);
    let roster = DaaHistoryRoster::compile(&plan).expect("native DAA roster");
    let scheduled = Scheduled::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled).expect("exact Eligible08 ROW plan");
    let batch = row_plan.stage_owner(OWNER).expect("atomic canonical owner ROW terms");
    batch.require_owner_parent(&plan, OWNER).expect("exact ROW owner and parent");
    assert_eq!(batch.terms().len(), EXPECTED_TERMS, "owner term census");

    // The 864 foreign alias values also require their actual source-owner
    // HEADER author and packed row. Scalar exports alone do not mint custody.
    let typed_context=TypedAuthorJoinPlan::new(&plan).expect("typed H21 parent");
    let local_lease=resolved.typed_author_lease(&binding).expect("local typed source");
    let source_owners=[843_647,843_775,843_903,844_031,844_159,844_287,
        844_415,844_543,844_671];
    let foreign_leases=source_owners.iter().map(|&source_owner|
        producer.mature_foreign_serializer_author_lease(source_owner)
            .expect("actual HEADER/export/packed serializer author"))
        .collect::<Vec<_>>();
    let foreign_refs=foreign_leases.iter().collect::<Vec<_>>();
    let typed=batch.join_mature_serializer_author_reads(
        &typed_context,&local_lease,&foreign_refs,
    ).expect("all Mature serializer alias occurrences source backed");
    assert_eq!(typed.reads().len(),EXPECTED_ACTIVE);
    let mut typed_foreign=0usize;
    let mut typed_open=0usize;
    for (read,expected) in typed.reads().zip(batch.active_operands()) {
        match *read {
            NativeTypedAuthorRead::Known{operand,cell}=>{
                assert_eq!(operand,expected,"ordered typed occurrence");
                assert_eq!(cell.wire(),operand.wire);
                if operand.wire/WIDTH!=OWNER {
                    assert_eq!(cell.author(),crate::packed_owner_assembly::NativeTypedAuthor::Header);
                    typed_foreign+=1;
                }
            }
            NativeTypedAuthorRead::Open{operand}=>{
                assert_eq!(operand,expected);
                typed_open+=1;
            }
        }
    }
    assert_eq!((typed_foreign,typed_open),(EXPECTED_FOREIGN,0));

    let base = OWNER * WIDTH;
    let bank_wire = batch.active_operands().find_map(|operand| {
        operand.wire.checked_sub(base).filter(|&local| local < WIDTH)
            .filter(|&local| BANKS.iter().any(|&(start, end)| (start..end).contains(&local)))
            .map(|_| operand.wire)
    }).expect("active DAA bank operand for isolated tag mutant");
    let bank_value = admit(Author::Daa, resolved.source_cell(&binding, bank_wire)
        .expect("real DAA bank source cell")).expect("real DAA bank author");
    assert!(admit(Author::Daa, MatureEipResolvedCell::Header(bank_value)).is_err(),
        "same-value DAA to HEADER tag mutant was admitted");

    // The residual adds one dense owner vector. The already checked typed
    // stage supplies every active value in occurrence order; no global X is built.
    let mut residuals = vec![Fr::zero(); ROWS];
    let mut active = batch.active_operands();
    let mut typed_values=typed.reads();
    let mut author_reads = [0usize; 3];
    let mut foreign_reads = 0usize;
    let mut checked_bit = |got: ActiveOperand, expected: ActiveOperand| -> bool {
        assert_eq!(got, expected, "active occurrence/relation/row/side/wire/flags");
        let NativeTypedAuthorRead::Known{operand,cell}=*typed_values.next()
            .expect("missing typed occurrence during residual") else {
            panic!("open typed occurrence during residual");
        };
        assert_eq!(operand,got,"typed residual occurrence/order/side/wire");
        if let Some(local) = got.wire.checked_sub(base).filter(|&local| local < WIDTH) {
            let in_daa = BANKS.iter().any(|&(start, end)| (start..end).contains(&local));
            assert!(!(in_daa && tree_mask[local]), "overlapping DAA and Tree owners");
            let author = if in_daa { Author::Daa }
                else if tree_mask[local] { Author::Tree }
                else { Author::Header };
            let typed_author=match author {
                Author::Header=>NativeTypedAuthor::Header,
                Author::Tree=>NativeTypedAuthor::Tree,
                Author::Daa=>NativeTypedAuthor::Daa,
            };
            assert_eq!(cell.author(),typed_author,"typed residual local physical author");
            author_reads[match author {
                Author::Header => 0, Author::Tree => 1, Author::Daa => 2,
            }] += 1;
            cell.value()
        } else {
            assert_ne!(got.wire / WIDTH, OWNER, "foreign read has local owner");
            assert_eq!(cell.author(),NativeTypedAuthor::Header,
                "typed residual foreign serializer physical author");
            foreign_reads += 1;
            cell.value()
        }
    };

    let mut term_count = 0usize;
    let mut active_count = 0usize;
    let mut relation_terms = [0usize; 3];
    for (occurrence, (relation, term)) in batch.terms().enumerate() {
        let local_row = term.row.checked_sub(OWNER * ROWS)
            .filter(|&row| row < ROWS).expect("term outside dense owner rows");
        relation_terms[match relation {
            Relation::Header => 0, Relation::DaaLane(_) => 1,
            Relation::Scheduled(_) => 2,
            Relation::Map(_) => panic!("ordinary dense residual cannot consume paired-v2 Map relations"),
        }] += 1;
        let gate = &term.gate;
        let c1_active = !gate.c1.is_zero();
        let c2_active = !gate.c2.is_zero();
        let c3_active = !gate.c3.is_zero();
        let left = if c1_active || c3_active {
            let expected = ActiveOperand { occurrence, relation, row: term.row,
                side: OperandSide::Left, wire: gate.left,
                c1_active, c2_active: false, c3_active };
            let got = active.next().expect("missing active left operand");
            active_count += 1;
            Fr::from(checked_bit(got, expected) as u64)
        } else { Fr::zero() };
        let right = if c2_active || c3_active {
            let expected = ActiveOperand { occurrence, relation, row: term.row,
                side: OperandSide::Right, wire: gate.right,
                c1_active: false, c2_active, c3_active };
            let got = active.next().expect("missing active right operand");
            active_count += 1;
            Fr::from(checked_bit(got, expected) as u64)
        } else { Fr::zero() };
        // Every term contributes, including c0-only terms. Rows may cancel only
        // after all terms are summed, so an individual nonzero term is valid.
        residuals[local_row] += gate.c0 + gate.c1 * left + gate.c2 * right
            + gate.c3 * left * right;
        term_count += 1;
    }
    assert!(active.next().is_none(), "trailing active operand");
    drop(checked_bit);
    assert!(typed_values.next().is_none(),"trailing typed residual occurrence");
    assert_eq!(term_count, EXPECTED_TERMS, "all canonical terms consumed");
    assert_eq!(active_count, EXPECTED_ACTIVE, "all active operands consumed");
    assert_eq!(foreign_reads, EXPECTED_FOREIGN, "foreign typed serializer census");
    assert!(
        author_reads[0] > 0 && author_reads[2] > 0,
        "Header and DAA active authors absent; counts={author_reads:?}"
    );
    assert_eq!(
        author_reads[1], 0,
        "Tree active reads contradict no-frame C380 census; counts={author_reads:?}"
    );
    assert_eq!(author_reads.iter().sum::<usize>() + foreign_reads, active_count);
    assert!(relation_terms[0] > 0 && relation_terms[1] > 0,
        "Header and DAA relation producers absent");
    let mut nonzero = 0usize;
    let mut first_nonzero = None;
    for (row, value) in residuals.iter().enumerate() {
        if !value.is_zero() {
            nonzero += 1;
            first_nonzero.get_or_insert(row);
        }
    }
    assert_eq!(nonzero, 0, "nonzero dense owner residual rows; first local q {first_nonzero:?}");
    println!("C379_DENSE_OWNER_RESIDUAL_PASS owner={OWNER} terms={term_count} active={active_count} header_reads={} tree_reads={} daa_reads={} foreign_reads={foreign_reads} residual_rows={ROWS} nonzero={nonzero}",
        author_reads[0], author_reads[1], author_reads[2]);
}

#[test]
fn c380_no_frame_mature_eip_active_author_census() {
    use crate::daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS};
    use crate::daa_integer::Epoch;
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::RowPlan;

    const OWNER: usize = 844_672;
    const WIDTH: usize = 1 << 20;
    const EXPECTED_TERMS: usize = 821_307;
    const EXPECTED_ACTIVE: usize = 1_289_184;
    const EXPECTED_FOREIGN: usize = 864;

    // Structural geometry does not depend on a native prefix or frame values.
    let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x5a; 32], [0x42; 28])
        .expect("fixed H21 structural plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("fixed DAA roster");
    assert_eq!(
        roster.owner_class(OWNER as u64).unwrap(),
        OwnerClass::Mature(Epoch::Eip)
    );
    let scheduled = Scheduled::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled).expect("fixed Eligible08 ROW plan");
    let batch = row_plan
        .stage_owner(OWNER)
        .expect("canonical owner ROW terms");
    batch
        .require_owner_parent(&plan, OWNER)
        .expect("owner and structural parent");
    assert_eq!(
        batch.terms().len(),
        EXPECTED_TERMS,
        "structural term census"
    );

    let tree_mask = plan
        .physical_assignment_replacement_mask(OWNER as u64)
        .expect("independent physical Tree ownership mask");
    assert_eq!(tree_mask.len(), WIDTH);
    let bank_bits: usize = BANKS.iter().map(|&(start, end)| end - start).sum();
    assert_eq!(bank_bits, 81_920, "DAA physical bank census");
    assert_eq!(
        tree_mask.iter().filter(|&&owned| owned).count(),
        401_362,
        "Tree physical ownership census"
    );
    for &(start, end) in &BANKS {
        assert!(
            tree_mask[start..end].iter().all(|&owned| !owned),
            "DAA bank and Tree physical owners overlap"
        );
    }
    assert_eq!(
        WIDTH - 401_362 - bank_bits,
        565_294,
        "complementary Header physical ownership census"
    );

    let base = OWNER * WIDTH;
    let mut counts = [0usize; 4]; // Header, Tree, DAA, foreign.
    for operand in batch.active_operands() {
        if let Some(local) = operand
            .wire
            .checked_sub(base)
            .filter(|&local| local < WIDTH)
        {
            let in_daa = BANKS
                .iter()
                .any(|&(start, end)| (start..end).contains(&local));
            counts[if in_daa {
                2
            } else if tree_mask[local] {
                1
            } else {
                0
            }] += 1;
        } else {
            assert_ne!(operand.wire / WIDTH, OWNER, "foreign wire has local owner");
            counts[3] += 1;
        }
    }
    println!("C380_NO_FRAME_ACTIVE_AUTHOR_CENSUS owner={OWNER} header_reads={} tree_reads={} daa_reads={} foreign_reads={} active={} tree_owned=401362 daa_owned={bank_bits} header_owned=565294",
        counts[0], counts[1], counts[2], counts[3], counts.iter().sum::<usize>());
    assert_eq!(
        counts.iter().sum::<usize>(),
        EXPECTED_ACTIVE,
        "active operand census"
    );
    assert_eq!(counts[3], EXPECTED_FOREIGN, "foreign operand census");
    assert!(
        counts[0] > 0 && counts[2] > 0,
        "Header and DAA active authors absent; counts={counts:?}"
    );
    assert_eq!(
        counts[1], 0,
        "Tree is physically owned but unexpectedly read by this ROW subset; counts={counts:?}"
    );
}

#[test]
fn c381_no_frame_carry_active_author_census() {
    use crate::daa_header_window::Action;
    use crate::daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::{OperandSide, Relation, RowPlan};
    use crate::work_tree_layout::Endpoints;

    const OWNER: usize = 844_673;
    const WIDTH: usize = 1 << 20;
    const ROWS: usize = 1 << 19;

    // This is structural geometry only: no native prefix, source values or frame.
    let plan = WorkTreeHistoryPlan::compile(N as u64, H, [0x5a; 32], [0x42; 28])
        .expect("fixed H21 structural parent");
    let roster = DaaHistoryRoster::compile(&plan).expect("fixed DAA roster");
    let native = crate::daa_header_window::for_child_height((OWNER + 1) as u32)
        .expect("adjacent native DAA child schedule");
    assert_eq!(native.action(), Action::Carry, "independent native Carry action");
    assert_eq!(roster.owner_class(OWNER as u64).unwrap(), OwnerClass::Carry);

    let scheduled = Scheduled::eligible08();
    let scheduled_counts = scheduled.visit_owner(OWNER, |_, _| Ok(()))
        .expect("Eligible08 scheduled owner census");
    let row_plan = RowPlan::new(&roster, &scheduled).expect("exact Eligible08 ROW plan");
    let batch = row_plan.stage_owner(OWNER).expect("canonical Carry ROW terms");
    batch.require_owner_parent(&plan, OWNER).expect("exact owner and parent binding");

    let tree_mask = plan.physical_assignment_replacement_mask(OWNER as u64)
        .expect("independent physical Tree ownership mask");
    assert_eq!(tree_mask.len(), WIDTH);
    assert_eq!(tree_mask.iter().filter(|&&owned| owned).count(), 401_362);
    let bank_bits: usize = BANKS.iter().map(|&(start, end)| end - start).sum();
    assert_eq!(bank_bits, 81_920);
    for &(start, end) in &BANKS {
        assert!(tree_mask[start..end].iter().all(|&owned| !owned),
            "Tree and DAA physical authors overlap");
    }

    let work_wires = Endpoints::new().work;
    let work_set = work_wires.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(work_wires.len(), 224, "independent Work endpoint width");
    assert_eq!(work_wires, (987_674..987_898).collect::<Vec<_>>(),
        "exact native Work endpoint positions");
    assert_eq!(work_set.len(), 224, "independent Work endpoint uniqueness");
    assert!(work_set.iter().all(|&wire| wire < WIDTH));
    let source_owners = [OWNER - 1, OWNER - 2];
    let source_tree_masks = source_owners.map(|source_owner| {
        plan.physical_assignment_replacement_mask(source_owner as u64)
            .expect("independent foreign Tree physical ownership mask")
    });
    for mask in &source_tree_masks {
        assert_eq!(mask.len(), WIDTH);
        assert_eq!(mask.iter().filter(|&&owned| owned).count(), 401_362);
        assert!(work_set.iter().all(|&wire| mask[wire]),
            "foreign Work endpoints lack their own Tree author");
    }
    let mut expected_lane2 = BTreeSet::new();
    for source_owner in source_owners {
        for &wire in &work_set {
            assert!(expected_lane2.insert(source_owner * WIDTH + wire));
        }
    }
    assert_eq!(expected_lane2.len(), 448);

    let relation_index = |relation: Relation| match relation {
        Relation::Header => 0,
        Relation::DaaLane(0) => 1,
        Relation::DaaLane(1) => 2,
        Relation::DaaLane(2) => 3,
        Relation::DaaLane(3) => 4,
        Relation::Scheduled(_) => 5,
        _ => panic!("unexpected DAA lane"),
    };
    let mut relation_terms = [0usize; 6];
    let mut expected_active = 0usize;
    let mut lane2_term_wires = BTreeSet::new();
    for (relation, term) in batch.terms() {
        relation_terms[relation_index(relation)] += 1;
        let gate = &term.gate;
        expected_active += (!gate.c1.is_zero() || !gate.c3.is_zero()) as usize;
        expected_active += (!gate.c2.is_zero() || !gate.c3.is_zero()) as usize;
        if relation == Relation::DaaLane(2) {
            assert_eq!(term.row, OWNER * ROWS + 262_144, "Carry numeric ROW placement");
            assert!(gate.c0.is_zero() && !gate.c1.is_zero()
                && gate.c2.is_zero() && gate.c3.is_zero() && gate.right == 0,
                "Carry EqualParent gate shape");
            assert!(lane2_term_wires.insert(gate.left),
                "duplicate Carry EqualParent Work coordinate");
        }
    }

    // These are candidate authors from independent physical ownership, not
    // authenticated values or a complete source admission.
    let base = OWNER * WIDTH;
    let mut author_reads = [0usize; 4]; // Header region, Tree, DAA, foreign.
    let mut relation_reads = [[0usize; 4]; 6];
    let mut lane2_active_wires = BTreeSet::new();
    for operand in batch.active_operands() {
        let author = if let Some(local) = operand.wire.checked_sub(base)
            .filter(|&local| local < WIDTH) {
            if BANKS.iter().any(|&(start, end)| (start..end).contains(&local)) {
                2
            } else if tree_mask[local] {
                1
            } else {
                0
            }
        } else {
            assert_ne!(operand.wire / WIDTH, OWNER, "foreign wire has local owner");
            if operand.relation == Relation::DaaLane(2) {
                assert_eq!(operand.side, OperandSide::Left,
                    "Carry EqualParent active side");
                assert_eq!(operand.row, OWNER * ROWS + 262_144,
                    "Carry EqualParent active ROW placement");
                let source_index = source_owners.iter()
                    .position(|&owner| owner == operand.wire / WIDTH)
                    .expect("Carry EqualParent foreign owner");
                assert!(source_tree_masks[source_index][operand.wire % WIDTH],
                    "active foreign Work read lacks physical Tree author");
                assert!(lane2_active_wires.insert(operand.wire),
                    "duplicate active Carry EqualParent coordinate");
            }
            3
        };
        author_reads[author] += 1;
        relation_reads[relation_index(operand.relation)][author] += 1;
    }
    let active = author_reads.iter().sum::<usize>();
    let terms = relation_terms.iter().sum::<usize>();
    println!("C381_NO_FRAME_CARRY_STRUCTURAL_CENSUS owner={OWNER} terms={terms} active={active} header_reads={} tree_reads={} daa_reads={} foreign_reads={} relation_terms={relation_terms:?} relation_reads={relation_reads:?} lane2_tree_foreign={} tree_owned=401362 daa_owned={bank_bits} author_geometry_only=true frame=false proof=false client=false",
        author_reads[0], author_reads[1], author_reads[2], author_reads[3],
        lane2_active_wires.len());

    assert!(terms > 0 && relation_terms[0] > 0, "Carry ROW producer absent");
    assert_eq!(active, expected_active, "active iterator/term coefficients disagree");
    assert_eq!(scheduled_counts.max, [0, 0], "unexpected adjacent MAX writer");
    assert_eq!(scheduled_counts.cap, [0, 0], "unexpected adjacent Cap writer");
    assert_eq!(relation_terms[5], 0, "unexpected scheduled ROW terms");
    assert_eq!(relation_terms[1], 0, "Carry has DAA arithmetic terms");
    assert_eq!(relation_terms[2], 0, "Carry has DAA alias terms");
    assert_eq!(relation_terms[3], 448, "Carry EqualParent term count");
    assert_eq!(lane2_term_wires, expected_lane2, "Carry EqualParent Work sources");
    assert_eq!(lane2_active_wires, expected_lane2,
        "all 448 Carry EqualParent operands are active and foreign");
    assert!(author_reads[0] > 0 && author_reads[2] > 0,
        "Header and DAA physical regions absent");
}

#[test]
#[ignore = "pinned H21 frame and fresh local C389 pair output; bounded runner required"]
fn c389_authentic_checked_adjacent_owner_pair_file() {
    use crate::daa_history_roster::DaaHistoryRoster;
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::RowPlan;
    use crate::packed_owner_assembly::write_checked_owner_pair;

    const FIRST: usize = 844_672;
    const SECOND: usize = 844_673;
    const ROW_BYTES: usize = 1 << 17;
    const PAIR_BYTES: u64 = 262_144;

    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME")
        .expect("pinned H21 frame environment variable");
    let frame_path = Path::new(&frame_path);
    assert!(frame_path.is_absolute(), "H21 frame path must be absolute");
    let before = fs::symlink_metadata(frame_path).expect("pinned frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES);
    let file = File::open(frame_path).expect("open pinned H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES);
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES);
    assert_eq!(extensions, EXTENSIONS);
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(frame_path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES);
    assert_eq!(after.modified().unwrap(), before.modified().unwrap(),
        "frame changed during complete SHA256");

    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())
        .expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
    let first_binding = HeaderSourceBinding::for_plan(&plan, FIRST).unwrap();
    let second_binding = HeaderSourceBinding::for_plan(&plan, SECOND).unwrap();
    for binding in [&first_binding, &second_binding] {
        assert!(binding.matches_sink(prefix.root(), prefix.total_be28(), prefix.profile(),
            &crate::bank53_map::CutDescriptor::eligible08().canonical_identity(),
            binding.owner()), "complete native parent/profile/cut/layout binding");
    }
    let roster = DaaHistoryRoster::compile(&plan).expect("native DAA roster");
    let scheduled = Scheduled::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled).expect("exact Eligible08 ROW plan");
    let batch = row_plan.stage_owner(SECOND).expect("canonical Carry ROW terms");
    batch.require_owner_parent(&plan, SECOND).expect("same Carry ROW parent");
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("one producer bound to the admitted prefix");
    let first = producer.checked_mature_eip_slice()
        .expect("complete Mature(Eip) physical source and ordinary ROW");
    let second = producer.checked_carry_slice(&batch)
        .expect("complete Carry physical source and CarryZero ROW");
    assert_eq!(first.binding(), &first_binding);
    assert_eq!(second.binding(), &second_binding);
    assert_eq!(first.packed_bytes().len(), ROW_BYTES);
    assert_eq!(second.packed_bytes().len(), ROW_BYTES);
    let expected_first = first.packed_bytes().to_vec();
    let expected_second = second.packed_bytes().to_vec();

    let output = std::env::var_os("NIPOPOW_C389_PAIR_OUTPUT")
        .expect("fresh local C389 pair output environment variable");
    let output = Path::new(&output);
    assert!(output.is_absolute(), "pair output path must be absolute");
    let parent = output.parent().expect("pair output parent");
    let parent_meta = fs::symlink_metadata(parent).expect("pair output parent metadata");
    assert!(parent_meta.is_dir() && !parent_meta.file_type().is_symlink());
    assert!(!output.exists(), "pair output must be fresh");
    let source = write_checked_owner_pair(output, first, second)
        .expect("checked owner pair create-new and exact readback");
    assert_eq!(source.input_len(), 1 << 21);
    assert_eq!(fs::metadata(output).expect("pair output metadata").len(), PAIR_BYTES);
    assert_eq!(source.read_row_bits(1 << 20, 0).unwrap(), expected_first);
    assert_eq!(source.read_row_bits(1 << 20, 1).unwrap(), expected_second);
    drop(source);
    let reopened = crate::packed::PackedFile::open(output, 21)
        .expect("independent reopen of exact two-owner file");
    let first_read = reopened.read_row_bits(1 << 20, 0).unwrap();
    let second_read = reopened.read_row_bits(1 << 20, 1).unwrap();
    assert_eq!(first_read, expected_first);
    assert_eq!(second_read, expected_second);
    let mut joined = first_read;
    joined.extend_from_slice(&second_read);
    assert_eq!(joined.len(), PAIR_BYTES as usize);
    let digest = hex(&role0_sha256(&joined).expect("exact pair SHA256"));
    println!("C389_AUTHENTIC_CHECKED_PAIR_FILE_PASS owners={FIRST},{SECOND} bytes={PAIR_BYTES} sha256={digest} same_parent=true full_physical_sources=true reopened=true frame=true global_x=false proof=false client=false");
}

#[test]
#[ignore = "full pinned H21 frame and Carry ROW; bounded C382 runner and independent review required"]
fn c382_authentic_carry_dense_owner_residuals() {
    use ark_ff::One;
    use crate::daa_header_window::Action;
    use crate::daa_history_layout::HeaderAssignmentTemplate;
    use crate::daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    use crate::header_daa_row_placement::{
        ActiveOperand, NativeRead, NativeTypedAuthorRead, OperandSide, Relation, RowPlan,
        TypedAuthorJoinPlan, UnresolvedRead,
    };
    use crate::packed_owner_assembly::{NativeHeaderSourceLease, NativeTypedAuthor};
    use crate::work_tree_layout::Endpoints;

    const OWNER: usize = 844_673;
    const WIDTH: usize = 1 << 20;
    const ROWS: usize = 1 << 19;
    const EXPECTED_TERMS: usize = 478_929;
    const EXPECTED_ACTIVE: usize = 679_414;
    const EXPECTED_READS: [usize; 4] = [588_854, 0, 90_112, 448];
    const ANCHOR_ROW: usize = 356_632;
    const ANCHOR_WIRE: usize = 999_424;
    const ANCHORS: usize = 5_442;

    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = File::open(path).expect("open H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES, "opened frame length");
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all ERFV records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact ERFV header prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact ERFV extension count");
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned ERFV identity");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES, "frame length after complete SHA256");
    assert_eq!(after.modified().unwrap(), before.modified().unwrap(),
        "frame changed during complete SHA256");

    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())
        .expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native parent exact root/total");
    let binding = HeaderSourceBinding::for_plan(&plan, OWNER).expect("exact Carry source binding");
    assert_eq!(binding.profile(), prefix.profile(), "canonical profile binding");
    assert!(binding.matches_sink(prefix.root(), prefix.total_be28(), prefix.profile(),
        &crate::bank53_map::CutDescriptor::eligible08().canonical_identity(), OWNER));
    let roster = DaaHistoryRoster::compile(&plan).expect("native DAA roster");
    let action = crate::daa_header_window::for_child_height((OWNER + 1) as u32)
        .expect("adjacent native DAA schedule");
    assert_eq!(action.action(), Action::Carry);
    assert_eq!(roster.owner_class(OWNER as u64).unwrap(), OwnerClass::Carry);
    let scheduled = Scheduled::eligible08();
    let scheduled_counts = scheduled.visit_owner(OWNER, |_, _| Ok(()))
        .expect("Eligible08 owner census");
    assert_eq!(scheduled_counts.max, [0, 0]);
    assert_eq!(scheduled_counts.cap, [0, 0]);
    let row_plan = RowPlan::new(&roster, &scheduled).expect("exact Eligible08 ROW plan");
    let batch = row_plan.stage_owner(OWNER).expect("atomic canonical Carry ROW terms");
    batch.require_owner_parent(&plan, OWNER).expect("exact ROW owner and parent");
    assert_eq!(batch.terms().len(), EXPECTED_TERMS);

    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("source-owned producer bound to admitted prefix");
    let (row, mut daa) = producer.produce_with_carry_zero_daa_source_lease(OWNER)
        .expect("actual Carry row and explicit zero-bank author");
    row.require_header_source_binding(&binding, OWNER, OwnerClass::Carry)
        .expect("actual Carry packed row identity");
    daa.check_carry_zero_source(&binding).expect("typed CarryZero bank author");
    assert_eq!(row.packed_bytes().len(), WIDTH / 8);

    // Recompute HEADER values from canonical prefix fields, never from the ROW
    // being checked. The generic HEADER lease deliberately omits reserved
    // zero anchors at this unscheduled owner, so it cannot cover this test.
    let previous = prefix.header(OWNER).expect("canonical previous header");
    let child = prefix.header(OWNER + 1).expect("canonical Carry child header");
    let leaf = prefix.header(OWNER + 2).expect("canonical Work leaf header");
    for header in [&previous, &child, &leaf] {
        assert_eq!(header.encode().expect("canonical header encode"),
            prefix.raw(header.height as usize).expect("pinned RAW header"));
    }
    let fields = crate::serializer::Fields::from_header(&child)
        .expect("canonical child serializer fields");
    let template = HeaderAssignmentTemplate::new().expect("fixed complete HEADER template");
    let mut header_values = template.assign(&fields).expect("prefix-derived HEADER values");
    template.assign_order(&mut header_values, &fields, previous.height,
        previous.timestamp, false).expect("prefix-derived order values");
    assert_eq!(header_values.len(), WIDTH);

    let tree_mask = plan.physical_assignment_replacement_mask(OWNER as u64)
        .expect("independent Carry Tree physical mask");
    assert_eq!(tree_mask.len(), WIDTH);
    assert_eq!(tree_mask.iter().filter(|&&owned| owned).count(), 401_362);
    let packed_bit = |bytes: &[u8], local: usize| (bytes[local / 8] >> (local % 8)) & 1 != 0;
    let in_daa = |local: usize| BANKS.iter().any(|&(start, end)| (start..end).contains(&local));
    for &(start, end) in &BANKS {
        assert!(tree_mask[start..end].iter().all(|&owned| !owned));
        for local in start..end {
            assert_eq!(daa.read_daa_bit(&binding, OWNER * WIDTH + local).unwrap(), Some(false));
            assert!(!packed_bit(row.packed_bytes(), local), "CarryZero packed bank bit {local}");
        }
    }
    for local in [671_744..688_128, ANCHOR_WIRE..ANCHOR_WIRE + ANCHORS]
        .into_iter().flatten() {
        assert!(!tree_mask[local] && !in_daa(local), "reserved HEADER physical author {local}");
        assert!(header_values[local].is_zero(), "reserved HEADER template zero {local}");
        assert!(!packed_bit(row.packed_bytes(), local), "reserved HEADER packed zero {local}");
    }
    let point = crate::point_membership::witness(fields.pk, fields.w)
        .expect("independent point witness from canonical child");
    assert_eq!(point.len(), crate::point_membership::POINT_WIDTH);
    for (bit, &value) in point.iter().enumerate() {
        let local = crate::segment_points::POINT_OFFSET + bit;
        assert!(!tree_mask[local] && !in_daa(local), "point HEADER physical author {local}");
        assert_eq!(header_values[local], Fr::from(value as u64), "point template witness {local}");
        assert_eq!(packed_bit(row.packed_bytes(), local), value, "point packed witness {local}");
    }

    // Foreign Work values come from the native scalar export and must agree
    // with the two actual predecessor ROW writers at their Tree-owned cells.
    let exports = NativeExports::new_for_history(&plan, &prefix)
        .expect("checked foreign scalar exports");
    let work = Endpoints::new().work;
    assert_eq!(work, (987_674..987_898).collect::<Vec<_>>());
    let source_owners = [OWNER - 1, OWNER - 2];
    let source_masks = source_owners.map(|source_owner| {
        plan.physical_assignment_replacement_mask(source_owner as u64)
            .expect("independent predecessor Tree physical mask")
    });
    let source_rows = source_owners.map(|source_owner| {
        let source_row = producer.produce(source_owner).expect("actual predecessor Tree-owner row");
        let source_binding = HeaderSourceBinding::for_plan(&plan, source_owner).unwrap();
        source_row.require_header_source_binding(&source_binding, source_owner,
            roster.owner_class(source_owner as u64).unwrap())
            .expect("actual predecessor packed row identity");
        source_row
    });
    let mut foreign = BTreeMap::new();
    for index in 0..2 {
        assert_eq!(source_masks[index].len(), WIDTH);
        assert_eq!(source_masks[index].iter().filter(|&&owned| owned).count(), 401_362);
        for &local in &work {
            assert!(source_masks[index][local], "predecessor Work not Tree-owned");
            let wire = source_owners[index] * WIDTH + local;
            let exported = exports.bit(wire).expect("native foreign Work export");
            assert_eq!(exported, packed_bit(source_rows[index].packed_bytes(), local),
                "foreign scalar/actual Tree ROW mismatch wire {wire}");
            assert!(foreign.insert(wire, exported).is_none(), "duplicate foreign Work source");
        }
    }
    assert_eq!(foreign.len(), 448);
    let unequal_work = work.iter().filter(|&&local| {
        foreign[&(source_owners[0] * WIDTH + local)]
            != foreign[&(source_owners[1] * WIDTH + local)]
    }).count();

    let base = OWNER * WIDTH;
    let mut residuals = vec![Fr::zero(); ROWS];
    let mut active = batch.active_operands();
    let mut reads = [0usize; 4]; // HEADER, local Tree, DAA, foreign Tree Work.
    let mut reserved_active = [0usize; 3]; // Bank53, Point, MAX/Cap anchors.
    let mut seen_foreign = BTreeSet::new();
    let mut read = |got: ActiveOperand, expected: ActiveOperand| -> bool {
        assert_eq!(got, expected, "active occurrence/relation/row/side/wire/flags");
        if let Some(local) = got.wire.checked_sub(base).filter(|&local| local < WIDTH) {
            if in_daa(local) {
                let value = daa.read_daa_bit(&binding, got.wire)
                    .expect("bound CarryZero DAA source cell")
                    .expect("active DAA cell missing CarryZero author");
                assert!(!value, "Carry DAA active bank must be zero");
                assert_eq!(value, packed_bit(row.packed_bytes(), local),
                    "active DAA source/ROW mismatch");
                reads[2] += 1;
                value
            } else {
                assert!(!tree_mask[local], "C381 found no active local Tree read");
                let value = header_values[local];
                assert!(value.is_zero() || value.is_one(), "active HEADER source non-Boolean");
                let value = value.is_one();
                assert_eq!(value, packed_bit(row.packed_bytes(), local),
                    "active prefix HEADER/ROW mismatch at {local}");
                if (671_744..688_128).contains(&local) { reserved_active[0] += 1; }
                if (786_432..794_624).contains(&local) { reserved_active[1] += 1; }
                if (ANCHOR_WIRE..ANCHOR_WIRE + ANCHORS).contains(&local) {
                    assert_eq!(got.relation, Relation::Header);
                    assert!(!value, "unscheduled HEADER anchor nonzero");
                    reserved_active[2] += 1;
                }
                reads[0] += 1;
                value
            }
        } else {
            assert_eq!(got.relation, Relation::DaaLane(2), "foreign non-DAA relation");
            assert_eq!(got.side, OperandSide::Left, "foreign EqualParent active side");
            assert_eq!(got.row, OWNER * ROWS + 262_144, "foreign EqualParent ROW");
            let source_index = source_owners.iter().position(|&owner| owner == got.wire / WIDTH)
                .expect("foreign owner outside exact predecessors");
            assert!(source_masks[source_index][got.wire % WIDTH], "foreign non-Tree Work source");
            assert!(seen_foreign.insert(got.wire), "duplicate foreign EqualParent operand");
            reads[3] += 1;
            *foreign.get(&got.wire).expect("foreign Work source absent")
        }
    };

    let mut relation_terms = [0usize; 6];
    let mut anchor_terms = 0usize;
    let mut term_count = 0usize;
    let mut active_count = 0usize;
    for (occurrence, (relation, term)) in batch.terms().enumerate() {
        let q = term.row.checked_sub(OWNER * ROWS)
            .filter(|&row| row < ROWS).expect("term outside dense Carry rows");
        relation_terms[match relation {
            Relation::Header => 0,
            Relation::DaaLane(0) => 1,
            Relation::DaaLane(1) => 2,
            Relation::DaaLane(2) => 3,
            Relation::DaaLane(3) => 4,
            Relation::Scheduled(_) => 5,
            _ => panic!("unexpected DAA lane"),
        }] += 1;
        let gate = &term.gate;
        if relation == Relation::Header && (ANCHOR_ROW..ANCHOR_ROW + ANCHORS).contains(&q) {
            let local = ANCHOR_WIRE + q - ANCHOR_ROW;
            assert_eq!(gate.left, base + local, "unscheduled HEADER anchor source");
            assert_eq!(gate.right, base, "unscheduled HEADER anchor placeholder");
            assert!(gate.c0.is_zero() && gate.c1.is_one()
                && gate.c2.is_zero() && gate.c3.is_zero(), "unscheduled HEADER anchor gate");
            anchor_terms += 1;
        }
        if relation == Relation::DaaLane(2) {
            assert_eq!(q, 262_144, "Carry EqualParent numeric ROW");
            assert!(gate.c0.is_zero() && !gate.c1.is_zero()
                && gate.c2.is_zero() && gate.c3.is_zero(), "Carry EqualParent gate");
        }
        let c1_active = !gate.c1.is_zero();
        let c2_active = !gate.c2.is_zero();
        let c3_active = !gate.c3.is_zero();
        let left = if c1_active || c3_active {
            let expected = ActiveOperand { occurrence, relation, row: term.row,
                side: OperandSide::Left, wire: gate.left,
                c1_active, c2_active: false, c3_active };
            let got = active.next().expect("missing active left operand");
            active_count += 1;
            Fr::from(read(got, expected) as u64)
        } else { Fr::zero() };
        let right = if c2_active || c3_active {
            let expected = ActiveOperand { occurrence, relation, row: term.row,
                side: OperandSide::Right, wire: gate.right,
                c1_active: false, c2_active, c3_active };
            let got = active.next().expect("missing active right operand");
            active_count += 1;
            Fr::from(read(got, expected) as u64)
        } else { Fr::zero() };
        // Constant-only terms still contribute. Only the complete row sum may cancel.
        residuals[q] += gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
        term_count += 1;
    }
    assert!(active.next().is_none(), "trailing active operand");
    drop(read);
    assert_eq!(term_count, EXPECTED_TERMS);
    assert_eq!(active_count, EXPECTED_ACTIVE);
    assert_eq!(reads, EXPECTED_READS, "complete typed active source census");
    assert_eq!(relation_terms, [396_561, 0, 0, 448, 81_920, 0]);
    assert_eq!(anchor_terms, ANCHORS, "all unscheduled HEADER anchors retained");
    assert_eq!(reserved_active[2], ANCHORS, "all MAX/Cap zero anchors read");
    assert_eq!(seen_foreign.len(), 448, "complete foreign Work occurrence census");
    assert!(foreign.keys().all(|wire| seen_foreign.contains(wire)),
        "foreign Work source/ROW occurrence mismatch");
    let mut nonzero = 0usize;
    let mut first_nonzero = None;
    for (q, value) in residuals.iter().enumerate() {
        if !value.is_zero() {
            nonzero += 1;
            first_nonzero.get_or_insert(q);
        }
    }
    assert_eq!((unequal_work, nonzero), (0, 0),
        "authentic Carry EqualParent or dense residual failed; first local q {first_nonzero:?}");
    println!("C382_AUTHENTIC_CARRY_DENSE_OWNER_PASS owner={OWNER} terms={term_count} active={active_count} header_reads={} tree_reads={} daa_reads={} foreign_tree_reads={} reserved_active={reserved_active:?} source_rows=2 unequal_work={unequal_work} residual_rows={ROWS} nonzero={nonzero} frame=true proof=false client=false",
        reads[0], reads[1], reads[2], reads[3]);

    // Join the same authenticated H21 ROW occurrences to the two source-owner
    // Work leases. Local HEADER and DAA reads stay explicit open obligations.
    let typed_context = TypedAuthorJoinPlan::new(&plan)
        .expect("same H21 parent typed author context");
    let typed_leases = [OWNER - 2, OWNER - 1].map(|source_owner| {
        producer.carry_foreign_tree_work_author_lease(source_owner, OWNER)
            .expect("actual adjacent Tree Work author lease")
    });
    let typed_stage = batch.join_typed_author_reads(
        &typed_context, &[&typed_leases[0], &typed_leases[1]],
    ).expect("actual Carry ROW typed author join");
    assert!(std::ptr::eq(typed_stage.batch(), &batch));
    assert_eq!(typed_stage.reads().len(), EXPECTED_ACTIVE);
    let mut typed_known = 0usize;
    let mut typed_open = 0usize;
    for (read, expected) in typed_stage.reads().zip(batch.active_operands()) {
        match *read {
            NativeTypedAuthorRead::Known { operand, cell } => {
                assert_eq!(operand, expected, "typed known ROW occurrence order");
                assert_eq!(cell.wire(), operand.wire, "typed Work wire");
                assert_eq!(cell.author(), NativeTypedAuthor::Tree,
                    "foreign Work must retain its physical Tree author");
                assert_eq!(cell.value(), *foreign.get(&operand.wire)
                    .expect("typed Work wire missing checked scalar/ROW value"));
                typed_known += 1;
            }
            NativeTypedAuthorRead::Open { operand } => {
                assert_eq!(operand, expected, "typed open ROW occurrence order");
                assert_eq!(operand.wire / WIDTH, OWNER,
                    "foreign Work read cannot remain open");
                typed_open += 1;
            }
        }
    }
    assert_eq!((typed_known, typed_open), (448, EXPECTED_ACTIVE - 448));

    // Reconcile the same ordered active occurrences with canonical local
    // HEADER/DAA leases. The typed Tree leases above close the 448 foreign
    // occurrences that checked_native_reads intentionally leaves unresolved.
    let header = producer.header_source_lease(OWNER)
        .expect("canonical local HEADER lease from the same frame");
    header.check_binding(&binding).expect("HEADER frame/owner binding");
    daa.check_carry_zero_source(&binding).expect("DAA frame/owner binding");
    let (header_before, daa_before) =
        (header.read_count_for_test(), daa.read_count_for_test());
    let native_reads = batch.checked_native_reads(&header, &daa)
        .expect("canonical local HEADER/DAA active reads");
    assert_eq!(native_reads.len(), EXPECTED_ACTIVE);
    let (mut native_header, mut native_daa, mut native_foreign) = (0usize, 0usize, 0usize);
    let (mut native_point_open, mut native_anchor_open) = (0usize, 0usize);
    for ((native, typed), operand) in native_reads.iter()
        .zip(typed_stage.reads()).zip(batch.active_operands()) {
        match (*native, *typed) {
            (NativeRead::Header { operand: actual, value },
                NativeTypedAuthorRead::Open { operand: typed_operand }) => {
                assert_eq!(actual, operand, "HEADER active occurrence order");
                assert_eq!(typed_operand, operand, "HEADER typed open occurrence");
                let local = operand.wire - base;
                assert!(!in_daa(local) && !tree_mask[local], "HEADER physical author");
                assert_eq!(value, packed_bit(row.packed_bytes(), local),
                    "HEADER source value/packed wire");
                assert_eq!(header_values[local].is_one(), value,
                    "HEADER prefix value at physical wire");
                native_header += 1;
            }
            (NativeRead::Daa { operand: actual, value },
                NativeTypedAuthorRead::Open { operand: typed_operand }) => {
                assert_eq!(actual, operand, "DAA active occurrence order");
                assert_eq!(typed_operand, operand, "DAA typed open occurrence");
                let local = operand.wire - base;
                assert!(in_daa(local) && !tree_mask[local], "DAA physical author");
                assert!(!value, "CarryZero DAA source value");
                assert_eq!(value, packed_bit(row.packed_bytes(), local),
                    "DAA source value/packed wire");
                native_daa += 1;
            }
            (NativeRead::Unresolved { operand: actual,
                reason: UnresolvedRead::ForeignOwner },
                NativeTypedAuthorRead::Known { operand: typed_operand, cell }) => {
                assert_eq!(actual, operand, "foreign native occurrence order");
                assert_eq!(typed_operand, operand, "foreign typed occurrence order");
                assert_eq!(cell.wire(), operand.wire, "foreign physical wire");
                assert_eq!(cell.author(), NativeTypedAuthor::Tree,
                    "foreign physical Tree author");
                assert_eq!(operand.relation, Relation::DaaLane(2));
                assert_eq!(cell.value(), foreign[&operand.wire],
                    "foreign scalar/Tree lease source value");
                assert_eq!(cell.value(), exports.bit(operand.wire).unwrap(),
                    "foreign canonical export at physical wire");
                native_foreign += 1;
            }
            (NativeRead::Unresolved { operand: actual,
                reason: UnresolvedRead::UnqualifiedLocal },
                NativeTypedAuthorRead::Open { operand: typed_operand }) => {
                assert_eq!(actual, operand, "unresolved local occurrence order");
                assert_eq!(typed_operand, operand, "unresolved typed open occurrence");
                let local = operand.wire.checked_sub(base).filter(|&local| local < WIDTH)
                    .expect("unresolved local physical owner");
                let point_open = (786_432..794_624).contains(&local);
                let anchor_open = (ANCHOR_WIRE..ANCHOR_WIRE + ANCHORS).contains(&local);
                assert!(point_open || anchor_open,
                    "C386 only Point/unscheduled MAX-Cap anchors may remain open: {local}");
                assert!(!in_daa(local) && !tree_mask[local],
                    "C386 open local retains its independently classified physical region");
                let prefix_value = header_values[local];
                assert!(prefix_value.is_zero() || prefix_value.is_one(),
                    "C386 open source value is not Boolean at {local}");
                let packed_value = packed_bit(row.packed_bytes(), local);
                assert_eq!(prefix_value.is_one(), packed_value,
                    "C386 open prefix/packed value at {local}");
                if anchor_open {
                    assert_eq!(operand.relation, Relation::Header,
                        "C386 unscheduled anchor relation");
                    assert!(!prefix_value.is_one(), "C386 unscheduled anchor must be zero");
                    native_anchor_open += 1;
                } else {
                    native_point_open += 1;
                }
            }
            other => panic!("C386 local/foreign author reconciliation mismatch: {other:?}"),
        }
    }
    assert_eq!((native_header, native_daa, native_foreign,
        native_point_open, native_anchor_open),
        (582_884, 90_112, 448, 528, ANCHORS), "C386 full occurrence disposition census");
    assert_eq!(native_header + native_daa + native_foreign
        + native_point_open + native_anchor_open,
        EXPECTED_ACTIVE, "C386 exact active occurrence coverage");
    assert_eq!(header.read_count_for_test() - header_before, 582_884,
        "C386 canonical HEADER read count");
    assert_eq!(daa.read_count_for_test() - daa_before, 90_112,
        "C386 canonical DAA read count");
    println!("C386_AUTHENTIC_CARRY_NATIVE_LOCAL_RECONCILIATION owner={OWNER} active={} header={native_header} daa={native_daa} foreign_tree={native_foreign} open_point={native_point_open} open_anchor={native_anchor_open} unresolved={}",
        native_header + native_daa + native_foreign + native_point_open + native_anchor_open,
        native_point_open + native_anchor_open);

    // The C386 base lease intentionally left these two regions unresolved.
    // Qualify only the 528 and 5,442 active ROW occurrences through a fresh
    // physical-author replay of the ordinary Carry HEADER writer.
    let (qualified_header, full_author_counts) = producer.carry_header_source_lease_for_row(&batch, &row)
        .expect("exact Carry physical HEADER writer and active ROW census");
    qualified_header.check_binding(&binding).expect("C387 same frame/owner binding");
    let c387_closed = |source: &NativeHeaderSourceLease| -> Result<[usize; 3], String> {
        let native = batch.checked_native_reads(source, &daa)?;
        if native.len() != EXPECTED_ACTIVE { return Err("C387 active read length".into()); }
        let mut counts = [0usize; 3]; // HEADER, DAA, foreign Tree.
        let mut point_count = 0usize;
        let mut anchor_count = 0usize;
        for ((read, typed), operand) in native.iter()
            .zip(typed_stage.reads()).zip(batch.active_operands()) {
            match (*read, *typed) {
                (NativeRead::Header { operand: actual, value },
                    NativeTypedAuthorRead::Open { operand: typed_operand }) => {
                    if actual != operand || typed_operand != operand {
                        return Err("C387 ordered HEADER occurrence".into());
                    }
                    let local = operand.wire.checked_sub(base)
                        .filter(|&wire| wire < WIDTH)
                        .ok_or("C387 local HEADER owner")?;
                    if in_daa(local) || tree_mask[local]
                        || value != header_values[local].is_one()
                        || value != packed_bit(row.packed_bytes(), local) {
                        return Err(format!("C387 HEADER source/ROW mismatch wire{local}"));
                    }
                    if (crate::segment_points::POINT_OFFSET
                        ..crate::segment_points::POINT_OFFSET + crate::point_membership::POINT_WIDTH)
                        .contains(&local) {
                        if value != point[local - crate::segment_points::POINT_OFFSET] {
                            return Err(format!("C387 canonical Point witness wire{local}"));
                        }
                        point_count += 1;
                    }
                    if (ANCHOR_WIRE..ANCHOR_WIRE + ANCHORS).contains(&local) {
                        if operand.relation != Relation::Header || value {
                            return Err(format!("C387 unscheduled zero anchor wire{local}"));
                        }
                        anchor_count += 1;
                    }
                    counts[0] += 1;
                }
                (NativeRead::Daa { operand: actual, value },
                    NativeTypedAuthorRead::Open { operand: typed_operand }) => {
                    if actual != operand || typed_operand != operand || value
                        || operand.wire.checked_sub(base)
                            .filter(|&local| local < WIDTH && in_daa(local))
                            .is_none() {
                        return Err("C387 ordered CarryZero DAA occurrence".into());
                    }
                    counts[1] += 1;
                }
                (NativeRead::Unresolved { operand: actual,
                    reason: UnresolvedRead::ForeignOwner },
                    NativeTypedAuthorRead::Known { operand: typed_operand, cell }) => {
                    if actual != operand || typed_operand != operand
                        || cell.author() != NativeTypedAuthor::Tree
                        || cell.wire() != operand.wire
                        || foreign.get(&operand.wire) != Some(&cell.value()) {
                        return Err("C387 ordered foreign Tree author/value".into());
                    }
                    counts[2] += 1;
                }
                _ => return Err("C387 active occurrence lacks a qualified author".into()),
            }
        }
        if counts != [588_854, 90_112, 448]
            || point_count != 528 || anchor_count != ANCHORS
            || counts.iter().sum::<usize>() != EXPECTED_ACTIVE {
            return Err("C387 exact ordered known-read census".into());
        }
        Ok(counts)
    };
    assert_eq!(c387_closed(&qualified_header), Ok([588_854, 90_112, 448]),
        "all authentic active ROW reads have ordered physical authors");

    let point_zero = (1..=528).find(|&bit| !point[bit])
        .map(|bit| crate::segment_points::POINT_OFFSET + bit)
        .expect("authentic active Point zero for isolated mutants");
    for local in [point_zero, ANCHOR_WIRE] {
        let physical = base + local;
        assert_eq!(qualified_header.read_header_bit(&binding, physical), Ok(Some(false)),
            "authentic Point/anchor zero from HEADER author");
        let wrong_author = NativeHeaderSourceLease::wrong_author_for_test(
            binding.clone(), physical, false);
        assert_eq!(wrong_author.removed_author_check_mutant_for_test(&binding, physical),
            Ok(Some(false)), "same-zero wrong author has the same value");
        assert!(wrong_author.read_header_bit(&binding, physical).is_err(),
            "same-zero Point/anchor wrong author must reject before read");
        assert!(c387_closed(&wrong_author).is_err(),
            "same-zero Point/anchor wrong author must reject whole join");
    }
    for local in [point_zero, ANCHOR_WIRE] {
        let mut flipped = qualified_header.clone();
        flipped.flip_source_value_for_test(local);
        assert!(c387_closed(&flipped).is_err(),
            "isolated Point/anchor value flip must fail source/ROW reconciliation");
    }
    println!("C387_AUTHENTIC_CARRY_ACTIVE_HEADER_AUTHOR_PASS owner={OWNER} known={EXPECTED_ACTIVE} header=588854 daa=90112 foreign_tree=448 active_point=528 unscheduled_anchors={ANCHORS} open=0 wrong_author_and_flip_mutants=true frame=true proof=false client=false");
    assert_eq!(full_author_counts, [565_294, 401_362, 81_920],
        "every authentic Carry bit has its exact physical author");
    println!("C388_AUTHENTIC_CARRY_FULL_AUTHOR_CENSUS_PASS owner={OWNER} bits=1048576 header={} tree={} daa={} full_source_and_packed=true frame=true proof=false client=false",
        full_author_counts[0], full_author_counts[1], full_author_counts[2]);

    let header_zero_wire = native_reads.iter().find_map(|read| match *read {
        NativeRead::Header { operand, value: false } => Some(operand.wire),
        _ => None,
    }).expect("authentic active HEADER zero for author mutant");
    let mut wrong_header = producer.header_source_lease(OWNER)
        .expect("fresh canonical HEADER lease for author mutant");
    assert_eq!(wrong_header.read_header_bit(&binding, header_zero_wire), Ok(Some(false)),
        "same-zero canonical HEADER source cell");
    wrong_header.wrong_author_mutant_for_test();
    let header_before_wrong_author = wrong_header.read_count_for_test();
    let daa_before_wrong_header = daa.read_count_for_test();
    let header_wrong = batch.checked_native_reads(&wrong_header, &daa).err()
        .expect("same-value wrong-author HEADER lease must reject");
    assert!(header_wrong.contains("HEADER source author mismatch before read admission"));
    assert_eq!(wrong_header.read_count_for_test(), header_before_wrong_author,
        "C386 wrong HEADER author rejected before value read");
    assert_eq!(daa.read_count_for_test(), daa_before_wrong_header,
        "C386 wrong HEADER author rejects before DAA read");

    let daa_zero_wire = native_reads.iter().find_map(|read| match *read {
        NativeRead::Daa { operand, value: false } => Some(operand.wire),
        _ => None,
    }).expect("authentic active DAA zero for author mutant");
    assert_eq!(daa.read_daa_bit(&binding, daa_zero_wire), Ok(Some(false)),
        "same-zero canonical DAA source cell");
    daa.wrong_author_mutant_for_test();
    let good_header = producer.header_source_lease(OWNER)
        .expect("fresh canonical HEADER lease for DAA author mutant");
    let daa_before_wrong_author = daa.read_count_for_test();
    let daa_wrong = batch.checked_native_reads(&good_header, &daa).err()
        .expect("same-zero wrong-author DAA lease must reject");
    assert!(daa_wrong.contains("DAA source author mismatch before read admission"));
    assert_eq!(good_header.read_count_for_test(), 0,
        "C386 wrong DAA author rejected before HEADER value read");
    assert_eq!(daa.read_count_for_test(), daa_before_wrong_author,
        "C386 wrong DAA author rejected before value read");

    // Preserve the authentic zero value and wire while changing only its
    // claimed author; the join must reject the same-zero wrong-writer lease.
    let zero_wire = work.iter().map(|&local| (OWNER - 2) * WIDTH + local)
        .find(|wire| !foreign[wire]).expect("actual predecessor Work zero cell");
    let authentic_zero = typed_leases[0].read_cell(&binding, zero_wire)
        .expect("authentic zero cell read").expect("authentic zero cell present");
    assert_eq!((authentic_zero.author(), authentic_zero.value()),
        (NativeTypedAuthor::Tree, false));
    let mut wrong_author = typed_leases[0].clone();
    wrong_author.wrong_author_for_test();
    let forged_zero = wrong_author.read_cell(&binding, zero_wire)
        .expect("forged zero cell read").expect("forged zero cell present");
    assert_eq!((forged_zero.wire(), forged_zero.author(), forged_zero.value()),
        (zero_wire, NativeTypedAuthor::Header, false));
    assert!(batch.join_typed_author_reads(
        &typed_context, &[&wrong_author, &typed_leases[1]],
    ).is_err(), "same-zero wrong-author lease must fail before publication");
    println!("C385_AUTHENTIC_CARRY_TYPED_AUTHOR_JOIN_PASS owner={OWNER} known_tree={typed_known} open={typed_open} same_zero_wrong_author_rejected=true frame=true proof=false client=false");
}

/// Reuse the complete pinned ERFV reader, without exporting its internals or
/// allowing a borrowed native source to escape the consumer closure.
pub(crate) fn c574_with_pinned_prefix<R>(
    consume: impl FnOnce(&NativePrefix) -> Result<R, String>,
) -> Result<R, String> {
    let path = std::env::var_os("NIPOPOW_H21_FRAME").ok_or("C574 pinned frame environment")?;
    let path = Path::new(&path);
    if !path.is_absolute() { return Err("C574 absolute frame path".into()); }
    let before = fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() != FRAME_BYTES {
        return Err("C574 pinned regular frame extent".into());
    }
    let file = File::open(path).map_err(|e|e.to_string())?;
    if file.metadata().map_err(|e|e.to_string())?.len() != FRAME_BYTES {
        return Err("C574 opened frame extent".into());
    }
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES)?;
    preamble(&mut frame,1_827_839,N as u32)?;
    let (prefix,extensions) = {
        let mut headers = HeaderIter::new(&mut frame,N);
        let prefix = NativePrefix::from_raw_iter(N,&mut headers)?;
        if headers.remaining != 0 { return Err("C574 incomplete ERFV records".into()); }
        (prefix,headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C574 complete native prefix/extension extent".into());
    }
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256)?;
    let after = fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    if !after.is_file() || after.file_type().is_symlink() || after.len() != before.len()
        || after.modified().map_err(|e|e.to_string())? != before.modified().map_err(|e|e.to_string())? {
        return Err("C574 pinned frame changed".into());
    }
    consume(&prefix)
}

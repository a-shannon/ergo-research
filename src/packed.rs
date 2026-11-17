//! Immutable packed-bit witness adapter for the transparent Dory PCS.
//! The file stays open without write/delete sharing for every commit/open scan.
use ark_bn254::{Fr,G1Projective};
use ark_ec::CurveGroup;
use ark_ff::Zero;
use dory_pcs::backends::arkworks::{ArkDoryProof, ArkFr, ArkG1, ArkGT, BN254, G1Routines, G2Routines};
use dory_pcs::primitives::arithmetic::{DoryRoutines, Group, PairingCurve};
use dory_pcs::{MultilinearLagrange, Polynomial, ProverSetup, Transparent};
use rayon::prelude::*;
use blake2::{Blake2b512,Digest};
use std::cell::{RefCell,RefMut};
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path,PathBuf};
#[cfg(test)]
use std::sync::{Arc,Mutex};
#[cfg(test)]
use std::time::Instant;

#[cfg(test)]
#[derive(Clone,Copy,Debug,Default,Eq,PartialEq)]
pub(crate) struct PackedIoSnapshot {
    pub read_calls:u64,
    pub read_bytes:u64,
    pub read_ns:u128,
    pub write_calls:u64,
    pub write_bytes:u64,
    pub write_ns:u128,
    pub sync_calls:u64,
    pub sync_ns:u128,
}

#[cfg(test)]
type SharedPackedIo=Arc<Mutex<PackedIoSnapshot>>;

#[cfg(test)]
std::thread_local! {
    static PACKED_FALLBACK_CALLS:std::cell::Cell<[u64;2]>=const {std::cell::Cell::new([0,0])};
}

#[cfg(test)]
fn record_read(metrics:&SharedPackedIo,bytes:usize,result:&std::io::Result<()>,started:Instant){
    if result.is_ok(){
        let elapsed_ns=started.elapsed().as_nanos();
        let mut stats=metrics.lock().unwrap_or_else(|error|error.into_inner());
        stats.read_calls=stats.read_calls.saturating_add(1);
        stats.read_bytes=stats.read_bytes.saturating_add(bytes as u64);
        stats.read_ns=stats.read_ns.saturating_add(elapsed_ns);
    }
}

#[cfg(test)]
fn record_write(metrics:&SharedPackedIo,bytes:usize,result:&std::io::Result<()>,started:Instant){
    if result.is_ok(){
        let elapsed_ns=started.elapsed().as_nanos();
        let mut stats=metrics.lock().unwrap_or_else(|error|error.into_inner());
        stats.write_calls=stats.write_calls.saturating_add(1);
        stats.write_bytes=stats.write_bytes.saturating_add(bytes as u64);
        stats.write_ns=stats.write_ns.saturating_add(elapsed_ns);
    }
}

#[cfg(test)]
fn record_sync(metrics:&SharedPackedIo,result:&std::io::Result<()>,started:Instant){
    if result.is_ok(){
        let elapsed_ns=started.elapsed().as_nanos();
        let mut stats=metrics.lock().unwrap_or_else(|error|error.into_inner());
        stats.sync_calls=stats.sync_calls.saturating_add(1);
        stats.sync_ns=stats.sync_ns.saturating_add(elapsed_ns);
    }
}

use crate::{pcs::{self, Setup}, transcript::Transcript};

const COMMIT_WINDOW:usize=4;
const MAX_COMMIT_TABLE_BYTES:usize=2usize*1024*1024*1024;
const MAX_COMMIT_READ_BATCH_BYTES:usize=32usize*1024*1024;
const SUBSET_CHUNK_ENTRIES:usize=32768;

#[derive(Clone,Copy)]
struct CommitWindow {start:usize,width:usize,table_offset:usize}

fn commit_table_entries(width:usize)->Result<usize,String>{
    (0..width).step_by(COMMIT_WINDOW).try_fold(0usize,|entries,start|{
        entries.checked_add(1usize.checked_shl((width-start).min(COMMIT_WINDOW) as u32)
            .ok_or("commit subset width overflow")?).ok_or_else(||"commit subset table size overflow".into())
    })
}

fn commit_table_required_bytes(width:usize)->Result<usize,String>{
    let entries=commit_table_entries(width)?;
    let groups=width.div_ceil(COMMIT_WINDOW);
    let per_entry=std::mem::size_of::<G1Projective>()
        .checked_add(std::mem::size_of::<ark_bn254::G1Affine>())
        .and_then(|bytes|bytes.checked_add(std::mem::size_of::<ark_bn254::Fq>()))
        .ok_or("commit table entry byte size overflow")?;
    entries.checked_mul(per_entry)
        .and_then(|bytes|groups.checked_mul(std::mem::size_of::<CommitWindow>()).and_then(|metadata|bytes.checked_add(metadata)))
        .ok_or_else(||"commit table byte size overflow".into())
}

fn commit_subset_table(setup:&Setup,width:usize)->Result<(Vec<CommitWindow>,Vec<ark_bn254::G1Affine>),String>{
    let (windows,table,_) = commit_subset_table_chunked(setup,width,SUBSET_CHUNK_ENTRIES)?;
    Ok((windows,table))
}

#[derive(Default)]
struct SubsetConstructionStats {
    windows_capacity:usize,
    table_capacity:usize,
    projective_capacity:usize,
    affine_chunk_capacity_max:usize,
    normalization_calls:usize,
}
fn reserved_subset_vec<T>(count:usize)->Result<Vec<T>,String>{
    count.checked_mul(std::mem::size_of::<T>()).ok_or("subset reservation byte overflow")?;
    let mut values=Vec::new();values.try_reserve_exact(count).map_err(|_|"subset reservation failed")?;
    if values.capacity()!=count{return Err("subset reservation capacity mismatch".into());}
    Ok(values)
}
fn normalize_subset_chunk(projective:&mut Vec<G1Projective>,table:&mut Vec<ark_bn254::G1Affine>,
                          entries:usize,stats:&mut SubsetConstructionStats)->Result<(),String>{
    if projective.is_empty(){return Ok(());}
    let end=table.len().checked_add(projective.len()).ok_or("subset normalized count overflow")?;
    if end>entries||end>table.capacity(){return Err("subset normalized destination extent".into());}
    // Pinned normalize_batch has infallible internal allocations. A library
    // allocation abort remains a failed process, not a successful partial table.
    let affine=G1Projective::normalize_batch(projective);
    if affine.len()!=projective.len()||affine.capacity()>projective.capacity(){
        return Err("subset normalization capacity mismatch".into());
    }
    stats.affine_chunk_capacity_max=stats.affine_chunk_capacity_max.max(affine.capacity());
    stats.normalization_calls=stats.normalization_calls.checked_add(1).ok_or("subset chunk count overflow")?;
    table.extend(affine);
    projective.clear();
    Ok(())
}
fn commit_subset_table_chunked(setup:&Setup,width:usize,chunk_entries:usize)
    ->Result<(Vec<CommitWindow>,Vec<ark_bn254::G1Affine>,SubsetConstructionStats),String>{
    commit_subset_table_chunked_from_g1(&setup.prover.g1_vec,width,chunk_entries)
}

fn commit_subset_table_chunked_from_g1(g1:&[ArkG1],width:usize,chunk_entries:usize)
    ->Result<(Vec<CommitWindow>,Vec<ark_bn254::G1Affine>,SubsetConstructionStats),String>{
    if chunk_entries<16||chunk_entries>SUBSET_CHUNK_ENTRIES||chunk_entries%16!=0{
        return Err("subset chunk limit must be 16..32768 and divisible by 16".into());
    }
    if g1.len()<width{return Err("commitment G1 setup too short".into());}
    let entries=commit_table_entries(width)?;
    if commit_table_required_bytes(width)?>MAX_COMMIT_TABLE_BYTES{
        return Err("commit subset table exceeds memory budget".into());
    }
    let groups=width.div_ceil(COMMIT_WINDOW);
    let chunk_capacity=entries.min(chunk_entries);
    // The pinned parallel normalizer reserves four affine slots for two entries.
    // Keep the logical flush limit; only this physical reservation accommodates it.
    let projective_capacity=if chunk_capacity==2{4}else{chunk_capacity};
    let mut windows=reserved_subset_vec::<CommitWindow>(groups)?;
    let mut table=reserved_subset_vec::<ark_bn254::G1Affine>(entries)?;
    let mut projective=reserved_subset_vec::<G1Projective>(projective_capacity)?;
    let mut stats=SubsetConstructionStats{windows_capacity:windows.capacity(),table_capacity:table.capacity(),
        projective_capacity:projective.capacity(),..Default::default()};
    for start in (0..width).step_by(COMMIT_WINDOW){
        let window_width=(width-start).min(COMMIT_WINDOW);
        let window_entries=1usize.checked_shl(window_width as u32).ok_or("subset window count overflow")?;
        if projective.len().checked_add(window_entries).ok_or("subset chunk extent overflow")?>chunk_capacity{
            normalize_subset_chunk(&mut projective,&mut table,entries,&mut stats)?;
        }
        if window_entries>chunk_capacity{return Err("subset complete window exceeds chunk".into());}
        let table_offset=table.len().checked_add(projective.len()).ok_or("subset global offset overflow")?;
        let local_offset=projective.len();
        windows.push(CommitWindow{start,width:window_width,table_offset});
        projective.push(G1Projective::zero());
        for mask in 1usize..window_entries{
            let bit=mask.trailing_zeros() as usize;let previous=mask&(mask-1);
            let generator=start.checked_add(bit).ok_or("subset generator offset overflow")?;
            let base=g1.get(generator).ok_or("subset generator extent")?.0;
            let prior=local_offset.checked_add(previous).ok_or("subset local offset overflow")?;
            projective.push(if previous==0{base}else{*projective.get(prior).ok_or("subset recurrence extent")?+base});
        }
    }
    normalize_subset_chunk(&mut projective,&mut table,entries,&mut stats)?;
    if table.len()!=entries||windows.len()!=groups{return Err("commit subset table count mismatch".into());}
    Ok((windows,table,stats))
}

#[cfg(test)]
#[path = "log41_width_sample_tests.rs"]
mod log41_width_sample_tests;

#[cfg(test)]
#[path = "candidate94_real_rows_packed_tests.rs"]
pub(crate) mod candidate94_real_rows_packed_tests;

#[cfg(test)]
#[path = "c312_projection_tests.rs"]
pub(crate) mod c312_projection_tests;

#[cfg(test)]
mod pcs_construction_tests {
    use super::*;
    use ark_ff::One;
    use blake2::{Blake2b512,Digest};
    use serde_json::json;
    const BITS_BLAKE:&str="C38B534BA44D657238ABA94ED1EA860AC8A448BDAFEE2476295F08CF04B995F97829390008C0FAF1E5BBACE8A8A886CA17FED34980BC9889CAE30A8127EAA623";
    const GKR_BLAKE:&str="767797ABFBB15E8B25D130DFF1677AD5D256B2F5327A1B693FACA881F59FF27720023574E964ECB8B65C138A86EF522FE6D5B7956BB926B00CCDE765EBA9BCB0";
    fn blake(bytes:&[u8])->String{Blake2b512::digest(bytes).iter().map(|b|format!("{b:02X}")).collect()}
    fn ledger(t:&Transcript)->(u64,u64,u64){(t.challenges(),t.raw_queries(),t.bytes_absorbed())}
    fn ordinary_prefix(setup:&Setup,commitment:&[u8])->Transcript{
        let mut t=Transcript::new(b"core-pool-four-owner-packed-join-v1");
        t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"commitment",commitment);t
    }
    fn regular(path:&Path,directory:bool){
        let md=std::fs::symlink_metadata(path).unwrap();assert!(!md.file_type().is_symlink());
        assert_eq!(md.is_dir(),directory);assert_eq!(md.is_file(),!directory);
        #[cfg(windows)]{use std::os::windows::fs::MetadataExt;assert_eq!(md.file_attributes()&0x400,0);}
    }
    fn archived_gkr(root:&Path)->Vec<u8>{
        let path=root.join("core-pool.gkr");regular(&path,false);
        let mut options=OpenOptions::new();options.read(true);
        #[cfg(windows)]{use std::os::windows::fs::OpenOptionsExt;options.share_mode(0);}
        let mut f=options.open(path).unwrap();let before=f.metadata().unwrap();assert_eq!(before.len(),5024);
        let mut bytes=vec![0;5024];f.read_exact(&mut bytes).unwrap();let mut tail=[0;1];assert_eq!(f.read(&mut tail).unwrap(),0);
        let after=f.metadata().unwrap();assert_eq!(before.len(),after.len());assert_eq!(before.modified().unwrap(),after.modified().unwrap());
        assert_eq!(blake(&bytes),GKR_BLAKE);bytes
    }
    // Complete frozen original recurrence and single normalization oracle.
    fn original_table(setup:&Setup,width:usize)->(Vec<CommitWindow>,Vec<ark_bn254::G1Affine>){
        assert!(setup.prover.g1_vec.len()>=width);let entries=commit_table_entries(width).unwrap();
        assert!(commit_table_required_bytes(width).unwrap()<=MAX_COMMIT_TABLE_BYTES);
        let mut windows=Vec::with_capacity(width.div_ceil(COMMIT_WINDOW));let mut projective=Vec::with_capacity(entries);
        for start in (0..width).step_by(COMMIT_WINDOW){let window_width=(width-start).min(COMMIT_WINDOW);let table_offset=projective.len();
            windows.push(CommitWindow{start,width:window_width,table_offset});projective.push(G1Projective::zero());
            for mask in 1usize..1usize<<window_width{let bit=mask.trailing_zeros()as usize;let previous=mask&(mask-1);
                let base=setup.prover.g1_vec[start+bit].0;projective.push(if previous==0{base}else{projective[table_offset+previous]+base});}}
        assert_eq!(projective.len(),entries);(windows,G1Projective::normalize_batch(&projective))
    }
    fn window_tuples(windows:&[CommitWindow])->Vec<(usize,usize,usize)>{windows.iter().map(|w|(w.start,w.width,w.table_offset)).collect()}
    fn table_controls()->(usize,usize){
        let mut math=0;let mut negatives=0;
        for log_n in 0usize..=4{let setup=pcs::generate_setup(log_n).unwrap();let width=1usize<<log_n.div_ceil(2);
            let(old_w,old_t)=original_table(&setup,width);
            for limit in [16,48,4096,32768]{let(w,t,s)=commit_subset_table_chunked(&setup,width,limit).unwrap();
                assert_eq!(window_tuples(&w),window_tuples(&old_w));assert_eq!(t,old_t);math+=2;
                assert!(s.projective_capacity<=limit&&s.affine_chunk_capacity_max<=s.projective_capacity);
                if width==1{assert_eq!(t.len(),2);assert_eq!(s.table_capacity,2);assert_eq!(s.windows_capacity,1);
                    assert_eq!(s.projective_capacity,4);assert_eq!(s.affine_chunk_capacity_max,4);assert_eq!(s.normalization_calls,1);}
                if log_n==0{let(ew,et,es)=commit_subset_table_chunked(&setup,0,limit).unwrap();
                    assert!(ew.is_empty()&&et.is_empty());assert_eq!(es.windows_capacity,0);assert_eq!(es.table_capacity,0);
                    assert_eq!(es.projective_capacity,0);assert_eq!(es.affine_chunk_capacity_max,0);assert_eq!(es.normalization_calls,0);}}}
        // Isolate the original capacity fault: correct lengths/destination, but
        // physical projective capacity two must still reject affine capacity four.
        let mut undersized=reserved_subset_vec::<G1Projective>(2).unwrap();undersized.resize(2,G1Projective::zero());
        let mut destination=reserved_subset_vec::<ark_bn254::G1Affine>(2).unwrap();let mut unchanged=SubsetConstructionStats::default();
        assert_eq!(normalize_subset_chunk(&mut undersized,&mut destination,2,&mut unchanged),Err("subset normalization capacity mismatch".into()));
        assert_eq!(undersized.len(),2);assert_eq!(undersized.capacity(),2);assert!(undersized.iter().all(|point|point.is_zero()));
        assert!(destination.is_empty());assert_eq!(destination.capacity(),2);
        assert_eq!(unchanged.windows_capacity,0);assert_eq!(unchanged.table_capacity,0);assert_eq!(unchanged.projective_capacity,0);
        assert_eq!(unchanged.affine_chunk_capacity_max,0);assert_eq!(unchanged.normalization_calls,0);negatives+=1;
        let setup=pcs::generate_setup(6).unwrap();let(w,t)=original_table(&setup,8);
        // Each probe selects the single changed entry/window. Identity masks
        // remain positive controls and are not counted as rejection evidence.
        let probe=|ww:&[CommitWindow],tt:&[ark_bn254::G1Affine],bits:u8|commit_subset_row(ww,tt,&[bits],0);
        let original=probe(&w,&t,1);
        let mut swapped=t.clone();for i in 0..16{swapped.swap(i,i+16);}assert_ne!(probe(&w,&swapped,1),original);negatives+=1;
        let mut omitted=t.clone();omitted.remove(1);assert_ne!(probe(&w,&omitted,1),original);negatives+=1;
        let mut duplicate=t.clone();duplicate.insert(1,t[1]);assert_ne!(probe(&w,&duplicate,2),probe(&w,&t,2));negatives+=1;
        let mut recurrence=t.clone();recurrence[3]=(G1Projective::from(t[3])+setup.prover.g1_vec[0].0).into_affine();
        assert_ne!(probe(&w,&recurrence,3),probe(&w,&t,3));assert_eq!(probe(&w,&recurrence,0),probe(&w,&t,0));negatives+=1;
        let mut offset=w.clone();offset[0].table_offset=16;assert_ne!(probe(&offset,&t,1),original);negatives+=1;
        let mut start=w.clone();start[0].start=4;assert_ne!(probe(&start,&t,1),original);negatives+=1;
        let mut width=w.clone();width[0].width=3;assert_ne!(probe(&width,&t,8),probe(&w,&t,8));negatives+=1;
        for limit in [0,15,17,32784]{assert!(commit_subset_table_chunked(&setup,8,limit).is_err());negatives+=1;}
        assert!(commit_subset_table_chunked(&setup,9,16).is_err());negatives+=1;
        assert!(reserved_subset_vec::<G1Projective>(usize::MAX).is_err());negatives+=1;
        let invalid_dimension_path=std::env::temp_dir().join("nipopow-invalid-dimension-never-created.bits");
        assert!(PackedFileWriter::create_new(&invalid_dimension_path,25).is_err());negatives+=1;
        assert!(PackedFile::open(&invalid_dimension_path,25).is_err());negatives+=1;
        assert_eq!((math,negatives),(40,16));(math,negatives)
    }

    #[test]
    #[ignore]
    fn pcs_construction_matches_original_and_archived_consumer(){
        let started=Instant::now();let evidence=PathBuf::from(std::env::var_os("NIPOPOW_PCS_CONSTRUCTION_EVIDENCE").expect("bound construction evidence"));
        assert!(crate::preview_test_paths::absolute_outside_source(&evidence));regular(&evidence,true);assert!(std::fs::read_dir(&evidence).unwrap().next().is_none());
        let golden=PathBuf::from(std::env::var_os("NIPOPOW_PCS_CONSTRUCTION_GOLDEN").expect("bound original evidence"));
        assert!(crate::preview_test_paths::absolute_outside_source(&golden));regular(&golden,true);
        let controls_started=Instant::now();let(setup_math,setup_negatives,tiny_proofs)=pcs::construction_setup_controls();
        let(table_math,table_negatives)=table_controls();let controls_seconds=controls_started.elapsed().as_secs_f64();
        let setup_started=Instant::now();let(setup,setup_stats,setup22_math)=pcs::construction_setup22();
        let key_bytes=include_bytes!("../fixtures/verifier-keys-v1/log22.vk");let key=crate::verifier_key::admit(22,key_bytes).unwrap();assert_eq!(key.id(),&setup.id);
        let oracle_and_setup22_seconds=setup_started.elapsed().as_secs_f64();
        let fixture_started=Instant::now();regular(&golden.join("witness-main.bits"),false);
        let source=PackedFile::open(golden.join("witness-main.bits"),22).unwrap();let view=source.h2_boolean_view().unwrap();view.require_same_source(&source).unwrap();
        {let mut f=source.file.borrow_mut();let before=f.metadata().unwrap();assert_eq!(before.len(),524288);f.seek(SeekFrom::Start(0)).unwrap();
            let mut bytes=vec![0;524288];f.read_exact(&mut bytes).unwrap();let mut tail=[0;1];assert_eq!(f.read(&mut tail).unwrap(),0);
            let after=f.metadata().unwrap();assert_eq!(before.len(),after.len());assert_eq!(before.modified().unwrap(),after.modified().unwrap());assert_eq!(blake(&bytes),BITS_BLAKE);}
        view.require_same_source(&source).unwrap();let golden_gkr=archived_gkr(&golden);let plan=crate::core_pool::Plan::new(2).unwrap();
        let fixture_seconds=fixture_started.elapsed().as_secs_f64();
        let table_started=Instant::now();let table_stats={let(old_w,old_t)=original_table(&setup,2048);let mut final_stats=None;
            for limit in [16,48,4096,32768]{let(w,t,s)=commit_subset_table_chunked(&setup,2048,limit).unwrap();
                assert_eq!(window_tuples(&w),window_tuples(&old_w));assert_eq!(t,old_t);
                assert_eq!(s.normalization_calls,8192usize.div_ceil(limit));assert_eq!(s.table_capacity,8192);assert_eq!(s.windows_capacity,512);
                final_stats=Some(s);}final_stats.unwrap()};
        let table22_seconds=table_started.elapsed().as_secs_f64();
        source.reset_io_metrics();let commit_started=Instant::now();
        let(old_rows,old_commitment)={let(w,t)=original_table(&setup,2048);let rows=commit_rows_batched(&source,&w,&t,2048,2048).unwrap();
            let commitment=BN254::multi_pair_g2_setup(&rows,&setup.prover.g2_vec[..2048]);(rows,commitment)};
        let committed=commit(&source,&setup).unwrap();assert_eq!(committed.rows,old_rows);assert_eq!(committed.commitment,old_commitment);drop(old_rows);
        let commitment_bytes=pcs::encode_commitment(&committed.commitment).unwrap();let commitment_comparison_seconds=commit_started.elapsed().as_secs_f64();
        let verify_started=Instant::now();let decoded=plan.decode(&golden_gkr).unwrap();let mut producer=ordinary_prefix(&setup,&commitment_bytes);
        let claim=plan.verify(&decoded,&mut producer).unwrap();let mut verifier=producer.clone();
        assert_eq!(source.evaluate(&claim.point).unwrap(),claim.value);view.require_same_source(&source).unwrap();
        let before_ledger=ledger(&producer);let mut p=producer.clone();let mut v=verifier.clone();assert_eq!(p.challenge_scalar(b"before-pcs-continuation"),v.challenge_scalar(b"before-pcs-continuation"));
        let golden_verify_seconds=verify_started.elapsed().as_secs_f64();
        let open_started=Instant::now();let opening=open(&committed,&source,&claim.point,&setup,&mut producer).unwrap();
        let opening_bytes=pcs::encode_proof(&opening).unwrap();assert_eq!(opening_bytes.len(),29421);assert!(opening_bytes.capacity()<=65536);
        let decoded_opening=pcs::decode_proof(&opening_bytes,22).unwrap();let opening_seconds=open_started.elapsed().as_secs_f64();
        let pcs_started=Instant::now();pcs::verify_admitted(committed.commitment,claim.value,&claim.point,&decoded_opening,&key,&mut verifier).unwrap();
        assert_eq!(ledger(&producer),ledger(&verifier));let mut p=producer.clone();let mut v=verifier.clone();assert_eq!(p.challenge_scalar(b"after-pcs-continuation"),v.challenge_scalar(b"after-pcs-continuation"));
        view.require_same_source(&source).unwrap();let pcs_seconds=pcs_started.elapsed().as_secs_f64();
        let mut consumer_negatives=0;
        let mut wrong_value=ordinary_prefix(&setup,&commitment_bytes);plan.verify(&decoded,&mut wrong_value).unwrap();
        assert!(pcs::verify_admitted(committed.commitment,claim.value+Fr::one(),&claim.point,&decoded_opening,&key,&mut wrong_value).is_err());consumer_negatives+=1;
        let mut wrong_point=claim.point.clone();wrong_point[20]+=Fr::one();let mut t=ordinary_prefix(&setup,&commitment_bytes);plan.verify(&decoded,&mut t).unwrap();
        assert!(pcs::verify_admitted(committed.commitment,claim.value,&wrong_point,&decoded_opening,&key,&mut t).is_err());consumer_negatives+=1;
        let mut drift=ordinary_prefix(&setup,&commitment_bytes);plan.verify(&decoded,&mut drift).unwrap();drift.append_bytes(b"pcs-continuation-drift",b"one-fault");
        assert!(pcs::verify_admitted(committed.commitment,claim.value,&claim.point,&decoded_opening,&key,&mut drift).is_err());consumer_negatives+=1;
        assert_eq!((setup_math,setup_negatives,tiny_proofs,table_math,table_negatives,setup22_math,consumer_negatives),(34,22,5,40,16,9,3));
        let io=source.io_metrics_snapshot();let setup_report=json!({"g1_capacity":setup_stats.g1_capacity,"g2_capacity":setup_stats.g2_capacity,
            "seen1_capacity":setup_stats.seen1_capacity,"seen2_capacity":setup_stats.seen2_capacity,"compressed_point_capacity_bytes":setup_stats.compressed_point_capacity_bytes,
            "prover_serialized_bytes":setup_stats.prover_serialized_bytes,"verifier_serialized_bytes":setup_stats.verifier_serialized_bytes});
        let table_report=json!({"windows_capacity":table_stats.windows_capacity,"table_capacity":table_stats.table_capacity,"projective_capacity":table_stats.projective_capacity,
            "affine_chunk_capacity_max":table_stats.affine_chunk_capacity_max,"normalization_calls":table_stats.normalization_calls,"library_scratch_capacity_closed":false});
        let controls=json!({"setup_math":setup_math,"setup_negatives":setup_negatives,"tiny_proofs":tiny_proofs,"table_math":table_math,
            "table_negatives":table_negatives,"setup22_math":setup22_math,"consumer_negatives":consumer_negatives,"table22_cases":4});
        let mut report=json!({"schema":"private-pcs-construction-log22-v1","scope":"same-algorithm admitted PCS22 construction and archived GKR consumer",
            "input_log":22,"key_bytes":key_bytes.len(),"dory_bytes":opening_bytes.len(),"witness_blake2b512":BITS_BLAKE,"gkr_blake2b512":GKR_BLAKE,
            "setup_id":setup.id.iter().map(|b|format!("{b:02x}")).collect::<String>(),"setup":setup_report,"table":table_report,"controls":controls,
            "source_read_calls":io.read_calls,"source_read_bytes":io.read_bytes,"before_pcs_ledger":[before_ledger.0,before_ledger.1,before_ledger.2],
            "after_pcs_ledger":[producer.challenges(),producer.raw_queries(),producer.bytes_absorbed()]});
        let timing=json!({"controls_seconds":controls_seconds,"oracle_and_setup22_seconds":oracle_and_setup22_seconds,"fixture_seconds":fixture_seconds,
            "table22_seconds":table22_seconds,"commitment_comparison_seconds":commitment_comparison_seconds,"golden_verify_seconds":golden_verify_seconds,
            "opening_seconds":opening_seconds,"pcs_seconds":pcs_seconds,"total_before_report_seconds":started.elapsed().as_secs_f64(),
            "gkr_proof_created":false,"pcs_proof_created":true,"setup_invoked":true,"global_admission":false,"same_source_pcs_verified":true,"continuation_equal":true});
        let serde_json::Value::Object(tail)=timing else{unreachable!()};for(k,v)in tail{assert!(report.as_object_mut().unwrap().insert(k,v).is_none());}
        let summary=serde_json::to_vec(&report).unwrap();assert!(summary.len()<=16384&&summary.capacity()<=32768);
        for(name,bytes)in [("log22.vk",key_bytes.as_slice()),("core-pool.dory",opening_bytes.as_slice()),("construction-summary.json",summary.as_slice())]{
            let mut f=OpenOptions::new().write(true).create_new(true).open(evidence.join(name)).unwrap();f.write_all(bytes).unwrap();f.sync_all().unwrap();}
        println!("\npcs_construction_log22 {}",std::str::from_utf8(&summary).unwrap());
    }
}

fn commit_subset_row(windows:&[CommitWindow],table:&[ark_bn254::G1Affine],bytes:&[u8],offset:usize)->ArkG1{
    let mut result=G1Projective::zero();
    for window in windows{
        let position=offset+window.start;
        let mask=if position%COMMIT_WINDOW==0{
            ((bytes[position/8]>>(position%8)) as usize)&((1usize<<window.width)-1)
        }else{
            let mut mask=0usize;
            for bit in 0..window.width{
                let position=offset+window.start+bit;
                if (bytes[position/8]>>(position%8))&1!=0{mask|=1<<bit;}
            }
            mask
        };
        if mask!=0{result+=table[window.table_offset+mask];}
    }
    ArkG1(result)
}

fn commit_rows_batched_with_limit(source:&PackedFile,windows:&[CommitWindow],table:&[ark_bn254::G1Affine],
                                  width:usize,row_count:usize,max_batch_bytes:usize)->Result<Vec<ArkG1>,String>{
    if max_batch_bytes==0{return Err("packed commit batch budget is zero".into());}
    if width<8 {
        let mut rows=Vec::with_capacity(row_count);
        source.scan_rows(width,|_,bytes,offset|{
            rows.push(commit_subset_row(windows,table,bytes,offset));Ok(())
        })?;
        return Ok(rows);
    }
    let row_bytes=width/8;
    if row_bytes>max_batch_bytes{return Err("packed commit row exceeds read batch budget".into());}
    let rows_per_batch=(max_batch_bytes/row_bytes).min(row_count);
    let batch_bytes=rows_per_batch.checked_mul(row_bytes).ok_or("packed commit batch size overflow")?;
    let mut rows=Vec::with_capacity(row_count);
    let mut bytes=vec![0u8;batch_bytes];
    let mut file=source.file.borrow_mut();
    file.seek(SeekFrom::Start(0)).map_err(|e|format!("packed seek: {e}"))?;
    let mut remaining=row_count;
        while remaining>0 {
            let batch_rows=remaining.min(rows_per_batch);
            let active_bytes=batch_rows.checked_mul(row_bytes).ok_or("packed commit batch size overflow")?;
            #[cfg(test)] let read_started=Instant::now();
            let read_result=file.read_exact(&mut bytes[..active_bytes]);
            #[cfg(test)] record_read(&source.io_metrics,active_bytes,&read_result,read_started);
            read_result.map_err(|e|format!("packed read: {e}"))?;
        let committed:Vec<ArkG1>=bytes[..active_bytes].par_chunks_exact(row_bytes)
            .map(|row|commit_subset_row(windows,table,row,0)).collect();
        if committed.len()!=batch_rows{return Err("packed commitment batch row count mismatch".into());}
        rows.extend(committed);
        remaining-=batch_rows;
    }
    Ok(rows)
}

fn commit_rows_batched(source:&PackedFile,windows:&[CommitWindow],table:&[ark_bn254::G1Affine],
                       width:usize,row_count:usize)->Result<Vec<ArkG1>,String>{
    commit_rows_batched_with_limit(source,windows,table,width,row_count,MAX_COMMIT_READ_BATCH_BYTES)
}

pub struct PackedFile {
    file: RefCell<File>,
    log_n: usize,
    #[cfg(test)]
    io_metrics:SharedPackedIo,
}

/// Test-only h0 source for the OLD sixteen-bank Boolean producer. Construction
/// and reads use the original locked handle, never a reopened pathname.
#[cfg(test)]
pub(crate) struct PackedOwnerView<'a> {
    source: &'a PackedFile,
}

#[cfg(test)]
pub(crate) struct PackedOwnerBits {
    bytes: Vec<u8>,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum PackedReaderFault {
    Short,
    ShortByOneByte,
    Io,
}

#[cfg(test)]
impl PackedOwnerBits {
    pub(crate) fn into_bytes(self) -> Vec<u8> { self.bytes }
    pub(crate) fn len(&self) -> usize { self.bytes.len() * 8 }
    pub(crate) fn capacity_bytes(&self) -> usize { self.bytes.capacity() }
    pub(crate) fn bit_at(&self, index: usize) -> bool {
        self.bytes[index / 8] >> (index % 8) & 1 != 0
    }
    pub(crate) fn matches_bytes(&self, expected: &[u8]) -> bool {
        self.bytes.as_slice() == expected
    }
    pub(crate) fn bit(&self, bank: usize, local: usize) -> Result<bool, String> {
        if bank >= 16 || local >= 65536 { return Err("packed Boolean bit range".into()); }
        let index = bank.checked_mul(65536).and_then(|x| x.checked_add(local))
            .ok_or("packed Boolean bit overflow")?;
        Ok(self.bit_at(index))
    }
}

#[cfg(test)]
impl PackedFile {
    pub(crate) fn h0_boolean_view(&self) -> Result<PackedOwnerView<'_>, String> {
        if self.log_n != 22 || self.input_len() != 1usize << 22 {
            return Err("packed Boolean source requires exact TEST22 extent".into());
        }
        Ok(PackedOwnerView { source: self })
    }
}

#[cfg(test)]
impl PackedOwnerView<'_> {
    pub(crate) fn require_same_source(&self, source: &PackedFile) -> Result<(), String> {
        if !std::ptr::eq(self.source, source) {
            return Err("packed Boolean detached source".into());
        }
        Ok(())
    }

    /// Compare all four PCS owners AFTER writer.finish/open has acquired the
    /// immutable lock. This closes the fixture's writer-close/reopen gap.
    pub(crate) fn check_expected(&self, expected: &[u8]) -> Result<(), String> {
        if expected.len() != 524288 { return Err("packed Boolean snapshot extent".into()); }
        let mut bytes = vec![0u8; 131072];
        if bytes.capacity() > 131072 { return Err("packed Boolean snapshot capacity".into()); }
        let mut file = self.source.file.borrow_mut();
        file.seek(SeekFrom::Start(0)).map_err(|e| format!("packed Boolean snapshot seek: {e}"))?;
        for chunk in expected.chunks_exact(131072) {
            let started = Instant::now();
            let result = file.read_exact(&mut bytes);
            record_read(&self.source.io_metrics, bytes.len(), &result, started);
            result.map_err(|e| format!("packed Boolean snapshot read: {e}"))?;
            if bytes.as_slice() != chunk { return Err("packed Boolean snapshot mismatch".into()); }
        }
        Ok(())
    }

    pub(crate) fn read_copy(&self, copy: usize) -> Result<PackedOwnerBits, String> {
        self.read_owner(copy, None)
    }

    /// Fault injection is confined to the Read boundary AFTER a genuine view
    /// has been admitted. No external reader/bytes enter the proof factory.
    pub(crate) fn reader_fault_for_test(&self, fault: PackedReaderFault) -> Result<PackedOwnerBits, String> {
        self.read_owner(0, Some(fault))
    }

    fn read_owner(&self, copy: usize, fault: Option<PackedReaderFault>) -> Result<PackedOwnerBits, String> {
        if copy != 0 { return Err("packed Boolean logical owner range".into()); }
        let mut bytes = vec![0u8; 131072];
        if bytes.capacity() > 131072 { return Err("packed Boolean owner capacity".into()); }
        let mut file = self.source.file.borrow_mut();
        file.seek(SeekFrom::Start(0)).map_err(|e| format!("packed Boolean owner seek: {e}"))?;
        struct Reader<'a> { file: &'a mut File, fault: Option<PackedReaderFault> }
        impl Read for Reader<'_> {
            fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
                match self.fault {
                    Some(PackedReaderFault::Short) => Ok(0),
                    Some(PackedReaderFault::ShortByOneByte) => Err(std::io::Error::other("one-byte-short packed reader fault")),
                    Some(PackedReaderFault::Io) => Err(std::io::Error::other("isolated packed reader fault")),
                    None => self.file.read(out),
                }
            }
        }
        let started = Instant::now();
        let result = Reader { file: &mut file, fault }.read_exact(&mut bytes);
        record_read(&self.source.io_metrics, bytes.len(), &result, started);
        result.map_err(|e| format!("packed Boolean owner read: {e}"))?;
        Ok(PackedOwnerBits { bytes })
    }
}

/// Separate TEST22 factory: every physical owner is a logical OLD owner.
#[cfg(test)]
pub(crate) struct PackedFourOwnerView<'a> {
    source: &'a PackedFile,
}

#[cfg(test)]
impl PackedFile {
    pub(crate) fn h2_boolean_view(&self) -> Result<PackedFourOwnerView<'_>, String> {
        if self.log_n != 22 || self.input_len() != 1usize << 22 {
            return Err("packed four-owner source requires exact TEST22 extent".into());
        }
        Ok(PackedFourOwnerView { source: self })
    }
}

#[cfg(test)]
impl PackedFourOwnerView<'_> {
    pub(crate) fn require_same_source(&self, source: &PackedFile) -> Result<(), String> {
        if !std::ptr::eq(self.source, source) {
            return Err("packed four-owner detached source".into());
        }
        Ok(())
    }

    pub(crate) fn check_expected(&self, expected: &[u8]) -> Result<(), String> {
        // The unchanged h0 snapshot checker covers the entire TEST22 file.
        PackedOwnerView { source: self.source }.check_expected(expected)
    }

    pub(crate) fn read_copy(&self, owner: usize) -> Result<PackedOwnerBits, String> {
        self.read_owner(owner, None)
    }

    pub(crate) fn reader_fault_for_test(&self, owner: usize, fault: PackedReaderFault) -> Result<PackedOwnerBits, String> {
        self.read_owner(owner, Some(fault))
    }

    fn read_owner(&self, owner: usize, fault: Option<PackedReaderFault>) -> Result<PackedOwnerBits, String> {
        if owner >= 4 { return Err("packed four-owner logical range".into()); }
        let offset = owner.checked_mul(131072).ok_or("packed four-owner offset overflow")?;
        let end = offset.checked_add(131072).ok_or("packed four-owner end overflow")?;
        if end > 524288 { return Err("packed four-owner source extent".into()); }
        let mut bytes = vec![0u8; 131072];
        if bytes.capacity() > 131072 { return Err("packed four-owner capacity".into()); }
        let mut file = self.source.file.borrow_mut();
        file.seek(SeekFrom::Start(u64::try_from(offset).map_err(|_| "packed four-owner seek overflow")?))
            .map_err(|e| format!("packed four-owner seek: {e}"))?;
        struct Reader<'a> { file: &'a mut File, fault: Option<PackedReaderFault> }
        impl Read for Reader<'_> {
            fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
                match self.fault {
                    Some(PackedReaderFault::Short) => Ok(0),
                    Some(PackedReaderFault::ShortByOneByte) => Err(std::io::Error::other("one-byte-short packed four-owner reader fault")),
                    Some(PackedReaderFault::Io) => Err(std::io::Error::other("isolated packed four-owner reader fault")),
                    None => self.file.read(out),
                }
            }
        }
        let started = Instant::now();
        let result = Reader { file: &mut file, fault }.read_exact(&mut bytes);
        record_read(&self.source.io_metrics, bytes.len(), &result, started);
        result.map_err(|e| format!("packed four-owner read: {e}"))?;
        Ok(PackedOwnerBits { bytes })
    }
}

/// Test-only log32 owner windows over the same immutably locked packed source.
#[cfg(test)]
pub(crate) struct PackedNativeRole0View<'a> {
    source: &'a PackedFile,
}

#[cfg(test)]
impl PackedFile {
    pub(crate) fn native_role0_view(&self) -> Result<PackedNativeRole0View<'_>, String> {
        if self.log_n != 32 || self.input_len() != 1usize << 32 {
            return Err("native role0 source requires exact log32 extent".into());
        }
        Ok(PackedNativeRole0View { source: self })
    }
}

#[cfg(test)]
impl PackedNativeRole0View<'_> {
    pub(crate) fn require_same_source(&self, source: &PackedFile) -> Result<(), String> {
        if !std::ptr::eq(self.source, source) {
            return Err("native role0 detached packed source".into());
        }
        Ok(())
    }

    pub(crate) fn read_copy(&self, owner: usize) -> Result<PackedOwnerBits, String> {
        self.read_owner(owner, None)
    }

    pub(crate) fn reader_fault_for_test(
        &self, owner: usize, fault: PackedReaderFault,
    ) -> Result<PackedOwnerBits, String> {
        self.read_owner(owner, Some(fault))
    }

    fn read_owner(
        &self, owner: usize, fault: Option<PackedReaderFault>,
    ) -> Result<PackedOwnerBits, String> {
        const OWNER_COUNT: usize = 4096;
        const OWNER_BYTES: usize = 131072;
        if owner >= OWNER_COUNT { return Err("native role0 owner range".into()); }
        if self.source.log_n != 32 || self.source.input_len() != 1usize << 32 {
            return Err("native role0 source geometry changed".into());
        }
        let offset = owner.checked_mul(OWNER_BYTES).ok_or("native role0 offset overflow")?;
        let end = offset.checked_add(OWNER_BYTES).ok_or("native role0 end overflow")?;
        if end > 1usize << 29 { return Err("native role0 source byte extent".into()); }
        let mut bytes = vec![0u8; OWNER_BYTES];
        if bytes.capacity() != OWNER_BYTES { return Err("native role0 owner capacity".into()); }
        let mut file = self.source.file.borrow_mut();
        file.seek(SeekFrom::Start(u64::try_from(offset).map_err(|_| "native role0 seek overflow")?))
            .map_err(|e| format!("native role0 seek: {e}"))?;
        struct Reader<'a> { file: &'a mut File, fault: Option<PackedReaderFault>, short_remaining: usize }
        impl Read for Reader<'_> {
            fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
                match self.fault {
                    Some(PackedReaderFault::Short) => Ok(0),
                    Some(PackedReaderFault::ShortByOneByte) if self.short_remaining > 0 => {
                        let limit = out.len().min(self.short_remaining);
                        let read = self.file.read(&mut out[..limit])?;
                        self.short_remaining -= read;
                        Ok(read)
                    }
                    Some(PackedReaderFault::ShortByOneByte) => Ok(0),
                    Some(PackedReaderFault::Io) => Err(std::io::Error::other("isolated native role0 reader fault")),
                    None => self.file.read(out),
                }
            }
        }
        let started = Instant::now();
        let result = Reader { file: &mut file, fault, short_remaining: OWNER_BYTES - 1 }.read_exact(&mut bytes);
        record_read(&self.source.io_metrics, bytes.len(), &result, started);
        result.map_err(|e| format!("native role0 owner read: {e}"))?;
        Ok(PackedOwnerBits { bytes })
    }
}

/// Bounded, create-once writer for the canonical LSB-first witness file read by `PackedFile`.
pub struct PackedFileWriter {
    file: Option<File>,
    path: PathBuf,
    log_n: usize,
    expected_bytes: usize,
    written_bytes: usize,
    last_byte: u8,
    keep_file: bool,
    #[cfg(test)]
    io_metrics:SharedPackedIo,
}

impl PackedFileWriter {
    pub fn create_new(path: impl AsRef<Path>, log_n: usize) -> Result<Self,String> {
        if log_n>pcs::MAX_LOG_N {return Err("packed dimension exceeds prototype bound".into());}
        let bits=1usize.checked_shl(log_n as u32).ok_or("packed dimension overflow")?;
        let expected_bytes=bits.div_ceil(8);
        let path=path.as_ref().to_path_buf();
        let file=OpenOptions::new().write(true).create_new(true).open(&path)
            .map_err(|e|format!("packed create: {e}"))?;
        Ok(Self {file:Some(file),path,log_n,expected_bytes,written_bytes:0,last_byte:0,keep_file:false,
            #[cfg(test)] io_metrics:Arc::new(Mutex::new(PackedIoSnapshot::default()))})
    }

    /// Appends byte-aligned chunks without allowing the declared packed size to be exceeded.
    pub fn write_bytes(&mut self,bytes:&[u8])->Result<(),String> {
        let next=self.written_bytes.checked_add(bytes.len()).ok_or("packed byte count overflow")?;
        if next>self.expected_bytes {return Err("packed writer exceeds declared dimension".into());}
        let file=self.file.as_mut().ok_or("packed writer already finished")?;
        #[cfg(test)] let write_started=Instant::now();
        let write_result=file.write_all(bytes);
        #[cfg(test)] record_write(&self.io_metrics,bytes.len(),&write_result,write_started);
        if let Err(error)=write_result {
            self.file.take();
            return Err(format!("packed write: {error}"));
        }
        if let Some(last)=bytes.last(){self.last_byte=*last;}
        self.written_bytes=next;
        Ok(())
    }

    /// Syncs and reopens the exact-size canonical output under the immutable reader lock.
    pub fn finish(mut self)->Result<PackedFile,String> {
        if self.written_bytes!=self.expected_bytes {
            return Err(format!("packed writer length mismatch: expected {}, got {}",self.expected_bytes,self.written_bytes));
        }
        let tail_bits=(1usize<<self.log_n)%8;
        let allowed_tail_mask=(1u16<<tail_bits)-1;
        if tail_bits!=0 && ((self.last_byte as u16)&!allowed_tail_mask)!=0 {
            return Err("packed writer has noncanonical tail bits".into());
        }
        let file=self.file.take().ok_or("packed writer already finished")?;
        #[cfg(test)] let sync_started=Instant::now();
        let sync_result=file.sync_all();
        #[cfg(test)] record_sync(&self.io_metrics,&sync_result,sync_started);
        sync_result.map_err(|e|format!("packed sync: {e}"))?;
        drop(file);
        let mut source=PackedFile::open(&self.path,self.log_n)?;
        #[cfg(test)] {
            let opened=source.io_metrics_snapshot();
            let mut stats=self.io_metrics.lock().unwrap_or_else(|error|error.into_inner());
            stats.read_calls=stats.read_calls.saturating_add(opened.read_calls);
            stats.read_bytes=stats.read_bytes.saturating_add(opened.read_bytes);
            stats.read_ns=stats.read_ns.saturating_add(opened.read_ns);
            source.io_metrics=Arc::clone(&self.io_metrics);
        }
        self.keep_file=true;
        Ok(source)
    }
}

impl Drop for PackedFileWriter {
    fn drop(&mut self) {
        if !self.keep_file {
            self.file.take();
            let _=std::fs::remove_file(&self.path);
        }
    }
}

// Separate H21 diagnostic writer. Ordinary writer/setup admission stays at
// MAX_LOG_N. Failed and unfinished outputs are retained for project cleanup.
#[cfg(test)]
const H21_OWNER_BYTES:usize=1<<17;
#[cfg(test)]
const H21_OWNERS:usize=1<<21;
#[cfg(test)]
struct H21OwnerCursor { expected:usize,next:usize,bytes:u64 }
#[cfg(test)]
impl H21OwnerCursor {
    fn check(&self,owner:usize,len:usize)->Result<(),String> {
        if owner!=self.next || owner>=self.expected || len!=H21_OWNER_BYTES {
            return Err("H21 packed owner order/extent".into());
        }
        Ok(())
    }
    fn complete(&self)->Result<u64,String> {
        let expected=(self.expected as u64).checked_mul(H21_OWNER_BYTES as u64)
            .ok_or("H21 packed extent overflow")?;
        if self.next!=self.expected || self.bytes!=expected {
            return Err("H21 packed incomplete owner census".into());
        }
        Ok(expected)
    }
}

#[cfg(test)]
pub(crate) struct H21PackedWriter {
    file:Option<File>,path:PathBuf,cursor:H21OwnerCursor,
    hash:Blake2b512,full:bool,poisoned:bool,
}
#[cfg(test)]
pub(crate) struct H21PackedFragment {
    _file:File,owners:usize,bytes:u64,digest:[u8;64],
}
#[cfg(test)]
impl H21PackedFragment {
    pub(crate) fn owners(&self)->usize {self.owners}
    pub(crate) fn bytes(&self)->u64 {self.bytes}
    pub(crate) fn digest(&self)->[u8;64] {self.digest}
}

#[cfg(test)]
fn verify_h21_file(file:&mut File,expected:u64,digest:[u8;64])->Result<(),String> {
    if file.metadata().map_err(|e|e.to_string())?.len()!=expected {
        return Err("H21 packed readback extent".into());
    }
    file.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;
    let mut hash=Blake2b512::new();let mut left=expected;let mut buffer=[0u8;32768];
    while left!=0 {
        let take=usize::try_from(left.min(buffer.len()as u64)).map_err(|_|"H21 readback chunk")?;
        file.read_exact(&mut buffer[..take]).map_err(|e|format!("H21 readback: {e}"))?;
        hash.update(&buffer[..take]);left-=take as u64;
    }
    let mut extra=[0u8;1];
    if file.read(&mut extra).map_err(|e|e.to_string())?!=0
        || file.metadata().map_err(|e|e.to_string())?.len()!=expected
        || hash.finalize().as_slice()!=&digest[..] {
        return Err("H21 packed readback digest/EOF".into());
    }
    file.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;Ok(())
}

#[cfg(test)]
impl H21PackedWriter {
    pub(crate) fn prefix(path:&Path,owners_log:usize)->Result<Self,String> {
        if owners_log>4 {return Err("H21 fragment owner log must be 0..4".into());}
        Self::create(path,1usize<<owners_log,false)
    }
    pub(crate) fn all(path:&Path)->Result<Self,String> {Self::create(path,H21_OWNERS,true)}
    fn create(path:&Path,expected:usize,full:bool)->Result<Self,String> {
        if !crate::preview_test_paths::absolute_outside_source(path) {
            return Err("H21 packed output must be absolute and outside source".into());
        }
        #[cfg(not(windows))]
        return Err("H21 packed custody requires Windows".into());
        #[cfg(windows)]
        {
            use std::os::windows::fs::OpenOptionsExt;
            let file=OpenOptions::new().write(true).create_new(true).share_mode(1)
                .open(path).map_err(|e|format!("H21 packed create: {e}"))?;
            Ok(Self {file:Some(file),path:path.to_path_buf(),
                cursor:H21OwnerCursor {expected,next:0,bytes:0},hash:Blake2b512::new(),full,poisoned:false})
        }
    }
    pub(crate) fn write_owner(&mut self,owner:usize,bytes:&[u8])->Result<(),String> {
        if self.poisoned {return Err("H21 packed writer poisoned".into());}
        if let Err(e)=self.cursor.check(owner,bytes.len()) {self.poisoned=true;return Err(e);}
        let result=self.file.as_mut().ok_or("H21 packed writer closed")?.write_all(bytes);
        if let Err(e)=result {self.poisoned=true;return Err(format!("H21 packed write: {e}"));}
        self.hash.update(bytes);self.cursor.next+=1;self.cursor.bytes+=bytes.len()as u64;Ok(())
    }
    fn close(mut self)->Result<(PathBuf,usize,u64,[u8;64]),String> {
        if self.poisoned {return Err("H21 packed writer poisoned".into());}
        let bytes=self.cursor.complete()?;
        let file=self.file.take().ok_or("H21 packed writer closed")?;
        if file.metadata().map_err(|e|e.to_string())?.len()!=bytes {return Err("H21 packed writer file extent".into());}
        file.sync_all().map_err(|e|format!("H21 packed sync: {e}"))?;
        drop(file);Ok((self.path,self.cursor.expected,bytes,self.hash.finalize().into()))
    }
    pub(crate) fn finish_fragment(self)->Result<H21PackedFragment,String> {
        if self.full || self.cursor.expected>16 {return Err("H21 complete writer cannot finish as fragment".into());}
        let(path,owners,bytes,digest)=self.close()?;
        #[cfg(not(windows))]
        return Err("H21 packed custody requires Windows".into());
        #[cfg(windows)]
        {
            use std::os::windows::fs::OpenOptionsExt;
            let mut file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|e|e.to_string())?;
            verify_h21_file(&mut file,bytes,digest)?;
            Ok(H21PackedFragment {_file:file,owners,bytes,digest})
        }
    }
    pub(crate) fn finish_all(self)->Result<(PackedFile,[u8;64]),String> {
        if !self.full || self.cursor.expected!=H21_OWNERS {return Err("H21 fragment cannot finish as complete source".into());}
        let(path,owners,bytes,digest)=self.close()?;
        if owners!=H21_OWNERS || bytes!=256u64*1024*1024*1024 {return Err("H21 complete extent".into());}
        let source=PackedFile::open_admitted(&path,41,41)?;
        verify_h21_file(&mut source.file.borrow_mut(),bytes,digest)?;
        Ok((source,digest))
    }
}

#[cfg(test)]
mod h21_packed_writer_tests {
    use super::*;
    fn output(label:&str)->PathBuf {
        // The bounded test launcher supplies a project-local TEMP/TMP. Keep
        // these exact outputs, including failures, for its storage receipt.
        let tick=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        std::env::temp_dir().join(format!("c588-sink-{label}-{}-{tick}.bits",std::process::id()))
    }
    #[test]
    fn c588_sink_owner_cursor_census_boundaries_without_full_file() {
        let mut cursor=H21OwnerCursor {expected:H21_OWNERS,next:0,bytes:0};
        assert!(cursor.complete().is_err());
        assert!(cursor.check(1,H21_OWNER_BYTES).is_err());
        assert!(cursor.check(0,H21_OWNER_BYTES-1).is_err());
        assert!(cursor.check(0,H21_OWNER_BYTES+1).is_err());
        cursor.next=H21_OWNERS;cursor.bytes=256u64*1024*1024*1024;
        assert_eq!(cursor.complete().unwrap(),256u64*1024*1024*1024);
        assert!(cursor.check(H21_OWNERS,H21_OWNER_BYTES).is_err());
        cursor.bytes-=1;assert!(cursor.complete().is_err());
        // Arithmetic-only counters issue no file, writer or native Source.
        assert_eq!(pcs::MAX_LOG_N,24);
    }
    #[test]
    fn c588_sink_fragment_pairing_digest_and_no_complete_conversion()->Result<(),String> {
        let path=output("pair");let a=vec![0xa5;H21_OWNER_BYTES];let b=vec![0x3c;H21_OWNER_BYTES];
        let mut writer=H21PackedWriter::prefix(&path,1)?;
        writer.write_owner(0,&a)?;writer.write_owner(1,&b)?;
        let fragment=writer.finish_fragment()?;
        let bytes=std::fs::read(&path).map_err(|e|e.to_string())?;
        assert_eq!(bytes.len(),1<<18);assert_eq!(&bytes[..H21_OWNER_BYTES],a);
        assert_eq!(&bytes[H21_OWNER_BYTES..],b);
        assert_eq!((fragment.owners(),fragment.bytes()),(2,1<<18));
        assert_eq!(fragment.digest().as_slice(),Blake2b512::digest(&bytes).as_slice());
        assert!(OpenOptions::new().write(true).open(&path).is_err());
        assert!(PackedFile::open(&path,41).is_err());
        let path=output("cannot-promote");let mut writer=H21PackedWriter::prefix(&path,0)?;
        writer.write_owner(0,&a)?;assert!(writer.finish_all().is_err());
        assert_eq!(std::fs::metadata(path).map_err(|e|e.to_string())?.len(),H21_OWNER_BYTES as u64);
        Ok(())
    }
    #[test]
    fn c588_sink_order_short_extra_and_incomplete_refusals_retain_outputs()->Result<(),String> {
        let row=vec![0u8;H21_OWNER_BYTES];
        for fault in 0..4 {
            let path=output(&format!("fault{fault}"));let mut writer=H21PackedWriter::prefix(&path,0)?;
            let result=match fault {
                0=>writer.write_owner(1,&row),
                1=>writer.write_owner(0,&row[..row.len()-1]),
                2=>writer.write_owner(0,&vec![0;row.len()+1]),
                _=>{writer.write_owner(0,&row)?;writer.write_owner(0,&row)},
            };
            assert!(result.is_err());assert!(writer.write_owner(0,&row).is_err());
            assert!(writer.finish_fragment().is_err());assert!(path.is_file());
        }
        let path=output("incomplete");let writer=H21PackedWriter::prefix(&path,1)?;
        assert!(writer.finish_fragment().is_err());assert!(path.is_file());
        let path=output("full-incomplete");let mut writer=H21PackedWriter::all(&path)?;
        writer.write_owner(0,&row)?;assert!(writer.finish_all().is_err());assert!(path.is_file());
        let path=output("log5");assert!(H21PackedWriter::prefix(&path,5).is_err());assert!(!path.exists());
        Ok(())
    }
    #[test]
    fn c588_sink_readback_detects_digest_truncation_and_trailing_bytes()->Result<(),String> {
        let path=output("readback");let bytes=vec![0x69u8;H21_OWNER_BYTES];
        let digest:[u8;64]=Blake2b512::digest(&bytes).into();
        let mut file=OpenOptions::new().read(true).write(true).create_new(true).open(path).map_err(|e|e.to_string())?;
        file.write_all(&bytes).map_err(|e|e.to_string())?;
        verify_h21_file(&mut file,bytes.len()as u64,digest)?;
        file.write_all(&[0x68]).map_err(|e|e.to_string())?;
        assert!(verify_h21_file(&mut file,bytes.len()as u64,digest).is_err());
        file.set_len(bytes.len()as u64-1).map_err(|e|e.to_string())?;
        assert!(verify_h21_file(&mut file,bytes.len()as u64,digest).is_err());
        file.set_len(bytes.len()as u64+1).map_err(|e|e.to_string())?;
        assert!(verify_h21_file(&mut file,bytes.len()as u64,digest).is_err());Ok(())
    }
}

impl PackedFile {
    pub fn open(path: impl AsRef<Path>, log_n: usize) -> Result<Self, String> {
        Self::open_admitted(path, log_n, pcs::MAX_LOG_N)
    }

    #[cfg(test)]
    pub(crate) fn open_with_limit(path: impl AsRef<Path>, log_n: usize, admitted_max_log_n: usize) -> Result<Self, String> {
        Self::open_admitted(path, log_n, admitted_max_log_n)
    }

    fn open_admitted(path: impl AsRef<Path>, log_n: usize, admitted_max_log_n: usize) -> Result<Self, String> {
        #[cfg(not(windows))]
        {
            let _ = (path, log_n, admitted_max_log_n);
            return Err("packed immutable file lock is only supported on Windows".into());
        }
        #[cfg(windows)]
        {
        if log_n > admitted_max_log_n || log_n >= usize::BITS as usize {
            return Err("packed dimension exceeds admitted bound".into());
        }
        let mut options = OpenOptions::new();
        options.read(true);
        #[cfg(test)] let io_metrics=Arc::new(Mutex::new(PackedIoSnapshot::default()));
        #[cfg(windows)]
        {
            use std::os::windows::fs::OpenOptionsExt;
            options.share_mode(0x00000001); // FILE_SHARE_READ; no write/delete sharing.
        }
        let mut file = options.open(path).map_err(|e| format!("packed open: {e}"))?;
        let bits = 1usize << log_n;
        let bytes = bits.div_ceil(8);
        let observed = file.metadata().map_err(|e| format!("packed metadata: {e}"))?.len();
        if observed != bytes as u64 {
            return Err(format!("packed length mismatch: expected {bytes}, got {observed}"));
        }
        if bits % 8 != 0 {
            let mut last = [0u8; 1];
            file.seek(SeekFrom::Start((bytes - 1) as u64)).map_err(|e| e.to_string())?;
            #[cfg(test)] let read_started=Instant::now();
            let read_result=file.read_exact(&mut last);
            #[cfg(test)] record_read(&io_metrics,last.len(),&read_result,read_started);
            read_result.map_err(|e|e.to_string())?;
            if last[0] >> (bits % 8) != 0 { return Err("noncanonical packed tail bits".into()); }
        }
        Ok(Self { file:RefCell::new(file), log_n,
            #[cfg(test)] io_metrics })
        }
    }

    pub fn input_len(&self) -> usize { 1usize << self.log_n }

    /// Private frontend read: one canonical LSB-first row, without field expansion.
    pub(crate) fn read_row_bits(&self, width: usize, row: usize) -> Result<Vec<u8>, String> {
        if width < 8 || !width.is_power_of_two() || self.input_len() % width != 0
            || row >= self.input_len() / width {
            return Err("packed bit row bounds invalid".into());
        }
        let row_bytes = width / 8;
        let offset = row.checked_mul(row_bytes).ok_or("packed bit row offset overflow")?;
        let mut bytes = vec![0u8; row_bytes];
        let mut file = self.file.try_borrow_mut().map_err(|_| "packed bit row handle already borrowed")?;
        file.seek(SeekFrom::Start(offset as u64)).map_err(|e| format!("packed bit row seek: {e}"))?;
        #[cfg(test)] let started = Instant::now();
        let read = file.read_exact(&mut bytes);
        #[cfg(test)] record_read(&self.io_metrics, bytes.len(), &read, started);
        read.map_err(|e| format!("packed bit row read: {e}"))?;
        Ok(bytes)
    }

    #[cfg(test)]
    pub(crate) fn reset_io_metrics(&self){
        *self.io_metrics.lock().unwrap_or_else(|error|error.into_inner())=PackedIoSnapshot::default();
    }

    #[cfg(test)]
    pub(crate) fn fallback_calls_for_test(&self)->[u64;2]{PACKED_FALLBACK_CALLS.with(|counts|counts.get())}

    #[cfg(test)]
    pub(crate) fn io_metrics_snapshot(&self)->PackedIoSnapshot{
        *self.io_metrics.lock().unwrap_or_else(|error|error.into_inner())
    }

    pub fn evaluate(&self, point: &[Fr]) -> Result<Fr, String> {
        self.evaluation(&point.iter().copied().map(ArkFr).collect::<Vec<_>>())
            .map(|value| value.0)
    }

    /// Read one bounded contiguous logical copy in LSB-first bit order.
    pub fn read_copy(&self, base_len: usize, copy: usize) -> Result<Vec<Fr>, String> {
        #[cfg(test)] {
            PACKED_FALLBACK_CALLS.with(|counter|{let mut counts=counter.get();counts[0]+=1;counter.set(counts);});
        }
        if base_len == 0 || base_len > (1 << 16) || !base_len.is_power_of_two()
            || self.input_len() % base_len != 0 || copy >= self.input_len() / base_len {
            return Err("packed copy bounds invalid".into());
        }
        let first_bit = copy * base_len;
        let first_byte = first_bit / 8;
        let bit_offset = first_bit % 8;
        let byte_count = (bit_offset + base_len).div_ceil(8);
        let mut bytes = vec![0u8; byte_count];
        let mut file = self.file.borrow_mut();
        file.seek(SeekFrom::Start(first_byte as u64)).map_err(|e| format!("packed seek: {e}"))?;
        #[cfg(test)] let read_started=Instant::now();
        let read_result=file.read_exact(&mut bytes);
        #[cfg(test)] record_read(&self.io_metrics,bytes.len(),&read_result,read_started);
        read_result.map_err(|e|format!("packed read: {e}"))?;
        let boolean_fields=[Fr::from(0u64),Fr::from(1u64)];
        Ok((0..base_len).map(|bit| {
            let position = bit_offset + bit;
            boolean_fields[((bytes[position / 8] >> (position % 8)) & 1) as usize]
        }).collect())
    }

    /// Test-only bounded byte readback through this file's existing locked handle.
    /// The caller owns the mapping from local slots to global PCS row indices.
    #[cfg(test)]
    pub(crate) fn read_rows_bytes_with_limit_for_test(
        &self,
        row_len_bits: usize,
        max_total_bytes: usize,
    ) -> Result<Vec<Vec<u8>>, String> {
        const MAX_TEST_READ_BYTES: usize = 16 * 1024 * 1024;
        if max_total_bytes == 0
            || max_total_bytes > MAX_TEST_READ_BYTES
            || row_len_bits != (1 << 21)
            || self.input_len() % row_len_bits != 0
            || self.input_len() / 8 > max_total_bytes
        {
            return Err("bounded test row read shape or budget".into());
        }
        let expected_rows = self.input_len() / row_len_bits;
        if expected_rows == 0 || expected_rows > 64 {
            return Err("bounded test row read count".into());
        }
        let row_bytes = row_len_bits / 8;
        let mut rows = Vec::with_capacity(expected_rows);
        self.scan_rows(row_len_bits, |slot, bytes, bit_offset| {
            if slot != rows.len() || bit_offset != 0 || bytes.len() != row_bytes {
                return Err("bounded test row read order or width".into());
            }
            rows.push(bytes.to_vec());
            Ok(())
        })?;
        if rows.len() != expected_rows {
            return Err("bounded test row read count".into());
        }
        Ok(rows)
    }

    #[cfg(test)]
    pub(crate) fn read_copy_legacy_for_test(&self, base_len: usize, copy: usize) -> Result<Vec<Fr>, String> {
        if base_len == 0 || base_len > (1 << 16) || !base_len.is_power_of_two()
            || self.input_len() % base_len != 0 || copy >= self.input_len() / base_len {
            return Err("packed copy bounds invalid".into());
        }
        let first_bit = copy * base_len;
        let first_byte = first_bit / 8;
        let bit_offset = first_bit % 8;
        let byte_count = (bit_offset + base_len).div_ceil(8);
        let mut bytes = vec![0u8; byte_count];
        let mut file = self.file.borrow_mut();
        file.seek(SeekFrom::Start(first_byte as u64)).map_err(|e| format!("packed seek: {e}"))?;
        #[cfg(test)] let read_started=Instant::now();
        let read_result=file.read_exact(&mut bytes);
        #[cfg(test)] record_read(&self.io_metrics,bytes.len(),&read_result,read_started);
        read_result.map_err(|e|format!("packed read: {e}"))?;
        Ok((0..base_len).map(|bit| {
            let position = bit_offset + bit;
            Fr::from(((bytes[position / 8] >> (position % 8)) & 1) as u64)
        }).collect())
    }

    fn scan_rows<F>(&self, row_len: usize, mut consume: F) -> Result<(), String>
    where F: FnMut(usize, &[u8], usize) -> Result<(), String> {
        if row_len == 0 || !row_len.is_power_of_two() || self.input_len() % row_len != 0 {
            return Err("packed row shape invalid".into());
        }
        let row_count = self.input_len() / row_len;
        let mut file = self.file.borrow_mut();
        file.seek(SeekFrom::Start(0)).map_err(|e| format!("packed seek: {e}"))?;
        if row_len >= 8 {
            let mut bytes = vec![0u8; row_len / 8];
            for row in 0..row_count {
                #[cfg(test)] let read_started=Instant::now();
                let read_result=file.read_exact(&mut bytes);
                #[cfg(test)] record_read(&self.io_metrics,bytes.len(),&read_result,read_started);
                read_result.map_err(|e|format!("packed read: {e}"))?;
                consume(row, &bytes, 0)?;
            }
        } else {
            let mut byte = [0u8; 1];
            for row in 0..row_count {
                if row * row_len % 8 == 0 {
                    #[cfg(test)] let read_started=Instant::now();
                    let read_result=file.read_exact(&mut byte);
                    #[cfg(test)] record_read(&self.io_metrics,byte.len(),&read_result,read_started);
                    read_result.map_err(|e|format!("packed read: {e}"))?;
                }
                consume(row, &byte, row * row_len % 8)?;
            }
        }
        Ok(())
    }

    fn vector_product(&self, left: &[ArkFr], nu: usize, sigma: usize) -> Result<Vec<ArkFr>, String> {
        #[cfg(test)] {
            PACKED_FALLBACK_CALLS.with(|counter|{let mut counts=counter.get();counts[1]+=1;counter.set(counts);});
        }
        self.vector_product_with_limit(left,nu,sigma,MAX_COMMIT_READ_BATCH_BYTES)
    }

    fn vector_product_with_limit(&self,left:&[ArkFr],nu:usize,sigma:usize,
                                 max_batch_bytes:usize)->Result<Vec<ArkFr>,String>{
        if nu + sigma != self.log_n || left.len() != 1usize << nu {
            return Err("packed vector product shape mismatch".into());
        }
        if max_batch_bytes==0{return Err("packed vector product batch budget is zero".into());}
        let cols = 1usize << sigma;
        let mut result = vec![ArkFr(Fr::zero()); cols];
        if cols<8{
            self.scan_rows(cols, |row, bytes, offset| {
                for col in 0..cols {
                    let bit = offset + col;
                    if ((bytes[bit / 8] >> (bit % 8)) & 1) != 0 {
                        result[col].0 += left[row].0;
                    }
                }
                Ok(())
            })?;
            return Ok(result);
        }
        let row_bytes=cols/8;
        if row_bytes>max_batch_bytes{return Err("packed vector product row exceeds read batch budget".into());}
        let row_count=1usize<<nu;
        let rows_per_batch=(max_batch_bytes/row_bytes).min(row_count);
        let batch_bytes=rows_per_batch.checked_mul(row_bytes).ok_or("packed vector product batch size overflow")?;
        let column_chunks=rayon::current_num_threads().saturating_mul(4).max(1);
        let column_chunk_len=cols.div_ceil(column_chunks);
        let mut bytes=vec![0u8;batch_bytes];
        let mut file=self.file.borrow_mut();
        file.seek(SeekFrom::Start(0)).map_err(|e|format!("packed seek: {e}"))?;
        let mut first_row=0usize;
        while first_row<row_count{
            let batch_rows=(row_count-first_row).min(rows_per_batch);
            let active_bytes=batch_rows.checked_mul(row_bytes).ok_or("packed vector product batch size overflow")?;
            #[cfg(test)] let read_started=Instant::now();
            let read_result=file.read_exact(&mut bytes[..active_bytes]);
            #[cfg(test)] record_read(&self.io_metrics,active_bytes,&read_result,read_started);
            read_result.map_err(|e|format!("packed read: {e}"))?;
            let active=&bytes[..active_bytes];
            result.par_chunks_mut(column_chunk_len).enumerate().for_each(|(chunk_index,accumulators)|{
                let first_column=chunk_index*column_chunk_len;
                for row_index in 0..batch_rows{
                    let row=&active[row_index*row_bytes..(row_index+1)*row_bytes];
                    let weight=left[first_row+row_index].0;
                    for (local_column,accumulator) in accumulators.iter_mut().enumerate(){
                        let column=first_column+local_column;
                        if ((row[column/8]>>(column%8))&1)!=0{accumulator.0+=weight;}
                    }
                }
            });
            first_row+=batch_rows;
        }
        Ok(result)
    }

    fn evaluation(&self, point: &[ArkFr]) -> Result<ArkFr, String> {
        if point.len() != self.log_n { return Err("packed evaluation dimension mismatch".into()); }
        let nu = self.log_n / 2;
        let sigma = self.log_n.div_ceil(2);
        let (left, right) = self.compute_evaluation_vectors(point, nu, sigma);
        let columns = self.vector_product(&left, nu, sigma)?;
        let mut value = Fr::zero();
        for (a,b) in columns.iter().zip(right.iter()) { value += a.0 * b.0; }
        Ok(ArkFr(value))
    }
}

impl Polynomial<ArkFr> for PackedFile {
    fn num_vars(&self) -> usize { self.log_n }

    fn evaluate(&self, point: &[ArkFr]) -> ArkFr {
        self.evaluation(point).expect("packed source read failed during Dory evaluation")
    }

    fn commit<E, Mo, M1>(&self, nu: usize, sigma: usize, setup: &ProverSetup<E>)
        -> Result<(E::GT, Vec<E::G1>, ArkFr), dory_pcs::error::DoryError>
    where
        E: PairingCurve,
        Mo: dory_pcs::mode::Mode,
        M1: DoryRoutines<E::G1>,
        E::G1: Group<Scalar = ArkFr>,
        E::GT: Group<Scalar = ArkFr>,
    {
        use dory_pcs::error::DoryError;
        if nu + sigma != self.log_n || setup.g1_vec.len() < (1 << sigma)
            || setup.g2_vec.len() < (1 << nu) {
            return Err(DoryError::InvalidInput("packed commitment shape mismatch".into()));
        }
        let columns = 1usize << sigma;
        let mut rows = Vec::with_capacity(1 << nu);
        self.scan_rows(columns, |_row, bytes, offset| {
            let fields: Vec<ArkFr> = (0..columns).map(|column| {
                let bit = offset + column;
                ArkFr(Fr::from(((bytes[bit / 8] >> (bit % 8)) & 1) as u64))
            }).collect();
            rows.push(M1::msm(&setup.g1_vec[..columns], &fields));
            Ok(())
        }).map_err(DoryError::InvalidInput)?;
        let tier2 = E::multi_pair_g2_setup(&rows, &setup.g2_vec[..1 << nu]);
        let blind = Mo::sample();
        Ok((Mo::mask(tier2, &setup.ht, &blind), rows, blind))
    }
}

impl MultilinearLagrange<ArkFr> for PackedFile {
    fn vector_matrix_product(&self, left: &[ArkFr], nu: usize, sigma: usize) -> Vec<ArkFr> {
        self.vector_product(left, nu, sigma)
            .expect("packed source read failed during Dory vector product")
    }
}

pub struct PackedCommitted {
    pub rows: Vec<ArkG1>,
    pub commitment: ArkGT,
    pub nu: usize,
    pub sigma: usize,
}

/// Opaque source-bound commitment for the complete native N3/H2 owner domain.
/// The digest is computed alongside all row commitments, never supplied by a
/// caller or inferred from only a selected row.
pub(crate) struct NativePcsCommitted {
    packed: PackedCommitted,
    digest: [u8; 64],
    source_binding: [u8; 32],
    setup_id: [u8; 32],
}

impl NativePcsCommitted {
    pub(crate) fn packed(&self) -> &PackedCommitted { &self.packed }
    pub(crate) fn commitment(&self) -> ArkGT { self.packed.commitment }
}

fn native_digest_start(source_binding: [u8; 32], setup: &Setup) -> Blake2b512 {
    let mut hash = Blake2b512::new();
    hash.update(b"nipopow-native-owner-pcs-complete-rows-v1");
    hash.update(setup.id);
    hash.update(source_binding);
    hash.update((setup.log_n as u64).to_le_bytes());
    hash.update((crate::packed_owner_assembly::NativePcsSource::ROW_BITS as u64).to_le_bytes());
    hash.update((crate::packed_owner_assembly::NativePcsSource::ROWS as u64).to_le_bytes());
    hash
}

fn native_digest_row(hash: &mut Blake2b512, index: usize, bytes: &[u8]) {
    hash.update((index as u64).to_le_bytes());
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

fn native_admit(source: &crate::packed_owner_assembly::NativePcsSource<'_, '_>,
    setup: &Setup) -> Result<BitpackedDimensions, String> {
    if setup.log_n != crate::packed_owner_assembly::NativePcsSource::LOG_N
        || setup.log_n > pcs::MAX_LOG_N {
        return Err("native PCS requires admitted log22 prover setup".into());
    }
    let dim = bitpacked_dimensions(setup.log_n, source.input_len())?;
    if dim.width != crate::packed_owner_assembly::NativePcsSource::ROW_BITS
        || dim.rows != crate::packed_owner_assembly::NativePcsSource::ROWS {
        return Err("native PCS complete row geometry mismatch".into());
    }
    bitpacked_setup_shape(dim, dim.rows, setup.prover.g1_vec.len(),
        setup.prover.g2_vec.len(), MAX_COMMIT_TABLE_BYTES)?;
    Ok(dim)
}

pub(crate) fn commit_native(
    source: &crate::packed_owner_assembly::NativePcsSource<'_, '_>,
    setup: &Setup,
) -> Result<NativePcsCommitted, String> {
    let dim = native_admit(source, setup)?;
    let (windows, table) = commit_subset_table(setup, dim.width)?;
    let source_binding = source.binding();
    let mut hash = native_digest_start(source_binding, setup);
    let mut rows = Vec::with_capacity(dim.rows);
    source.scan_rows(|index, bytes| {
        if index != rows.len() { return Err("native PCS commit row order drift".into()); }
        if bytes.len() != dim.row_bytes { return Err("native PCS commit row byte width drift".into()); }
        native_digest_row(&mut hash, index, bytes);
        rows.push(commit_subset_row(&windows, &table, bytes, 0));
        Ok(())
    })?;
    if rows.len() != dim.rows { return Err("native PCS commit complete row count drift".into()); }
    let digest = hash.finalize().into();
    let commitment = BN254::multi_pair_g2_setup(&rows, &setup.prover.g2_vec[..dim.rows]);
    Ok(NativePcsCommitted {
        packed: PackedCommitted { rows, commitment, nu: setup.log_n / 2,
            sigma: setup.log_n.div_ceil(2) },
        digest, source_binding, setup_id: setup.id,
    })
}

/// Verify a fresh complete sequential pass before consuming its rows. The
/// callback can form a frontend projection or the PCS vector product, but it
/// cannot substitute its own source digest or commitment authority.
pub(crate) fn scan_native_verified(
    source: &crate::packed_owner_assembly::NativePcsSource<'_, '_>,
    committed: &NativePcsCommitted,
    setup: &Setup,
    mut consume: impl FnMut(usize, &[u8]) -> Result<(), String>,
) -> Result<(), String> {
    let dim = native_admit(source, setup)?;
    if committed.setup_id != setup.id || committed.source_binding != source.binding()
        || committed.packed.nu != setup.log_n / 2
        || committed.packed.sigma != setup.log_n.div_ceil(2)
        || committed.packed.rows.len() != dim.rows {
        return Err("native PCS committed source/setup/row shape mismatch".into());
    }
    let (windows, table) = commit_subset_table(setup, dim.width)?;
    let mut hash = native_digest_start(source.binding(), setup);
    let mut count = 0usize;
    source.scan_rows(|index, bytes| {
        if count >= dim.rows || index != count { return Err("native PCS pass row order drift".into()); }
        if bytes.len() != dim.row_bytes { return Err("native PCS pass row byte width drift".into()); }
        native_digest_row(&mut hash, index, bytes);
        if commit_subset_row(&windows, &table, bytes, 0) != committed.packed.rows[index] {
            return Err("native PCS pass row commitment drift".into());
        }
        consume(index, bytes)?;
        count += 1;
        Ok(())
    })?;
    if count != dim.rows { return Err("native PCS pass complete row count drift".into()); }
    let observed: [u8; 64] = hash.finalize().into();
    if observed != committed.digest { return Err("native PCS pass ordered digest drift".into()); }
    let aggregate = BN254::multi_pair_g2_setup(&committed.packed.rows,
        &setup.prover.g2_vec[..dim.rows]);
    if aggregate != committed.packed.commitment {
        return Err("native PCS pass aggregate commitment drift".into());
    }
    Ok(())
}

pub fn commit(source: &PackedFile, setup: &Setup) -> Result<PackedCommitted, String> {
    if source.log_n != setup.log_n { return Err("packed/setup dimension mismatch".into()); }
    let nu = setup.log_n / 2;
    let sigma = setup.log_n.div_ceil(2);
    let width=1usize.checked_shl(sigma as u32).ok_or("packed commitment width overflow")?;
    let rows_count=1usize.checked_shl(nu as u32).ok_or("packed commitment rows overflow")?;
    if setup.prover.g1_vec.len()<width||setup.prover.g2_vec.len()<rows_count{
        return Err("packed commitment setup vectors are too short".into());
    }
    let table_bytes=commit_table_required_bytes(width)?;
    let (commitment,rows,blind)=if table_bytes>MAX_COMMIT_TABLE_BYTES{
        source.commit::<BN254,Transparent,G1Routines>(nu,sigma,&setup.prover).map_err(|e|e.to_string())?
    }else{
        let (windows,table)=commit_subset_table(setup,width)?;
        let rows=commit_rows_batched(source,&windows,&table,width,rows_count)?;
        let commitment=BN254::multi_pair_g2_setup(&rows,&setup.prover.g2_vec[..1usize<<nu]);
        (commitment,rows,ArkFr(Fr::zero()))
    };
    if !blind.0.is_zero() { return Err("unexpected packed commitment blind".into()); }
    Ok(PackedCommitted { rows, commitment, nu, sigma })
}

pub fn open(committed: &PackedCommitted, source: &PackedFile, point: &[Fr],
            setup: &Setup, transcript: &mut Transcript) -> Result<ArkDoryProof, String> {
    if source.log_n != setup.log_n || point.len() != setup.log_n
        || committed.nu != setup.log_n / 2 || committed.sigma != setup.log_n.div_ceil(2) {
        return Err("packed opening dimensions mismatch".into());
    }
    let point_ark: Vec<ArkFr> = point.iter().copied().map(ArkFr).collect();
    let value = source.evaluation(&point_ark)?.0;
    pcs::bind_statement(setup, &committed.commitment, &value, point, transcript)?;
    let (proof, blind) = dory_pcs::prove::<_, BN254, G1Routines, G2Routines, _, _, Transparent>(
        source, &point_ark, committed.rows.clone(), ArkFr(Fr::zero()),
        committed.nu, committed.sigma, &setup.prover, transcript,
    ).map_err(|e| e.to_string())?;
    if blind.is_some() { return Err("unexpected packed proof blind".into()); }
    Ok(proof)
}

// This private adapter tests a fallible preflight for Transparent Dory without
// changing the admitted producer. Dory's trait calls below never touch a file.
#[derive(Clone,Copy,Debug)]
pub(crate) struct BitpackedDimensions {
    pub(crate) width:usize,
    pub(crate) rows:usize,
    row_bytes:usize,
    extent:u64,
    table_bytes:usize,
}

/// Arithmetic only: this is not production admission or a witness allocation.
pub(crate) fn bitpacked_dimensions(log_n:usize,input_len:usize)->Result<BitpackedDimensions,String>{
    if log_n>pcs::MAX_VERIFY_LOG_N || log_n>=usize::BITS as usize || log_n.div_ceil(2)<3 {
        return Err("bitpacked dimension bound".into());
    }
    let bits=1usize.checked_shl(log_n as u32).ok_or("bitpacked input extent overflow")?;
    if input_len!=bits{return Err("bitpacked input extent mismatch".into());}
    let width=1usize.checked_shl(log_n.div_ceil(2) as u32).ok_or("bitpacked width overflow")?;
    let rows=1usize.checked_shl((log_n/2) as u32).ok_or("bitpacked rows overflow")?;
    let row_bytes=width/8;
    let extent=rows.checked_mul(row_bytes).ok_or("bitpacked byte extent overflow")?;
    if extent!=bits/8{return Err("bitpacked byte extent mismatch".into());}
    let extent=u64::try_from(extent).map_err(|_|"bitpacked file extent overflow")?;
    let table_bytes=commit_table_required_bytes(width)?;
    Ok(BitpackedDimensions{width,rows,row_bytes,extent,table_bytes})
}

fn bitpacked_extent(dim:BitpackedDimensions,observed:u64)->Result<(),String>{
    if observed!=dim.extent{return Err("sealed packed length drift".into());}
    Ok(())
}

fn bitpacked_setup_shape(dim:BitpackedDimensions,rows:usize,g1:usize,g2:usize,budget:usize)
    ->Result<(),String>{
    if rows!=dim.rows || g1<dim.width || g2<dim.rows {
        return Err("sealed PCS row/setup shape mismatch".into());
    }
    if dim.table_bytes>budget{return Err("sealed PCS row comparison exceeds table budget".into());}
    Ok(())
}

trait SealedBitRows {
    fn read_row(&mut self, expected: usize, out: &mut [u8])
        -> Result<Option<(usize,usize)>, String>;
    fn finish(&mut self) -> Result<(), String>;
}

struct LockedPackedRows<'a> {
    source: &'a PackedFile,
    file: RefMut<'a,File>,
    next: usize,
    row_count: usize,
    expected_len: u64,
}

impl<'a> LockedPackedRows<'a> {
    fn new(source: &'a PackedFile, row_count: usize) -> Result<Self,String> {
        let dim=bitpacked_dimensions(source.log_n,source.input_len())?;
        if row_count!=dim.rows{return Err("sealed packed row count mismatch".into());}
        let mut file=source.file.try_borrow_mut().map_err(|_|"sealed packed handle already borrowed")?;
        let expected_len=dim.extent;
        bitpacked_extent(dim,file.metadata().map_err(|e|format!("sealed metadata: {e}"))?.len())?;
        file.seek(SeekFrom::Start(0)).map_err(|e|format!("sealed seek: {e}"))?;
        Ok(Self{source,file,next:0,row_count,expected_len})
    }
}

impl SealedBitRows for LockedPackedRows<'_> {
    fn read_row(&mut self, expected: usize, out: &mut [u8])
        -> Result<Option<(usize,usize)>,String> {
        if expected!=self.next || self.next>=self.row_count {
            return Err("sealed packed row request out of order".into());
        }
        #[cfg(test)] let started=Instant::now();
        let read=self.file.read_exact(out);
        #[cfg(test)] record_read(&self.source.io_metrics,out.len(),&read,started);
        read.map_err(|e|format!("sealed packed row read: {e}"))?;
        self.next+=1;
        Ok(Some((expected,out.len())))
    }

    fn finish(&mut self)->Result<(),String>{
        if self.next!=self.row_count{return Err("sealed packed row count mismatch".into());}
        let mut extra=[0u8;1];
        if self.file.read(&mut extra).map_err(|e|format!("sealed packed EOF read: {e}"))?!=0 {
            return Err("sealed packed trailing bytes".into());
        }
        if self.file.metadata().map_err(|e|format!("sealed metadata: {e}"))?.len()!=self.expected_len {
            return Err("sealed packed length drift after scan".into());
        }
        Ok(())
    }
}

struct SealedPrecomputedV<'a> {
    _source: &'a PackedFile, // Keep the immutable Windows handle alive through proof.
    committed: &'a PackedCommitted,
    setup: &'a Setup,
    point: Vec<Fr>,
    point_ark: Vec<ArkFr>,
    left: Vec<ArkFr>,
    v: Vec<ArkFr>,
    value: ArkFr,
}

fn prepare_precomputed_v_from_rows<'a,R:SealedBitRows>(
    source:&'a PackedFile,committed:&'a PackedCommitted,setup:&'a Setup,
    point:&[Fr],expected_digest:&[u8;64],rows:&mut R,
)->Result<SealedPrecomputedV<'a>,String>{
    if source.log_n!=setup.log_n || point.len()!=setup.log_n
        || committed.nu!=setup.log_n/2 || committed.sigma!=setup.log_n.div_ceil(2) {
        return Err("sealed PCS dimensions mismatch".into());
    }
    let nu=committed.nu;let sigma=committed.sigma;
    let dim=bitpacked_dimensions(setup.log_n,source.input_len())?;
    bitpacked_setup_shape(dim,committed.rows.len(),setup.prover.g1_vec.len(),setup.prover.g2_vec.len(),MAX_COMMIT_TABLE_BYTES)?;
    let row_count=dim.rows;let width=dim.width;
    let (windows,table)=commit_subset_table(setup,width)?;
    let point_ark=point.iter().copied().map(ArkFr).collect::<Vec<_>>();
    let (left,right)=source.compute_evaluation_vectors(&point_ark,nu,sigma);
    if left.len()!=row_count || right.len()!=width {
        return Err("sealed PCS evaluation vector shape".into());
    }
    let mut v=vec![ArkFr(Fr::zero());width];
    let mut bytes=vec![0u8;dim.row_bytes];
    let mut digest=Blake2b512::new();
    for row in 0..row_count {
        let Some((actual,len))=rows.read_row(row,&mut bytes)? else {
            return Err("sealed PCS missing row".into());
        };
        if actual!=row{return Err("sealed PCS row order mismatch".into());}
        if len!=bytes.len(){return Err("sealed PCS short row".into());}
        digest.update(&bytes);
        if commit_subset_row(&windows,&table,&bytes,0)!=committed.rows[row] {
            return Err("sealed PCS row commitment mismatch".into());
        }
        let weight=left[row].0;
        for (column,element) in v.iter_mut().enumerate() {
            if bytes[column/8]>>(column%8)&1!=0 {element.0+=weight;}
        }
    }
    rows.finish()?;
    if digest.finalize().as_slice()!=expected_digest {
        return Err("sealed PCS source digest mismatch".into());
    }
    let recomputed=BN254::multi_pair_g2_setup(&committed.rows,&setup.prover.g2_vec[..row_count]);
    if recomputed!=committed.commitment {
        return Err("sealed PCS aggregate commitment mismatch".into());
    }
    let value=ArkFr(v.iter().zip(right.iter()).fold(Fr::zero(),|sum,(a,b)|sum+a.0*b.0));
    Ok(SealedPrecomputedV{_source:source,committed,setup,point:point.to_vec(),point_ark,left,v,value})
}

fn prepare_precomputed_v<'a>(
    source:&'a PackedFile,committed:&'a PackedCommitted,setup:&'a Setup,
    point:&[Fr],expected_digest:&[u8;64],
)->Result<SealedPrecomputedV<'a>,String>{
    // Validate before touching the locked file or transcript.
    if source.log_n!=setup.log_n || point.len()!=setup.log_n {
        return Err("sealed PCS dimensions mismatch".into());
    }
    let dim=bitpacked_dimensions(setup.log_n,source.input_len())?;
    bitpacked_setup_shape(dim,committed.rows.len(),setup.prover.g1_vec.len(),setup.prover.g2_vec.len(),MAX_COMMIT_TABLE_BYTES)?;
    let mut rows=LockedPackedRows::new(source,dim.rows)?;
    prepare_precomputed_v_from_rows(source,committed,setup,point,expected_digest,&mut rows)
}

impl Polynomial<ArkFr> for SealedPrecomputedV<'_> {
    fn num_vars(&self)->usize{self.setup.log_n}
    fn evaluate(&self,point:&[ArkFr])->ArkFr{
        assert_eq!(point,self.point_ark,"sealed PCS point drift");
        self.value
    }
    fn commit<E,Mo,M1>(&self,_nu:usize,_sigma:usize,_setup:&ProverSetup<E>)
        ->Result<(E::GT,Vec<E::G1>,ArkFr),dory_pcs::error::DoryError>
    where E:PairingCurve,Mo:dory_pcs::mode::Mode,M1:DoryRoutines<E::G1>,
          E::G1:Group<Scalar=ArkFr>,E::GT:Group<Scalar=ArkFr> {
        Err(dory_pcs::error::DoryError::InvalidInput(
            "sealed precomputed-V adapter cannot commit".into()))
    }
}

impl MultilinearLagrange<ArkFr> for SealedPrecomputedV<'_> {
    fn vector_matrix_product(&self,left:&[ArkFr],nu:usize,sigma:usize)->Vec<ArkFr>{
        assert_eq!((nu,sigma),(self.committed.nu,self.committed.sigma),"sealed PCS shape drift");
        assert_eq!(left,self.left,"sealed PCS left vector drift");
        self.v.clone()
    }
}

fn open_precomputed_v(prepared:&SealedPrecomputedV<'_>,point:&[Fr],
    transcript:&mut Transcript)->Result<ArkDoryProof,String>{
    if point!=prepared.point || prepared.setup.log_n!=prepared.point.len() {
        return Err("sealed PCS opening point drift".into());
    }
    // Commit the transcript only after a complete proof; all source reads and
    // digest/row checks have already succeeded in prepare_precomputed_v.
    let mut next=transcript.clone();
    pcs::bind_statement(prepared.setup,&prepared.committed.commitment,&prepared.value.0,point,&mut next)?;
    let (proof,blind)=dory_pcs::prove::<_,BN254,G1Routines,G2Routines,_,_,Transparent>(
        prepared,&prepared.point_ark,prepared.committed.rows.clone(),ArkFr(Fr::zero()),
        prepared.committed.nu,prepared.committed.sigma,&prepared.setup.prover,&mut next,
    ).map_err(|e|e.to_string())?;
    if blind.is_some(){return Err("unexpected sealed PCS proof blind".into());}
    *transcript=next;
    Ok(proof)
}

/// Private bitpacked frontend join. The scan validates every row and digest
/// before the fallible-free Dory trait adapter is called.
pub(crate) fn open_precomputed_v_bound(
    source:&PackedFile,committed:&PackedCommitted,setup:&Setup,point:&[Fr],
    expected_digest:&[u8;64],transcript:&mut Transcript,
)->Result<ArkDoryProof,String>{
    #[cfg(test)]
    let trace_prefix=if setup.log_n==28 &&
        std::env::var("NIPOPOW_K28_EXACT_TRACE").as_deref()==Ok("1") {
        Some("k28_exact_pcs")
    } else if matches!(setup.log_n,30|32) &&
        std::env::var("NIPOPOW_C174_EXACT_TRACE").as_deref()==Ok("1") {
        Some("c174_exact_pcs")
    } else {None};
    #[cfg(test)]
    if let Some(prefix)=trace_prefix {
        println!("{prefix} phase=prepare edge=begin");
        std::io::stdout().flush().map_err(|e|e.to_string())?;
    }
    #[cfg(test)]
    let phase_started=Instant::now();
    let prepared=prepare_precomputed_v(source,committed,setup,point,expected_digest)?;
    #[cfg(test)]
    if let Some(prefix)=trace_prefix {
        println!("{prefix} phase=prepare edge=end elapsed_us={}",phase_started.elapsed().as_micros());
        println!("{prefix} phase=prove edge=begin");
        std::io::stdout().flush().map_err(|e|e.to_string())?;
    }
    #[cfg(test)]
    let phase_started=Instant::now();
    let proof=open_precomputed_v(&prepared,point,transcript)?;
    #[cfg(test)]
    if let Some(prefix)=trace_prefix {
        println!("{prefix} phase=prove edge=end elapsed_us={}",phase_started.elapsed().as_micros());
        std::io::stdout().flush().map_err(|e|e.to_string())?;
    }
    Ok(proof)
}

struct NativePrecomputedV<'a> {
    committed: &'a NativePcsCommitted,
    setup: &'a Setup,
    point_ark: Vec<ArkFr>,
    left: Vec<ArkFr>,
    v: Vec<ArkFr>,
    value: ArkFr,
}

impl Polynomial<ArkFr> for NativePrecomputedV<'_> {
    fn num_vars(&self) -> usize { self.setup.log_n }
    fn evaluate(&self, point: &[ArkFr]) -> ArkFr {
        assert_eq!(point, self.point_ark, "native PCS point drift");
        self.value
    }
    fn commit<E, Mo, M1>(&self, _nu: usize, _sigma: usize, _setup: &ProverSetup<E>)
        -> Result<(E::GT, Vec<E::G1>, ArkFr), dory_pcs::error::DoryError>
    where E: PairingCurve, Mo: dory_pcs::mode::Mode, M1: DoryRoutines<E::G1>,
        E::G1: Group<Scalar = ArkFr>, E::GT: Group<Scalar = ArkFr> {
        Err(dory_pcs::error::DoryError::InvalidInput(
            "native precomputed-V adapter cannot commit".into()))
    }
}

impl MultilinearLagrange<ArkFr> for NativePrecomputedV<'_> {
    fn vector_matrix_product(&self, left: &[ArkFr], nu: usize, sigma: usize) -> Vec<ArkFr> {
        assert_eq!((nu, sigma), (self.committed.packed.nu, self.committed.packed.sigma),
            "native PCS shape drift");
        assert_eq!(left, self.left, "native PCS left vector drift");
        self.v.clone()
    }
}

/// Every PCS source read is a third authenticated full pass. Dory receives
/// only a precomputed vector after all fallible producer work has succeeded.
pub(crate) fn open_native(
    source: &crate::packed_owner_assembly::NativePcsSource<'_, '_>,
    committed: &NativePcsCommitted,
    setup: &Setup,
    point: &[Fr],
    transcript: &mut Transcript,
) -> Result<ArkDoryProof, String> {
    let dim = native_admit(source, setup)?;
    if point.len() != setup.log_n { return Err("native PCS opening point dimension mismatch".into()); }
    let point_ark: Vec<ArkFr> = point.iter().copied().map(ArkFr).collect();
    let (left, right) = dory_pcs::primitives::poly::compute_left_right_vectors(
        &point_ark, committed.packed.nu, committed.packed.sigma);
    if left.len() != dim.rows || right.len() != dim.width {
        return Err("native PCS evaluation vector shape mismatch".into());
    }
    let mut v = vec![ArkFr(Fr::zero()); dim.width];
    scan_native_verified(source, committed, setup, |row, bytes| {
        let weight = left[row].0;
        for (column, element) in v.iter_mut().enumerate() {
            if bytes[column / 8] >> (column % 8) & 1 != 0 { element.0 += weight; }
        }
        Ok(())
    })?;
    let value = ArkFr(v.iter().zip(right.iter()).fold(Fr::zero(),
        |sum, (a, b)| sum + a.0 * b.0));
    let prepared = NativePrecomputedV {
        committed, setup, point_ark, left, v, value,
    };
    let mut next = transcript.clone();
    pcs::bind_statement(setup, &committed.packed.commitment, &value.0, point, &mut next)?;
    let (proof, blind) = dory_pcs::prove::<_, BN254, G1Routines, G2Routines, _, _, Transparent>(
        &prepared, &prepared.point_ark, committed.packed.rows.clone(), ArkFr(Fr::zero()),
        committed.packed.nu, committed.packed.sigma, &setup.prover, &mut next,
    ).map_err(|e| e.to_string())?;
    if blind.is_some() { return Err("unexpected native PCS proof blind".into()); }
    *transcript = next;
    Ok(proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{io::Write, sync::atomic::{AtomicU64, Ordering}};

    static NEXT: AtomicU64 = AtomicU64::new(0);
    fn temp_file(bytes: &[u8]) -> std::path::PathBuf {
        let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let path = std::env::temp_dir().join(format!("packed-dory-{}-{nonce}-{}.bin",
            std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
        let mut file = OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
        file.write_all(bytes).unwrap();
        drop(file);
        path
    }
    fn temp_path() -> std::path::PathBuf {
        std::env::temp_dir().join(format!("packed-dory-writer-{}-{}.bin",
            std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)))
    }

    #[test]
    fn boolean_decoder_lookup_matches_legacy_exhaustive() {
        let bytes=(0..(1<<17)).map(|i|(i%256) as u8).collect::<Vec<_>>();
        let path=temp_file(&bytes);let source=PackedFile::open(&path,20).unwrap();
        for width in [1usize,2,4,8,16,65536] {
            let copies=source.input_len()/width;
            let indices=if width<=16 {(0..(2048/width)).collect::<Vec<_>>()}
                else {vec![0,1,copies-1]};
            for copy in indices {
                source.reset_io_metrics();let a=source.read_copy(width,copy).unwrap();let ai=source.io_metrics_snapshot();
                source.reset_io_metrics();let b=source.read_copy_legacy_for_test(width,copy).unwrap();let bi=source.io_metrics_snapshot();
                assert_eq!(a,b);assert_eq!(a.len(),width);assert_eq!(a.capacity(),b.capacity());
                assert_eq!((ai.read_calls,ai.read_bytes),(bi.read_calls,bi.read_bytes));
                for (i,value) in a.iter().enumerate(){let bit=copy*width+i;
                    assert_eq!(*value,Fr::from(((bytes[bit/8]>>(bit%8))&1) as u64));}
            }
        }
        for (width,copy) in [(0,0),(3,0),(1<<17,0),(16,1<<16)] {
            source.reset_io_metrics();assert!(source.read_copy(width,copy).is_err());
            assert!(source.read_copy_legacy_for_test(width,copy).is_err());assert_eq!(source.io_metrics_snapshot().read_calls,0);
        }
        drop(source);std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn rejects_noncanonical_lengths_and_tail() {
        let short = temp_file(&[]);
        assert!(PackedFile::open(&short, 3).is_err());
        std::fs::remove_file(short).unwrap();
        let trailing = temp_file(&[0, 0]);
        assert!(PackedFile::open(&trailing, 3).is_err());
        std::fs::remove_file(trailing).unwrap();
        let bad_tail = temp_file(&[0x80]);
        assert!(PackedFile::open(&bad_tail, 0).is_err());
        std::fs::remove_file(bad_tail).unwrap();
    }

    #[test]
    fn packed_writer_streams_exact_chunks_and_reopens_immutable_source() {
        let path=temp_path();
        let expected=[vec![0x55;7],vec![0x33;120],vec![0x03]].concat();
        let mut writer=PackedFileWriter::create_new(&path,10).unwrap();
        writer.write_bytes(&expected[..13]).unwrap();
        writer.write_bytes(&expected[13..]).unwrap();
        let source=writer.finish().unwrap();
        assert_eq!(std::fs::read(&path).unwrap(),expected);
        assert_eq!(source.input_len(),1<<10);
        let dense=(0..1<<10).map(|bit|Fr::from(((expected[bit/8]>>(bit%8))&1) as u64)).collect::<Vec<_>>();
        assert_eq!(source.read_copy(1<<10,0).unwrap(),dense);
        drop(source);std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn packed_writer_rejects_overflow_short_noncanonical_tail_and_collision() {
        let path=temp_path();
        let mut overflow=PackedFileWriter::create_new(&path,2).unwrap();
        assert!(overflow.write_bytes(&[0,0]).is_err());
        assert!(PackedFileWriter::create_new(&path,2).is_err());
        drop(overflow);assert!(!path.exists());

        let existing=temp_file(&[0x35]);
        assert!(PackedFileWriter::create_new(&existing,3).is_err());
        assert_eq!(std::fs::read(&existing).unwrap(),[0x35]);
        std::fs::remove_file(existing).unwrap();

        let path=temp_path();
        let short=PackedFileWriter::create_new(&path,2).unwrap();
        assert!(short.finish().is_err());
        assert!(!path.exists());

        let path=temp_path();
        let mut tail=PackedFileWriter::create_new(&path,2).unwrap();
        tail.write_bytes(&[0x80]).unwrap();
        assert!(tail.finish().is_err());
        assert!(!path.exists());

        let path=temp_path();
        let mut abandoned=PackedFileWriter::create_new(&path,3).unwrap();
        abandoned.write_bytes(&[0]).unwrap();
        drop(abandoned);assert!(!path.exists());

        assert!(PackedFileWriter::create_new(temp_path(),pcs::MAX_LOG_N+1).is_err());
    }

    #[test]
    fn packed_matches_dense_commit_and_open() {
        for log_n in [0usize, 2, 3, 4, 10] {
            let n = 1usize << log_n;
            let bytes: Vec<u8> = (0..n.div_ceil(8)).map(|i| {
                (i as u8).wrapping_mul(73).wrapping_add(0x35)
            }).collect();
            let mut canonical = bytes;
            if n % 8 != 0 { *canonical.last_mut().unwrap() &= (1 << (n % 8)) - 1; }
            let path = temp_file(&canonical);
            let packed = PackedFile::open(&path, log_n).unwrap();
            let dense: Vec<Fr> = (0..n).map(|i| Fr::from(((canonical[i/8] >> (i%8)) & 1) as u64)).collect();
            assert_eq!(packed.read_copy(n.min(1 << 16), 0).unwrap(), dense);
            let setup = pcs::generate_setup(log_n).unwrap();
            let packed_commit = commit(&packed, &setup).unwrap();
            let dense_commit = pcs::commit(&dense, &setup).unwrap();
            assert_eq!(packed_commit.rows,dense_commit.rows,"packed Dory row commitments at log_n={log_n}");
            assert_eq!(pcs::encode_commitment(&packed_commit.commitment).unwrap(),
                       pcs::encode_commitment(&dense_commit.commitment).unwrap());
            let point: Vec<Fr> = (0..log_n).map(|i| Fr::from((i+3) as u64)).collect();
            let value = packed.evaluate(&point).unwrap();
            assert_eq!(value, crate::gkr::mle(&dense, &point).unwrap());
            let packed_proof = open(&packed_commit, &packed, &point, &setup,
                                    &mut Transcript::new(b"packed-test")).unwrap();
            let dense_proof = pcs::open(&dense_commit, &point, &setup,
                                        &mut Transcript::new(b"packed-test")).unwrap();
            assert_eq!(pcs::encode_proof(&packed_proof).unwrap(), pcs::encode_proof(&dense_proof).unwrap());
            pcs::verify(packed_commit.commitment, value, &point, &packed_proof, &setup,
                        &mut Transcript::new(b"packed-test")).unwrap();
            drop(packed);
            std::fs::remove_file(path).unwrap();
        }
    }

    struct ScriptedRows {
        rows: Vec<(usize,Vec<u8>)>,
        next: usize,
        fail_at: Option<usize>,
    }

    #[test]
    fn bitpacked_k41_dimension_extent_table_preflight_without_witness_allocation(){
        let k=41;let bits=1usize<<k;
        let dim=bitpacked_dimensions(k,bits).unwrap();
        assert_eq!((dim.width,dim.rows,dim.row_bytes),(1<<21,1<<20,1<<18));
        assert_eq!(dim.extent,256u64*1024*1024*1024);
        bitpacked_extent(dim,dim.extent).unwrap();
        assert!(bitpacked_extent(dim,dim.extent-1).is_err());
        assert!(bitpacked_extent(dim,dim.extent+1).is_err());
        assert!(bitpacked_dimensions(k,bits-1).is_err());
        assert!(bitpacked_dimensions(k+1,1usize<<(k+1)).is_err());
        assert!(bitpacked_dimensions(usize::MAX,0).is_err());
        assert!(bitpacked_dimensions(4,16).is_err());
        bitpacked_setup_shape(dim,dim.rows,dim.width,dim.rows,MAX_COMMIT_TABLE_BYTES).unwrap();
        bitpacked_setup_shape(dim,dim.rows,dim.width,dim.rows,dim.table_bytes).unwrap();
        assert!(bitpacked_setup_shape(dim,dim.rows,dim.width,dim.rows,dim.table_bytes-1)
            .unwrap_err().contains("table budget"));
        for (rows,g1,g2) in [(dim.rows-1,dim.width,dim.rows),
            (dim.rows+1,dim.width,dim.rows),(dim.rows,dim.width-1,dim.rows),
            (dim.rows,dim.width,dim.rows-1)] {
            assert!(bitpacked_setup_shape(dim,rows,g1,g2,MAX_COMMIT_TABLE_BYTES)
                .unwrap_err().contains("shape"));
        }
        assert_eq!(pcs::MAX_LOG_N,24);
        assert!(pcs::generate_setup(k).is_err());
        assert!(PackedFile::open(temp_path(),k).err().unwrap().contains("admitted bound"));
        println!("k41 arithmetic only: width={} rows={} bytes={} table_bytes={} budget={}",
            dim.width,dim.rows,dim.extent,dim.table_bytes,MAX_COMMIT_TABLE_BYTES);
    }

    impl SealedBitRows for ScriptedRows {
        fn read_row(&mut self,_expected:usize,out:&mut [u8])
            ->Result<Option<(usize,usize)>,String>{
            if self.fail_at==Some(self.next){return Err("injected sealed row read failure".into());}
            let Some((index,bytes))=self.rows.get(self.next) else{return Ok(None)};
            let copied=bytes.len().min(out.len());
            out[..copied].copy_from_slice(&bytes[..copied]);
            self.next+=1;
            Ok(Some((*index,bytes.len())))
        }
        fn finish(&mut self)->Result<(),String>{
            if self.next!=self.rows.len(){return Err("injected sealed trailing row".into());}
            Ok(())
        }
    }

    #[test]
    fn sealed_precomputed_v_odd_log9_is_exact_dory_differential() {
        let log_n=9usize;let n=1usize<<log_n;
        let bytes=(0..n/8).map(|i|((i*37+i/7+11)%251) as u8).collect::<Vec<_>>();
        let path=temp_file(&bytes);
        let source=PackedFile::open(&path,log_n).unwrap();
        let setup=pcs::generate_setup(log_n).unwrap();
        let committed=commit(&source,&setup).unwrap();
        let point=(0..log_n).map(|i|Fr::from((i*17+5) as u64)).collect::<Vec<_>>();
        let mut seal=[0u8;64];seal.copy_from_slice(&Blake2b512::digest(&bytes));
        let prepared=prepare_precomputed_v(&source,&committed,&setup,&point,&seal).unwrap();
        assert_eq!(prepared.value.0,source.evaluate(&point).unwrap());
        assert!(prepared.commit::<BN254,Transparent,G1Routines>(committed.nu,committed.sigma,&setup.prover).is_err());
        let domain=b"sealed-precomputed-v-odd-log9-v1";
        let mut baseline_t=Transcript::new(domain);
        let baseline=open(&committed,&source,&point,&setup,&mut baseline_t).unwrap();
        let mut precomputed_t=Transcript::new(domain);
        let reads_before=source.io_metrics_snapshot();
        let proof=open_precomputed_v(&prepared,&point,&mut precomputed_t).unwrap();
        assert_eq!(source.io_metrics_snapshot(),reads_before,"Dory trait calls must perform no source I/O");
        assert_eq!(pcs::encode_proof(&proof).unwrap(),pcs::encode_proof(&baseline).unwrap());
        assert_eq!((precomputed_t.challenges(),precomputed_t.raw_queries(),precomputed_t.bytes_absorbed()),
                   (baseline_t.challenges(),baseline_t.raw_queries(),baseline_t.bytes_absorbed()));
        assert_eq!(precomputed_t.challenge_scalar(b"continuation"),baseline_t.challenge_scalar(b"continuation"));
        pcs::verify(committed.commitment,prepared.value.0,&point,&proof,&setup,
            &mut Transcript::new(domain)).unwrap();
        pcs::verify(committed.commitment,prepared.value.0,&point,&baseline,&setup,
            &mut Transcript::new(domain)).unwrap();
        drop(prepared);drop(source);std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn sealed_precomputed_v_rejects_each_row_and_seal_fault_before_proof() {
        let log_n=9usize;let n=1usize<<log_n;
        let bytes=(0..n/8).map(|i|((i*29+i/3+7)%251) as u8).collect::<Vec<_>>();
        let path=temp_file(&bytes);let source=PackedFile::open(&path,log_n).unwrap();
        let setup=pcs::generate_setup(log_n).unwrap();let committed=commit(&source,&setup).unwrap();
        let point=(0..log_n).map(|i|Fr::from((i*13+3) as u64)).collect::<Vec<_>>();
        let mut seal=[0u8;64];seal.copy_from_slice(&Blake2b512::digest(&bytes));
        let canonical=bytes.chunks_exact(4).enumerate().map(|(i,row)|(i,row.to_vec())).collect::<Vec<_>>();
        let attempt=|rows:Vec<(usize,Vec<u8>)>,fault:Option<usize>,digest:&[u8;64],expected:&str|{
            let mut stream=ScriptedRows{rows,next:0,fail_at:fault};
            let error=prepare_precomputed_v_from_rows(&source,&committed,&setup,&point,digest,&mut stream)
                .err().expect("fault must not yield a prepared proof adapter");
            assert!(error.contains(expected),"expected {expected}, got {error}");
        };
        let mut wrong_order=canonical.clone();wrong_order[3].0=4;
        attempt(wrong_order,None,&seal,"order");
        let mut missing=canonical.clone();missing.pop();
        attempt(missing,None,&seal,"missing");
        let mut short=canonical.clone();short[6].1.pop();
        attempt(short,None,&seal,"short");
        let mut bit_mutation=canonical.clone();bit_mutation[7].1[1]^=1;
        attempt(bit_mutation,None,&seal,"row commitment");
        attempt(canonical.clone(),Some(9),&seal,"read failure");
        let mut wrong_seal=seal;wrong_seal[0]^=1;
        attempt(canonical.clone(),None,&wrong_seal,"digest");
        let mut trailing=canonical.clone();trailing.push((16,vec![0;4]));
        attempt(trailing,None,&seal,"trailing row");
        // A second pass over bytes that differ from the commitment pass cannot
        // use a previously admitted seal/row commitment, even if its order holds.
        let mut pass_drift=canonical.clone();pass_drift[13].1[3]^=0x80;
        attempt(pass_drift,None,&seal,"row commitment");
        let mut wrong_aggregate=commit(&source,&setup).unwrap();
        // A nonidentity change must be rejected even when all source rows match.
        wrong_aggregate.commitment=wrong_aggregate.commitment
            +BN254::pair(&setup.prover.g1_vec[0],&setup.prover.g2_vec[0]);
        let mut clean=ScriptedRows{rows:canonical,next:0,fail_at:None};
        assert!(prepare_precomputed_v_from_rows(&source,&wrong_aggregate,&setup,&point,&seal,&mut clean)
            .err().unwrap().contains("aggregate commitment"));
        let prepared=prepare_precomputed_v(&source,&committed,&setup,&point,&seal).unwrap();
        let mut drifted_point=point.clone();drifted_point[0]+=Fr::from(1u64);
        let mut transcript=Transcript::new(b"sealed-negative-no-transcript");
        let mut untouched=transcript.clone();
        assert!(open_precomputed_v(&prepared,&drifted_point,&mut transcript).is_err());
        assert_eq!(transcript.challenge_scalar(b"continuation"),untouched.challenge_scalar(b"continuation"));
        drop(prepared);drop(source);std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn packed_parallel_commit_preserves_distinct_multi_batch_order() {
        let log_n=8usize;let n=1usize<<log_n;
        let dense=(0..n).map(|i|Fr::from(((i*37+i/7+3)%13<6) as u64)).collect::<Vec<_>>();
        let mut bytes=vec![0u8;n/8];
        for (index,value) in dense.iter().enumerate(){if !value.is_zero(){bytes[index/8]|=1<<(index%8);}}
        let path=temp_file(&bytes);let source=PackedFile::open(&path,log_n).unwrap();
        let setup=pcs::generate_setup(log_n).unwrap();let nu=log_n/2;let sigma=log_n.div_ceil(2);
        let width=1usize<<sigma;let row_count=1usize<<nu;let rows_per_batch=3usize;
        assert_ne!(row_count%rows_per_batch,0,"fixture must leave a partial final batch");
        let (windows,table)=commit_subset_table(&setup,width).unwrap();
        let actual=commit_rows_batched_with_limit(&source,&windows,&table,width,row_count,rows_per_batch*(width/8)).unwrap();
        let expected=pcs::commit(&dense,&setup).unwrap().rows;
        assert_eq!(actual,expected,"parallel batch boundaries changed row order or commitments");
        drop(source);std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn packed_parallel_vector_product_matches_dense_across_partial_batches() {
        let log_n=8usize;let n=1usize<<log_n;let nu=log_n/2;let sigma=log_n.div_ceil(2);
        let cols=1usize<<sigma;let row_bytes=cols/8;let row_count=1usize<<nu;let rows_per_batch=3usize;
        let dense=(0..n).map(|i|Fr::from(((i*29+i/5+1)%11<5) as u64)).collect::<Vec<_>>();
        let mut bytes=vec![0u8;n/8];
        for (index,value) in dense.iter().enumerate(){if !value.is_zero(){bytes[index/8]|=1<<(index%8);}}
        let path=temp_file(&bytes);let source=PackedFile::open(&path,log_n).unwrap();
        let left=(0..row_count).map(|row|Fr::from((row*17+9) as u64)).collect::<Vec<_>>();
        let left_ark=left.iter().copied().map(ArkFr).collect::<Vec<_>>();
        let mut expected=vec![Fr::zero();cols];
        for row in 0..row_count{for column in 0..cols{
            if !dense[row*cols+column].is_zero(){expected[column]+=left[row];}
        }}
        assert_ne!(row_count%rows_per_batch,0,"fixture must leave a partial final batch");
        let actual=source.vector_product_with_limit(&left_ark,nu,sigma,rows_per_batch*row_bytes).unwrap();
        assert_eq!(actual.iter().map(|field|field.0).collect::<Vec<_>>(),expected,
            "parallel vector product changed values or row order across batches");
        assert!(source.vector_product_with_limit(&left_ark,nu,sigma,row_bytes-1).is_err(),
            "a row larger than the configured read budget must fail closed");
        drop(source);std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn chunked_witness_feed_matches_one_global_dory_commitment_and_opening() {
        let log_n=10usize;let n=1usize<<log_n;
        let bits=(0..n).map(|i|((i*73+19)%11)<5).collect::<Vec<_>>();
        let mut contiguous=vec![0u8;n.div_ceil(8)];
        for (i,bit) in bits.iter().enumerate(){if *bit{contiguous[i/8]|=1<<(i%8);}}

        // Simulate independently produced chunks whose boundaries cross both
        // byte and Dory-row boundaries, then feed one canonical LSB-first file.
        let mut chunks=Vec::new();let mut sizes=Vec::new();let mut start=0usize;
        for end in [13usize,139,402,511,n] {
            let fragment=&bits[start..end];let mut bytes=vec![0u8;fragment.len().div_ceil(8)];
            for (local,bit) in fragment.iter().enumerate(){if *bit{bytes[local/8]|=1<<(local%8);}}
            chunks.push(bytes);sizes.push(fragment.len());start=end;
        }
        let assembled_path=std::env::temp_dir().join(format!("packed-dory-stream-{}-{}.bin",
            std::process::id(),NEXT.fetch_add(1,Ordering::Relaxed)));
        let mut output=PackedFileWriter::create_new(&assembled_path,log_n).unwrap();
        let mut pending=0u8;let mut pending_bits=0usize;let mut global=0usize;
        for (chunk,bit_len) in chunks.iter().zip(&sizes){
            for local in 0..*bit_len {
                if ((chunk[local/8]>>(local%8))&1)!=0{pending|=1<<pending_bits;}
                pending_bits+=1;
                if pending_bits==8{output.write_bytes(&[pending]).unwrap();pending=0;pending_bits=0;}
                global+=1;
            }
        }
        if pending_bits!=0{output.write_bytes(&[pending]).unwrap();}
        let chunked=output.finish().unwrap();
        assert_eq!(global,n);assert_eq!(std::fs::read(&assembled_path).unwrap(),contiguous,
            "chunk order/bit offsets changed the logical witness");

        let flat_path=temp_file(&contiguous);
        let flat=PackedFile::open(&flat_path,log_n).unwrap();
        let setup=pcs::generate_setup(log_n).unwrap();
        let flat_commit=commit(&flat,&setup).unwrap();let chunked_commit=commit(&chunked,&setup).unwrap();
        let encoded=|commitment:&ArkGT|pcs::encode(commitment).unwrap();
        assert_eq!(encoded(&flat_commit.commitment),encoded(&chunked_commit.commitment));
        let point=(0..log_n).map(|i|Fr::from((i*17+5) as u64)).collect::<Vec<_>>();
        let flat_value=flat.evaluate(&point).unwrap();let chunked_value=chunked.evaluate(&point).unwrap();
        assert_eq!(flat_value,chunked_value);
        let flat_proof=open(&flat_commit,&flat,&point,&setup,&mut Transcript::new(b"chunked-global-dory-v1")).unwrap();
        let chunked_proof=open(&chunked_commit,&chunked,&point,&setup,&mut Transcript::new(b"chunked-global-dory-v1")).unwrap();
        assert_eq!(pcs::encode_proof(&flat_proof).unwrap(),pcs::encode_proof(&chunked_proof).unwrap());
        pcs::verify(flat_commit.commitment,flat_value,&point,&flat_proof,&setup,
            &mut Transcript::new(b"chunked-global-dory-v1")).unwrap();
        drop((flat,chunked));std::fs::remove_file(flat_path).unwrap();std::fs::remove_file(assembled_path).unwrap();
    }

    #[cfg(windows)]
    #[test]
    #[ignore = "manual packed Dory streaming scale diagnostic; set NIPOPOW_PACKED_DIAGNOSTIC_LOG_N to 28..=36"]
    fn diagnostic_packed_scale_commit_open_and_verify() {
        let phase_started = std::time::Instant::now();
        let log_n=std::env::var("NIPOPOW_PACKED_DIAGNOSTIC_LOG_N")
            .map(|value|value.parse::<usize>().expect("diagnostic log_n must be an integer"))
            .unwrap_or(28);
        assert!((28..=36).contains(&log_n),"diagnostic scale must be in 28..=36");
        let bit_bytes:usize=1usize.checked_shl((log_n-3) as u32).expect("diagnostic file size overflow");
        assert!(pcs::generate_setup(log_n).is_err(), "public setup cap must remain at 24");
        let mut phase_seq = 0u32;
        let mut trace = |phase: &str, edge: &str| {
            println!("dory_packed_phase schema=1 log_n={} seq={} phase={} edge={} elapsed_us={}",
                log_n, phase_seq, phase, edge, phase_started.elapsed().as_micros());
            std::io::stdout().flush().expect("diagnostic phase stdout flush");
            phase_seq = phase_seq.checked_add(1).expect("diagnostic phase sequence overflow");
        };
        trace("setup", "begin");
        let started = std::time::Instant::now();
        let setup = pcs::generate_setup_for_scale_diagnostic(log_n).unwrap();
        let setup_ms = started.elapsed().as_millis();
        trace("setup", "end");

        trace("input", "begin");
        let path=temp_file(&[]);
        let mut file=OpenOptions::new().write(true).open(&path).unwrap();
        let mut bytes=vec![0u8;MAX_COMMIT_READ_BATCH_BYTES.min(bit_bytes)];
        let mut first_byte=0usize;
        while first_byte<bit_bytes{
            let batch_bytes=(bit_bytes-first_byte).min(bytes.len());
            for (offset,byte) in bytes[..batch_bytes].iter_mut().enumerate(){
                let index=(first_byte+offset) as u64;
                *byte=(index as u8)
                    ^ ((index>>8) as u8).rotate_left(1)
                    ^ ((index>>16) as u8).rotate_left(2)
                    ^ ((index>>24) as u8).rotate_left(3)
                    ^ ((index>>32) as u8).rotate_left(4)
                    ^ ((index>>40) as u8).rotate_left(5);
            }
            file.write_all(&bytes[..batch_bytes]).unwrap();
            first_byte+=batch_bytes;
        }
        file.flush().unwrap();
        drop(file);drop(bytes);
        trace("input", "end");
        trace("admission", "begin");
        assert!(PackedFile::open(&path, log_n).is_err(), "public packed-source cap must remain at 24");
        let source = PackedFile::open_with_limit(&path, log_n, log_n).unwrap();
        trace("admission", "end");

        trace("commit", "begin");
        let commit_started = std::time::Instant::now();
        let committed = commit(&source, &setup).unwrap();
        let commit_ms = commit_started.elapsed().as_millis();
        trace("commit", "end");
        let point = (0..log_n).map(|i| Fr::from((i * 17 + 5) as u64)).collect::<Vec<_>>();
        let point_ark = point.iter().copied().map(ArkFr).collect::<Vec<_>>();
        let nu=log_n/2;let sigma=log_n.div_ceil(2);
        let left=(0..1usize<<nu).map(|i|ArkFr(Fr::from((i*31+7) as u64))).collect::<Vec<_>>();
        trace("vector_product", "begin");
        let product_started=std::time::Instant::now();
        let _product=source.vector_product(&left,nu,sigma).unwrap();
        let vector_product_ms=product_started.elapsed().as_millis();
        trace("vector_product", "end");
        trace("evaluation", "begin");
        let evaluation_started=std::time::Instant::now();
        let value = source.evaluation(&point_ark).unwrap();
        let evaluation_ms=evaluation_started.elapsed().as_millis();
        trace("evaluation", "end");

        trace("open", "begin");
        let open_started = std::time::Instant::now();
        let proof = open(&committed, &source, &point, &setup, &mut Transcript::new(b"packed-scale-v1")).unwrap();
        let open_ms = open_started.elapsed().as_millis();
        trace("open", "end");
        trace("encode", "begin");
        let proof_bytes = pcs::encode(&proof).unwrap();
        trace("encode", "end");

        trace("verify", "begin");
        let verify_started = std::time::Instant::now();
        let mut verifier_transcript = Transcript::new(b"packed-scale-v1");
        pcs::bind_statement(&setup, &committed.commitment, &value.0, &point, &mut verifier_transcript).unwrap();
        dory_pcs::verify::<_, BN254, G1Routines, G2Routines, _>(
            committed.commitment.clone(), value, &point_ark, &proof, setup.verifier.clone(), &mut verifier_transcript,
        ).unwrap();
        let verify_ms = verify_started.elapsed().as_millis();
        trace("verify", "end");

        trace("reject_wrong_value", "begin");
        let mut wrong_transcript = Transcript::new(b"packed-scale-v1");
        let wrong_value = ArkFr(value.0 + Fr::from(1u64));
        pcs::bind_statement(&setup, &committed.commitment, &wrong_value.0, &point, &mut wrong_transcript).unwrap();
        assert!(dory_pcs::verify::<_, BN254, G1Routines, G2Routines, _>(
            committed.commitment.clone(), wrong_value, &point_ark, &proof, setup.verifier.clone(), &mut wrong_transcript,
        ).is_err(), "fresh verifier must reject a wrong packed evaluation");
        trace("reject_wrong_value", "end");

        println!("dory_packed_scale log_n={} bits={} file_bytes={} setup_ms={} commit_ms={} vector_product_ms={} evaluation_ms={} open_ms={} verify_ms={} proof_bytes={} setup_id={}",
            log_n, 1usize << log_n, bit_bytes, setup_ms, commit_ms, vector_product_ms, evaluation_ms, open_ms, verify_ms, proof_bytes.len(),
            setup.id.iter().map(|byte| format!("{byte:02x}")).collect::<String>());
        trace("cleanup", "begin");
        drop(source);
        std::fs::remove_file(path).unwrap();
        trace("cleanup", "end");
    }

    #[cfg(windows)]
    #[test]
    fn live_source_denies_concurrent_writer() {
        let path = temp_file(&[0x55]);
        let packed = PackedFile::open(&path, 3).unwrap();
        let writer = OpenOptions::new().write(true).open(&path);
        assert!(writer.is_err());
        assert!(std::fs::remove_file(&path).is_err());
        drop(packed);
        assert!(OpenOptions::new().write(true).open(&path).is_ok());
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn rejects_copy_bounds_and_wrong_point() {
        let path = temp_file(&[0x35]);
        let packed = PackedFile::open(&path, 3).unwrap();
        assert!(packed.read_copy(0, 0).is_err());
        assert!(packed.read_copy(3, 0).is_err());
        assert!(packed.read_copy(1 << 17, 0).is_err());
        assert!(packed.read_copy(4, 2).is_err());
        assert!(packed.evaluate(&[]).is_err());
        drop(packed);
        std::fs::remove_file(path).unwrap();
    }
}

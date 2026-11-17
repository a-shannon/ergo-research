//! Bounded producer/consumer join for the eleven code-owned compression banks.
use crate::{
    circuit::{self, CompressionInput},
    core_pool::Plan,
    gkr::{self, GkrError},
    packed::{self, PackedFile, PackedFileWriter},
    pcs, sparse,
    transcript::Transcript,
    verifier_key, work_tree_fixed_hash as fixed, work_tree_layout as layout,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use serde_json::json;
use std::{fs::OpenOptions, io::Write, time::Instant};

fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |out, (bit, x)| {
        out * if index >> bit & 1 == 1 {
            *x
        } else {
            Fr::one() - x
        }
    })
}

fn read_slot(source: &PackedFile, slot: usize) -> Result<Vec<Fr>, String> {
    let chunks = layout::WIDTH / layout::CORE;
    let first = slot
        .checked_mul(chunks)
        .ok_or("slot chunk index overflow")?;
    let mut values = Vec::with_capacity(layout::WIDTH);
    for chunk in 0..chunks {
        values.extend(source.read_copy(layout::CORE, first + chunk)?);
    }
    Ok(values)
}

fn packed_view_blake(bytes: &[u8]) -> String {
    use blake2::{Blake2b512, Digest};
    Blake2b512::digest(bytes).iter().map(|byte| format!("{byte:02X}")).collect()
}

const H2_BITS_BLAKE: &str = "C38B534BA44D657238ABA94ED1EA860AC8A448BDAFEE2476295F08CF04B995F97829390008C0FAF1E5BBACE8A8A886CA17FED34980BC9889CAE30A8127EAA623";
const H2_GKR_BLAKE: &str = "767797ABFBB15E8B25D130DFF1677AD5D256B2F5327A1B693FACA881F59FF27720023574E964ECB8B65C138A86EF522FE6D5B7956BB926B00CCDE765EBA9BCB0";

fn h2_golden_bytes(name:&str,size:usize,blake:&str)->Vec<u8> {
    use std::io::Read;
    let root=std::path::PathBuf::from(std::env::var_os("NIPOPOW_H2_GOLDEN_EVIDENCE").expect("bound golden fixture"));
    assert!(crate::preview_test_paths::absolute_outside_source(&root), "golden fixture directory must be absolute and outside source");
    assert!(matches!(name,"witness-main.bits"|"core-pool.gkr"));assert!(size<=524288);
    let md=std::fs::symlink_metadata(&root).unwrap();assert!(md.is_dir()&&!md.file_type().is_symlink());
    let path=root.join(name);let md=std::fs::symlink_metadata(&path).unwrap();assert!(md.is_file()&&!md.file_type().is_symlink());
    #[cfg(windows)] {use std::os::windows::fs::MetadataExt;
        assert_eq!(std::fs::symlink_metadata(&root).unwrap().file_attributes()&0x400,0);
        assert_eq!(md.file_attributes()&0x400,0);}
    let mut options=OpenOptions::new();options.read(true);
    #[cfg(windows)] {use std::os::windows::fs::OpenOptionsExt;options.share_mode(0);}
    let mut file=options.open(&path).unwrap();let before=file.metadata().unwrap();assert_eq!(before.len(),size as u64);
    let mut bytes=vec![0u8;size];assert_eq!(bytes.capacity(),size);file.read_exact(&mut bytes).unwrap();
    let mut tail=[0u8;1];assert_eq!(file.read(&mut tail).unwrap(),0);
    let after=file.metadata().unwrap();assert_eq!(before.len(),after.len());assert_eq!(before.modified().unwrap(),after.modified().unwrap());
    assert_eq!(packed_view_blake(&bytes),blake);bytes
}

#[test]
#[ignore]
fn spooled_four_owner_high_phases_match_archived_proof_and_pcs() {
    use crate::high_phase_spool;
    let started=Instant::now();
    let evidence=std::path::PathBuf::from(std::env::var_os("NIPOPOW_CORE_POOL_EVIDENCE").expect("bound integrated evidence"));
    assert!(crate::preview_test_paths::absolute_outside_source(&evidence), "integrated fixture directory must be absolute and outside source");
    assert!(std::fs::read_dir(&evidence).unwrap().next().is_none());
    // Full standalone assertion gate before any setup, commitment or whole proof.
    let preflight=high_phase_spool::combined_preflight(&evidence);
    assert_eq!((preflight.phase_cases,preflight.math_checks,preflight.codec_checks,preflight.negative_checks),(8,14,8,33));
    let preflight_seconds=started.elapsed().as_secs_f64();
    crate::core_pool_boolean::dense_dispatch_controls();
    let golden_bits=h2_golden_bytes("witness-main.bits",524288,H2_BITS_BLAKE);
    let golden_proof=h2_golden_bytes("core-pool.gkr",5024,H2_GKR_BLAKE);
    let plan=Plan::new(2).unwrap();let engine=fixed::engine().unwrap();
    let mut expected=vec![0u8;524288];assert_eq!(expected.capacity(),524288);
    // Literal original recipe:44 OLD compressions; f is not physical bank p(f).
    for owner in 0..4 {
        for (family,offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
            let mut block=[0u8;128];
            for (i,byte) in block.iter_mut().enumerate(){*byte=(family*37+i*11+owner*19)as u8;}
            let mut state=circuit::blake2b256_initial_state();
            for (i,word) in state.iter_mut().enumerate(){*word^=(family as u64)<<i;*word^=(owner as u64)<<(i+1);}
            let input=CompressionInput{state,block,counter:128+family as u64+owner as u64*4096,final_flag:true};
            let assigned=circuit::build_compression(Some(&input)).unwrap();
            assert_eq!(assigned.compiled.circuit,engine.core);assert_eq!(assigned.layout,engine.base.compression);
            let values=assigned.compiled.input.unwrap();assert_eq!(values.len(),65536);
            for (wire,value) in values.iter().enumerate(){assert!(value.is_zero()||value.is_one());
                if value.is_one(){let index=(owner<<20)+offset+wire;expected[index/8]|=1<<(index%8);}}
        }
        for bank in [8usize,9,10,12,15]{for wire in [7usize,19,43]{let index=(owner<<20)+(bank<<16)+wire;expected[index/8]|=1<<(index%8);}}
    }
    assert_eq!(expected,golden_bits);assert_eq!(packed_view_blake(&expected),H2_BITS_BLAKE);
    drop(golden_bits);
    let source=four_owner_write(&evidence.join("witness-main.bits"),&expected);
    let view=source.h2_boolean_view().unwrap();view.require_same_source(&source).unwrap();view.check_expected(&expected).unwrap();
    drop(expected);
    let tuple_math=four_owner_tuple_oracle(&plan,&engine.core);assert_eq!(tuple_math,109);
    let bits=view.read_copy(0).unwrap();let raw_math=crate::core_pool_boolean::packed_math_controls(&bits);assert_eq!(raw_math,89);drop(bits);
    let fixture_seconds=started.elapsed().as_secs_f64()-preflight_seconds;
    let setup_started=Instant::now();let setup=pcs::generate_setup(22).unwrap();
    let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();assert_eq!(key.id(),&setup.id);
    let setup_seconds=setup_started.elapsed().as_secs_f64();
    let commit_started=Instant::now();let committed=packed::commit(&source,&setup).unwrap();
    let commitment_bytes=pcs::encode_commitment(&committed.commitment).unwrap();let commitment_seconds=commit_started.elapsed().as_secs_f64();
    let transcript=||{let mut t=Transcript::new(b"core-pool-four-owner-packed-join-v1");t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"commitment",&commitment_bytes);t};
    let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
    // Decode and ordinary VERIFY archived proof before the new producer/opening.
    let golden_started=Instant::now();let golden=plan.decode(&golden_proof).unwrap();
    assert_eq!(golden.layers.len(),1);assert_eq!(golden.layers[0].rounds.len(),44);
    let mut golden_t=transcript();let golden_claim=plan.verify(&golden,&mut golden_t).unwrap();
    let golden_ledger=ledger(&golden_t);let mut next=golden_t.clone();let golden_next=next.challenge_scalar(b"before-pcs-continuation");
    let golden_verify_seconds=golden_started.elapsed().as_secs_f64();drop(golden);
    let mut real=high_phase_spool::RealEvidence::new(&evidence);
    let mut source_negatives=0;
    for wrong in [Plan::new(0).unwrap(),Plan::new(1).unwrap()]{
        let mut t=transcript();let before=ledger(&t);source.reset_io_metrics();
        assert_eq!(wrong.prove_packed_four_owners_spooled_for_test(&source,&mut real,&mut t).err().unwrap(),"packed four-owner production requires exact OLD h2");
        assert_eq!(ledger(&t),before);assert_eq!(source.io_metrics_snapshot().read_calls,0);source_negatives+=1;
    }
    source.reset_io_metrics();let producer_started=Instant::now();let mut producer=transcript();
    let (proof,claim)=plan.prove_packed_four_owners_spooled_for_test(&source,&mut real,&mut producer).unwrap();
    let producer_seconds=producer_started.elapsed().as_secs_f64();let io=source.io_metrics_snapshot();
    assert_eq!((io.read_calls,io.read_bytes),(92,12058624));
    let real_report=real.finish(); // release every real handle before PCS.
    let proof_bytes=gkr::encode_proof(&proof).unwrap();assert_eq!(proof_bytes.len(),5024);assert!(proof_bytes.capacity()<=65536);drop(proof);
    assert_eq!(proof_bytes,golden_proof);drop(golden_proof);assert_eq!(claim,golden_claim);assert_eq!(ledger(&producer),golden_ledger);
    let mut next=producer.clone();assert_eq!(next.challenge_scalar(b"before-pcs-continuation"),golden_next);
    let verifier_started=Instant::now();let decoded=plan.decode(&proof_bytes).unwrap();let mut verifier=transcript();
    assert_eq!(plan.verify(&decoded,&mut verifier).unwrap(),claim);assert_eq!(ledger(&producer),ledger(&verifier));
    let verifier_seconds=verifier_started.elapsed().as_secs_f64();
    let mut consumer_negatives=0;
    let mut round=decoded.clone();round.layers[0].rounds[0][0]+=Fr::one();assert_eq!(plan.verify(&round,&mut transcript()).err(),Some(GkrError::SumcheckIdentity));consumer_negatives+=1;drop(round);
    let mut line=decoded.clone();line.layers[0].line_coefficients[1]+=Fr::one();assert_eq!(plan.verify(&line,&mut transcript()).err(),Some(GkrError::LineEndpoints));consumer_negatives+=1;drop(line);
    assert_eq!(source.evaluate(&claim.point).unwrap(),claim.value);view.require_same_source(&source).unwrap();
    let opening_started=Instant::now();let opening=packed::open(&committed,&source,&claim.point,&setup,&mut producer).unwrap();
    let opening_bytes=pcs::encode_proof(&opening).unwrap();assert_eq!(opening_bytes.len(),29421);assert!(opening_bytes.capacity()<=65536);
    let decoded_opening=pcs::decode_proof(&opening_bytes,22).unwrap();let opening_seconds=opening_started.elapsed().as_secs_f64();
    let pcs_started=Instant::now();pcs::verify_admitted(committed.commitment,claim.value,&claim.point,&decoded_opening,&key,&mut verifier).unwrap();
    assert_eq!(ledger(&producer),ledger(&verifier));let mut p=producer.clone();let mut v=verifier.clone();assert_eq!(p.challenge_scalar(b"after-pcs-continuation"),v.challenge_scalar(b"after-pcs-continuation"));
    let pcs_seconds=pcs_started.elapsed().as_secs_f64();
    let mut wrong_value=transcript();plan.verify(&decoded,&mut wrong_value).unwrap();assert!(pcs::verify_admitted(committed.commitment,claim.value+Fr::one(),&claim.point,&decoded_opening,&key,&mut wrong_value).is_err());consumer_negatives+=1;
    let mut wrong_point=claim.point.clone();wrong_point[20]+=Fr::one();let mut t=transcript();plan.verify(&decoded,&mut t).unwrap();assert!(pcs::verify_admitted(committed.commitment,claim.value,&wrong_point,&decoded_opening,&key,&mut t).is_err());consumer_negatives+=1;drop(wrong_point);
    let mut drift=transcript();plan.verify(&decoded,&mut drift).unwrap();drift.append_bytes(b"pcs-continuation-drift",b"one-fault");assert!(pcs::verify_admitted(committed.commitment,claim.value,&claim.point,&decoded_opening,&key,&mut drift).is_err());consumer_negatives+=1;
    assert_eq!((source_negatives,consumer_negatives),(2,5));
    let mut report=json!({"schema":"private-initial-stream-h2-join-v1","scope":"OLD h2 GKR/PCS22 fixture only",
        "copy_bits":2,"logical_owners":4,"physical_banks":16,"selected_banks":11,"input_log":22,"row_log":23,"commitment_log":22,
        "witness_bytes":524288,"witness_blake2b512":H2_BITS_BLAKE,"gkr_bytes":proof_bytes.len(),"gkr_blake2b512":packed_view_blake(&proof_bytes),
        "dory_bytes":opening_bytes.len(),"packed_owner_loads":io.read_calls,"packed_read_bytes":io.read_bytes,
        "source_negatives":source_negatives,"consumer_negatives":consumer_negatives,"tuple_math":tuple_math,"raw_math":raw_math});
    let tail=json!({"preflight_seconds":preflight_seconds,"fixture_seconds":fixture_seconds,"setup_seconds":setup_seconds,
        "commitment_seconds":commitment_seconds,"golden_verify_seconds":golden_verify_seconds,"producer_seconds":producer_seconds,
        "verifier_seconds":verifier_seconds,"opening_seconds":opening_seconds,"pcs_seconds":pcs_seconds,"total_before_report_seconds":started.elapsed().as_secs_f64(),
        "preflight":preflight,"real":real_report,"proof_claim_ledger_equal":true,"continuation_equal":true,"same_source_pcs_verified":true,
        "historical_generic_oracle":true,"gkr_proof_created":true,"pcs_proof_created":true,"setup_invoked":true,"global_admission":false,
        "dense_dispatch_verified":true});
    let serde_json::Value::Object(fields)=tail else{unreachable!("join report")};
    for (key,value) in fields {assert!(report.as_object_mut().unwrap().insert(key,value).is_none());}
    let summary=serde_json::to_vec(&report).unwrap();assert!(summary.len()<=16384&&summary.capacity()<=32768);
    println!("\nhigh_phase_initial_stream_h2_join {}",std::str::from_utf8(&summary).unwrap());
    for (name,bytes) in [("core-pool.gkr",proof_bytes),("core-pool.dory",opening_bytes),("join-summary.json",summary)] {
        let mut f=OpenOptions::new().create_new(true).write(true).open(evidence.join(name)).unwrap();f.write_all(&bytes).unwrap();f.sync_all().unwrap();
    }
}

// OLD artifacts were paired and SHA256-verified before root added these dual
// fingerprints. They also detect a bug shared by both refactored producers.
const OLD_H0_BITS_BLAKE: &str = "A790D856C8BCFDFF4D47E56B921C9DB62DD1E3265EB1271D654D1A80C9B33B8838E2AAA7974A18586C086BBE7C2FACB3FFFEA2C219723ADC61B51F0AD936C143";
const OLD_H0_GKR_BLAKE: &str = "D8DC77760ED66E810FA3F336183987B3F1E1677DAB99550C0556612DB482BE679BCE7F7EE7281596E6E0D9A746FAB98E26CA01B6845F633E75FFC23F305E0855";

fn packed_view_write(path: &std::path::Path, bytes: &[u8]) -> PackedFile {
    assert_eq!(bytes.len(), 524288);
    let mut writer = PackedFileWriter::create_new(path, 22).unwrap();
    writer.write_bytes(bytes).unwrap();
    let source = writer.finish().unwrap();
    source.h0_boolean_view().unwrap().check_expected(bytes).unwrap();
    source
}

/// Addresses follow compression_program's allocation order: two initial XOR
/// words, 96 G operations of six ADD65/four XOR64, then sixteen final XOR64.
/// Compare the cursor and outputs against the actual frozen source layout.
fn packed_view_advice_faults(layout: &circuit::CompressionLayout) -> Vec<(&'static str, usize)> {
    let first_xor = 1602;
    let mut cursor = first_xor + 128;
    let first_sum = cursor;
    let first_carry = first_sum + 64;
    let mut last_sum = 0;
    for _ in 0..96 {
        for is_add in [true, true, false, true, false, true, true, false, true, false] {
            if is_add { last_sum = cursor; cursor += 65; } else { cursor += 64; }
        }
    }
    assert_eq!(cursor, 63746);
    for word in 0..8 {
        cursor += 64;
        assert_eq!(layout.output[word][0], cursor);
        assert_eq!(layout.output[word][63], cursor + 63);
        cursor += 64;
    }
    assert_eq!(cursor, layout.used_input_len);
    assert_eq!(cursor, 64770);
    vec![("padding-last", 65535), ("add-carry-first", first_carry),
        ("sum-first", first_sum), ("sum-last", last_sum + 63),
        ("xor-first", first_xor), ("xor-last", layout.output[7][63]),
        ("upper-output", layout.output[7][0])]
}

#[test]
fn packed_boolean_view_matches_fr_proof_and_admitted_pcs() {
    std::thread::Builder::new().name("packed-boolean-view-join".into())
        .stack_size(32 * 1024 * 1024).spawn(run_packed_boolean_view_join).unwrap().join().unwrap();
}

fn run_packed_boolean_view_join() {
    let started = Instant::now();
    let evidence = std::path::PathBuf::from(std::env::var_os("NIPOPOW_CORE_POOL_EVIDENCE")
        .expect("packed Boolean join requires controller-bound evidence directory"));
    assert!(evidence.is_absolute());
    assert!(crate::preview_test_paths::absolute_outside_source(&evidence), "fixture directory must be absolute and outside source");
    assert_eq!(evidence.file_name().and_then(|x| x.to_str()), Some("evidence"));
    assert!(!evidence.components().any(|x| matches!(x, std::path::Component::ParentDir)));
    assert!(evidence.is_dir());
    assert_eq!(std::mem::size_of::<Fr>(), 32);
    let engine = fixed::engine().unwrap();
    let plan = Plan::new(0).unwrap();
    assert_eq!((plan.input_log(), plan.row_log(), plan.term_count()), (20, 21, 1897280));

    // Identical OLD h0 input recipe/packing as run_join97-136, including f vs
    // physical p(f). Keep the original builder as the compatibility oracle.
    let mut bytes = vec![0u8; layout::WIDTH / 8];
    for (bank, offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
        let mut block = [0u8; 128];
        for (i, byte) in block.iter_mut().enumerate() { *byte = (bank * 37 + i * 11) as u8; }
        let mut state = circuit::blake2b256_initial_state();
        for (i, word) in state.iter_mut().enumerate() { *word ^= (bank as u64) << i; }
        let input = CompressionInput { state, block, counter: 128 + bank as u64, final_flag: true };
        let assigned = circuit::build_compression(Some(&input)).unwrap();
        assert_eq!(assigned.compiled.circuit, engine.core);
        assert_eq!(assigned.layout, engine.base.compression);
        let values = assigned.compiled.input.unwrap();
        assert_eq!(values.len(), layout::CORE);
        for (wire, value) in values.iter().enumerate() {
            assert!(value.is_zero() || value.is_one());
            if value.is_one() { let global = offset + wire; bytes[global / 8] |= 1 << (global % 8); }
        }
    }
    for bank in [8, 9, 10, 12, 15] {
        for wire in [7, 19, 43] {
            let global = bank * layout::CORE + wire; bytes[global / 8] |= 1 << (global % 8);
        }
    }
    let mut expected = Vec::with_capacity(524288);
    expected.extend_from_slice(&bytes);
    expected.resize(524288, 0);
    drop(bytes);
    assert_eq!(expected.capacity(), 524288);
    let witness_blake = packed_view_blake(&expected);
    assert_eq!(witness_blake, OLD_H0_BITS_BLAKE);
    let source = packed_view_write(&evidence.join("witness-main.bits"), &expected);
    let view = source.h0_boolean_view().unwrap();
    view.require_same_source(&source).unwrap();
    // Compare again under the retained lock before ANY scalar/binding. The
    // full expected snapshot is independently bound to the OLD artifact hash.
    view.check_expected(&expected).unwrap();
    let snapshot_seconds = started.elapsed().as_secs_f64();

    let mut source_negatives = 0usize;
    for copy in [1, usize::MAX] { assert_eq!(view.read_copy(copy).err().unwrap(), "packed Boolean logical owner range"); source_negatives += 1; }
    let bits = view.read_copy(0).unwrap();
    assert_eq!(bits.len(), 1048576);
    assert_eq!(bits.capacity_bytes(), 131072);
    for (bank, local) in [(16, 0), (0, 65536), (usize::MAX, 0)] { assert!(bits.bit(bank, local).is_err()); source_negatives += 1; }
    for fault in [packed::PackedReaderFault::Short, packed::PackedReaderFault::Io] {
        assert!(view.reader_fault_for_test(fault).err().unwrap().starts_with("packed Boolean owner read:"));
        source_negatives += 1;
    }
    for bank in 0..16 {
        for local in 0..65536 {
            let index = bank * 65536 + local;
            assert_eq!(bits.bit(bank, local).unwrap(), expected[index / 8] >> (index % 8) & 1 != 0);
        }
    }
    let math_checks = crate::core_pool_boolean::packed_math_controls(&bits);
    assert_eq!(math_checks, 89);
    drop(bits);
    assert_eq!(view.check_expected(&expected[..524287]).err().unwrap(), "packed Boolean snapshot extent");
    source_negatives += 1;
    let mut extra = expected.clone(); extra.push(0);
    assert_eq!(view.check_expected(&extra).err().unwrap(), "packed Boolean snapshot extent");
    source_negatives += 1; drop(extra);
    let mut mismatch = expected.clone(); mismatch[0] ^= 1;
    let before_read = source.io_metrics_snapshot();
    let snapshot_t = Transcript::new(b"snapshot-before-challenge");
    let snapshot_ledger = (snapshot_t.challenges(), snapshot_t.raw_queries(), snapshot_t.bytes_absorbed());
    assert_eq!(view.check_expected(&mismatch).err().unwrap(), "packed Boolean snapshot mismatch");
    assert!(source.io_metrics_snapshot().read_calls > before_read.read_calls);
    assert_eq!((snapshot_t.challenges(), snapshot_t.raw_queries(), snapshot_t.bytes_absorbed()), snapshot_ledger);
    source_negatives += 1; drop(mismatch);
    let detached = packed_view_write(&evidence.join("detached-copy.bits"), &expected);
    assert_eq!(view.require_same_source(&detached).err().unwrap(), "packed Boolean detached source");
    source_negatives += 1; drop(detached);
    for (name, content) in [("short.bits", expected[..524287].to_vec()), ("extra.bits", {
        let mut x = expected.clone(); x.push(0); x
    })] {
        let path = evidence.join(name);
        let mut file = OpenOptions::new().create_new(true).write(true).open(&path).unwrap();
        file.write_all(&content).unwrap(); file.sync_all().unwrap(); drop(file);
        assert!(PackedFile::open(&path, 22).is_err()); source_negatives += 1;
    }
    let wrong_width_path = evidence.join("wrong-width.bits");
    let mut writer = PackedFileWriter::create_new(&wrong_width_path, 21).unwrap();
    writer.write_bytes(&expected[..262144]).unwrap();
    let wrong_width = writer.finish().unwrap();
    assert_eq!(wrong_width.h0_boolean_view().err().unwrap(), "packed Boolean source requires exact TEST22 extent");
    source_negatives += 1;
    assert!(OpenOptions::new().write(true).open(evidence.join("witness-main.bits")).is_err());
    source_negatives += 1;
    assert!(std::fs::remove_file(evidence.join("witness-main.bits")).is_err());
    source_negatives += 1;
    assert_eq!(source_negatives, 16);

    let setup_started = Instant::now();
    let setup = pcs::generate_setup(22).unwrap();
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    assert_eq!(key.id(), &setup.id);
    let setup_seconds = setup_started.elapsed().as_secs_f64();
    let commit_started = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap();
    let commitment_seconds = commit_started.elapsed().as_secs_f64();
    // EXACT original domain and prefix: legacy proof bytes must match too.
    let transcript = || {
        let mut t = Transcript::new(b"core-pool-single-slot-join-v1");
        t.append_bytes(b"setup-id", &setup.id); t.append_bytes(b"commitment", &commitment_bytes); t
    };
    let ledger = |t: &Transcript| (t.challenges(), t.raw_queries(), t.bytes_absorbed());
    let mut factory_negatives = 0usize;
    let mut bad_t = transcript(); let before = ledger(&bad_t); source.reset_io_metrics();
    assert_eq!(Plan::new(1).unwrap().prove_packed_boolean_for_test(&source, &mut bad_t).err().unwrap(),
        "packed core-pool production is admitted only for exact OLD h0");
    assert_eq!(ledger(&bad_t), before); assert_eq!(source.io_metrics_snapshot().read_calls, 0);
    factory_negatives += 1;
    let mut bad_t = transcript(); let before = ledger(&bad_t); wrong_width.reset_io_metrics();
    assert!(plan.prove_packed_boolean_for_test(&wrong_width, &mut bad_t).is_err());
    assert_eq!(ledger(&bad_t), before); assert_eq!(wrong_width.io_metrics_snapshot().read_calls, 0);
    factory_negatives += 1; drop(wrong_width);

    let mut faults = vec![("sentinel-first-bank", layout::CORE_OFFSETS[0]),
        ("sentinel-last-bank", layout::CORE_OFFSETS[10])];
    for (name, wire) in packed_view_advice_faults(&engine.base.compression) { faults.push((name, wire)); }
    assert_eq!(faults.len(), 9);
    let mut residual_negatives = 0usize;
    for (case, (name, wire)) in faults.iter().copied().enumerate() {
        assert!(wire < 1048576);
        let mut mutant = expected.clone(); mutant[wire / 8] ^= 1 << (wire % 8);
        assert_ne!(mutant, expected);
        let mutant_source = packed_view_write(&evidence.join(format!("mutant-{case:02}.bits")), &mutant);
        drop(mutant);
        let mut packed_t = transcript(); let initial = ledger(&packed_t);
        let packed_error = plan.prove_packed_boolean_for_test(&mutant_source, &mut packed_t).err().unwrap();
        assert_eq!(packed_error, GkrError::NonzeroOutput.to_string(), "{name}");
        assert_eq!(ledger(&packed_t), initial);
        let mut dense_t = transcript();
        let dense_error = plan.prove_boolean_for_test(|copy| read_slot(&mutant_source, copy), &mut dense_t).err().unwrap();
        assert_eq!(dense_error, packed_error, "original residual predicate: {name}");
        assert_eq!(ledger(&dense_t), initial);
        residual_negatives += 1;
    }
    for (case, bank_swap) in [(9usize, true), (10usize, false)] {
        let mut mutant = expected.clone();
        if bank_swap {
            for byte in 0..8192 { mutant.swap(11 * 8192 + byte, 8 * 8192 + byte); }
        } else { for byte in &mut mutant[..131072] { *byte = byte.reverse_bits(); } }
        assert_ne!(mutant, expected);
        let mutant_source = packed_view_write(&evidence.join(format!("mutant-{case:02}.bits")), &mutant);
        drop(mutant);
        let mut packed_t = transcript(); let initial = ledger(&packed_t);
        let packed_error = plan.prove_packed_boolean_for_test(&mutant_source, &mut packed_t).err().unwrap();
        assert_eq!(packed_error, GkrError::NonzeroOutput.to_string()); assert_eq!(ledger(&packed_t), initial);
        let mut dense_t = transcript();
        assert_eq!(plan.prove_boolean_for_test(|copy| read_slot(&mutant_source, copy), &mut dense_t).err().unwrap(), packed_error);
        assert_eq!(ledger(&dense_t), initial); residual_negatives += 1;
    }
    assert_eq!(residual_negatives, 11);
    let mut dense_negatives = 0usize;
    for bank in [8, 9, 10, 12, 15] {
        let mut values = read_slot(&source, 0).unwrap(); values[bank * 65536 + 7] = Fr::from(2u64);
        let mut bad_t = transcript(); let before = ledger(&bad_t);
        let mut values = Some(values);
        let error = plan.prove_boolean_for_test(|_| Ok(values.take().unwrap()), &mut bad_t).err().unwrap();
        assert_eq!(error, format!("non-Boolean input at copy 0, coordinate {}", bank * 65536 + 7));
        assert_eq!(ledger(&bad_t), before); dense_negatives += 1;
    }
    let mut bad_t = transcript(); let before = ledger(&bad_t);
    assert_eq!(plan.prove_boolean_for_test(|_| Ok(vec![Fr::zero(); 1048575]), &mut bad_t).err().unwrap(),
        GkrError::InvalidInputWidth.to_string());
    assert_eq!(ledger(&bad_t), before); dense_negatives += 1;

    source.reset_io_metrics();
    let golden_started = Instant::now();
    let golden_loads = std::cell::Cell::new(0usize);
    let mut golden_t = transcript();
    let (golden, golden_claim) = plan.prove_boolean_for_test(|copy| {
        golden_loads.set(golden_loads.get() + 1); read_slot(&source, copy)
    }, &mut golden_t).unwrap();
    let golden_seconds = golden_started.elapsed().as_secs_f64();
    let golden_io = source.io_metrics_snapshot();
    let golden_bytes = gkr::encode_proof(&golden).unwrap();
    assert_eq!(golden_loads.get(), 21); assert_eq!(golden_io.read_calls, 336); assert_eq!(golden_io.read_bytes, 2752512);
    assert_eq!(golden_bytes.len(), 4576); assert!(golden_bytes.capacity() <= 65536);
    assert_eq!(packed_view_blake(&golden_bytes), OLD_H0_GKR_BLAKE);
    drop(golden);
    source.reset_io_metrics();
    let packed_started = Instant::now(); let mut packed_t = transcript();
    let (proof, claim) = plan.prove_packed_boolean_for_test(&source, &mut packed_t).unwrap();
    let packed_seconds = packed_started.elapsed().as_secs_f64();
    let packed_io = source.io_metrics_snapshot();
    assert_eq!(packed_io.read_calls, 21); assert_eq!(packed_io.read_bytes, 2752512);
    let proof_bytes = gkr::encode_proof(&proof).unwrap();
    assert_eq!(proof_bytes, golden_bytes); assert_eq!(packed_view_blake(&proof_bytes), OLD_H0_GKR_BLAKE);
    assert_eq!(claim, golden_claim); assert_eq!(ledger(&packed_t), ledger(&golden_t));
    let mut next_golden = golden_t.clone(); let mut next_packed = packed_t.clone();
    assert_eq!(next_golden.challenge_scalar(b"before-pcs-continuation"), next_packed.challenge_scalar(b"before-pcs-continuation"));
    drop(golden_bytes); drop(golden_t);
    let decoded = plan.decode(&proof_bytes).unwrap();
    let verifier_started = Instant::now(); let mut verifier = transcript();
    assert_eq!(plan.verify(&decoded, &mut verifier).unwrap(), claim);
    assert_eq!(ledger(&verifier), ledger(&packed_t));
    let verifier_seconds = verifier_started.elapsed().as_secs_f64();
    let mut proof_negatives = 0usize;
    let mut round_fault = decoded.clone(); round_fault.layers[0].rounds[0][0] += Fr::one();
    assert_eq!(plan.verify(&round_fault, &mut transcript()).err(), Some(GkrError::SumcheckIdentity)); proof_negatives += 1;
    let derivative = std::cell::Cell::new(Fr::zero());
    gkr::verify_with_wiring(&[plan.input_log()], plan.row_count(), &decoded, &mut transcript(),
        |t| plan.bind(t), |_, r, u, v| {
            let w = plan.coefficients(r, u, v)?; derivative.set(w[2] + w[3] * decoded.layers[0].left_value); Ok(w)
        }).unwrap();
    assert!(!derivative.get().is_zero());
    let mut right_fault = decoded.clone(); right_fault.layers[0].right_value += Fr::one();
    assert_eq!(plan.verify(&right_fault, &mut transcript()).err(), Some(GkrError::TerminalExpression)); proof_negatives += 1;
    let mut line_fault = decoded.clone(); line_fault.layers[0].line_coefficients[1] += Fr::one();
    assert_eq!(plan.verify(&line_fault, &mut transcript()).err(), Some(GkrError::LineEndpoints)); proof_negatives += 1;
    let mut codec_negatives = 0usize;
    assert!(plan.decode(&proof_bytes[..proof_bytes.len() - 1]).is_err()); codec_negatives += 1;
    let mut extra = proof_bytes.clone(); extra.push(0); assert!(plan.decode(&extra).is_err()); codec_negatives += 1; drop(extra);
    let mut point = claim.point.clone(); point.resize(22, Fr::zero());
    assert_eq!(source.evaluate(&point).unwrap(), claim.value);
    let open_started = Instant::now();
    let opening = packed::open(&committed, &source, &point, &setup, &mut packed_t).unwrap();
    let opening_bytes = pcs::encode_proof(&opening).unwrap();
    assert_eq!(opening_bytes.len(), 29421); assert!(opening_bytes.capacity() <= 65536);
    let decoded_opening = pcs::decode_proof(&opening_bytes, 22).unwrap();
    let opening_seconds = open_started.elapsed().as_secs_f64();
    let pcs_started = Instant::now();
    pcs::verify_admitted(committed.commitment, claim.value, &point, &decoded_opening, &key, &mut verifier).unwrap();
    assert_eq!(ledger(&packed_t), ledger(&verifier));
    let mut next_prover = packed_t.clone(); let mut next_verifier = verifier.clone();
    assert_eq!(next_prover.challenge_scalar(b"after-pcs-continuation"), next_verifier.challenge_scalar(b"after-pcs-continuation"));
    let pcs_verify_seconds = pcs_started.elapsed().as_secs_f64();
    let mut wrong_value_t = transcript(); plan.verify(&decoded, &mut wrong_value_t).unwrap();
    assert!(pcs::verify_admitted(committed.commitment, claim.value + Fr::one(), &point,
        &decoded_opening, &key, &mut wrong_value_t).is_err());
    let pcs_negatives = 1usize;
    let negative_cases = source_negatives + factory_negatives + residual_negatives + dense_negatives
        + proof_negatives + codec_negatives + pcs_negatives;
    assert_eq!(negative_cases, 41);
    let mut report = json!({
        "scope": "OLD h0 eleven-bank packed Boolean producer; no headers or historical admission",
        "copy_bits": 0, "logical_owners": 1, "physical_pcs_owners": 4,
        "input_log": 20, "row_log": 21, "commitment_log": 22,
        "selected_banks": 11, "physical_banks": 16, "core_terms": 172480,
        "global_terms": 1897280, "witness_bytes": 524288, "witness_blake2b512": witness_blake,
        "gkr_bytes": proof_bytes.len(), "gkr_blake2b512": packed_view_blake(&proof_bytes), "dory_bytes": opening_bytes.len(),
        "fixture_and_snapshot_seconds": snapshot_seconds,
        "setup_seconds": setup_seconds, "commitment_seconds": commitment_seconds,
        "golden_fr_seconds": golden_seconds, "packed_seconds": packed_seconds,
        "verifier_seconds": verifier_seconds, "opening_seconds": opening_seconds,
        "pcs_verify_seconds": pcs_verify_seconds, "total_before_report_seconds": started.elapsed().as_secs_f64(),
    });
    let report_tail = json!({
        "golden_owner_loads": golden_loads.get(), "packed_owner_loads": packed_io.read_calls,
        "golden_read_bytes": golden_io.read_bytes, "packed_read_bytes": packed_io.read_bytes,
        "raw_fr_decodings_removed": 22020096, "raw_owner_capacity_bytes": 131072,
        "packed_line_initial_capacity_bound_bytes": 33554432, "expected_capacity_bytes": expected.capacity(),
        "math_checks": math_checks, "negative_cases": negative_cases,
        "source_negatives": source_negatives, "factory_negatives": factory_negatives,
        "residual_negatives": residual_negatives, "dense_negatives": dense_negatives,
        "proof_negatives": proof_negatives, "codec_negatives": codec_negatives, "pcs_negatives": pcs_negatives,
        "legacy_fingerprints_equal": true, "proof_claim_ledger_equal": true,
        "same_source_pcs_verified": true, "global_admission": false, "result": "pass"
    });
    let serde_json::Value::Object(tail_fields) = report_tail else {
        unreachable!("join report tail is an object");
    };
    report.as_object_mut().expect("join report is an object").extend(tail_fields);
    assert_eq!(report.as_object().unwrap().len(), 47);
    // Capture parsers may see libtest's unfinished pending header. This single
    // operation places the closed diagnostic at column zero after all checks.
    println!("\ncore_pool_packed_view_join {report}");
    for (name, content) in [("core-pool.gkr", proof_bytes), ("core-pool.dory", opening_bytes),
        ("packed-view-join.json", serde_json::to_vec_pretty(&report).unwrap())] {
        let mut file = OpenOptions::new().create_new(true).write(true).open(evidence.join(name)).unwrap();
        file.write_all(&content).unwrap(); file.sync_all().unwrap();
    }
}

fn four_owner_write(path: &std::path::Path, bytes: &[u8]) -> PackedFile {
    assert_eq!(bytes.len(), 524288);
    let mut writer = PackedFileWriter::create_new(path, 22).unwrap();
    writer.write_bytes(bytes).unwrap();
    let source = writer.finish().unwrap();
    source.h2_boolean_view().unwrap().check_expected(bytes).unwrap();
    source
}

/// Independent LSB table construction, checked at literal selected indices.
fn four_owner_basis(point: &[Fr]) -> Vec<Fr> {
    let mut table = vec![Fr::one()];
    for coordinate in point {
        let old = table.len();
        table.resize(2 * old, Fr::zero());
        for i in 0..old {
            let value = table[i];
            table[i] = value * (Fr::one() - coordinate);
            table[i + old] = value * coordinate;
        }
    }
    for i in [0, 1, table.len() / 2, table.len() - 1] { assert_eq!(table[i], eq(point, i)); }
    table
}

fn four_owner_tuple_oracle(plan: &Plan, core: &sparse::Circuit) -> usize {
    let r: Vec<_> = (0..23).map(|i| Fr::from((2 * i + 3) as u64)).collect();
    let u: Vec<_> = (0..22).map(|i| Fr::from((3 * i + 5) as u64)).collect();
    let v: Vec<_> = (0..22).map(|i| Fr::from((5 * i + 7) as u64)).collect();
    let wr = four_owner_basis(&r[..17]);
    let wu = four_owner_basis(&u[..16]);
    let wv = four_owner_basis(&v[..16]);
    let mut local = [Fr::zero(); 4];
    for term in &core.terms {
        let scale = wr[term.row] * wu[term.gate.left] * wv[term.gate.right];
        for (sum, c) in local.iter_mut().zip([term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]) { *sum += scale * c; }
    }
    drop(wr); drop(wu); drop(wv);
    let physical = [0usize, 1, 2, 3, 4, 5, 6, 7, 11, 13, 14];
    assert_eq!(layout::CORE_OFFSETS.map(|x| x / 65536), physical);
    let mut factor = Fr::zero();
    for owner in 0..4 {
        for (family, bank) in physical.iter().copied().enumerate() {
            factor += eq(&r[17..19], owner) * eq(&r[19..], family)
                * eq(&u[16..20], bank) * eq(&u[20..], owner)
                * eq(&v[16..20], bank) * eq(&v[20..], owner);
        }
    }
    assert_eq!(plan.coefficients(&r, &u, &v).unwrap(), local.map(|x| x * factor));
    let mut checks = 1usize;
    for owner in 0..4 {
        for family in [0usize, 8, 10] {
            for term_index in [0usize, core.terms.len() - 1] {
                let term = &core.terms[term_index];
                let row = term.row + (owner << 17) + (family << 19);
                let left = term.gate.left + (physical[family] << 16) + (owner << 20);
                let right = term.gate.right + (physical[family] << 16) + (owner << 20);
                assert!(row < 1 << 23 && left < 1 << 22 && right < 1 << 22);
                let literal = eq(&r, row) * eq(&u, left) * eq(&v, right);
                let decomposed = eq(&r[..17], term.row) * eq(&r[17..19], owner) * eq(&r[19..], family)
                    * eq(&u[..16], term.gate.left) * eq(&u[16..20], physical[family]) * eq(&u[20..], owner)
                    * eq(&v[..16], term.gate.right) * eq(&v[16..20], physical[family]) * eq(&v[20..], owner);
                assert_eq!(literal, decomposed);
                // Independent coordinate mutations, including formal axes.
                assert_ne!(literal, eq(&r, row) * eq(&u, left) * eq(&v, (right & ((1 << 20) - 1)) + (((owner + 1) % 4) << 20)));
                assert_ne!(literal, eq(&r, row) * eq(&u, left ^ (1 << 20)) * eq(&v, right));
                if family == 8 {
                    // Selected ordinal8 is physical bank11. Mutate each
                    // formal wire axis separately against the fixed mapping.
                    let ordinal_left = term.gate.left + (8 << 16) + (owner << 20);
                    let ordinal_right = term.gate.right + (8 << 16) + (owner << 20);
                    assert_ne!(literal, eq(&r, row) * eq(&u, ordinal_left) * eq(&v, right));
                    assert_ne!(literal, eq(&r, row) * eq(&u, left) * eq(&v, ordinal_right));
                    checks += 2;
                }
                let swapped_row = term.row + (family << 17) + (owner << 21);
                if swapped_row != row {
                    assert_ne!(literal, eq(&r, swapped_row) * eq(&u, left) * eq(&v, right));
                    checks += 1;
                }
                checks += 3;
            }
        }
    }
    // Owner0/family0 is identical under row-axis interchange: it contributes
    // the positive tuple identity, never a vacuous negative assertion.
    checks
}

#[test]
fn packed_boolean_four_owners_match_generic_proof_and_admitted_pcs() {
    std::thread::Builder::new().name("packed-boolean-four-owner-join".into())
        .stack_size(32 * 1024 * 1024).spawn(run_packed_boolean_four_owner_join).unwrap().join().unwrap();
}

fn run_packed_boolean_four_owner_join() {
    let started = Instant::now();
    let evidence = std::path::PathBuf::from(std::env::var_os("NIPOPOW_CORE_POOL_EVIDENCE")
        .expect("four-owner join requires controller-bound evidence"));
    assert!(evidence.is_absolute());
    assert!(crate::preview_test_paths::absolute_outside_source(&evidence), "fixture directory must be absolute and outside source");
    assert_eq!(evidence.file_name().and_then(|x| x.to_str()), Some("evidence"));
    assert!(!evidence.components().any(|x| matches!(x, std::path::Component::ParentDir)));
    assert!(evidence.is_dir());
    assert_eq!(std::mem::size_of::<Fr>(), 32);
    let engine = fixed::engine().unwrap(); let plan = Plan::new(2).unwrap();
    assert_eq!((plan.input_log(), plan.row_log(), plan.term_count()), (22, 23, 7589120));
    let mut expected = vec![0u8; 524288]; assert_eq!(expected.capacity(), 524288);
    for owner in 0..4 {
        for (family, offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
            let mut block = [0u8; 128];
            for (i, byte) in block.iter_mut().enumerate() { *byte = (family * 37 + i * 11 + owner * 19) as u8; }
            let mut state = circuit::blake2b256_initial_state();
            for (i, word) in state.iter_mut().enumerate() { *word ^= (family as u64) << i; *word ^= (owner as u64) << (i + 1); }
            let input = CompressionInput { state, block, counter: 128 + family as u64 + owner as u64 * 4096, final_flag: true };
            let assigned = circuit::build_compression(Some(&input)).unwrap();
            assert_eq!(assigned.compiled.circuit, engine.core); assert_eq!(assigned.layout, engine.base.compression);
            let values = assigned.compiled.input.unwrap(); assert_eq!(values.len(), 65536);
            for (wire, value) in values.iter().enumerate() {
                assert!(value.is_zero() || value.is_one());
                if value.is_one() { let index = (owner << 20) + offset + wire; expected[index / 8] |= 1 << (index % 8); }
            }
        }
        for bank in [8usize, 9, 10, 12, 15] {
            for wire in [7usize, 19, 43] { let index = (owner << 20) + (bank << 16) + wire; expected[index / 8] |= 1 << (index % 8); }
        }
    }
    for owner in 0..4 { for other in 0..owner { assert_ne!(&expected[owner * 131072..(owner + 1) * 131072], &expected[other * 131072..(other + 1) * 131072]); } }
    let source = four_owner_write(&evidence.join("witness-main.bits"), &expected);
    let view = source.h2_boolean_view().unwrap(); view.require_same_source(&source).unwrap(); view.check_expected(&expected).unwrap();
    let mut source_negatives = 0usize;
    source.reset_io_metrics();
    for owner in [4usize, usize::MAX] { assert_eq!(view.read_copy(owner).err().unwrap(), "packed four-owner logical range"); source_negatives += 1; }
    assert_eq!(source.io_metrics_snapshot().read_calls, 0);
    for owner in 0..4 {
        let bits = view.read_copy(owner).unwrap(); assert_eq!((bits.len(), bits.capacity_bytes()), (1048576, 131072));
        for bank in 0..16 { for wire in [0usize, 7, 19, 43, 65535] {
            let index = (owner << 20) + (bank << 16) + wire;
            assert_eq!(bits.bit(bank, wire).unwrap(), expected[index / 8] >> (index % 8) & 1 != 0);
        } }
        for fault in [packed::PackedReaderFault::Short, packed::PackedReaderFault::Io] {
            assert!(view.reader_fault_for_test(owner, fault).err().unwrap().starts_with("packed four-owner read:")); source_negatives += 1;
        }
    }
    assert_eq!(view.check_expected(&expected[..524287]).err().unwrap(), "packed Boolean snapshot extent"); source_negatives += 1;
    let mut extra = expected.clone(); extra.push(0);
    assert_eq!(view.check_expected(&extra).err().unwrap(), "packed Boolean snapshot extent"); source_negatives += 1; drop(extra);
    let detached = four_owner_write(&evidence.join("detached-copy.bits"), &expected);
    assert_eq!(view.require_same_source(&detached).err().unwrap(), "packed four-owner detached source"); source_negatives += 1; drop(detached);
    for (name, content) in [("short.bits", expected[..524287].to_vec()), ("extra.bits", { let mut x = expected.clone(); x.push(0); x })] {
        let mut file = OpenOptions::new().create_new(true).write(true).open(evidence.join(name)).unwrap(); file.write_all(&content).unwrap(); file.sync_all().unwrap();
        assert!(PackedFile::open(evidence.join(name), 22).is_err()); source_negatives += 1;
    }
    let mut wrong_writer = PackedFileWriter::create_new(evidence.join("wrong-width.bits"), 21).unwrap(); wrong_writer.write_bytes(&vec![0u8; 262144]).unwrap();
    let wrong = wrong_writer.finish().unwrap(); assert!(wrong.h2_boolean_view().is_err()); source_negatives += 1;
    let mut mapping_negatives = 0usize;
    // Fixed expected-source snapshot detects these isolated mappings, not an
    // assertion that the relation rejects every permutation of valid owners.
    for fault in 0..5 {
        let mut mutant = expected.clone();
        match fault {
            0 => { for i in 0..131072 { mutant.swap(131072 + i, 262144 + i); } }
            1 => { for i in 0..131072 { mutant.swap(i, 393216 + i); } }
            2 => mutant[393216..].fill(0),
            3 => { let first = expected[..131072].to_vec(); mutant[393216..].copy_from_slice(&first); }
            _ => mutant[0] ^= 1,
        }
        assert_ne!(mutant, expected);
        assert_eq!(view.check_expected(&mutant).err().unwrap(), "packed Boolean snapshot mismatch"); mapping_negatives += 1;
    }
    let mut math_checks = four_owner_tuple_oracle(&plan, &engine.core);
    let bits = view.read_copy(0).unwrap(); math_checks += crate::core_pool_boolean::packed_math_controls(&bits); drop(bits);
    let snapshot_seconds = started.elapsed().as_secs_f64();
    let setup_started = Instant::now(); let setup = pcs::generate_setup(22).unwrap();
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap(); assert_eq!(key.id(), &setup.id);
    let setup_seconds = setup_started.elapsed().as_secs_f64();
    let commit_started = Instant::now(); let committed = packed::commit(&source, &setup).unwrap();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap(); let commitment_seconds = commit_started.elapsed().as_secs_f64();
    let transcript = || { let mut t = Transcript::new(b"core-pool-four-owner-packed-join-v1"); t.append_bytes(b"setup-id", &setup.id); t.append_bytes(b"commitment", &commitment_bytes); t };
    let ledger = |t: &Transcript| (t.challenges(), t.raw_queries(), t.bytes_absorbed());
    for bad_plan in [Plan::new(0).unwrap(), Plan::new(1).unwrap()] {
        let mut t = transcript(); let initial = ledger(&t); source.reset_io_metrics();
        assert_eq!(bad_plan.prove_packed_four_owners_for_test(&source, &mut t).err().unwrap(), "packed four-owner production requires exact OLD h2");
        assert_eq!(ledger(&t), initial); assert_eq!(source.io_metrics_snapshot().read_calls, 0); source_negatives += 1;
    }
    let mut t = transcript(); let initial = ledger(&t); wrong.reset_io_metrics();
    assert!(plan.prove_packed_four_owners_for_test(&wrong, &mut t).is_err()); assert_eq!(ledger(&t), initial); assert_eq!(wrong.io_metrics_snapshot().read_calls, 0); source_negatives += 1; drop(wrong);
    let advice = packed_view_advice_faults(&engine.base.compression);
    let mut residual_faults = Vec::with_capacity(24);
    for owner in 0..4 {
        // Six distinct source/definition classes for EACH genuine owner. The
        // OLD cursor helper also checks last SUM/XOR/padding coordinates; the
        // unchanged h0 aggregate's first/last/padding predicates are reused.
        for (name, local) in [
            ("sentinel", 0usize), ("state-source", 1usize),
            ("sum-first", advice[2].1), ("add-carry-first", advice[1].1),
            ("xor-first", advice[4].1), ("upper-output", advice[6].1),
        ] { residual_faults.push((name, (owner << 20) + local)); }
    }
    assert_eq!(residual_faults.len(), 24);
    let mut residual_negatives = 0usize;
    for (case, (name, wire)) in residual_faults.iter().copied().enumerate() {
        let mut mutant = expected.clone();
        mutant[wire / 8] ^= 1 << (wire % 8);
        assert_ne!(mutant, expected);
        let bad = four_owner_write(&evidence.join(format!("residual-{case:02}.bits")), &mutant); drop(mutant);
        let mut p = transcript(); let initial = ledger(&p);
        assert_eq!(plan.prove_packed_four_owners_for_test(&bad, &mut p).err().unwrap(), GkrError::NonzeroOutput.to_string(), "{name} owner {}", wire >> 20); assert_eq!(ledger(&p), initial);
        let mut g = transcript(); assert_eq!(plan.prove_four_owner_reference_for_test(|owner| read_slot(&bad, owner), &mut g).err().unwrap(), GkrError::NonzeroOutput.to_string(), "{name} owner {}", wire >> 20); assert_eq!(ledger(&g), initial);
        residual_negatives += 1;
    }
    // Dense Boolean admission stays stricter than a generic Fr relation on
    // unconstrained excluded banks. Test this unchanged wrapper separately.
    for owner in 0..4 {
        let mut t = transcript(); let initial = ledger(&t);
        let error = crate::core_pool_boolean::prove_with_copy_bits_for_test(&engine.core, 4, &[0,1,2,3,4,5,6,7,11,13,14], 2,
            |copy| { let mut x = read_slot(&source, copy)?; if copy == owner { x[8 * 65536 + 7] = Fr::from(2u64); } Ok(x) },
            &mut t, |t| plan.bind(t), |r,u,v| plan.coefficients(r,u,v).map_err(|e| e.to_string())).err().unwrap();
        assert_eq!(error, format!("non-Boolean input at copy {owner}, coordinate {}", 8 * 65536 + 7)); assert_eq!(ledger(&t), initial); source_negatives += 1;
    }
    // Fail early on the candidate, before the slower independent reference.
    // Both algorithms drop all witness/coefficient tables on return; retain
    // only the encoded proof, claim and transcript across their lifetimes.
    source.reset_io_metrics(); let packed_started = Instant::now(); let mut packed_t = transcript();
    let (proof, claim) = plan.prove_packed_four_owners_for_test(&source, &mut packed_t).unwrap();
    let packed_seconds = packed_started.elapsed().as_secs_f64(); let packed_io = source.io_metrics_snapshot();
    assert_eq!((packed_io.read_calls, packed_io.read_bytes), (84, 11010048));
    let proof_bytes = gkr::encode_proof(&proof).unwrap(); assert_eq!(proof_bytes.len(), 5024); assert!(proof_bytes.capacity() <= 65536); drop(proof);
    let verifier_started = Instant::now(); let mut verifier = transcript();
    let early_decoded = plan.decode(&proof_bytes).unwrap();
    assert_eq!(plan.verify(&early_decoded, &mut verifier).unwrap(), claim); assert_eq!(ledger(&verifier), ledger(&packed_t));
    let verifier_seconds = verifier_started.elapsed().as_secs_f64(); drop(early_decoded);
    let generic_started = Instant::now(); let loads = std::cell::Cell::new(0usize); source.reset_io_metrics();
    let mut generic_t = transcript();
    let (golden, golden_claim) = plan.prove_four_owner_reference_for_test(|owner| { loads.set(loads.get() + 1); read_slot(&source, owner) }, &mut generic_t).unwrap();
    let generic_seconds = generic_started.elapsed().as_secs_f64(); let generic_io = source.io_metrics_snapshot();
    assert_eq!((loads.get(), generic_io.read_calls, generic_io.read_bytes), (180, 2880, 23592960));
    let golden_bytes = gkr::encode_proof(&golden).unwrap(); assert_eq!(golden_bytes.len(), 5024); assert!(golden_bytes.capacity() <= 65536); drop(golden);
    assert_eq!(proof_bytes, golden_bytes); assert_eq!(claim, golden_claim); assert_eq!(ledger(&packed_t), ledger(&generic_t));
    let mut gp = generic_t.clone(); let mut pp = packed_t.clone(); assert_eq!(gp.challenge_scalar(b"before-pcs-continuation"), pp.challenge_scalar(b"before-pcs-continuation"));
    drop(golden_bytes); drop(generic_t);
    let decoded = plan.decode(&proof_bytes).unwrap();
    let mut consumer_negatives = 0usize;
    for fault in 0..4 {
        let rejected = gkr::verify_with_wiring(&[22], plan.row_count(), &decoded, &mut transcript(), |t| plan.bind(t), |_,r,u,v| {
            let mut rr = r.to_vec(); let mut uu = u.to_vec(); let mut vv = v.to_vec();
            match fault { 0 => uu.swap(20,21), 1 => vv[20] = Fr::one() - vv[20], 2 => rr.swap(17,19), _ => uu[16] = Fr::one() - uu[16] }
            let wrong = plan.coefficients(&rr,&uu,&vv)?; let correct = plan.coefficients(r,u,v)?;
            let l = decoded.layers[0].left_value; let rv = decoded.layers[0].right_value;
            let expression = |w: [Fr;4]| w[0]+w[1]*l+w[2]*rv+w[3]*l*rv;
            assert_ne!(expression(wrong), expression(correct)); Ok(wrong)
        });
        assert_eq!(rejected.err(), Some(GkrError::TerminalExpression)); consumer_negatives += 1;
    }
    let mut round = decoded.clone(); round.layers[0].rounds[0][0] += Fr::one(); assert_eq!(plan.verify(&round, &mut transcript()).err(), Some(GkrError::SumcheckIdentity)); consumer_negatives += 1;
    let mut line = decoded.clone(); line.layers[0].line_coefficients[1] += Fr::one(); assert_eq!(plan.verify(&line, &mut transcript()).err(), Some(GkrError::LineEndpoints)); consumer_negatives += 1;
    assert!(plan.decode(&proof_bytes[..proof_bytes.len()-1]).is_err()); consumer_negatives += 1;
    let mut extra = proof_bytes.clone(); extra.push(0); assert!(plan.decode(&extra).is_err()); consumer_negatives += 1; drop(extra);
    assert_eq!(claim.point.len(), 22); assert_eq!(source.evaluate(&claim.point).unwrap(), claim.value);
    view.require_same_source(&source).unwrap();
    let opening_started = Instant::now(); let opening = packed::open(&committed, &source, &claim.point, &setup, &mut packed_t).unwrap();
    let opening_bytes = pcs::encode_proof(&opening).unwrap(); assert_eq!(opening_bytes.len(), 29421); assert!(opening_bytes.capacity() <= 65536);
    let decoded_opening = pcs::decode_proof(&opening_bytes, 22).unwrap(); let opening_seconds = opening_started.elapsed().as_secs_f64();
    let pcs_started = Instant::now(); pcs::verify_admitted(committed.commitment, claim.value, &claim.point, &decoded_opening, &key, &mut verifier).unwrap();
    assert_eq!(ledger(&packed_t), ledger(&verifier));
    let mut p = packed_t.clone(); let mut v = verifier.clone(); assert_eq!(p.challenge_scalar(b"after-pcs-continuation"), v.challenge_scalar(b"after-pcs-continuation"));
    let pcs_seconds = pcs_started.elapsed().as_secs_f64();
    let mut wrong_value = transcript(); plan.verify(&decoded, &mut wrong_value).unwrap();
    assert!(pcs::verify_admitted(committed.commitment, claim.value + Fr::one(), &claim.point, &decoded_opening, &key, &mut wrong_value).is_err()); consumer_negatives += 1;
    let mut wrong_point = claim.point.clone(); wrong_point[20] += Fr::one();
    let mut point_verifier = transcript(); plan.verify(&decoded, &mut point_verifier).unwrap();
    assert!(pcs::verify_admitted(committed.commitment, claim.value, &wrong_point, &decoded_opening, &key, &mut point_verifier).is_err()); consumer_negatives += 1;
    drop(wrong_point);
    let mut drifted_verifier = transcript(); plan.verify(&decoded, &mut drifted_verifier).unwrap();
    drifted_verifier.append_bytes(b"pcs-continuation-drift", b"one-fault");
    assert!(pcs::verify_admitted(committed.commitment, claim.value, &claim.point, &decoded_opening, &key, &mut drifted_verifier).is_err()); consumer_negatives += 1;
    let mut report = json!({
        "scope":"OLD h2 pooled compression fixture; no header/MAX/global admission", "copy_bits":2,
        "logical_owners":4, "input_log":22, "row_log":23, "commitment_log":22,
        "selected_banks":11, "physical_banks":16, "global_terms":7589120,
        "witness_bytes":524288, "witness_blake2b512":packed_view_blake(&expected),
        "gkr_bytes":proof_bytes.len(), "gkr_blake2b512":packed_view_blake(&proof_bytes), "dory_bytes":opening_bytes.len(),
        "generic_owner_loads":loads.get(), "packed_owner_loads":packed_io.read_calls,
        "generic_read_calls":generic_io.read_calls, "generic_read_bytes":generic_io.read_bytes,
        "packed_read_bytes":packed_io.read_bytes, "generic_returned_fr_coordinates":188743680u64,
    });
    let tail = json!({
        "generic_returned_fr_bytes":6039797760u64, "fixture_and_controls_seconds":snapshot_seconds,
        "setup_seconds":setup_seconds, "commitment_seconds":commitment_seconds,
        "generic_seconds":generic_seconds, "packed_seconds":packed_seconds,
        "verifier_seconds":verifier_seconds, "opening_seconds":opening_seconds, "pcs_verify_seconds":pcs_seconds,
        "total_before_report_seconds":started.elapsed().as_secs_f64(), "math_checks":math_checks,
        "negative_cases":source_negatives+mapping_negatives+residual_negatives+consumer_negatives,
        "source_negatives":source_negatives, "mapping_negatives":mapping_negatives,
        "residual_negatives":residual_negatives, "consumer_negatives":consumer_negatives,
        "proof_claim_ledger_equal":true, "same_source_pcs_verified":true,
        "generic_reference_independent":true, "global_admission":false, "result":"pass",
    });
    let serde_json::Value::Object(fields) = tail else { unreachable!("report object"); };
    let object = report.as_object_mut().unwrap(); for (key,value) in fields { assert!(object.insert(key,value).is_none()); }
    println!("\ncore_pool_packed_four_owner_join {report}");
    for (name, bytes) in [("core-pool.gkr",proof_bytes),("core-pool.dory",opening_bytes),("four-owner-join.json",serde_json::to_vec_pretty(&report).unwrap())] {
        let mut file = OpenOptions::new().create_new(true).write(true).open(evidence.join(name)).unwrap(); file.write_all(&bytes).unwrap(); file.sync_all().unwrap();
    }
}

#[test]
fn pooled_real_compressions_bind_one_claim_to_admitted_pcs() {
    std::thread::Builder::new()
        .name("core-pool-bounded-join".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(|| run_join(Alternative::Replay))
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pooled_boolean_compressions_match_cached_proof_and_admitted_pcs() {
    std::thread::Builder::new()
        .name("core-pool-boolean-join".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(|| run_join(Alternative::Boolean))
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pooled_boolean_two_slots_match_reference_and_admitted_pcs() {
    std::thread::Builder::new()
        .name("core-pool-two-slot-join".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(|| run_join(Alternative::TwoSlots))
        .unwrap()
        .join()
        .unwrap();
}

#[derive(Clone, Copy)]
enum Alternative {
    Replay,
    Boolean,
    TwoSlots,
}

fn run_join(mode: Alternative) {
    let started = Instant::now();
    let evidence = std::env::var_os("NIPOPOW_CORE_POOL_EVIDENCE")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let witness_path = evidence.join(format!("core-pool-{}-{nonce}.bits", std::process::id()));
    let engine = fixed::engine().unwrap();
    let slots = if matches!(mode, Alternative::TwoSlots) {
        2
    } else {
        1
    };
    let copy_bits = if slots == 2 { 1 } else { 0 };
    let plan = Plan::new(copy_bits).unwrap();
    let mut witness_slots = Vec::with_capacity(slots);
    for slot in 0..slots {
        let mut bytes = vec![0u8; layout::WIDTH / 8];
        for (bank, offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
            let mut block = [0u8; 128];
            for (i, byte) in block.iter_mut().enumerate() {
                *byte = (bank * 37 + i * 11 + slot * 19) as u8;
            }
            let mut state = circuit::blake2b256_initial_state();
            for (i, word) in state.iter_mut().enumerate() {
                *word ^= (bank as u64) << i;
                *word ^= (slot as u64) << (i + 1);
            }
            let input = CompressionInput {
                state,
                block,
                counter: 128 + bank as u64 + (slot as u64) * 4096,
                final_flag: true,
            };
            let assigned = circuit::build_compression(Some(&input)).unwrap();
            assert_eq!(assigned.compiled.circuit, engine.core);
            assert_eq!(assigned.layout, engine.base.compression);
            let values = assigned.compiled.input.unwrap();
            assert_eq!(values.len(), layout::CORE);
            for (wire, value) in values.iter().enumerate() {
                assert!(value.is_zero() || value.is_one());
                if value.is_one() {
                    let global = offset + wire;
                    bytes[global / 8] |= 1 << (global % 8);
                }
            }
        }
        // Excluded physical-bank bits are committed and checked for both real
        // slots, while padding slots remain all zero.
        for bank in [8, 9, 10, 12, 15] {
            for wire in [7, 19, 43] {
                let global = bank * layout::CORE + wire;
                bytes[global / 8] |= 1 << (global % 8);
            }
        }
        witness_slots.push(bytes);
    }
    if slots == 2 {
        assert_ne!(witness_slots[0], witness_slots[1]);
    }
    let mut writer = PackedFileWriter::create_new(&witness_path, 22).unwrap();
    for bytes in &witness_slots {
        writer.write_bytes(bytes).unwrap();
    }
    let zero_slot = vec![0u8; layout::WIDTH / 8];
    for _ in slots..4 {
        writer.write_bytes(&zero_slot).unwrap();
    }
    let source = writer.finish().unwrap();
    let witness_seconds = started.elapsed().as_secs_f64();
    let setup_started = Instant::now();
    let setup = pcs::generate_setup(22).unwrap();
    let key =
        verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    assert_eq!(key.id(), &setup.id);
    let setup_seconds = setup_started.elapsed().as_secs_f64();
    let commit_started = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap();
    let commitment_seconds = commit_started.elapsed().as_secs_f64();
    let transcript = || {
        let mut t = Transcript::new(b"core-pool-single-slot-join-v1");
        t.append_bytes(b"setup-id", &setup.id);
        t.append_bytes(b"commitment", &commitment_bytes);
        t
    };
    let prove_started = Instant::now();
    let mut prover = transcript();
    let cached_loads = std::cell::Cell::new(0usize);
    let (proof, claim, reference_passes) = match mode {
        Alternative::TwoSlots => {
            let (proof, claim, passes) = plan
                .prove_two_slot_reference_for_test(
                    |copy| {
                        cached_loads.set(cached_loads.get() + 1);
                        read_slot(&source, copy)
                    },
                    &mut prover,
                )
                .unwrap();
            (proof, claim, Some(passes))
        }
        _ => {
            let (proof, claim) = plan
                .prove(
                    |copy| {
                        cached_loads.set(cached_loads.get() + 1);
                        read_slot(&source, copy)
                    },
                    &mut prover,
                )
                .unwrap();
            (proof, claim, None)
        }
    };
    let producer_seconds = prove_started.elapsed().as_secs_f64();
    let proof_bytes = gkr::encode_proof(&proof).unwrap();
    let decoded = plan.decode(&proof_bytes).unwrap();
    let verify_started = Instant::now();
    let mut verifier = transcript();
    let checked = plan.verify(&decoded, &mut verifier).unwrap();
    let verifier_seconds = verify_started.elapsed().as_secs_f64();
    assert_eq!(checked, claim);
    assert_eq!(claim.point.len(), plan.input_log());
    let ledger = |t: &Transcript| (t.challenges(), t.raw_queries(), t.bytes_absorbed());
    assert_eq!(ledger(&prover), ledger(&verifier));
    let replay_loads = std::cell::Cell::new(0usize);
    let mut replay_transcript = transcript();
    let replay_started = Instant::now();
    let load = |copy| {
        replay_loads.set(replay_loads.get() + 1);
        read_slot(&source, copy)
    };
    let (replay_proof, replay_claim, replay_passes) = match mode {
        Alternative::Replay => plan
            .prove_replay_for_test(load, &mut replay_transcript)
            .unwrap(),
        Alternative::Boolean => {
            let (p, c) = plan
                .prove_boolean_for_test(load, &mut replay_transcript)
                .unwrap();
            (p, c, 0)
        }
        Alternative::TwoSlots => {
            let (p, c) = plan
                .prove_boolean_two_slots_for_test(load, &mut replay_transcript)
                .unwrap();
            (p, c, 0)
        }
    };
    let replay_seconds = replay_started.elapsed().as_secs_f64();
    assert_eq!(gkr::encode_proof(&replay_proof).unwrap(), proof_bytes);
    assert_eq!(replay_claim, claim);
    assert_eq!(ledger(&replay_transcript), ledger(&prover));
    let mut cached_next = prover.clone();
    let mut replay_next = replay_transcript.clone();
    assert_eq!(
        cached_next.challenge_scalar(b"before-pcs-continuation"),
        replay_next.challenge_scalar(b"before-pcs-continuation")
    );
    let forbidden_loads = std::cell::Cell::new(0usize);
    let forbidden_plan = Plan::new(if slots == 2 { 0 } else { 1 }).unwrap();
    let forbidden_load = |copy| {
        forbidden_loads.set(forbidden_loads.get() + 1);
        read_slot(&source, copy)
    };
    let mut forbidden_t = transcript();
    let forbidden_initial = ledger(&forbidden_t);
    let forbidden = match mode {
        Alternative::Replay => forbidden_plan
            .prove_replay_for_test(forbidden_load, &mut forbidden_t)
            .map(|_| ()),
        Alternative::Boolean => forbidden_plan
            .prove_boolean_for_test(forbidden_load, &mut forbidden_t)
            .map(|_| ()),
        Alternative::TwoSlots => forbidden_plan
            .prove_boolean_two_slots_for_test(forbidden_load, &mut forbidden_t)
            .map(|_| ()),
    };
    assert!(forbidden.is_err());
    assert_eq!(forbidden_loads.get(), 0);
    assert_eq!(ledger(&forbidden_t), forbidden_initial);
    let mut global_point = claim.point.clone();
    global_point.resize(22, Fr::zero());
    assert_eq!(source.evaluate(&global_point).unwrap(), claim.value);
    let open_started = Instant::now();
    let opening = packed::open(&committed, &source, &global_point, &setup, &mut prover).unwrap();
    let opening_bytes = pcs::encode_proof(&opening).unwrap();
    let decoded_opening = pcs::decode_proof(&opening_bytes, 22).unwrap();
    let opening_seconds = open_started.elapsed().as_secs_f64();
    let opening_verify_started = Instant::now();
    pcs::verify_admitted(
        committed.commitment,
        claim.value,
        &global_point,
        &decoded_opening,
        &key,
        &mut verifier,
    )
    .unwrap();
    let opening_verify_seconds = opening_verify_started.elapsed().as_secs_f64();
    assert_eq!(ledger(&prover), ledger(&verifier));
    assert_eq!(
        prover.challenge_scalar(b"continuation"),
        verifier.challenge_scalar(b"continuation")
    );

    // Each bank's constrained input zero is changed alone. The producer must
    // reject before it can emit a proof; the immutable committed file stays fixed.
    let producer_bank_mutants = if matches!(mode, Alternative::TwoSlots) {
        for slot in 0..2 {
            for offset in layout::CORE_OFFSETS {
                let mut input = read_slot(&source, slot).unwrap();
                assert!(input[offset].is_zero());
                input[offset] = Fr::one();
                let mut bad_t = transcript();
                let original = bad_t.clone();
                let result = plan.prove_boolean_two_slots_for_test(
                    |copy| {
                        if copy == slot {
                            Ok(input.clone())
                        } else {
                            read_slot(&source, copy)
                        }
                    },
                    &mut bad_t,
                );
                assert_eq!(result.err().unwrap(), GkrError::NonzeroOutput.to_string());
                assert_eq!(ledger(&bad_t), ledger(&original));
            }
        }
        22
    } else {
        for offset in layout::CORE_OFFSETS {
            let mut input = read_slot(&source, 0).unwrap();
            assert!(input[offset].is_zero());
            input[offset] = Fr::one();
            let mut bad_t = transcript();
            let original = bad_t.clone();
            let result = match mode {
                Alternative::Replay => plan.prove(|_| Ok(input.clone()), &mut bad_t),
                Alternative::Boolean => {
                    plan.prove_boolean_for_test(|_| Ok(input.clone()), &mut bad_t)
                }
                Alternative::TwoSlots => unreachable!(),
            };
            assert_eq!(result.err().unwrap(), GkrError::NonzeroOutput.to_string());
            assert_eq!(ledger(&bad_t), ledger(&original));
        }
        11
    };

    // Boolean specialization validates every excluded physical bank too.
    let non_boolean_excluded_bank_negatives = if matches!(mode, Alternative::Boolean) {
        for bank in [8, 9, 10, 12, 15] {
            let mut input = read_slot(&source, 0).unwrap();
            input[bank * layout::CORE + 7] = Fr::from(2u64);
            let mut bad_t = transcript();
            let original = bad_t.clone();
            assert!(plan
                .prove_boolean_for_test(|_| Ok(input.clone()), &mut bad_t)
                .is_err());
            assert_eq!(ledger(&bad_t), ledger(&original));
        }
        5
    } else if matches!(mode, Alternative::TwoSlots) {
        for slot in 0..2 {
            for bank in [8, 9, 10, 12, 15] {
                let mut input = read_slot(&source, slot).unwrap();
                input[bank * layout::CORE + 7] = Fr::from(2u64);
                let mut bad_t = transcript();
                let original = bad_t.clone();
                assert!(plan
                    .prove_boolean_two_slots_for_test(
                        |copy| {
                            if copy == slot {
                                Ok(input.clone())
                            } else {
                                read_slot(&source, copy)
                            }
                        },
                        &mut bad_t,
                    )
                    .is_err());
                assert_eq!(ledger(&bad_t), ledger(&original));
            }
        }
        10
    } else {
        0
    };

    if matches!(mode, Alternative::TwoSlots) {
        let rejected_plan = Plan::new(2).unwrap();
        let calls = std::cell::Cell::new(0usize);
        let mut bad_t = transcript();
        let original = bad_t.clone();
        assert!(rejected_plan
            .prove_boolean_two_slots_for_test(
                |_| {
                    calls.set(calls.get() + 1);
                    Err("copy-bits admission should precede loading".into())
                },
                &mut bad_t,
            )
            .is_err());
        assert_eq!(calls.get(), 0);
        assert_eq!(ledger(&bad_t), ledger(&original));

        let reference_calls = std::cell::Cell::new(0usize);
        let mut bad_reference_t = transcript();
        let original_reference = bad_reference_t.clone();
        assert!(rejected_plan
            .prove_two_slot_reference_for_test(
                |_| {
                    reference_calls.set(reference_calls.get() + 1);
                    Err("copy-bits admission should precede loading".into())
                },
                &mut bad_reference_t,
            )
            .is_err());
        assert_eq!(reference_calls.get(), 0);
        assert_eq!(ledger(&bad_reference_t), ledger(&original_reference));
    }

    // All wrong callbacks keep the original statement binding and proof. They
    // isolate omitted bank families and incorrect physical bank selectors.
    let core_shape = sparse::validate(&engine.core, 0).unwrap();
    let terminal_callback_mutants = if matches!(mode, Alternative::TwoSlots) {
        14
    } else {
        13
    };
    for mutant in 0..terminal_callback_mutants {
        let wrong = gkr::verify_with_wiring(
            &[plan.input_log()],
            plan.row_count(),
            &decoded,
            &mut transcript(),
            |t| plan.bind(t),
            |_, r, u, v| {
                let base = sparse::wiring(&engine.core, &core_shape, &r[..17], &u[..16], &v[..16])?;
                let family_start = 17 + plan.copy_bits();
                let mut selector = Fr::zero();
                for (family, offset) in layout::CORE_OFFSETS.iter().copied().enumerate() {
                    if mutant < 11 && family == mutant {
                        continue;
                    }
                    let bank = if mutant == 11 && family == 8 {
                        layout::CORE_OFFSETS[9] / layout::CORE
                    } else if mutant == 11 && family == 9 {
                        layout::CORE_OFFSETS[8] / layout::CORE
                    } else {
                        offset / layout::CORE
                    };
                    let right = if mutant == 12 {
                        Fr::one()
                    } else {
                        eq(&v[16..20], bank)
                    };
                    selector += eq(&r[family_start..family_start + 4], family)
                        * eq(&u[16..20], bank)
                        * right;
                }
                let mut factor = selector;
                if plan.copy_bits() == 1 && mutant != 13 {
                    let slot_factor = (0..plan.copy_bits()).fold(Fr::one(), |acc, bit| {
                        let (row, left, right) = (r[17 + bit], u[20 + bit], v[20 + bit]);
                        acc * ((Fr::one() - row) * (Fr::one() - left) * (Fr::one() - right)
                            + row * left * right)
                    });
                    factor *= slot_factor;
                }
                Ok(base.map(|coefficient| coefficient * factor))
            },
        );
        assert_eq!(
            wrong.err(),
            Some(GkrError::TerminalExpression),
            "callback {mutant}"
        );
    }
    let mut changed = decoded.clone();
    changed.layers[0].rounds[0][0] += Fr::one();
    assert!(plan.verify(&changed, &mut transcript()).is_err());
    assert!(Plan::new(if slots == 2 { 0 } else { 1 })
        .unwrap()
        .verify(&decoded, &mut transcript())
        .is_err());
    assert!(plan.decode(&proof_bytes[..proof_bytes.len() - 1]).is_err());
    let mut extended = proof_bytes.clone();
    extended.push(0);
    assert!(plan.decode(&extended).is_err());
    for mutate_point in 0..if slots == 2 { 3 } else { 2 } {
        let mut point = global_point.clone();
        let mut value = claim.value;
        if mutate_point == 0 {
            point[16] += Fr::one();
        } else if mutate_point == 1 && slots == 2 {
            point[21] += Fr::one();
        } else {
            value += Fr::one();
        }
        let mut bad_t = transcript();
        plan.verify(&decoded, &mut bad_t).unwrap();
        assert!(pcs::verify_admitted(
            committed.commitment,
            value,
            &point,
            &decoded_opening,
            &key,
            &mut bad_t
        )
        .is_err());
    }
    let cost = plan.cost_report().unwrap();
    if slots == 2 {
        assert_eq!(
            (plan.input_log(), plan.row_log(), plan.term_count()),
            (21, 22, 3_794_560)
        );
        assert_eq!(cost.cache_bound_bytes, 674_238_928);
        assert!(cost.cache_bound_bytes > 512 * 1024 * 1024);
        assert_eq!(proof_bytes.len(), (7 * 21 + 3) * 32);
    }
    let report = json!({
        "scope": if slots == 2 { "two artificial compression slots, eleven banks per slot; no headers, PoW, history, or production admission" } else { "one compression slot, eleven banks; no header semantics, PoW or historical producer qualification" },
        "real_slots": slots, "padding_slots": 4 - slots,
        "input_log": plan.input_log(), "row_log": plan.row_log(), "commitment_log": 22,
        "global_terms": plan.term_count(), "cache_bound_bytes": cost.cache_bound_bytes,
        "default_cache_cap_bytes": 512 * 1024 * 1024,
        "gkr_bytes": proof_bytes.len(), "dory_bytes": opening_bytes.len(),
        "witness_seconds": witness_seconds, "setup_seconds": setup_seconds,
        "commitment_seconds": commitment_seconds, "producer_seconds": producer_seconds,
        "reference_seconds": if slots == 2 { Some(producer_seconds) } else { None },
        "reference_slot_loads": if slots == 2 { Some(cached_loads.get()) } else { None },
        "forced_replay_seconds": if matches!(mode, Alternative::Replay) { Some(replay_seconds) } else { None },
        "forced_replay_emitter_passes": if matches!(mode, Alternative::Replay) { Some(replay_passes) } else { None },
        "baseline": if slots == 2 { "default_cap_stream_reference" } else { "h0_cached_producer" },
        "baseline_slot_loads": cached_loads.get(),
        "cached_slot_loads": if slots == 2 { None } else { Some(cached_loads.get()) },
        "stream_reference_emitter_passes": reference_passes,
        "forced_replay_slot_loads": if matches!(mode, Alternative::Replay) { Some(replay_loads.get()) } else { None },
        "alternative": if matches!(mode, Alternative::Replay) { "forced_replay" } else if slots == 2 { "two_slot_boolean_kernel" } else { "shared_boolean_kernel" },
        "alternative_seconds": replay_seconds, "alternative_slot_loads": replay_loads.get(),
        "alternative_parity": "exact GKR bytes, claim, transcript counters and next challenge before one shared PCS continuation",
        "alternative_admission_negatives": if slots == 2 { 3 } else { 1 },
        "non_boolean_excluded_bank_negatives": non_boolean_excluded_bank_negatives,
        "verifier_seconds": verifier_seconds, "opening_seconds": opening_seconds,
        "opening_verify_seconds": opening_verify_seconds,
        "producer_bank_mutants": producer_bank_mutants, "terminal_callback_mutants": terminal_callback_mutants,
        "proof_and_dimension_negatives": 4, "pcs_negatives": if slots == 2 { 3 } else { 2 },
        "transcript_continuation": "equal", "result": "pass"
    });
    println!("core_pool_bounded_join {report}");
    if std::env::var_os("NIPOPOW_CORE_POOL_EVIDENCE").is_some() {
        for (name, content) in [
            ("core-pool.gkr", proof_bytes),
            ("core-pool.dory", opening_bytes),
            (
                "bounded-join.json",
                serde_json::to_vec_pretty(&report).unwrap(),
            ),
        ] {
            let mut f = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(evidence.join(name))
                .unwrap();
            f.write_all(&content).unwrap();
            f.sync_all().unwrap();
        }
    }
}

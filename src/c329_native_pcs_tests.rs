use super::*;
use crate::{
    daa_history_roster::OwnerClass,
    packed::PackedFileWriter,
    packed_owner_assembly::{NativeOwnerProducer, NativePcsFault, NativePcsFaultKind,
        NativePcsSource, NativePrefix},
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

fn fixture() -> (NativePrefix, WorkTreeHistoryPlan) {
    let pack: serde_json::Value = serde_json::from_str(include_str!(
        "../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"
    )).unwrap();
    let raws = (0..3).map(|i| {
        let hex = pack["networks"]["mainnet"]["source_headers_hex"][i].as_str().unwrap();
        Ok(hex.as_bytes().chunks_exact(2).map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap()
        }).collect())
    });
    let input = NativePrefix::from_raw_iter(3, raws).unwrap();
    let plan = WorkTreeHistoryPlan::compile(3, 2, input.root(), input.total_be28()).unwrap();
    (input, plan)
}

fn point_for_bit(index: usize) -> Vec<Fr> {
    (0..22).map(|bit| Fr::from(((index >> bit) & 1) as u64)).collect()
}

fn ledger(t: &Transcript) -> (u64, u64, u64) {
    (t.challenges(), t.raw_queries(), t.bytes_absorbed())
}

#[test]
fn complete_n3_native_pcs_matches_file_and_rejects_each_drifting_pass() {
    let (input, plan) = fixture();
    let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
    let native_source = NativePcsSource::new(&producer).unwrap();
    let setup = pcs::generate_setup(22).unwrap();
    let native = packed::commit_native(&native_source, &setup).unwrap();
    assert_eq!(native_source.pass_count_for_test(), 1);
    assert_eq!(native.packed().rows.len(), 2048);

    let path = std::env::temp_dir().join(format!(
        "c329-native-pcs-{}-{}.bits", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let mut writer = PackedFileWriter::create_new(&path, 22).unwrap();
    let mut plain_digest = Blake2b512::new();
    for owner in 0..4 {
        let row = producer.produce(owner).unwrap();
        assert_eq!(row.owner(), owner);
        if owner == 0 { assert_eq!(row.class(), OwnerClass::Genesis); }
        if owner == 3 { assert_eq!(row.class(), OwnerClass::Padding); }
        plain_digest.update(row.packed_bytes());
        writer.write_bytes(row.packed_bytes()).unwrap();
    }
    let packed_source = writer.finish().unwrap();
    let owner3 = producer.produce(3).unwrap();
    assert!(owner3.packed_bytes().iter().any(|byte| *byte != 0));
    for local in 0..512 {
        let selected = packed_source.read_row_bits(2048, 1536 + local).unwrap();
        assert_eq!(selected.as_slice(), &owner3.packed_bytes()[local * 256..(local + 1) * 256]);
    }
    let packed_commit = packed::commit(&packed_source, &setup).unwrap();
    assert_eq!(native.packed().rows, packed_commit.rows);
    assert_eq!(native.commitment(), packed_commit.commitment);

    let positions = [0, 1, 8191, 65536, (1 << 20) + 17, (2 << 20) + 255, (3 << 20) + 8191];
    let claims = std::array::from_fn(|j| {
        let point = point_for_bit(positions[j]);
        let row = positions[j] / 2048;
        let column = positions[j] % 2048;
        let bytes = packed_source.read_row_bits(2048, row).unwrap();
        let value = Fr::from(((bytes[column / 8] >> (column % 8)) & 1) as u64);
        Claim { point, value }
    });
    assert_eq!(packed_source.evaluate(&claims[4].point).unwrap(), claims[4].value);
    let statement = Statement { log_n: 22, setup_id: setup.id,
        commitment: native.commitment(), corpus_id: None, claims };
    let mut plain = [0u8; 64];
    plain.copy_from_slice(plain_digest.finalize().as_slice());
    let (file_proof, _, file_transcript) = prove_bitpacked_precomputed_v(
        &packed_source, &packed_commit, &setup, &statement, &plain).unwrap();
    let mut native_transcript = Transcript::new(DOMAIN);
    let (native_proof, _) = prove_native_on(
        &native_source, &native, &setup, &statement, &mut native_transcript).unwrap();
    assert_eq!(encode_proof(&native_proof, 22).unwrap(), encode_proof(&file_proof, 22).unwrap());
    assert_eq!(ledger(&native_transcript), ledger(&file_transcript));
    assert_eq!(ledger(&verify(&statement, &setup, &native_proof).unwrap()),
        ledger(&native_transcript));
    assert_eq!(ledger(&verify(&statement, &setup, &file_proof).unwrap()),
        ledger(&file_transcript));

    let cases = [
        (NativePcsFaultKind::Reorder, 400, 0, "row order"),
        (NativePcsFaultKind::Short, 450, 0, "row byte width"),
        (NativePcsFaultKind::Flip, 500, 0, "row commitment"),
        (NativePcsFaultKind::Flip, 1536, 0, "row commitment"),
        (NativePcsFaultKind::Flip, 2047, 2, "row commitment"),
        (NativePcsFaultKind::Omit, 2047, 0, "row count"),
    ];
    for (kind, row, pass_offset, expected) in cases {
        let pass = native_source.pass_count_for_test() + pass_offset;
        native_source.set_fault_for_test(Some(NativePcsFault { pass, row, kind }));
        let mut candidate = Transcript::new(DOMAIN);
        let unchanged = candidate.clone();
        let error = prove_native_on(&native_source, &native, &setup, &statement, &mut candidate)
            .err().expect("mutant must fail");
        assert!(error.contains(expected), "{kind:?}: {error}");
        assert_eq!(ledger(&candidate), ledger(&unchanged));
        let mut actual = candidate.clone();
        let mut reference = unchanged.clone();
        assert_eq!(actual.try_challenge_scalar(b"c329-unchanged").unwrap(),
            reference.try_challenge_scalar(b"c329-unchanged").unwrap());
        native_source.set_fault_for_test(None);
    }
    drop(packed_source);
    std::fs::remove_file(path).unwrap();
}

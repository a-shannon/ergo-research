//! Full-frame native-parent binding for the selected q9 owner-10175 Map.
//! This test does not claim global ROW/X composition, proof admission, or security.

use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    io::{BufReader, Write},
    path::Path,
};

use serde_json::Value;

use super::{
    preamble, FrameReader, HeaderIter, CHUNK, EXTENSIONS, FRAME_BYTES, FRAME_SHA256, H, N,
    PREFIX_BYTES, TAIL_BYTES,
};
use crate::{
    packed_owner_assembly::{validate_native_plan_input, NativePrefix},
    q9_selected_raw_fixture::CheckedQ9RawFixture,
    selected_raw_map_source::{
        assert_native_q9_faults_for_test, Destination, NativeQ9Binding, SelectedRawMapSource,
    },
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const SELECTED_RAW_HEIGHTS: [usize; 10] =
    [2048, 3072, 4096, 5120, 6144, 7168, 8192, 9216, 10176, 10177];
const READ_COUNT: usize = 2592;
const HELPER_COUNT: usize = 5757;
const TERM_COUNT: usize = 68233;
const ARTIFACT_NAME: &str = "native-q9-selection.json";
const ARTIFACT_FORMAT: &str = "C131-NATIVE-Q9-SELECTION-1";
const PASS_MARKER: &str = "C131_NATIVE_Q9_FULL_H21_SEAL_PASS";

fn upper_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02X}")).collect()
}

fn canonical_selection_record(binding: &NativeQ9Binding<'_>) -> Result<Vec<u8>, String> {
    let selected_raw = binding
        .selected_raw_hashes()?
        .into_iter()
        .map(|(height, digest)| {
            let entry = BTreeMap::from([
                ("height".to_owned(), Value::from(height)),
                ("sha256".to_owned(), Value::String(upper_hex(&digest))),
            ]);
            serde_json::to_value(entry).map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    let record = BTreeMap::from([
        (
            "format".to_owned(),
            Value::String(ARTIFACT_FORMAT.to_owned()),
        ),
        (
            "source_frame_sha256".to_owned(),
            Value::String(FRAME_SHA256.to_ascii_uppercase()),
        ),
        ("n".to_owned(), Value::from(binding.headers())),
        ("h".to_owned(), Value::from(binding.slot_log())),
        (
            "parent_root32_hex".to_owned(),
            Value::String(upper_hex(&binding.root())),
        ),
        (
            "parent_total28_hex".to_owned(),
            Value::String(upper_hex(&binding.total_be28())),
        ),
        (
            "profile32_hex".to_owned(),
            Value::String(upper_hex(&binding.profile())),
        ),
        ("selected_raw".to_owned(), Value::Array(selected_raw)),
        (
            "physical_read_count".to_owned(),
            Value::from(binding.selected_read_count()),
        ),
        (
            "physical_read_sha256".to_owned(),
            Value::String(upper_hex(&binding.selected_read_digest()?)),
        ),
    ]);
    let mut bytes = serde_json::to_vec(&record).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    if bytes.len() > 64 * 1024 {
        return Err("native q9 selection record exceeds 64 KiB".into());
    }
    Ok(bytes)
}

fn write_selection_record(binding: &NativeQ9Binding<'_>) -> Result<(), String> {
    let output = std::env::var_os("NIPOPOW_STAGE1B_OUTPUT_DIR")
        .ok_or("bounded runner producer output directory missing")?;
    let output = Path::new(&output);
    if !output.is_absolute() {
        return Err("producer output directory must be absolute".into());
    }
    let directory = fs::symlink_metadata(output).map_err(|error| error.to_string())?;
    if !directory.is_dir() || directory.file_type().is_symlink() {
        return Err("producer output directory must be a real directory".into());
    }
    let artifact_path = output.join(ARTIFACT_NAME);
    let bytes = canonical_selection_record(binding)?;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&artifact_path)
        .map_err(|error| format!("create-only native q9 artifact: {error}"))?;
    file.write_all(&bytes).map_err(|error| error.to_string())?;
    file.sync_all().map_err(|error| error.to_string())?;
    drop(file);

    let metadata = fs::symlink_metadata(&artifact_path).map_err(|error| error.to_string())?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.len() as usize != bytes.len()
    {
        return Err("native q9 artifact post-write type/length mismatch".into());
    }
    let written = fs::read(&artifact_path).map_err(|error| error.to_string())?;
    if written != bytes
        || serde_json::to_vec(
            &serde_json::from_slice::<Value>(&written).map_err(|error| error.to_string())?,
        )
        .map_err(|error| error.to_string())?
            != written[..written.len() - 1]
    {
        return Err("native q9 artifact canonical readback mismatch".into());
    }
    Ok(())
}

#[test]
#[ignore = "full pinned H21 frame; run only through the reviewed 4 GiB/600 s c78 Job"]
fn full_h21_q9_native_seal() {
    let frame_path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned H21 frame path");
    let frame_path = Path::new(&frame_path);
    assert!(frame_path.is_absolute(), "frame path must be absolute");
    let before = fs::symlink_metadata(frame_path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned H21 frame length");
    let file = File::open(frame_path).expect("open pinned H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES);
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (native, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let native = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical contiguous native H21 prefix");
        assert_eq!(headers.remaining, 0, "consume every ERFV record");
        (native, headers.extensions)
    };
    assert_eq!(native.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact H21 prefix extent");
    assert_eq!(extensions, EXTENSIONS, "exact H21 extension count");
    frame
        .finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("full pinned frame SHA256 and tail drain");
    let after = fs::symlink_metadata(frame_path).expect("frame restat after full hash");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES, "frame length after full hash");

    let parent = WorkTreeHistoryPlan::compile(N as u64, H, native.root(), native.total_be28())
        .expect("exact native root/total H21 parent");
    validate_native_plan_input(&parent, &native).expect("native parent exact root/total/profile");
    let q9_path =
        std::env::var_os("NIPOPOW_H21_Q9_HEADERS_DIR").expect("pinned q9 RAW bundle path");
    let fixture = CheckedQ9RawFixture::load(Path::new(&q9_path)).expect("checked exact q9 bundle");
    let binding = NativeQ9Binding::from_native(&parent, &native, &fixture)
        .expect("exact native q9 identity and all 2592 native READ values");
    assert_eq!(binding.headers(), N as u64);
    assert_eq!(binding.slot_log(), H);
    assert_eq!(binding.root(), native.root());
    assert_eq!(binding.total_be28(), native.total_be28());
    assert_eq!(binding.profile(), native.profile());
    assert_eq!(binding.selected_read_count(), READ_COUNT);
    let raw_hashes = binding
        .selected_raw_hashes()
        .expect("ten selected RAW hashes");
    assert_eq!(
        raw_hashes
            .iter()
            .map(|(height, _)| *height)
            .collect::<Vec<_>>(),
        SELECTED_RAW_HEIGHTS
    );

    let source = SelectedRawMapSource::new(&fixture).expect("fixed selected q9 Map source");
    let batch = source
        .stage_native(&binding)
        .expect("native-bound q9 Map staging");
    assert_eq!(batch.counts(), (READ_COUNT, HELPER_COUNT, TERM_COUNT));
    source
        .validate_native(&batch, &binding)
        .expect("fresh native q9 batch validation");
    assert_eq!(
        assert_native_q9_faults_for_test(&source, &binding)
            .expect("isolated native q9 fault and atomicity checks"),
        (4, 1, 1, 1),
    );
    let mut destination = Destination::default();
    assert!(!destination.is_native_parent_bound());
    source
        .publish_native(&mut destination, batch, &binding)
        .expect("atomic native-bound q9 diagnostic publication");
    assert!(destination.is_native_parent_bound());

    let (joined, mutants) =
        crate::q9_common_join::run_live_with_mutants(&parent, &native, &fixture)
            .expect("scoped q9 Map/Work/HEADER nBits common-X and ROW join");
    assert_eq!(
        (joined.map_reads, joined.map_helpers, joined.map_terms),
        (READ_COUNT, HELPER_COUNT, TERM_COUNT)
    );
    assert_eq!(joined.header_nbits_claims, 32);
    assert_eq!(joined.header_alias_terms, 32);
    assert_eq!(joined.header_alias_rows, 32);
    assert!(joined.work_claims > 0 && joined.work_terms > 0 && joined.work_rows > 0);
    assert_eq!(
        joined.total_claims,
        joined.work_claims + joined.map_helpers + joined.header_nbits_claims
    );
    assert_eq!(
        joined.total_rows,
        joined.map_rows + joined.work_rows + joined.header_alias_rows
    );
    assert_eq!(
        (
            mutants.a_map_failures,
            mutants.a_other_work_failures,
            mutants.a_header_alias_failures,
            mutants.b_map_failures,
            mutants.b_work_failures
        ),
        (0, 0, 0, 0, 0)
    );
    assert!(mutants.a_decoded_work_failures > 0 && mutants.b_header_alias_failures > 0);

    write_selection_record(&binding).expect("create-only observed native q9 record");
    println!(
        "C132_Q9_WORK_HEADER_SCOPED_PASS map_reads={} map_helpers={} map_terms={} map_rows={} work_claims={} work_terms={} work_rows={} header_nbits={} aliases={} total_claims={} total_rows={} mutant_a_decoded_work={} mutant_b_header_alias={} proof=none",
        joined.map_reads, joined.map_helpers, joined.map_terms, joined.map_rows,
        joined.work_claims, joined.work_terms, joined.work_rows, joined.header_nbits_claims,
        joined.header_alias_terms, joined.total_claims, joined.total_rows,
        mutants.a_decoded_work_failures, mutants.b_header_alias_failures,
    );
    println!(
        "{PASS_MARKER} frame_sha256={} headers={} h={} reads={} helpers={} terms={} proof=none",
        FRAME_SHA256.to_ascii_uppercase(),
        N,
        H,
        READ_COUNT,
        HELPER_COUNT,
        TERM_COUNT,
    );
    std::io::stdout()
        .flush()
        .expect("flush unique completion marker");
}

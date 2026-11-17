//! Extract-only diagnostic. Original owners and sigma21 coordinates are retained.
//! No field consumer, packed-U kernel, full X, PoW/DAA check or proof runs here.
use super::*;
use std::{fs::OpenOptions, os::windows::fs::MetadataExt, path::PathBuf};
use serde_json::json;

const OWNERS: [usize; 4] = [1_810_840, 1_810_841, 1_810_902, 1_810_903];
const ROWS: [usize; 2] = [905_420, 905_451];
const TOTAL: &str = "2746808805241252741120";
const FIXTURE_BYTES: usize = 524_288;
const RAW_A: &[u8] = include_bytes!("../../fixtures/section3-A_control-checkpoint.raw");
const RAW_B: &[u8] = include_bytes!("../../fixtures/section3-B_candidate-checkpoint.raw");

fn digest(bytes: &[u8]) -> Result<String, String> { Ok(hex(&role0_sha256(bytes)?)) }
fn decimal(value: &str) -> BigUint { BigUint::parse_bytes(value.as_bytes(), 10).unwrap() }

fn regular(path: &Path, expected: u64) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.is_file() || meta.file_attributes() & 0x400 != 0 || meta.len() != expected {
        return Err("regular non-reparse file identity/length".into());
    }
    Ok(())
}

fn fragment_bit(bytes: &[u8], owner: usize, wire: usize) -> Result<bool, String> {
    if bytes.len() != FIXTURE_BYTES || wire >= OWNER_ROW_BITS {
        return Err("fragment byte/wire bounds".into());
    }
    let slot = OWNERS.iter().position(|&value| value == owner)
        .ok_or("fragment owner absent")?;
    // Slots are storage positions; owner/row arithmetic always uses original indices.
    if ROWS[slot / 2] != owner / 2 || slot % 2 != owner % 2 {
        return Err("fragment original row/half mapping".into());
    }
    let offset = (slot / 2) * REAL_SIGMA_ROW_BYTES
        + (owner % 2) * OWNER_ROW_BYTES + wire / 8;
    Ok((bytes[offset] >> (wire % 8)) & 1 == 1)
}

fn check_control(prefix: &NativePrefix, exports: &NativeExports<'_>, fixture: &[u8],
    label: &str, h: usize, f: usize, raw: &[u8], raw_sha: &str,
    floor_decimal: &str, audit_decimal: &str) -> Result<Value, String>
{
    if f != h + 63 || raw.len() != 220 || digest(raw)? != raw_sha {
        return Err(format!("{label} pinned public control"));
    }
    let native_raw = prefix.raw(h)?;
    let decoded = ergo_header_core::Header::decode(native_raw, None)
        .map_err(|e| format!("{label} RAW decode: {e:?}"))?;
    if native_raw != raw || decoded.height as usize != h
        || decoded.encode().map_err(|e| format!("{e:?}"))? != raw {
        return Err(format!("{label} full RAW/height/canonical re-encoding"));
    }
    // Independent integer values come from the admitted prefix, never mapped bits.
    let (_, floor) = prefix.interval(f)?;
    let total_integer = BigUint::from_bytes_be(&prefix.total_be28());
    let floor_integer = BigUint::from_bytes_be(&floor);
    if floor_integer != decimal(floor_decimal) || floor_integer >= total_integer
        || &total_integer - &floor_integer != decimal(audit_decimal) {
        return Err(format!("{label} independent W(f)/F integer controls"));
    }
    let baseline = crate::work_tree_layout::shared_baseline()?;
    if baseline.header_alias_wires.len() != 4112 + 10 + 64
        || baseline.endpoints.upper.len() != 224 {
        return Err("checkpoint source widths changed".into());
    }
    let header_owner = h - 1;
    let floor_owner = f - 2;
    for j in 0..4346 {
        let (owner, wire, expected) = if j < 4112 {
            (header_owner, baseline.header_alias_wires[j],
             raw.get(j / 8).is_some_and(|b| (b >> (j % 8)) & 1 == 1))
        } else if j < 4122 {
            (header_owner, baseline.header_alias_wires[j], (raw.len() >> (j - 4112)) & 1 == 1)
        } else {
            let bit = j - 4122;
            (floor_owner, baseline.endpoints.upper[bit],
             (floor[27 - bit / 8] >> (bit % 8)) & 1 == 1)
        };
        let global = owner.checked_mul(OWNER_ROW_BITS).and_then(|v| v.checked_add(wire))
            .ok_or("checkpoint global source overflow")?;
        if exports.bit(global)? != expected || fragment_bit(fixture, owner, wire)? != expected {
            return Err(format!("{label} extraction source row={j} owner={owner} wire={wire}"));
        }
    }
    Ok(json!({"label":label,"h":h,"f":f,"depth":64,
        "header_owner":header_owner,"floor_owner":floor_owner,"raw_bytes":raw.len(),
        "raw_sha256":raw_sha,"floor_be28":hex(&floor),"floor_decimal":floor_decimal,
        "audit_decimal":audit_decimal,"source_bits_checked":4346}))
}

fn create_file(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)
        .map_err(|e| e.to_string())?;
    file.write_all(bytes).and_then(|_| file.sync_all()).map_err(|e| e.to_string())?;
    drop(file);
    regular(path, bytes.len() as u64)?;
    if fs::read(path).map_err(|e| e.to_string())? != bytes { return Err("publication readback".into()); }
    Ok(())
}

#[test]
#[ignore = "Extract only; static independent review and bounded 4GiB/600s supervisor required"]
fn h21_c319_ab_fragment_extract_only() -> Result<(), String> {
    if std::env::var("C319_EXTRACT_ONLY").as_deref() != Ok("1") {
        return Err("explicit C319 Extract mode required".into());
    }
    let source_closure = std::env::var("C319_SOURCE_CLOSURE_SHA256")
        .map_err(|_| "source closure pin required")?;
    if source_closure.len() != 64 || !source_closure.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("source closure digest grammar".into());
    }
    let output = PathBuf::from(std::env::var_os("C319_EXTRACT_DIR").ok_or("output path required")?);
    if !output.is_absolute() || output.exists() || !output.parent().is_some_and(Path::is_dir) {
        return Err("absolute create-only output with existing parent required".into());
    }
    let frame_path = PathBuf::from(std::env::var_os("NIPOPOW_H21_FRAME").ok_or("frame path required")?);
    if !frame_path.is_absolute() { return Err("absolute frame path required".into()); }
    regular(&frame_path, FRAME_BYTES)?;
    let file = File::open(&frame_path).map_err(|e| e.to_string())?;
    if file.metadata().map_err(|e| e.to_string())?.len() != FRAME_BYTES { return Err("opened frame length".into()); }
    let started = Instant::now();
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
    preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 { return Err("unconsumed ERFV records".into()); }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("exact ERFV prefix/record/extension counts".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
    regular(&frame_path, FRAME_BYTES)?;
    if BigUint::from_bytes_be(&prefix.total_be28()) != decimal(TOTAL) { return Err("public parent total".into()); }
    let frame_seconds = started.elapsed().as_secs_f64();
    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
    validate_native_plan_input(&plan, &prefix)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let mut fixture = Vec::with_capacity(FIXTURE_BYTES);
    let mut owner_receipts = Vec::new();
    for (slot, owner) in OWNERS.into_iter().enumerate() {
        let row = producer.produce(owner)?;
        row.validate_identity_for_history_test(&plan, &prefix, owner)?;
        if row.owner() != owner || row.packed_bytes().len() != OWNER_ROW_BYTES
            || ROWS[slot / 2] != owner / 2 || slot % 2 != owner % 2 {
            return Err("native owner length/original sigma21 position".into());
        }
        owner_receipts.push(json!({"owner":owner,"sigma21_row":owner/2,"half":owner%2,
            "storage_slot":slot,"class":format!("{:?}",row.class()),"bytes":OWNER_ROW_BYTES,
            "sha256":digest(row.packed_bytes())?,
            "popcount":row.packed_bytes().iter().map(|b| b.count_ones() as u64).sum::<u64>()}));
        fixture.extend_from_slice(row.packed_bytes());
    }
    if fixture.len() != FIXTURE_BYTES { return Err("exact fragment fixture width".into()); }
    let exports = NativeExports::new_for_history(&plan, &prefix)?;
    let controls = vec![
        check_control(&prefix,&exports,&fixture,"A",1_810_842,1_810_905,RAW_A,
            "3af4be948ea36e8438ecb3dfcfe5863b55d8b760373cd9872c2a85b102f168dd",
            "2745402775092498268160","1406030148754472960")?,
        check_control(&prefix,&exports,&fixture,"B",1_810_841,1_810_904,RAW_B,
            "0f881c0d2546479acb69fd2970b75fb6e0789c0b28d0c515696f19da1bdef16d",
            "2745402699639720771584","1406105601531969536")?,
    ];
    let mut row_receipts = Vec::new();
    for (slot, row) in ROWS.into_iter().enumerate() {
        let bytes = &fixture[slot*REAL_SIGMA_ROW_BYTES..(slot+1)*REAL_SIGMA_ROW_BYTES];
        row_receipts.push(json!({"row":row,"storage_slot":slot,"owners":[row*2,row*2+1],
            "bytes":bytes.len(),"sha256":digest(bytes)?,
            "popcount":bytes.iter().map(|b| b.count_ones() as u64).sum::<u64>()}));
    }
    let fixture_sha = digest(&fixture)?;
    let receipt = json!({"schema":"c319-h21-ab-native-extract-v1","status":"EXTRACT_CHECKS_PASS",
        "mode":"extract-only","source_closure_sha256":source_closure,
        "parent":{"n":N,"slot_log":H,"input_log":41,"width":OWNER_ROW_BITS,
            "root":hex(&prefix.root()),"profile":hex(&prefix.profile()),
            "total_be28":hex(&prefix.total_be28()),"total_decimal":TOTAL,"tip":N},
        "frame":{"bytes":FRAME_BYTES,"sha256":FRAME_SHA256,"prefix_bytes":PREFIX_BYTES,
            "tail_bytes":TAIL_BYTES,"extensions":EXTENSIONS,"records":N,"anchor":N-1},
        "fixture":{"file":"c319-ab-sigma21.bin","bytes":FIXTURE_BYTES,"sha256":fixture_sha,
            "popcount":fixture.iter().map(|b| b.count_ones() as u64).sum::<u64>(),
            "owners":owner_receipts,"rows":row_receipts},"controls":controls,
        "frame_seconds":frame_seconds,"extract_seconds":started.elapsed().as_secs_f64(),
        "field_consumer_executed":false,"full_h21_witness":false,
        "pow_daa_validated":false,"proof_or_public_admission":false});
    drop(exports); drop(producer); drop(plan); drop(prefix);
    // All semantic checks precede any output. Rename publishes the complete directory
    // atomically on Windows; create_dir and rename refuse an existing destination.
    let staging = output.with_file_name(format!("{}.pending-{}",
        output.file_name().ok_or("output basename")?.to_string_lossy(),std::process::id()));
    fs::create_dir(&staging).map_err(|e| e.to_string())?;
    create_file(&staging.join("c319-ab-sigma21.bin"), &fixture)?;
    let mut receipt_bytes = serde_json::to_vec_pretty(&receipt).map_err(|e| e.to_string())?;
    receipt_bytes.push(b'\n');
    let receipt_sha = digest(&receipt_bytes)?;
    create_file(&staging.join("extraction.json"), &receipt_bytes)?;
    if output.exists() { return Err("output appeared before publication".into()); }
    fs::rename(&staging,&output).map_err(|e| e.to_string())?;
    println!("C319_EXTRACTION_PASS fixture_bytes={FIXTURE_BYTES} fixture_sha256={fixture_sha} receipt_sha256={receipt_sha} rows=905420,905451 owners=1810840,1810841,1810902,1810903 source_bits_checked=8692 full_h21_witness=false");
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

#[test]
fn c319_fragment_coordinate_bounds() {
    let bytes = vec![0u8; FIXTURE_BYTES];
    assert_eq!(fragment_bit(&bytes, OWNERS[0],0),Ok(false));
    assert!(fragment_bit(&bytes, OWNERS[0]-1,0).is_err());
    assert!(fragment_bit(&bytes, OWNERS[0],OWNER_ROW_BITS).is_err());
    assert!(fragment_bit(&bytes[..FIXTURE_BYTES-1], OWNERS[0],0).is_err());
}

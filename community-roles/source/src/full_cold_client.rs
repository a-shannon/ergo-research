//! Separate-process entry points for the retained two-snapshot experiment.
use super::{admit_structure, bounded_file, external, full_tail, native_audit, publish_local,
    relation, split_certificate, Outputs, VerifiedFullStructural, Word, MAX_CERT, MAX_X};
use std::{fs::File, io::{Read, Seek, SeekFrom}, time::Instant};
use serde_json::{json, Value};

const FINAL_TIP: usize = 1_827_840;
// This is the benchmark process's transport staging budget. Exhaustion stops
// the process without a selection result. It does not mark a proof invalid.
const BATCH_BYTES: usize = 1024 * 1024 * 1024;

fn id(bytes: &[u8]) -> String {
    ergo_header_core::blake2b256(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn exact_query() -> Result<u32, String> {
    std::env::var("NIPOPOW_V2_EXACT_QUERY").map_err(|e| e.to_string())?
        .parse().map_err(|_| "invalid requested exact query".into())
}

fn possible_extension(file: &mut (impl Read + Seek), len: u64, query: u32) -> Result<bool, String> {
    if len < 52 { return Ok(false); }
    let mut prefix = [0; 12];
    file.read_exact(&mut prefix).map_err(|e| e.to_string())?;
    let x_len = u32::from_be_bytes(prefix[8..].try_into().unwrap()) as usize;
    if &prefix[..8] != b"NPTAIL01" || x_len > MAX_X { return Ok(false); }
    let overhead = 52 + x_len as u64;
    if len < overhead { return Ok(false); }
    file.seek(SeekFrom::Start(12+x_len as u64)).map_err(|e|e.to_string())?;
    let mut geometry = [0; 8];
    file.read_exact(&mut geometry).map_err(|e| e.to_string())?;
    let h = u32::from_be_bytes(geometry[..4].try_into().unwrap());
    let n = u32::from_be_bytes(geometry[4..].try_into().unwrap());
    let b = crate::h21_snapshot::H as u32;
    if h != query || h < b || n > i32::MAX as u32 || n.checked_sub(h).is_none_or(|depth| depth < 64) {
        return Ok(false);
    }
    let count = u64::from(n-b);
    Ok((overhead+3*count..=overhead+516*count).contains(&len))
}

fn read_set(name: &str, extension_query: Option<u32>, remaining: &mut usize) -> Result<Vec<Vec<u8>>, String> {
    let value = std::env::var_os(name).ok_or_else(|| format!("missing {name}"))?;
    let mut result = Vec::new();
    if value.is_empty() { return Ok(result); }
    for path in std::env::split_paths(&value) {
        if !crate::preview_test_paths::absolute_outside_source(&path) {
            return Err(format!("invalid path in {name}"));
        }
        let mut file = File::open(path).map_err(|e| e.to_string())?;
        let meta = file.metadata().map_err(|e| e.to_string())?;
        if !meta.is_file() { return Err("candidate must be a regular file".into()); }
        // An oversized complete certificate is individually ineligible under the profile.
        // An empty byte vector is also unconditionally rejected by the certificate parser.
        let possible = match extension_query {
            Some(query) => possible_extension(&mut file, meta.len(), query)?,
            None => meta.len() <= MAX_CERT as u64,
        };
        if !possible {
            result.push(Vec::new());
            continue;
        }
        let len = usize::try_from(meta.len()).map_err(|_| "candidate extent outside host")?;
        if len > *remaining { return Err("cold input staging budget exhausted".into()); }
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(len).map_err(|_| "cold input buffer capacity")?;
        file.rewind().map_err(|e| e.to_string())?;
        bytes.resize(len, 0);
        file.read_exact(&mut bytes).map_err(|e|e.to_string())?;
        if file.read(&mut [0;1]).map_err(|e|e.to_string())? != 0 {
            return Err("candidate extent changed during acquisition".into());
        }
        *remaining -= len;
        result.push(bytes);
    }
    Ok(result)
}

fn ranked<'a>(packets: &'a [Vec<u8>]) -> Vec<(Word, &'a [u8])> {
    let mut order = Vec::new();
    for bytes in packets {
        let Ok((x, _, _)) = split_certificate(bytes) else { continue };
        let Ok((fields, _, _)) = Outputs::read_prefix(x) else { continue };
        let Ok((_, work, _, _, _)) = relation::read_statement_fields(fields) else { continue };
        order.push((work, bytes.as_slice()));
    }
    // The checked seal must certify this very work before the first candidate
    // may win. Every later candidate has lower work or lexicographically larger
    // complete packet bytes. Noncanonical inputs never acquire authority here.
    rank_distinct(&mut order);
    order
}

fn rank_distinct(order: &mut Vec<(Word, &[u8])>) {
    order.sort_unstable_by(|a,b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
    order.dedup();
}

fn sample_count(seal: &VerifiedFullStructural) -> usize {
    let mut scale = num_bigint::BigUint::from_bytes_be(&seal.following_work());
    let total = num_bigint::BigUint::from_bytes_be(&seal.work());
    let mut scales = 1;
    while scale < total { scale <<= 1usize; scales += 1; }
    scales * 466
}

fn compare_packets(packets: &[Vec<u8>], extensions: &[Vec<u8>], query: u32) -> Result<Value, String> {
    let start = Instant::now();
    let order = ranked(packets);
    let count = order.len();
    let mut structural_seconds = 0.0;
    let mut audit_seconds = 0.0;
    for (i, (work, bytes)) in order.into_iter().enumerate() {
        let (x, proof, audit) = split_certificate(bytes)?;
        let t = Instant::now();
        let admitted = admit_structure(x, proof);
        structural_seconds += t.elapsed().as_secs_f64();
        let Ok(seal) = admitted else { continue };
        if seal.work() != work { return Err("certified work differs from decoded rank".into()); }
        let t = Instant::now();
        let checked = native_audit::verify(&seal, audit);
        audit_seconds += t.elapsed().as_secs_f64();
        let Ok(bootstrap) = checked else { continue };
        let t = Instant::now();
        let tail = full_tail::select(&bootstrap, query, extensions.iter().map(Vec::as_slice))?;
        let tail_seconds = t.elapsed().as_secs_f64();
        let bootstrap_report = json!({
            "certificate_blake2b256": id(bytes), "certificate_bytes": bytes.len(),
            "canonical_x_bytes": x.len(), "structural_bytes": proof.len(), "native_audit_bytes": audit.len(),
            "structural_key_id": "ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6",
            "committed_tip_height": seal.header_count(), "committed_tip_id": hex(&seal.public.tip),
            "committed_work": num_bigint::BigUint::from_bytes_be(&work).to_string(),
            "checkpoint_height": seal.checkpoint_height(), "checkpoint_id": id(seal.checkpoint_raw()),
            "work_root": hex(&seal.root()), "sample_draws": sample_count(&seal),
            "distinct_sampled_headers": u32::from_be_bytes(audit[8..12].try_into().unwrap())
        });
        let exact = tail.as_ref().map(|selected| json!({
            "query_height": selected.query_height(), "query_header_raw": hex(selected.query_raw()),
            "query_id": id(selected.query_raw()), "tip_height": selected.terminal_height(),
            "tip_id": hex(&selected.terminal_id()),
            "total_work": num_bigint::BigUint::from_bytes_be(&selected.total_work()).to_string(),
            "checked_tail_headers": selected.terminal_height() - seal.checkpoint_height(),
            "extension_bytes": selected.canonical_extension().len(),
            "extension_blake2b256": id(selected.canonical_extension())
        }));
        return Ok(json!({
            "result": if exact.is_some() { "SELECTED" } else { "NO_EXACT_RESULT" },
            "bootstrap": bootstrap_report, "exact": exact, "requested_exact_query":query,
            "bootstrap_inputs":packets.len(),"rankable_distinct_bootstraps":count,
            "bootstrap_admissions_attempted": i+1, "exact_tail_inputs": extensions.len(),
            "structural_seconds":structural_seconds, "audit_seconds":audit_seconds,
            "tail_selection_seconds":tail_seconds, "packet_comparison_seconds":start.elapsed().as_secs_f64()
        }));
    }
    Ok(json!({"result":"NO_BOOTSTRAP_RESULT","requested_exact_query":query,
        "bootstrap_inputs":packets.len(),"rankable_distinct_bootstraps":count,
        "bootstrap_admissions_attempted":count,"exact_tail_inputs":extensions.len(),
        "structural_seconds":structural_seconds, "audit_seconds":audit_seconds,
        "packet_comparison_seconds":start.elapsed().as_secs_f64()}))
}

#[test]
#[ignore = "cold receiver; supply frozen certificate and extension path lists"]
fn cold_sync_from_exported_packets() -> Result<(), String> {
    let start = Instant::now();
    let query = exact_query()?;
    let mut remaining = BATCH_BYTES;
    let packets = read_set("NIPOPOW_V2_CERTIFICATES", None, &mut remaining)?;
    let extensions = read_set("NIPOPOW_V2_EXTENSIONS", Some(query), &mut remaining)?;
    let read_seconds = start.elapsed().as_secs_f64();
    let mut report = compare_packets(&packets, &extensions, query)?;
    report["frozen_input_payload_bytes"] = json!(BATCH_BYTES - remaining);
    report["file_read_seconds"] = json!(read_seconds);
    report["receiver_seconds_including_read"] = json!(start.elapsed().as_secs_f64());
    println!("V2_COLD_RECEIVER {}", report);
    Ok(())
}

#[test]
#[ignore = "retained full N1 source; requires an independently verified exported certificate"]
fn export_exact_tail_from_retained_frame() -> Result<(), String> {
    let certificate = bounded_file(&external("NIPOPOW_V2_CERTIFICATE")?, MAX_CERT)?;
    let (x, proof, audit) = split_certificate(&certificate)?;
    let seal = admit_structure(x, proof)?;
    let checked = native_audit::verify(&seal, audit)?;
    let query = exact_query()?;
    let target = external("NIPOPOW_V2_EXTENSION_OUTPUT")?;
    crate::h21_native_admission_tests::c574_with_pinned_prefix(|prefix| {
        let b = seal.checkpoint_height() as usize;
        if prefix.header_count() != FINAL_TIP || prefix.raw(b)? != seal.checkpoint_raw() {
            return Err("retained corpus differs from exact bootstrap".into());
        }
        let expected_tip = ergo_header_core::blake2b256(prefix.raw(FINAL_TIP)?);
        let raws: Vec<&[u8]> = (b+1..=FINAL_TIP).map(|h| prefix.raw(h)).collect::<Result<_,_>>()?;
        let wire = full_tail::encode(&checked, query, raws)?;
        let verified = full_tail::verify(&checked, query, &wire)?;
        if verified.terminal_id() != expected_tip || verified.total_work() != prefix.total_be28()
            || verified.query_raw() != prefix.raw(query as usize)? {
            return Err("tail serialization differs from retained corpus".into());
        }
        publish_local(&target, &wire)?;
        let limit = MAX_X + 64 + (FINAL_TIP - b) * (514 + 2);
        if bounded_file(&target, limit)? != wire { return Err("tail export readback".into()); }
        println!("V2_EXPORTED_TAIL {}", json!({"bytes":wire.len(),"blake2b256":id(&wire),
            "bootstrap":b,"tip_height":FINAL_TIP,"tip_id":hex(&expected_tip),"exact_query":query}));
        Ok(())
    })
}

#[test]
fn cold_empty_or_malformed_set_has_no_result() {
    for packets in [Vec::new(), vec![b"NPV2AUD1".to_vec(), vec![0;24]]] {
        let report = compare_packets(&packets, &[vec![1;9]], 1_820_159).unwrap();
        assert_eq!(report["result"], "NO_BOOTSTRAP_RESULT");
        assert_eq!(report["bootstrap_admissions_attempted"], 0);
        assert!(report.get("exact").is_none());
    }
}

#[test]
fn complete_bytes_resolve_equal_rank_and_duplicates() {
    let mut lower = [0;28];
    lower[27] = 1;
    let mut greater = [0;28];
    greater[26] = 1;
    let mut order: Vec<(Word,&[u8])> = vec![(lower,b"a"),(greater,b"x2"),(greater,b"x"),
        (greater,b"x1"),(greater,b"x1")];
    rank_distinct(&mut order);
    assert_eq!(order, vec![(greater,b"x".as_slice()),(greater,b"x1"),(greater,b"x2"),(lower,b"a")]);
}

#[test]
fn malformed_extension_geometry_rejected_before_payload_allocation() {
    use std::io::Cursor;
    let q = crate::h21_snapshot::H as u32;
    let mut prelude = b"NPTAIL01".to_vec();
    prelude.extend(1u32.to_be_bytes());
    prelude.push(7);
    prelude.extend(q.to_be_bytes());
    prelude.extend((q+64).to_be_bytes());
    prelude.extend([0;32]);
    let good = prelude.len() as u64 + 64 * 516;
    assert!(possible_extension(&mut Cursor::new(&prelude),good,q).unwrap());
    assert!(!possible_extension(&mut Cursor::new(&prelude),good+1,q).unwrap());
    assert!(!possible_extension(&mut Cursor::new(&prelude),55,q).unwrap());
    assert!(!possible_extension(&mut Cursor::new(&prelude),good,q+1).unwrap());
    prelude[0] ^= 1;
    assert!(!possible_extension(&mut Cursor::new(&prelude),good,q).unwrap());
}

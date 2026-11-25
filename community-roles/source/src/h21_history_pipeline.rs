//! Diagnostic entry points for the retained mainnet snapshot. The cold entry
//! consumes one packet. Production policy is outside the structural statement.
use super::*;
use crate::h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxStream, Plan as MaxPlan};
use crate::packed_owner_assembly::{HeaderSourceBinding, H21EligibleContext};
use h21_candidate_roles::H21CandidateRole;
use opening_batch::h21_producer::{H21PcsProver, H21PcsSession};
use std::{fs::File, io::Read, path::PathBuf};

use crate::h21_snapshot::N;
const SLOTS: usize = 1 << 21;

fn location(name: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(std::env::var_os(name).ok_or_else(|| format!("missing {name}"))?);
    if !crate::preview_test_paths::absolute_outside_source(&path) {
        return Err(format!("{name} must name an absolute location outside source"));
    }
    Ok(path)
}

fn bounded_read(path: &Path, maximum: usize) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    File::open(path).map_err(|e| e.to_string())?.take(maximum as u64 + 1)
        .read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() > maximum { return Err("input exceeds structural codec limit".into()); }
    Ok(bytes)
}

fn export(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut out = OpenOptions::new().write(true).create_new(true).open(path).map_err(|e| e.to_string())?;
    out.write_all(bytes).and_then(|_| out.sync_all()).map_err(|e| e.to_string())
}

fn generator_digest(mut reader: impl Read, length: u64) -> Result<[u8; 32], String> {
    if length == 0 { return Err("empty H21 generator binary".into()); }
    let mut hash = Blake2b::<U32>::new();
    hash.update(b"nipopow-h21-witness-generator-executable-v1");
    hash.update(length.to_le_bytes());
    let mut buffer = [0u8; 32 * 1024];
    let mut remaining = length;
    while remaining != 0 {
        let count = remaining.min(buffer.len() as u64) as usize;
        reader.read_exact(&mut buffer[..count]).map_err(|e| format!("reading H21 generator: {e}"))?;
        hash.update(&buffer[..count]);
        remaining -= count as u64;
    }
    if reader.read(&mut buffer[..1]).map_err(|e| e.to_string())? != 0 {
        return Err("H21 generator exceeds its opened length".into());
    }
    Ok(hash.finalize().into())
}

fn generation_binding() -> Result<Vec<u8>, String> {
    let path = std::env::current_exe().map_err(|e| format!("locating H21 generator: {e}"))?;
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(windows)] {
        use std::os::windows::fs::OpenOptionsExt;
        options.share_mode(1).custom_flags(0x00200000); // Read sharing only, open reparse point itself.
    }
    let file = options.open(path).map_err(|e| format!("opening H21 generator: {e}"))?;
    let metadata = file.metadata().map_err(|e| e.to_string())?;
    if !metadata.is_file() { return Err("H21 generator must be a regular file".into()); }
    #[cfg(windows)] {
        use std::os::windows::fs::MetadataExt;
        if metadata.file_attributes() & 0x400 != 0 { return Err("H21 generator is a reparse point".into()); }
    }
    // Resume requires the exact executable retained when the first chunk was written.
    let mut binding = b"H21-native-BN254-lsb20-owner21/v2/frame-sha256:a68d86562a56c5b71cf2180e4762bf8775b1061b6953bff7281ec50b7ee52c5e/generator-blake2b256:".to_vec();
    binding.extend_from_slice(&generator_digest(file, metadata.len())?);
    Ok(binding)
}

#[test]
fn witness_generator_digest_binds_every_byte_and_exact_extent() -> Result<(), String> {
    let mut bytes = vec![0x5a; 32 * 1024 + 1];
    let length = bytes.len() as u64;
    let first = generator_digest(bytes.as_slice(), length)?;
    bytes[32 * 1024] ^= 1;
    assert_ne!(first, generator_digest(bytes.as_slice(), length)?);
    assert!(generator_digest(bytes.as_slice(), length - 1).is_err());
    assert!(generator_digest(bytes.as_slice(), length + 1).is_err());
    assert!(generator_digest(&[][..], 0).is_err());
    Ok(())
}

fn native_statement(prefix: &crate::packed_owner_assembly::NativePrefix, native: &H21EligibleContext<'_>)
    -> Result<codec::H21Statement, String> {
    let tip = prefix.header(N)?;
    Ok(codec::H21Statement { root: prefix.root(), total: prefix.total_be28(),
        tip: tip.id().map_err(|e| format!("{e:?}"))?, tip_time: prefix.timestamp(N)?,
        parameters: native.structural_map_parameters()? })
}

#[test]
#[ignore = "export the structural statement from the retained authenticated mainnet input"]
fn export_native_statement() -> Result<(), String> {
    let output = location("NIPOPOW_H21_STATEMENT")?;
    crate::h21_native_admission_tests::with_selected_h21_prefix(|prefix| {
        let plan = WorkTreeHistoryPlan::compile(N as u64, 21, prefix.root(), prefix.total_be28())?;
        let native = H21EligibleContext::new(&plan, prefix)?;
        let s = native_statement(prefix, &native)?;
        let dto = codec::encode_statement(&s)?;
        if codec::decode_statement(&dto)? != s { return Err("statement round trip".into()); }
        export(&output, &dto)
    })
}

#[test]
#[ignore = "resumable full-domain witness production from the retained authenticated history"]
fn generate_history_witness() -> Result<(), String> {
    let stage = location("NIPOPOW_H21_CHUNKS")?;
    let target = location("NIPOPOW_H21_WITNESS")?;
    let statement_path = location("NIPOPOW_H21_STATEMENT")?;
    let end = number("NIPOPOW_H21_END_OWNER")?;
    if end > SLOTS || end == 0 { return Err("exclusive owner limit outside full domain".into()); }
    crate::h21_native_admission_tests::with_selected_h21_prefix(|prefix| {
        let plan = WorkTreeHistoryPlan::compile(N as u64, 21, prefix.root(), prefix.total_be28())?;
        let native = H21EligibleContext::new(&plan, prefix)?;
        let s = native_statement(prefix, &native)?;
        if bounded_read(&statement_path, codec::MAX_STATEMENT_BYTES)? != codec::encode_statement(&s)? {
            return Err("checkpoint statement differs from retained history".into());
        }
        let owned = H21StructuralDiagnostic::compile(s.root, s.total, s.tip, s.tip_time, s.parameters)?;
        let binding = generation_binding()?;
        let mut store = if stage.try_exists().map_err(|e| e.to_string())? {
            packed::H21UntrustedChunkStore::resume(&stage, &owned.public_bytes, &binding)?
        } else { packed::H21UntrustedChunkStore::create_new(&stage, &owned.public_bytes, &binding)? };
        if end < store.next_owner() { return Err("end precedes completed checkpoint".into()); }
        if store.next_owner() < end {
            let snapshot = Eligible08NativeSnapshot::new(&plan, prefix)?;
            let mut max = MaxStream::new(&plan, prefix, &snapshot)?;
            for (owner, _) in MaxPlan::eligible08().max_calendar() {
                max.push_native(native.native_owner_values_producer(), owner)?;
            }
            max.closed_native_snapshot(&plan, prefix)?;
            let mut stream = native.score_endpoint_stream(&max)?;
            while let Some(owner) = stream.next_owner() { stream.push_native(owner)?; }
            stream.terminal_r()?;
            let generate = |owner| -> Result<(usize, Vec<u8>), String> {
                let row = stream.native_owner_values(owner)?;
                row.require_context(&native)?;
                if row.owner() != owner || row.binding() != &HeaderSourceBinding::for_plan(&plan, owner)? {
                    return Err("native owner identity mismatch".into());
                }
                Ok((row.owner(), row.packed_bytes().to_vec()))
            };
            // The checked stream is immutable after terminal_r(). Workers
            // produce independent rows. Only this ordered writer owns the store.
            use rayon::prelude::*;
            let width = rayon::current_num_threads().clamp(1, 16);
            let begin = store.next_owner();
            for first in (begin..end).step_by(width) {
                let limit = end.min(first + width);
                let rows: Result<Vec<_>, _> = (first..limit).into_par_iter()
                    .map(&generate).collect();
                for (offset, (owner, bytes)) in rows?.into_iter().enumerate() {
                    if owner != first + offset { return Err("native writer owner ordering".into()); }
                    store.append_owner(owner, &bytes)?;
                }
                if (limit - begin) / 4096 != (first - begin) / 4096 {
                    println!("H21_NATIVE_PROGRESS sealed_owners={} generated_through={} workers={}",
                        store.completed_owners(), limit, width);
                }
            }
            store.checkpoint_tail()?;
        }
        if store.completed_owners() != end { return Err("checkpoint count mismatch".into()); }
        if end == SLOTS { let _complete = store.finish_candidate(&target)?; }
        Ok(())
    })
}

fn number(name: &str) -> Result<usize, String> {
    std::env::var(name).map_err(|_| format!("missing {name}"))?.parse()
        .map_err(|_| format!("invalid integer for {name}"))
}

#[test]
#[ignore = "full H21 proof production requires an admitted producer budget and complete witness"]
fn export_full_history_packet() -> Result<(), String> {
    let output = location("NIPOPOW_H21_EXPORT_DIR")?;
    let statement_path = location("NIPOPOW_H21_STATEMENT")?;
    let source_path = location("NIPOPOW_H21_WITNESS")?;
    let bytes = bounded_read(&statement_path, codec::MAX_STATEMENT_BYTES)?;
    let s = codec::decode_statement(&bytes)?;
    if codec::encode_statement(&s)? != bytes { return Err("noncanonical public statement".into()); }
    let limit = number("NIPOPOW_H21_ROLE_BUDGET_BYTES")?;
    let context = number("NIPOPOW_H21_CONTEXT_BYTES")?;
    let reserve = number("NIPOPOW_H21_RESERVE_BYTES")?;
    let edge = sparse_stream_roster::H21Role1Budget {limit_bytes: limit, caller_context_bytes: context,
        visitor_scratch_bytes: number("NIPOPOW_H21_VISITOR_BYTES")?, unmeasured_bytes: reserve};
    std::fs::create_dir(&output).map_err(|e| format!("fresh output directory: {e}"))?;
    let owned = H21StructuralDiagnostic::compile(s.root, s.total, s.tip, s.tip_time, s.parameters)?;
    let ctx = owned.context()?;
    let source = owned.open_untrusted_candidate(&source_path, None)?;
    let prover = H21PcsProver::regenerate(|phase| println!("setup {phase}"))?;
    let key_bytes = prover.key_bytes();
    let key = verifier_key::admit(41, key_bytes)?;
    let session = H21PcsSession::commit(&source, ctx.public_bytes, &prover)?;
    let c = pcs::encode_commitment(&session.commitment())?;
    drop(prover);
    let mut roles = Vec::with_capacity(7);
    let mut claims = Vec::with_capacity(7);
    for role in 0..7 {
        let (encoded, _) = match role {
            0 => ctx.admit_role0_diagnostic(key_bytes, &c)?.prove_untrusted_candidate(&source,
                core_pool_boolean::H21Role0DiagnosticBudget { limit_bytes: limit,
                    caller_graph_reservation_bytes: context, unmeasured_reservation_bytes: reserve })?,
            1 => ctx.prove_role1_untrusted_candidate(key_bytes, &c, &source, edge)?,
            5 => ctx.prove_role5_untrusted_candidate(key_bytes, &c, &source,
                crate::segment_adjacency::linear_for_test::H21Role5Budget {limit_bytes:limit,
                    caller_context_bytes:context, unmeasured_bytes:reserve})?,
            index => {
                let kind = match index { 2 => H21CandidateRole::Tree, 3 => H21CandidateRole::Point,
                    4 => H21CandidateRole::HeightDaa, 6 => H21CandidateRole::Metadata, _ => unreachable!() };
                ctx.prove_remaining_untrusted_candidate(kind, key_bytes, &c, &source, edge)?
            }
        };
        let file = output.join(format!("role-{role}.gkr"));
        export(&file, &encoded)?;
        let actual = bounded_read(&file, codec::GKR_BYTES[role])?;
        let proof = gkr::decode_dimensions(&[codec::INPUT_BITS[role] as usize], &actual)?;
        if gkr::encode_proof(&proof)? != actual { return Err("noncanonical exported role".into()); }
        claims.push(verify_h21_role(&ctx, &key, &c, role, &proof)?);
        roles.push(actual);
    }
    let statement = opening_batch::Statement { log_n:41, setup_id:*key.id(),
        commitment:session.commitment(), corpus_id:Some(Blake2b::<U32>::digest(&bytes).into()),
        claims:claims.try_into().map_err(|_|"seven verified claims required")? };
    let prover = H21PcsProver::regenerate(|phase| println!("setup {phase}"))?;
    let (common, _) = session.prove_unverified(&prover, &statement)?;
    let packet = codec::encode_packet(&codec::DecodedH21Packet { statement:s, statement_bytes:bytes,
        key:key_bytes.to_vec(), commitment:c, roles:roles.try_into().map_err(|_|"seven proofs required")?, common })?;
    export(&output.join("history.packet"), &packet)
}

#[test]
#[ignore = "independent packet-only structural consumer"]
fn verify_exported_history_packet() -> Result<(), String> {
    let packet = bounded_read(&location("NIPOPOW_H21_PACKET")?, codec::MAX_PACKET_BYTES)?;
    let verified = verify_h21_packet(&packet)?;
    println!("Structural history verified for {} headers, {} packet bytes", verified.headers(), packet.len());
    Ok(())
}

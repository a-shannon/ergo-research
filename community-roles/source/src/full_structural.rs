//! Public Score terminals and the complete pre-audit statement on the original
//! seven GKR roles and one log41 witness commitment.
use super::*;
use h21_candidate_roles::H21CandidateRole;
use opening_batch::h21_producer::{H21PcsProver, H21PcsSession};
use std::{fs, io::Read, path::PathBuf};

const IDENTITY_DOMAIN: &[u8] = b"nipopow-v2/r4/full-structural/v1\0";
const MAX_IDENTITY: usize = 1 << 20;
#[path="h21_detached_role.rs"]
pub(crate) mod detached_role;

// Version the common opening separately from the reusable F60 session identity.
fn common_corpus_id(public_identity: &[u8]) -> [u8; 32] {
    let mut hash = Blake2b::<U32>::new();
    hash.update(b"nipopow-v2/r4/full-structural/H21ATOM2/common-opening\0");
    hash.update(public_identity);
    hash.finalize().into()
}

pub(crate) fn statement_fields(root: [u8; 32], total: [u8; 28], tip: [u8; 32], tip_time: i64,
    parameters: [PublicMapParameters; 2]) -> Result<Vec<u8>, String> {
    codec::encode_statement(&codec::H21Statement { root, total, tip, tip_time, parameters })
}

pub(crate) fn read_statement_fields(bytes: &[u8]) ->
    Result<([u8; 32], [u8; 28], [u8; 32], i64, [PublicMapParameters; 2]), String> {
    let s = codec::decode_statement(bytes)?;
    if codec::encode_statement(&s)? != bytes { return Err("noncanonical structural fields".into()); }
    Ok((s.root, s.total, s.tip, s.tip_time, s.parameters))
}

fn check_public_scores(x: &[u8], total: [u8; 28], sampled: [u8; 28],
    exact: [u8; 29]) -> Result<(), String> {
    if x.is_empty() || x.len() > MAX_IDENTITY { return Err("full statement identity extent".into()); }
    if sampled > total { return Err("sampled-origin maturity".into()); }
    if exact[0] > 1 { return Err("exact bootstrap maximum exceeds U225".into()); }
    Ok(())
}

fn full_identity(base: &[u8], x: &[u8], total: [u8; 28], sampled: [u8; 28],
    exact: [u8; 29]) -> Result<Vec<u8>, String> {
    check_public_scores(x, total, sampled, exact)?;
    let length = IDENTITY_DOMAIN.len().checked_add(8 + 28 + 29)
        .and_then(|n| n.checked_add(base.len())).and_then(|n| n.checked_add(x.len()))
        .ok_or("full statement identity overflow")?;
    if base.is_empty() || length > MAX_IDENTITY {
        return Err("full statement identity extent".into());
    }
    let mut bytes = Vec::with_capacity(length);
    bytes.extend_from_slice(IDENTITY_DOMAIN);
    for field in [base, x] {
        bytes.extend_from_slice(&(field.len() as u32).to_be_bytes());
        bytes.extend_from_slice(field);
    }
    bytes.extend_from_slice(&sampled);
    bytes.extend_from_slice(&exact);
    Ok(bytes)
}

pub(crate) fn build_full_context(x: &[u8], root: [u8; 32], total: [u8; 28],
    tip: [u8; 32], tip_time: i64, parameters: [PublicMapParameters; 2],
    sampled: [u8; 28], a_b: [u8; 29]) -> Result<H21StructuralDiagnostic, String> {
    check_public_scores(x, total, sampled, a_b)?;
    let mut public = H21StructuralDiagnostic::compile(root, total, tip, tip_time, parameters)?;
    let identity = full_identity(&public.public_bytes, x, total, sampled, a_b)?;
    public.native_witness_identity = Some(std::mem::replace(&mut public.public_bytes, identity));
    let mut sample_word = [0; 29];
    sample_word[1..].copy_from_slice(&sampled);
    public.terminal_scores = Some([sample_word, a_b]);
    Ok(public)
}

/// Constructed only after rederiving all seven claims from their packet bytes
/// and verifying their common opening against the admitted log41 key.
pub(crate) struct VerifiedFullStructure {
    fields: codec::H21Statement,
    statement_bytes: Vec<u8>,
    sampled: [u8; 28],
    a_b: [u8; 29],
}

impl VerifiedFullStructure {
    pub(crate) fn headers(&self) -> usize { crate::h21_snapshot::N }
    pub(crate) fn root(&self) -> [u8; 32] { self.fields.root }
    pub(crate) fn total_be28(&self) -> [u8; 28] { self.fields.total }
    pub(crate) fn tip(&self) -> [u8; 32] { self.fields.tip }
    pub(crate) fn tip_time(&self) -> i64 { self.fields.tip_time }
    pub(crate) fn parameters(&self) -> [PublicMapParameters; 2] { self.fields.parameters }
    pub(crate) fn sampled_work_bound(&self) -> [u8; 28] { self.sampled }
    pub(crate) fn exact_bootstrap_bound(&self) -> [u8; 29] { self.a_b }
    pub(crate) fn canonical_statement_bytes(&self) -> &[u8] { &self.statement_bytes }
}

pub(crate) fn verify_full_structure(x: &[u8], sampled: [u8; 28], a_b: [u8; 29],
    bytes: &[u8]) -> Result<VerifiedFullStructure, String> {
    let packet = codec::decode_packet(bytes)?;
    if codec::encode_packet(&packet)? != bytes { return Err("noncanonical structural packet".into()); }
    let (key, proofs, opening) = preflight_packet(&packet)?;
    let s = &packet.statement;
    let owned = build_full_context(x, s.root, s.total, s.tip, s.tip_time, s.parameters, sampled, a_b)?;
    let context = owned.context()?;
    let mut claims = Vec::with_capacity(7);
    for (role, proof) in proofs.iter().enumerate() {
        claims.push(verify_h21_role(&context, &key, &packet.commitment, role, proof)?);
    }
    let statement = opening_batch::Statement {
        log_n: 41, setup_id: *key.id(), commitment: pcs::decode_commitment(&packet.commitment)?,
        corpus_id: Some(common_corpus_id(&owned.public_bytes)),
        claims: claims.try_into().map_err(|_| "full structural role count")?,
    };
    opening_batch::verify_admitted(&statement, &key, &opening)?;
    Ok(VerifiedFullStructure { fields: packet.statement, statement_bytes: packet.statement_bytes, sampled, a_b })
}

fn phase<T>(name: &str, work: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
    let start = Instant::now();
    println!("FULL_STRUCTURAL phase={name} event=start");
    let result = std::thread::scope(|scope| {
        let (stop, clock) = std::sync::mpsc::channel::<()>();
        scope.spawn(move || {
            while let Err(std::sync::mpsc::RecvTimeoutError::Timeout) =
                clock.recv_timeout(std::time::Duration::from_secs(30)) {
                println!("FULL_STRUCTURAL phase={name} event=running elapsed_ms={}", start.elapsed().as_millis());
            }
        });
        let result = work();
        drop(stop);
        result
    });
    println!("FULL_STRUCTURAL phase={name} event=end ok={} elapsed_ms={}", result.is_ok(), start.elapsed().as_millis());
    result
}

fn session_prefix(identity: &[u8], key: &[u8], witness: &[u8; 64]) -> Vec<u8> {
    let mut marker = b"R4GKR001".to_vec();
    marker.extend_from_slice(&Blake2b::<U32>::digest(identity));
    marker.extend_from_slice(&Blake2b::<U32>::digest(key));
    marker.extend_from_slice(witness);
    marker
}

fn read_held(path: &Path, size: usize) -> Result<Vec<u8>, String> {
    let mut file = packed::open_untrusted_held_regular(path, size as u64)?;
    let mut bytes = vec![0; size];
    file.read_exact(&mut bytes).map_err(|e| e.to_string())?;
    Ok(bytes)
}

struct RoleStage {
    root: PathBuf,
    _lock: fs::File,
    previous_marker: Option<Vec<u8>>,
    completed: usize,
}

// Role 6 changed relation and transcript. The F60 session and first six roles
// keep their names. A stale F60 role-6 file is outside the accepted inventory.
const ROLE_FILES: [&str; 7] = ["role-0.gkr","role-1.gkr","role-2.gkr","role-3.gkr",
    "role-4.gkr","role-5.gkr","role-6-era.gkr"];

impl RoleStage {
    fn open(path: &Path, prefix: &[u8]) -> Result<Self, String> {
        if !crate::preview_test_paths::absolute_outside_source(path) {
            return Err("role stage must be an absolute path outside source".into());
        }
        let parent = fs::canonicalize(path.parent().ok_or("role stage parent")?).map_err(|e| e.to_string())?;
        let root = parent.join(path.file_name().ok_or("role stage name")?);
        let fresh = match fs::create_dir(&root) {
            Ok(()) => true,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => false,
            Err(e) => return Err(e.to_string()),
        };
        packed::check_stage_directory(&root)?;
        let lock = packed::lock_stage_file(&root.join("writer.lock"), fresh)?;
        let mut completed = [false; 7];
        let mut marker_present = false;
        for entry in fs::read_dir(&root).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            let name = entry.file_name().into_string().map_err(|_| "invalid role stage name")?;
            if name == "writer.lock" { continue; }
            if name == "session.bin" { marker_present = true; continue; }
            if let Some(role) = ROLE_FILES.iter().position(|file| name == *file) {
                drop(packed::open_untrusted_held_regular(&entry.path(), codec::GKR_BYTES[role] as u64)?);
                completed[role] = true;
            } else { return Err(format!("unexpected or partial role stage file: {name}")); }
        }
        let count = completed.iter().take_while(|seen| **seen).count();
        if completed[count..].iter().any(|seen| *seen) { return Err("noncontiguous role stage".into()); }
        if (fresh && (marker_present || count != 0)) || (!fresh && !marker_present) {
            return Err("incomplete role session marker".into());
        }
        let previous_marker = if fresh { None } else {
            let marker = read_held(&root.join("session.bin"), prefix.len() + codec::COMMITMENT_BYTES)?;
            if !marker.starts_with(prefix) { return Err("different role stage statement, key or witness".into()); }
            Some(marker)
        };
        Ok(Self { root, _lock: lock, previous_marker, completed: count })
    }

    fn publish(&self, name: &str, bytes: &[u8]) -> Result<(), String> {
        let temp = self.root.join(format!("{name}.partial"));
        let dest = self.root.join(name);
        drop(packed::create_blob(&temp, bytes)?);
        packed::publish_noreplace(&temp, &dest)?;
        drop(packed::checked_blob(&dest, bytes)?);
        Ok(())
    }

    fn bind_commitment(&self, prefix: &[u8], commitment: &[u8]) -> Result<fs::File, String> {
        if commitment.len() != codec::COMMITMENT_BYTES { return Err("role stage commitment width".into()); }
        let mut expected = prefix.to_vec();
        expected.extend_from_slice(commitment);
        if let Some(old) = &self.previous_marker {
            if old != &expected { return Err("role stage disagrees with reconstructed commitment".into()); }
        } else { self.publish("session.bin", &expected)?; }
        packed::checked_blob(&self.root.join("session.bin"), &expected)
    }
}

pub(crate) fn prove_full_structure(x: &[u8], root: [u8; 32], total: [u8; 28],
    tip: [u8; 32], tip_time: i64, parameters: [PublicMapParameters; 2],
    sampled: [u8; 28], a_b: [u8; 29], source: &packed::UntrustedH21CandidateFile,
    budget: sparse_stream_roster::H21Role1Budget, stage: &Path) -> Result<Vec<u8>, String> {
    let owned = build_full_context(x, root, total, tip, tip_time, parameters, sampled, a_b)?;
    let context = owned.context()?;
    if source.requested_logical_public_identity() != owned.witness_identity() {
        return Err("full structural witness belongs to another snapshot or cut".into());
    }
    let prefix = session_prefix(&owned.public_bytes, include_bytes!("../fixtures/verifier-keys-v1/log41.vk"),
        source.actual_blake2b512());
    let stage = RoleStage::open(stage, &prefix)?;
    println!("FULL_STRUCTURAL source_bytes={} completed_roles={} total_roles=7",
        source.untrusted_polynomial().input_len() / 8, stage.completed);
    let prover = phase("setup-commit", || H21PcsProver::regenerate(|step| println!("FULL_STRUCTURAL setup={step}")))?;
    let key_bytes = prover.key_bytes();
    let key = verifier_key::admit(41, key_bytes)?;
    let commit_phase = if stage.previous_marker.is_some() { "reconstruct-commitment" } else { "commit" };
    let session = phase(commit_phase, || H21PcsSession::commit(source, owned.witness_identity(), &prover))?;
    let commitment = pcs::encode_commitment(&session.commitment())?;
    let _held_marker = stage.bind_commitment(&prefix, &commitment)?;
    drop(prover);
    let mut roles = Vec::with_capacity(7);
    let mut claims = Vec::with_capacity(7);
    for role in 0..7 {
        let name = ROLE_FILES[role];
        let role_phase = format!("role-{role}");
        if role >= stage.completed {
          let (encoded, _) = phase(&role_phase, || Ok(match role {
            0 => context.admit_role0_diagnostic(key_bytes, &commitment)?.prove_untrusted_candidate(
                source, core_pool_boolean::H21Role0DiagnosticBudget {
                    limit_bytes: budget.limit_bytes, caller_graph_reservation_bytes: budget.caller_context_bytes,
                    unmeasured_reservation_bytes: budget.unmeasured_bytes })?,
            1 => context.prove_role1_untrusted_candidate(key_bytes, &commitment, source, budget)?,
            #[cfg(all(windows, feature = "h21-snapshot-n0"))]
            2 if detached_role::requested(detached_role::TREE) => {
                match detached_role::community_at_ordinal(detached_role::TREE, x, &context, &key, key_bytes, &commitment, source, budget)? {
                    Some(imported) => imported,
                    None => context.prove_remaining_untrusted_candidate(H21CandidateRole::Tree, key_bytes, &commitment, source, budget)?,
                }
            }
            #[cfg(all(windows, feature = "h21-snapshot-n0"))]
            4 if detached_role::requested(detached_role::HEIGHT_DAA) => {
                match detached_role::community_at_ordinal(detached_role::HEIGHT_DAA, x, &context, &key, key_bytes, &commitment, source, budget)? {
                    Some(imported) => imported,
                    None => context.prove_remaining_untrusted_candidate(H21CandidateRole::HeightDaa, key_bytes, &commitment, source, budget)?,
                }
            }
            3 if detached_role::requested(detached_role::POINT) => detached_role::import(detached_role::POINT,&context,&key,key_bytes,&commitment,
                source.actual_blake2b512())?,
            6 => match detached_role::metadata_at_ordinal(&context,&key,key_bytes,&commitment,source.actual_blake2b512())? {
                Some(imported)=>imported,
                None=>context.prove_remaining_untrusted_candidate(H21CandidateRole::Metadata,key_bytes,&commitment,source,budget)?,
            },
            5 => context.prove_role5_untrusted_candidate(key_bytes, &commitment, source,
                crate::segment_adjacency::linear_for_test::H21Role5Budget {
                    limit_bytes: budget.limit_bytes, caller_context_bytes: budget.caller_context_bytes,
                    unmeasured_bytes: budget.unmeasured_bytes })?,
            index => {
                let kind = match index { 2 => H21CandidateRole::Tree, 3 => H21CandidateRole::Point,
                    4 => H21CandidateRole::HeightDaa,
                    _ => return Err("full structural role".into()) };
                context.prove_remaining_untrusted_candidate(kind, key_bytes, &commitment, source, budget)?
            }
          }))?;
          if encoded.len() != codec::GKR_BYTES[role] { return Err("produced role GKR extent".into()); }
          stage.publish(name, &encoded)?;
        }
        let encoded = read_held(&stage.root.join(name), codec::GKR_BYTES[role])?;
        let proof = gkr::decode_dimensions(&[codec::INPUT_BITS[role] as usize], &encoded)?;
        if gkr::encode_proof(&proof)? != encoded { return Err("noncanonical produced role".into()); }
        claims.push(phase(&format!("verify-role-{role}"), ||
            verify_h21_role(&context, &key, &commitment, role, &proof))?);
        println!("FULL_STRUCTURAL verified_roles={} total_roles=7 reused={} gkr_bytes={}",
            role+1, role < stage.completed, encoded.len());
        roles.push(encoded);
    }
    let statement = opening_batch::Statement { log_n: 41, setup_id: *key.id(),
        commitment: session.commitment(), corpus_id: Some(common_corpus_id(&owned.public_bytes)),
        claims: claims.try_into().map_err(|_| "full structural common role count")? };
    let prover = phase("setup-opening", || H21PcsProver::regenerate(|step| println!("FULL_STRUCTURAL setup={step}")))?;
    let (common, _) = phase("common-pcs", || session.prove_unverified(&prover, &statement))?;
    let opening = opening_batch::decode_proof(&common, 41)?;
    if opening_batch::encode_proof(&opening, 41)? != common { return Err("noncanonical produced common opening".into()); }
    phase("verify-common-pcs", || opening_batch::verify_admitted(&statement, &key, &opening))?;
    let fields = codec::H21Statement { root, total, tip, tip_time, parameters };
    codec::encode_packet(&codec::DecodedH21Packet { statement_bytes: codec::encode_statement(&fields)?,
        statement: fields, key: key_bytes.to_vec(), commitment,
        roles: roles.try_into().map_err(|_| "full structural packet role count")?, common })
}

#[test]
fn era_format_and_checkpoint_names_partition_the_revision() {
    assert!(matches!(codec::decode_packet(b"H21ATOM1"), Err(e) if e == "H21 packet magic"));
    assert!(matches!(codec::decode_packet(b"H21ATOM2"), Err(e) if e == "H21 truncated input"));
    for role in 0..6 {
        assert_eq!(ROLE_FILES[role], format!("role-{role}.gkr"));
    }
    assert!(!ROLE_FILES.contains(&"role-6.gkr"));
    assert_eq!(ROLE_FILES[6], "role-6-era.gkr");
}

#[cfg(all(test, windows, feature = "h21-snapshot-n0"))]
pub(crate) fn compare_f60_checkpoint_prefixes(owned: &H21StructuralDiagnostic,
    marker: &[u8]) -> Result<(), String> {
    let key_bytes = include_bytes!("../fixtures/verifier-keys-v1/log41.vk");
    let key = verifier_key::admit(41, key_bytes)?;
    let witness = marker.get(72..136).ok_or("short native marker")?.try_into().unwrap();
    let c = marker.get(136..).ok_or("missing commitment")?;
    let prefix = session_prefix(&owned.public_bytes, key_bytes, witness);
    if !marker.starts_with(&prefix) || c.len() != codec::COMMITMENT_BYTES ||
        pcs::encode_commitment(&pcs::decode_commitment(c)?)? != c {
        return Err("F60 public identity, marker or commitment changed".into());
    }
    assert_ne!(&common_corpus_id(&owned.public_bytes)[..], &marker[8..40]);
    let context = owned.context()?;
    for role in 0..7 {
        // Recreate the frozen F60 initialization independently of the new domain list.
        let mut legacy = if role == 0 {
            H21Role0DiagnosticInputs::new(&owned.public_bytes, key_bytes, c)?.fresh_transcript()?
        } else {
            let domain = format!("nipopow-h21-role{role}-atomic-structural-diagnostic-v1");
            let mut t = Transcript::new(domain.as_bytes());
            t.append_bytes(b"setup-id",key.id());
            t.append_u64(b"H21-atomic-key-log",key.log_n() as u64);
            t.append_bytes(b"commitment",c);
            t.append_bytes(b"H21-atomic-public-identity",&owned.public_bytes);
            t.append_u64(b"role-index",role as u64);
            t.append_bytes(b"role-domain",ROLES[role]);
            t
        };
        let mut revised = fresh_h21_role_prefix(&owned.public_bytes, &key, c, role)?;
        if role < 6 {
            bind_h21_role(&context,role,&mut legacy)?;
            bind_h21_role(&context,role,&mut revised)?;
            assert_eq!(legacy.bytes_absorbed(),revised.bytes_absorbed());
        }
        let old = legacy.try_challenge_scalar(b"checkpoint-prefix-comparison")?;
        let new = revised.try_challenge_scalar(b"checkpoint-prefix-comparison")?;
        assert_eq!(old == new, role < 6, "F60 prefix compatibility at role {role}");
    }
    Ok(())
}

#[test]
fn full_statement_identity_binds_cut_outputs_and_exact_bytes() {
    let total = [0xff; 28];
    let sampled = [0; 28];
    let ab = [0; 29];
    let id = full_identity(b"descriptor", b"profile", total, sampled, ab).unwrap();
    for split in 1..17 {
        let joined = b"descriptorprofile";
        if split != 10 {
            assert_ne!(id, full_identity(&joined[..split], &joined[split..], total, sampled, ab).unwrap());
        }
    }
    let mut changed = sampled;
    changed[27] = 1;
    assert_ne!(id, full_identity(b"descriptor", b"profile", total, changed, ab).unwrap());
    assert!(full_identity(b"descriptor", b"profile", [0; 28], changed, ab).is_err());
    let mut changed = ab;
    changed[0] = 1;
    assert_ne!(id, full_identity(b"descriptor", b"profile", total, sampled, changed).unwrap());
    changed[0] = 2;
    assert!(full_identity(b"descriptor", b"profile", total, sampled, changed).is_err());
}

#[test]
fn full_x_changes_every_role_first_challenge_including_role_zero() -> Result<(), String> {
    use dory_pcs::{backends::arkworks::ArkGT, primitives::arithmetic::Group};
    let key = verifier_key::admit(41, include_bytes!("../fixtures/verifier-keys-v1/log41.vk"))?;
    let c = pcs::encode_commitment(&ArkGT::identity())?;
    let original = full_identity(b"geometry", b"full-x-A", [0xff;28], [0;28], [0;29])?;
    let changed = full_identity(b"geometry", b"full-x-B", [0xff;28], [0;28], [0;29])?;
    for role in 0..7 {
        let first = |id: &[u8]| {
            let mut prefix = fresh_h21_role_prefix(id, &key, &c, role)?;
            assert_eq!((prefix.raw_queries(), prefix.challenges()), (0, 0));
            prefix.try_challenge_scalar(b"full-x-binding-test")
        };
        assert_ne!(first(&original)?, first(&changed)?, "role {role}");
        if role == 0 {
            let admitted = H21Role0DiagnosticInputs::new(&original,
                include_bytes!("../fixtures/verifier-keys-v1/log41.vk"), &c)?;
            assert_eq!(admitted.fresh_transcript()?.try_challenge_scalar(b"full-x-binding-test")?,
                first(&original)?);
        }
    }
    Ok(())
}

#[cfg(windows)]
#[test]
fn full_role_checkpoints_refuse_partial_or_different_sessions() -> Result<(), String> {
    let id = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let path = std::env::temp_dir().join(format!("r4-role-stage-{}-{id}", std::process::id()));
    let prefix = session_prefix(b"fixture-x", b"fixture-key", &[0x61;64]);
    let c = [0x42; codec::COMMITMENT_BYTES];
    {
        let stage = RoleStage::open(&path, &prefix)?;
        let _marker = stage.bind_commitment(&prefix, &c)?;
        assert!(RoleStage::open(&path, &prefix).is_err(), "concurrent stage writer");
        let bytes = vec![0x55; codec::GKR_BYTES[0]];
        stage.publish("role-0.gkr", &bytes)?;
        assert_eq!(read_held(&stage.root.join("role-0.gkr"), bytes.len())?, bytes);
    }
    for wrong in [
        session_prefix(b"different-x", b"fixture-key", &[0x61;64]),
        session_prefix(b"fixture-x", b"different-key", &[0x61;64]),
        session_prefix(b"fixture-x", b"fixture-key", &[0x62;64]),
    ] {
        assert!(matches!(RoleStage::open(&path, &wrong), Err(e) if e.contains("different role stage")));
    }
    {
        let stage = RoleStage::open(&path, &prefix)?;
        assert_eq!(stage.completed, 1);
        let mut wrong = c;
        wrong[0] ^= 1;
        assert!(matches!(stage.bind_commitment(&prefix, &wrong), Err(e) if e.contains("reconstructed commitment")));
        let _marker = stage.bind_commitment(&prefix, &c)?;
        // A torn/unpublished role is retained and requires a new clean stage
        // or explicit recovery. Earlier completed role bytes stay untouched.
        drop(packed::create_blob(&stage.root.join("role-1.gkr.partial"), b"torn")?);
    }
    assert!(matches!(RoleStage::open(&path, &prefix), Err(e) if e.contains("partial role stage file")));
    assert_eq!(read_held(&path.join("role-0.gkr"), codec::GKR_BYTES[0])?,
        vec![0x55; codec::GKR_BYTES[0]]);
    Ok(())
}

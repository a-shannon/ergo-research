//! Cold verification of the bounded internal C559 case, not a production codec.
use std::{fs::{self, File, Metadata}, io::Read, path::{Component, Path, PathBuf}, time::Instant};
use serde::{Deserialize, Serialize};
use blake2::{digest::consts::U32, Blake2b, Digest};

use super::{Core3TreeDiagnosticVerifier, Core3TreeProofBundle, Core3TreeProofHeader,
    JoinedHistoryProofEntry, JoinedHistoryProofHeader, CORE3_TREE_DOMAIN, CORE3_TREE_PROFILE};
use crate::{pcs, verifier_key, work_tree_history_plan::WorkTreeHistoryPlan, work_tree_layout};

const NAMES: [&str; 12] = ["work.gkr.bin", "work.pcs.bin", "pair0.gkr.bin", "pair0.pcs.bin",
    "pair2.gkr.bin", "pair2.pcs.bin", "tree.gkr.bin", "tree.pcs.bin", "commitment.bin",
    "log22.vk", "context.json", "files.json"];
const EXACT: [usize; 10] = [5024, 29421, 4800, 29421, 4800, 29421, 5024, 29421, 384, 23664];
const CASE_BOUND: usize = 1_048_576;
const CONTEXT_BOUND: usize = 32_768;
const MANIFEST_BOUND: usize = 16_384;
const MAX_INTEGER: u64 = 9_007_199_254_740_991;

#[derive(Debug)]
pub struct ColdCaseError {
    pub phase: &'static str,
    pub cause: String,
}
impl std::fmt::Display for ColdCaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.phase, self.cause)
    }
}
impl std::error::Error for ColdCaseError {}
fn error(phase: &'static str, cause: impl Into<String>) -> ColdCaseError {
    ColdCaseError { phase, cause: cause.into() }
}

/// A verified n4 statement and this call's distinct consumer costs.
#[derive(Debug)]
pub struct ColdCaseVerification {
    pub root: [u8; 32],
    pub total_be28: [u8; 28],
    pub key_id: [u8; 32],
    pub case_bytes: usize,
    pub io_hash_parse_ms: u128,
    pub key_admission_ms: u128,
    pub plan_construction_ms: u128,
    pub four_proof_replay_ms: u128,
}

// serde_json's deserialize_struct also accepts sequences. Require a map at
// EVERY object boundary, then reuse derive's duplicate/unknown-field checks.
macro_rules! closed_object {
    ($name:ident { $($field:ident: $ty:ty),* $(,)? }) => {
        #[derive(Clone, Serialize)]
        struct $name { $($field: $ty),* }
        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                #[derive(Deserialize)]
                #[serde(deny_unknown_fields)]
                struct Fields { $($field: $ty),* }
                struct ObjectVisitor;
                impl<'de> serde::de::Visitor<'de> for ObjectVisitor {
                    type Value = $name;
                    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        f.write_str("a JSON object")
                    }
                    fn visit_map<M: serde::de::MapAccess<'de>>(self, map: M) -> Result<$name, M::Error> {
                        let fields = Fields::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;
                        Ok($name { $($field: fields.$field),* })
                    }
                }
                deserializer.deserialize_map(ObjectVisitor)
            }
        }
    };
}
closed_object!(FileMeta { file: String, bytes: u64, blake2b256: String });
closed_object!(BodyMeta {
    role: String, tag: u64, gkr_input_log: u64, row_log: u64, pcs_input_log: u64,
    gkr: FileMeta, pcs: FileMeta,
});
closed_object!(Measurements {
    witness: u64, setup_and_key: u64, commit: u64, verifier_plan_admission: u64,
    proof_production: u64, verification_only: u64,
});
closed_object!(Context {
    schema: String, version: u64, profile: String, coverage: [u64; 4],
    root: String, total_be28: String, headers: u64, slot_log: u64, pair_starts: [u64; 2],
    key_log_n: u64, key_id: String, key_file: String, key_blake2b256: String,
    pcs_mode: String, vendor: String, commitment_file: String, commitment_hex: String,
    commitment_blake2b256: String, tree_source_blake2b256: String,
    tree_input_log: u64, tree_row_log: u64, tree_terms: u64, tree_families: u64,
    tree_domain: String, bodies: [BodyMeta; 4], measurements_ms: Measurements,
});

fn upper_hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{b:02X}")).collect() }
fn hash(bytes: &[u8]) -> String { upper_hex(&Blake2b::<U32>::digest(bytes)) }
fn hex<const N: usize>(text: &str, lowercase: bool, field: &str) -> Result<[u8; N], ColdCaseError> {
    let width = N.checked_mul(2).ok_or_else(|| error("context", "hex width overflow"))?;
    if text.len() != width { return Err(error("context", format!("{field} hex width"))); }
    fn digit(b: u8, lower: bool) -> Option<u8> {
        match b { b'0'..=b'9' => Some(b-b'0'), b'a'..=b'f' if lower => Some(b-b'a'+10),
            b'A'..=b'F' if !lower => Some(b-b'A'+10), _ => None }
    }
    let mut out = [0u8; N];
    for (dst, pair) in out.iter_mut().zip(text.as_bytes().chunks_exact(2)) {
        let hi = digit(pair[0], lowercase).ok_or_else(|| error("context", format!("{field} canonical hex case")))?;
        let lo = digit(pair[1], lowercase).ok_or_else(|| error("context", format!("{field} canonical hex case")))?;
        *dst = (hi << 4) | lo;
    }
    Ok(out)
}

// Inspect only tokens outside strings. The typed parser still owns JSON syntax,
// duplicate/unknown fields, UTF-8, fixed arrays and the recursion limit.
fn integer_tokens(bytes: &[u8]) -> Result<(), ColdCaseError> {
    if bytes.starts_with(&[0xef, 0xbb, 0xbf]) { return Err(error("json", "BOM is not accepted")); }
    std::str::from_utf8(bytes).map_err(|_| error("json", "invalid UTF-8"))?;
    let (mut i, mut quoted, mut escaped) = (0usize, false, false);
    while i < bytes.len() {
        let b = bytes[i];
        if quoted {
            if escaped { escaped = false; }
            else if b == b'\\' { escaped = true; }
            else if b == b'"' { quoted = false; }
            i += 1;
            continue;
        }
        if b == b'"' { quoted = true; i += 1; continue; }
        if b == b'-' { return Err(error("json", "negative integer token")); }
        if b.is_ascii_digit() {
            let start = i;
            let mut value = 0u64;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                value = value.checked_mul(10).and_then(|v| v.checked_add(u64::from(bytes[i]-b'0')))
                    .ok_or_else(|| error("json", "integer overflow"))?;
                if value > MAX_INTEGER { return Err(error("json", "unsafe integer token")); }
                i += 1;
            }
            if i-start > 1 && b == b'0' { return Err(error("json", "leading-zero integer token")); }
            if i < bytes.len() && matches!(bytes[i], b'.' | b'e' | b'E' | b'+' | b'-') {
                return Err(error("json", "fraction or exponent integer token"));
            }
            continue;
        }
        i += 1;
    }
    Ok(())
}
fn parse<T: serde::de::DeserializeOwned>(bytes: &[u8], cap: usize) -> Result<T, ColdCaseError> {
    if bytes.is_empty() || bytes.len() > cap { return Err(error("bounds", "JSON byte bound")); }
    integer_tokens(bytes)?;
    serde_json::from_slice(bytes).map_err(|e| error("json", e.to_string()))
}
fn debit(total: &mut usize, bytes: usize) -> Result<(), ColdCaseError> {
    let next = total.checked_add(bytes).ok_or_else(|| error("bounds", "aggregate overflow"))?;
    if next > CASE_BOUND { return Err(error("bounds", "aggregate byte bound")); }
    *total = next;
    Ok(())
}
fn check_length(index: usize, len: u64) -> Result<usize, ColdCaseError> {
    let len = usize::try_from(len).map_err(|_| error("bounds", "file length conversion"))?;
    let valid = if index < EXACT.len() { len == EXACT[index] }
        else { len > 0 && len <= if index == 10 { CONTEXT_BOUND } else { MANIFEST_BOUND } };
    if !valid { return Err(error("bounds", format!("{} file extent", NAMES[index]))); }
    Ok(len)
}

// Decide from the attributes this application observes. Windows may hide Cloud
// reparse attributes; this is not physical Cloud-file detection. The caller
// still supplies an immutable snapshot with no name redirection.
fn observed_nonreparse(is_symlink: bool, attributes: u32) -> bool {
    !is_symlink && attributes & 0x400 == 0
}
fn no_reparse(meta: &Metadata) -> bool {
    #[cfg(windows)] {
        use std::os::windows::fs::MetadataExt;
        observed_nonreparse(meta.file_type().is_symlink(), meta.file_attributes())
    }
    #[cfg(not(windows))] { observed_nonreparse(meta.file_type().is_symlink(), 0) }
}
fn require_regular_nonreparse(meta: &Metadata) -> Result<(), ColdCaseError> {
    if !meta.is_file() || !no_reparse(meta) {
        return Err(error("filesystem", "case file link or non-regular file"));
    }
    Ok(())
}
fn check_ancestors(path: &Path) -> Result<(), ColdCaseError> {
    if !path.is_absolute() || path.components().any(|c| matches!(c, Component::ParentDir | Component::CurDir)) {
        return Err(error("filesystem", "case root must be an absolute normalized path"));
    }
    #[cfg(windows)] {
        if !matches!(path.components().next(), Some(Component::Prefix(p)) if matches!(p.kind(), std::path::Prefix::Disk(_))) {
            return Err(error("filesystem", "case root must use a local Windows drive"));
        }
        for component in path.components() {
            if let Component::Normal(name) = component {
                let name = name.to_str().ok_or_else(|| error("filesystem", "non-UTF8 root component"))?;
                if name.contains(':') || name.ends_with('.') || name.ends_with(' ') {
                    return Err(error("filesystem", "root path alias or alternate stream"));
                }
            }
        }
    }
    for ancestor in path.ancestors() {
        let meta = fs::symlink_metadata(ancestor).map_err(|e| error("filesystem", e.to_string()))?;
        if !meta.is_dir() || !no_reparse(&meta) { return Err(error("filesystem", "root/ancestor link or non-directory")); }
    }
    Ok(())
}
fn check_roster(path: &Path) -> Result<(), ColdCaseError> {
    let mut seen = [false; 12];
    let entries = fs::read_dir(path).map_err(|e| error("filesystem", e.to_string()))?;
    let mut count = 0usize;
    for entry in entries.take(13) {
        count += 1;
        if count > 12 { return Err(error("filesystem", "extra case entry")); }
        let entry = entry.map_err(|e| error("filesystem", e.to_string()))?;
        let name = entry.file_name();
        let name = name.to_str().ok_or_else(|| error("filesystem", "non-UTF8 case name"))?;
        let index = NAMES.iter().position(|expected| *expected == name)
            .ok_or_else(|| error("filesystem", "unexpected literal case name"))?;
        if seen[index] { return Err(error("filesystem", "duplicate case name")); }
        let meta = fs::symlink_metadata(entry.path()).map_err(|e| error("filesystem", e.to_string()))?;
        require_regular_nonreparse(&meta)?;
        seen[index] = true;
    }
    if count != 12 || seen.contains(&false) { return Err(error("filesystem", "missing case file")); }
    Ok(())
}
fn open_snapshot(path: &Path) -> Result<File, ColdCaseError> {
    #[cfg(windows)] {
        use std::os::windows::fs::OpenOptionsExt;
        // FILE_SHARE_READ only; FILE_FLAG_OPEN_REPARSE_POINT. The controller
        // supplies immutable ancestors; this is not an ancestor-race theorem.
        let file = fs::OpenOptions::new().read(true).share_mode(1).custom_flags(0x0020_0000)
            .open(path).map_err(|e| error("filesystem", e.to_string()))?;
        let meta = file.metadata().map_err(|e| error("filesystem", e.to_string()))?;
        require_regular_nonreparse(&meta)?;
        if !meta.permissions().readonly() {
            return Err(error("filesystem", "snapshot file must be readonly"));
        }
        Ok(file)
    }
    #[cfg(not(windows))] {
        let _ = path;
        Err(error("filesystem", "internal snapshot reader currently requires Windows"))
    }
}

struct LoadedCase {
    files: [Vec<u8>; 12],
    context: Context,
    root: [u8; 32],
    total: [u8; 28],
    key_id: [u8; 32],
    bytes: usize,
    directory: PathBuf,
    _handles: Vec<File>,
}
fn check_meta(meta: &FileMeta, index: usize, bytes: &[u8]) -> Result<(), ColdCaseError> {
    hex::<32>(&meta.blake2b256, false, "file hash")?;
    if meta.file != NAMES[index] || meta.bytes != bytes.len() as u64 || meta.blake2b256 != hash(bytes) {
        return Err(error("integrity", format!("{} metadata/hash differs", NAMES[index])));
    }
    Ok(())
}
fn check_context(c: &Context, files: &[Vec<u8>; 12])
    -> Result<([u8; 32], [u8; 28], [u8; 32]), ColdCaseError>
{
    if c.schema != "nipopow-c559-internal-four-claim-case-v1" || c.version != 1
        || c.profile.as_bytes() != CORE3_TREE_PROFILE || c.coverage != [0,1,2,3]
        || c.headers != 4 || c.slot_log != 2 || c.pair_starts != [0,2] || c.key_log_n != 22
        || c.tree_input_log != 22 || c.tree_row_log != 21 || c.tree_terms != 126573 || c.tree_families != 23
        || c.tree_domain.as_bytes() != CORE3_TREE_DOMAIN || c.pcs_mode != "Transparent-dory-v1"
        || c.vendor != upper_hex(pcs::VENDOR_PIN)
    { return Err(error("context", "fixed profile/geometry/coverage/vendor differs")); }
    hex::<32>(&c.tree_source_blake2b256, true, "Tree source identity")?;
    if c.tree_source_blake2b256 != work_tree_layout::hash_bytes(include_bytes!("h4_analytic.rs")) {
        return Err(error("context", "Tree source identity differs"));
    }
    let root = hex::<32>(&c.root, false, "root")?;
    let total = hex::<28>(&c.total_be28, false, "total")?;
    let key_id = hex::<32>(&c.key_id, false, "key ID")?;
    let commitment = hex::<384>(&c.commitment_hex, false, "commitment")?;
    hex::<32>(&c.commitment_blake2b256, false, "commitment hash")?;
    hex::<32>(&c.key_blake2b256, false, "key hash")?;
    if c.commitment_file != NAMES[8] || c.key_file != NAMES[9]
        || commitment.as_slice() != files[8].as_slice()
        || c.commitment_blake2b256 != hash(&files[8]) || c.key_blake2b256 != hash(&files[9])
    { return Err(error("context", "C/key redundant metadata differs")); }
    for (i, body) in c.bodies.iter().enumerate() {
        if body.role != ["work","pair0","pair2","tree"][i] || body.tag != i as u64
            || body.gkr_input_log != [22,21,21,22][i] || body.row_log != [18,20,20,21][i]
            || body.pcs_input_log != 22
        { return Err(error("context", "ordered role/body dimensions differ")); }
        check_meta(&body.gkr, 2*i, &files[2*i])?;
        check_meta(&body.pcs, 2*i+1, &files[2*i+1])?;
    }
    // Existing canonical/subgroup decoder, before expensive public factories.
    pcs::decode_commitment(&files[8]).map_err(|e| error("commitment", e))?;
    Ok((root, total, key_id))
}
fn load_case(path: &Path) -> Result<LoadedCase, ColdCaseError> {
    check_ancestors(path)?;
    check_roster(path)?;
    let mut handles = Vec::new();
    handles.try_reserve_exact(12).map_err(|_| error("bounds", "handle allocation"))?;
    let mut lengths = [0usize; 12];
    let mut total = 0usize;
    for (i, name) in NAMES.iter().enumerate() {
        let handle = open_snapshot(&path.join(name))?;
        let meta = handle.metadata().map_err(|e| error("filesystem", e.to_string()))?;
        lengths[i] = check_length(i, meta.len())?;
        debit(&mut total, lengths[i])?;
        handles.push(handle);
    }
    let mut files: [Vec<u8>; 12] = std::array::from_fn(|_| Vec::new());
    for (i, file) in handles.iter_mut().enumerate() {
        let before = file.metadata().map_err(|e| error("filesystem", e.to_string()))?;
        let before_modified = before.modified().map_err(|e| error("filesystem", e.to_string()))?;
        files[i].try_reserve_exact(lengths[i]).map_err(|_| error("bounds", "bounded file allocation"))?;
        files[i].resize(lengths[i], 0);
        file.read_exact(&mut files[i]).map_err(|e| error("bounds", format!("bounded read: {e}")))?;
        let mut extra = [0u8; 1];
        if file.read(&mut extra).map_err(|e| error("filesystem", e.to_string()))? != 0 {
            return Err(error("bounds", "trailing snapshot byte"));
        }
        let after = file.metadata().map_err(|e| error("filesystem", e.to_string()))?;
        let after_modified = after.modified().map_err(|e| error("filesystem", e.to_string()))?;
        if before.len() != after.len() || before_modified != after_modified
            || !no_reparse(&after) || !after.permissions().readonly()
        { return Err(error("filesystem", "snapshot file changed")); }
    }
    check_ancestors(path)?;
    check_roster(path)?;
    let context: Context = parse(&files[10], CONTEXT_BOUND)?;
    let manifest: [FileMeta; 11] = parse(&files[11], MANIFEST_BOUND)?;
    for (i, meta) in manifest.iter().enumerate() { check_meta(meta, i, &files[i])?; }
    let (root, work_total, key_id) = check_context(&context, &files)?;
    Ok(LoadedCase { files, context, root, total: work_total, key_id, bytes: total,
        directory: path.to_path_buf(), _handles: handles })
}
fn bundle(case: &LoadedCase) -> Result<Core3TreeProofBundle, ColdCaseError> {
    let c = &case.context;
    let narrow = |v: u64| usize::try_from(v).map_err(|_| error("context", "dimension conversion"));
    let header = Core3TreeProofHeader {
        core3: JoinedHistoryProofHeader { root: case.root, total_be28: case.total,
            headers: c.headers, slot_log: narrow(c.slot_log)?, pair_starts: c.pair_starts,
            key_id: case.key_id, canonical_commitment: case.files[8].clone() },
        version: c.version, profile: c.profile.as_bytes().to_vec(),
        coverage: [u8::try_from(c.coverage[0]).map_err(|_| error("context", "role conversion"))?,
            u8::try_from(c.coverage[1]).map_err(|_| error("context", "role conversion"))?,
            u8::try_from(c.coverage[2]).map_err(|_| error("context", "role conversion"))?,
            u8::try_from(c.coverage[3]).map_err(|_| error("context", "role conversion"))?],
        pcs_input_log: narrow(c.key_log_n)?, tree_input_log: narrow(c.tree_input_log)?,
        tree_row_log: narrow(c.tree_row_log)?, tree_terms: narrow(c.tree_terms)?,
        tree_families: narrow(c.tree_families)?, tree_source: c.tree_source_blake2b256.clone(),
    };
    let entries = (0..4).map(|i| Ok(JoinedHistoryProofEntry {
        kind_tag: u8::try_from(c.bodies[i].tag).map_err(|_| error("context", "body tag conversion"))?,
        gkr_bytes: case.files[2*i].clone(), pcs_bytes: case.files[2*i+1].clone(),
    })).collect::<Result<Vec<_>, ColdCaseError>>()?;
    Ok(Core3TreeProofBundle { header, entries })
}

/// Verify the complete internal case from an immutable local Windows snapshot.
/// Ancestors and names are controlled by the caller; metadata guards use the
/// attributes observed by this application, not hidden physical Cloud state.
/// Custody receipts and producer measurements never replace cryptographic replay.
pub fn verify_internal_four_claim_case(path: &Path) -> Result<ColdCaseVerification, ColdCaseError> {
    let timer = Instant::now();
    let case = load_case(path)?;
    let encoded = bundle(&case)?;
    let mut io_hash_parse_ms = timer.elapsed().as_millis();
    let timer = Instant::now();
    let key = verifier_key::admit(22, &case.files[9]).map_err(|e| error("key_admission", e))?;
    if key.id() != &case.key_id { return Err(error("key_admission", "key ID differs from admitted key")); }
    let key_admission_ms = timer.elapsed().as_millis();
    let timer = Instant::now();
    let parent = WorkTreeHistoryPlan::compile(4, 2, case.root, case.total).map_err(|e| error("plan", e))?;
    let verifier = Core3TreeDiagnosticVerifier::new(&parent, &key, &case.files[8]).map_err(|e| error("plan", e))?;
    if encoded.header != verifier.expected_header() {
        return Err(error("context", "checked case header differs from verifier-owned header"));
    }
    let plan_construction_ms = timer.elapsed().as_millis();
    let guard_timer = Instant::now();
    check_ancestors(&case.directory)?;
    check_roster(&case.directory)?;
    // Account the final filesystem guard as I/O, outside plan and replay time.
    io_hash_parse_ms = io_hash_parse_ms.checked_add(guard_timer.elapsed().as_millis())
        .ok_or_else(|| error("bounds", "I/O duration overflow"))?;
    let timer = Instant::now();
    verifier.verify_bundle(&encoded).map_err(|e| error("replay", e))?;
    let four_proof_replay_ms = timer.elapsed().as_millis();
    let report = ColdCaseVerification { root: case.root, total_be28: case.total, key_id: case.key_id,
        case_bytes: case.bytes, io_hash_parse_ms, key_admission_ms, plan_construction_ms, four_proof_replay_ms };
    drop(case); // keep all snapshot handles alive through actual four-proof replay
    Ok(report)
}

#[cfg(test)]
#[path = "core3_tree_case_consumer_tests.rs"]
mod tests;

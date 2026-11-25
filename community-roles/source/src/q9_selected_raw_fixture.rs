//! Test-only custody for the selected q9 RAW header bundle.
//!
//! This fixture admits only scattered RAW bytes. It carries no authenticated
//! parent-root or total authority and deliberately exposes no decoded headers,
//! imports, terms, or caller-supplied witness state.

use serde::Deserialize;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Read,
    path::{Path, PathBuf},
};

const MANIFEST_BYTES: u64 = 2_146;
const MANIFEST_READ_CAP: u64 = 4_096;
const MANIFEST_SHA256: &str = "B24824F635CFDED201F0E45D6CD822A17A86D52550F8F2283576152CC16D32F2";
const FRAME_BYTES: u64 = 1_321_781_831;
const FRAME_SHA256: &str = "a68d86562a56c5b71cf2180e4762bf8775b1061b6953bff7281ec50b7ee52c5e";
const PREFIX_BYTES: u64 = 2_888_602;
const PREFIX_OPAQUE_TAIL_BYTES: u64 = 1_318_893_229;
const Q9_HEIGHTS: [u32; 10] = [
    2_048, 3_072, 4_096, 5_120, 6_144, 7_168, 8_192, 9_216, 10_176, 10_177,
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Q9RawIdentity {
    SelectedRawFixture,
}

#[derive(Debug)]
pub(crate) struct CheckedQ9RawFixture {
    identity: Q9RawIdentity,
    raw_by_height: BTreeMap<u32, Vec<u8>>,
}

impl CheckedQ9RawFixture {
    /// Validate the pinned eleven-member bundle (manifest plus ten RAW files).
    pub(crate) fn load(dir: &Path) -> Result<Self, String> {
        let manifest_path = dir.join("manifest.json");
        let manifest_bytes = read_bounded(&manifest_path, MANIFEST_READ_CAP)?;
        let json: serde_json::Value = serde_json::from_slice(&manifest_bytes)
            .map_err(|e| format!("q9 manifest JSON: {e}"))?;
        reject_parent_authority_claims(&json)?;
        if manifest_bytes.len() as u64 != MANIFEST_BYTES {
            return Err("q9 exact manifest length mismatch".into());
        }

        let mut canonical = serde_json::to_vec(&json)
            .map_err(|e| format!("q9 canonical JSON: {e}"))?;
        canonical.push(b'\n');
        if canonical != manifest_bytes {
            return Err("q9 manifest is not canonical compact sorted-key LF JSON".into());
        }
        let manifest: Manifest = serde_json::from_slice(&manifest_bytes)
            .map_err(|e| format!("q9 strict manifest schema: {e}"))?;
        if manifest_sha256(&manifest_bytes)? != MANIFEST_SHA256 {
            return Err("q9 exact manifest SHA256 mismatch".into());
        }
        validate_manifest(&manifest)?;
        validate_roster(dir)?;

        let mut raw_by_height = BTreeMap::new();
        let mut previous_end = 0u64;
        for (entry, expected_height) in manifest.headers.iter().zip(Q9_HEIGHTS) {
            if entry.height != expected_height {
                return Err("q9 exact sorted header-height roster mismatch".into());
            }
            let expected_name = format!("header-{expected_height:07}.bin");
            if entry.file != expected_name {
                return Err("q9 RAW filename is not the canonical basename".into());
            }
            if entry.bytes == 0 || entry.bytes > 514 {
                return Err("q9 RAW size outside per-header cap".into());
            }
            let end = entry.offset.checked_add(entry.bytes)
                .ok_or("q9 RAW offset extent overflow")?;
            if entry.offset < previous_end || end > manifest.prefix.bytes {
                return Err("q9 RAW offset outside ordered checked prefix".into());
            }
            previous_end = end;

            let bytes = read_bounded(&dir.join(&entry.file), 514)?;
            if bytes.len() as u64 != entry.bytes {
                return Err(format!("q9 RAW size mismatch at height {expected_height}"));
            }
            if manifest_sha256(&bytes)?.to_ascii_lowercase() != entry.sha256 {
                return Err(format!("q9 RAW SHA256 mismatch at height {expected_height}"));
            }
            let header = ergo_header_core::Header::decode(&bytes, None)
                .map_err(|e| format!("q9 RAW decode at height {expected_height}: {e:?}"))?;
            if header.height != expected_height {
                return Err(format!("q9 embedded header height mismatch at {expected_height}"));
            }
            let reencoded = header.encode()
                .map_err(|e| format!("q9 header reencode at height {expected_height}: {e:?}"))?;
            if reencoded != bytes {
                return Err(format!("q9 canonical header reencode mismatch at {expected_height}"));
            }
            if raw_by_height.insert(expected_height, bytes).is_some() {
                return Err("duplicate q9 RAW height".into());
            }
        }
        if raw_by_height.len() != Q9_HEIGHTS.len() {
            return Err("q9 RAW roster incomplete".into());
        }
        Ok(Self { identity: Q9RawIdentity::SelectedRawFixture, raw_by_height })
    }

    /// The only authority label admitted by this fixture.
    pub(crate) fn identity(&self) -> Q9RawIdentity {
        self.identity
    }

    /// Return immutable, previously checked canonical RAW bytes by embedded height.
    pub(crate) fn checked_raw(&self, height: u32) -> Result<&[u8], String> {
        self.raw_by_height.get(&height).map(Vec::as_slice)
            .ok_or_else(|| format!("height {height} is outside SelectedRawFixture"))
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawPin {
    height: u32,
    file: String,
    offset: u64,
    bytes: u64,
    sha256: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FramePin {
    bytes: u64,
    sha256: String,
    anchor_height: u32,
    tip_height: u32,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PrefixPin {
    last_height: u32,
    bytes: u64,
    opaque_tail_bytes: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    format: String,
    test_only: bool,
    validation_scope: String,
    frame: FramePin,
    prefix: PrefixPin,
    max_read_request: u64,
    source_pins_sha256: BTreeMap<String, String>,
    canonical_json: String,
    headers: Vec<RawPin>,
}

fn manifest_sha256(bytes: &[u8]) -> Result<String, String> {
    crate::native_prefix_auth_plan::role0_sha256(bytes)
        .map(|digest| digest.iter().map(|b| format!("{b:02X}")).collect())
        .map_err(|e| format!("q9 SHA256: {e}"))
}

fn read_bounded(path: &Path, cap: u64) -> Result<Vec<u8>, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|e| format!("q9 input metadata {}: {e}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() == 0 || metadata.len() > cap {
        return Err(format!("q9 input is not a nonempty regular file within cap: {}", path.display()));
    }
    let mut file = fs::File::open(path)
        .map_err(|e| format!("q9 input open {}: {e}", path.display()))?;
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    (&mut file).take(cap + 1).read_to_end(&mut bytes)
        .map_err(|e| format!("q9 bounded read {}: {e}", path.display()))?;
    if bytes.len() as u64 != metadata.len() || bytes.len() as u64 > cap {
        return Err(format!("q9 input changed or exceeded cap: {}", path.display()));
    }
    Ok(bytes)
}

fn reject_parent_authority_claims(json: &serde_json::Value) -> Result<(), String> {
    let object = json.as_object().ok_or("q9 manifest must be an object")?;
    for key in ["parent_root", "root", "total", "total_headers", "authenticated_parent"] {
        if object.contains_key(key) {
            return Err(format!("SelectedRawFixture forbids parent/root/total authority claim: {key}"));
        }
    }
    Ok(())
}

fn validate_manifest(manifest: &Manifest) -> Result<(), String> {
    if manifest.format != "H21-Q9-RAW-EXTRACT-1"
        || !manifest.test_only
        || manifest.validation_scope != "prefix-structure-and-whole-file-identity"
        || manifest.canonical_json != "ascii-sort-keys-compact-lf-v1"
    {
        return Err("q9 manifest format/scope mismatch".into());
    }
    if manifest.frame.bytes != FRAME_BYTES || manifest.frame.sha256 != FRAME_SHA256
        || (manifest.frame.anchor_height, manifest.frame.tip_height) != (1_827_839, 1_827_840)
    {
        return Err("q9 source frame identity mismatch".into());
    }
    if manifest.prefix.last_height != 10_177
        || manifest.prefix.bytes != PREFIX_BYTES
        || manifest.prefix.opaque_tail_bytes != PREFIX_OPAQUE_TAIL_BYTES
        || manifest.prefix.bytes.checked_add(manifest.prefix.opaque_tail_bytes) != Some(FRAME_BYTES)
        || manifest.max_read_request == 0 || manifest.max_read_request > 1_048_576
    {
        return Err("q9 prefix bounds mismatch".into());
    }
    let expected_sources = BTreeMap::from([
        ("BootstrapVerifierSourceV1.scala".to_owned(), "c63f1d6814419b5ca14f00194d30eb6dc66a9bdf3da989d21f62c455db13ecf0".to_owned()),
        ("MainnetReceiverFrameAssembler.scala".to_owned(), "ba231f96c7ae1b63c2ba4ad81e74c39982e2c5d7a86cc16a2e41cc96b28bfd35".to_owned()),
    ]);
    if manifest.source_pins_sha256 != expected_sources {
        return Err("q9 source pins mismatch".into());
    }
    if manifest.headers.len() != Q9_HEIGHTS.len() {
        return Err("q9 manifest must contain exactly ten RAW entries".into());
    }
    if manifest.headers.iter().map(|entry| entry.bytes).sum::<u64>() != 2_783 {
        return Err("q9 exact ten-RAW byte census mismatch".into());
    }
    Ok(())
}

fn validate_roster(dir: &Path) -> Result<(), String> {
    let mut expected = Q9_HEIGHTS.iter()
        .map(|height| format!("header-{height:07}.bin"))
        .collect::<BTreeSet<_>>();
    expected.insert("manifest.json".into());
    let mut actual = BTreeSet::new();
    for entry in fs::read_dir(dir).map_err(|e| format!("q9 bundle directory: {e}"))? {
        let entry = entry.map_err(|e| format!("q9 bundle entry: {e}"))?;
        let kind = entry.file_type().map_err(|e| format!("q9 bundle entry type: {e}"))?;
        if !kind.is_file() || !actual.insert(entry.file_name().to_string_lossy().into_owned()) {
            return Err("q9 bundle contains a non-file or duplicate member".into());
        }
    }
    if actual != expected {
        return Err("q9 bundle must contain exactly manifest plus the ten pinned RAW files".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT: AtomicU64 = AtomicU64::new(0);

    struct TempBundle(PathBuf);

    impl TempBundle {
        fn copy_from_source() -> Self {
            let source = PathBuf::from(std::env::var_os("NIPOPOW_H21_Q9_HEADERS_DIR")
                .expect("q9 RAW directory env"));
            let output = PathBuf::from(std::env::var_os("NIPOPOW_STAGE1B_OUTPUT_DIR")
                .expect("bounded runner output directory env"));
            assert!(output.is_dir(), "bounded runner output directory must exist");
            let dir = loop {
                let unique = NEXT.fetch_add(1, Ordering::Relaxed);
                let candidate = output.join(format!("q9-selected-raw-negative-{}-{unique}", std::process::id()));
                match fs::create_dir(&candidate) {
                    Ok(()) => break candidate,
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("create isolated q9 test copy: {error}"),
                }
            };
            for height in Q9_HEIGHTS {
                let name = format!("header-{height:07}.bin");
                fs::copy(source.join(&name), dir.join(name)).expect("copy bounded q9 RAW");
            }
            fs::copy(source.join("manifest.json"), dir.join("manifest.json"))
                .expect("copy bounded q9 manifest");
            Self(dir)
        }

        fn path(&self) -> &Path { &self.0 }
    }

    fn rewrite_manifest(dir: &Path, edit: impl FnOnce(&mut serde_json::Value)) {
        let path = dir.join("manifest.json");
        let bytes = fs::read(&path).unwrap();
        let mut json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        edit(&mut json);
        let mut bytes = serde_json::to_vec(&json).unwrap();
        bytes.push(b'\n');
        fs::write(path, bytes).unwrap();
    }

    #[test]
    #[ignore = "requires the pinned q9 RAW bundle through NIPOPOW_H21_Q9_HEADERS_DIR"]
    fn selected_raw_positive_binds_exact_bundle_and_exposes_only_checked_bytes() {
        let dir = PathBuf::from(std::env::var_os("NIPOPOW_H21_Q9_HEADERS_DIR")
            .expect("q9 RAW directory env"));
        let fixture = CheckedQ9RawFixture::load(&dir).expect("exact q9 RAW bundle");
        assert_eq!(fixture.identity(), Q9RawIdentity::SelectedRawFixture);
        for height in Q9_HEIGHTS {
            assert!(!fixture.checked_raw(height).unwrap().is_empty());
        }
        assert!(fixture.checked_raw(10_178).is_err());
    }

    #[test]
    #[ignore = "requires the pinned q9 RAW bundle through NIPOPOW_H21_Q9_HEADERS_DIR"]
    fn selected_raw_rejects_missing_and_extra_raw_members() {
        let missing = TempBundle::copy_from_source();
        fs::remove_file(missing.path().join("header-0002048.bin")).unwrap();
        assert!(CheckedQ9RawFixture::load(missing.path()).unwrap_err().contains("exactly manifest"));

        let extra = TempBundle::copy_from_source();
        fs::write(extra.path().join("extra.bin"), [0u8]).unwrap();
        assert!(CheckedQ9RawFixture::load(extra.path()).unwrap_err().contains("exactly manifest"));
    }

    #[test]
    #[ignore = "requires the pinned q9 RAW bundle through NIPOPOW_H21_Q9_HEADERS_DIR"]
    fn selected_raw_rejects_corrupt_raw_and_manifest() {
        let raw = TempBundle::copy_from_source();
        let path = raw.path().join("header-0002048.bin");
        let mut bytes = fs::read(&path).unwrap();
        bytes[0] ^= 1;
        fs::write(path, bytes).unwrap();
        assert!(CheckedQ9RawFixture::load(raw.path()).unwrap_err().contains("SHA256 mismatch"));

        let manifest = TempBundle::copy_from_source();
        fs::write(manifest.path().join("manifest.json"), b"{}\n").unwrap();
        assert!(CheckedQ9RawFixture::load(manifest.path()).is_err());
    }

    #[test]
    #[ignore = "requires the pinned q9 RAW bundle through NIPOPOW_H21_Q9_HEADERS_DIR"]
    fn selected_raw_rejects_parent_root_and_total_upgrade_attempts() {
        for (field, value) in [("parent_root", serde_json::Value::Null), ("total", 1_827_840.into())] {
            let bundle = TempBundle::copy_from_source();
            rewrite_manifest(bundle.path(), |json| {
                json.as_object_mut().unwrap().insert(field.into(), value);
            });
            let error = CheckedQ9RawFixture::load(bundle.path()).unwrap_err();
            assert!(error.contains("forbids parent/root/total authority claim"), "{error}");
        }
    }
}

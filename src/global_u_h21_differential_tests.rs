//! Observed H21 arithmetic differential only. The two pinned receipts do not
//! authenticate a canonical header chain, the shared X, or a proof.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Read,
    path::Path,
};

use num_bigint::{BigInt, BigUint};
use serde_json::Value;

use crate::{
    global_u_roster::{self as roster, CandidateSource, Schedule, SuppliedCandidate},
    legacy_envelope_map::{Inputs, Kind, LowerBranch, LowerSelector, LowerSource, Map},
    native_prefix_auth_plan::role0_sha256,
    work_tree_work,
};

const N: u64 = 1_827_840;
const H: usize = 21;
const D_RECEIPT_BYTES: u64 = 131_501;
const D_RECEIPT_SHA256: &str = "97541ee3cdc7fc12942e6904f277241d2ac74edbf4794a1f477f9b1bae1424e9";
const B_RESULT_BYTES: u64 = 68_166;
const B_RESULT_SHA256: &str = "f840b3a55c7187f69a8b5fc939da1aaaaedac59e9984cdc3b1be1c5366561edd";
const FRAME_SHA256: &str = "a68d86562a56c5b71cf2180e4762bf8775b1061b6953bff7281ec50b7ee52c5e";
const SCANNER_SHA256: &str = "2bb5dfa25b10fb53fb0ffdb579707329c946dedfa7f39cfc5127822870b8ad00";
const ANALYZER_SHA256: &str = "6181b7c1ffc9b582d2d320fb0dbe5dc9fe8c53ce615777766cd2c13de89a5710";
const ROSTER_SHA256: &str = "ab02eaa395d5c885c236a700b87723faeb42b462aba6a4f539cc2b2c174fc647";
const LEGACY_SHA256: &str = "b2095927faf65060576d4ee89bf71ffa4ce5772cfc646628b9b91fe62e46347c";
const Q1: &str = "22538929735599";

#[derive(Clone)]
struct Anchor {
    timestamp: u64,
    difficulty: BigUint,
}

fn sha256(bytes: &[u8]) -> String {
    role0_sha256(bytes)
        .unwrap()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn get<'a>(item: &'a Value, name: &str) -> &'a Value {
    item.get(name).unwrap_or_else(|| panic!("missing {name}"))
}

fn as_u64(item: &Value) -> u64 {
    item.as_u64().expect("u64 JSON field")
}
fn as_str(item: &Value) -> &str {
    item.as_str().expect("string JSON field")
}

fn decimal(item: &Value) -> BigUint {
    let text = as_str(item);
    assert!(!text.is_empty() && (text == "0" || !text.starts_with('0')));
    assert!(text.bytes().all(|byte| byte.is_ascii_digit()));
    text.parse().expect("canonical decimal")
}

fn read_pinned(name: &str, size: u64, digest: &str) -> Value {
    let path = std::env::var_os(name).expect("pinned receipt path environment variable");
    let path = Path::new(&path);
    assert!(path.is_absolute(), "receipt path must be absolute");
    let before = fs::symlink_metadata(path).expect("receipt metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), size, "receipt byte length");
    let mut file = fs::File::open(path).expect("open pinned receipt");
    assert_eq!(
        file.metadata().unwrap().len(),
        size,
        "opened receipt length"
    );
    let mut bytes = Vec::with_capacity(size as usize);
    (&mut file)
        .take(size + 1)
        .read_to_end(&mut bytes)
        .expect("bounded receipt read");
    assert_eq!(
        bytes.len() as u64,
        size,
        "no short or trailing receipt bytes"
    );
    assert_eq!(sha256(&bytes), digest, "independent receipt SHA256 pin");
    let after = fs::symlink_metadata(path).expect("receipt restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), size, "receipt path length changed");
    assert!(bytes.is_ascii(), "canonical receipt ASCII");
    let parsed: Value = serde_json::from_slice(&bytes).expect("receipt JSON");
    let mut canonical = serde_json::to_vec(&parsed).expect("canonical JSON serialization");
    canonical.push(b'\n');
    assert_eq!(
        canonical, bytes,
        "sorted compact LF JSON, no duplicate keys"
    );
    parsed
}

fn expected_heights() -> Vec<u64> {
    let mut heights = BTreeSet::from([1u64, 417_793]);
    for height in 1..=843_776 {
        if matches!(height % 1024, 0 | 960 | 961) {
            heights.insert(height);
        }
    }
    assert_eq!(heights.len(), 2474);
    heights.into_iter().collect()
}

fn read_anchors(receipt: &Value) -> BTreeMap<u64, Anchor> {
    let rows = get(receipt, "legacy_anchors")
        .as_array()
        .expect("anchor rows");
    let expected = expected_heights();
    assert_eq!(rows.len(), expected.len(), "complete sparse anchor roster");
    let mut anchors = BTreeMap::new();
    for (row, height) in rows.iter().zip(expected) {
        let fields = row.as_array().expect("anchor tuple");
        assert_eq!(fields.len(), 4);
        assert_eq!(as_u64(&fields[0]), height, "sorted anchor height");
        let timestamp = as_u64(&fields[1]);
        assert!(timestamp > 0 && timestamp <= i64::MAX as u64);
        let nbits = u32::try_from(as_u64(&fields[2])).expect("nBits u32");
        let difficulty = decimal(&fields[3]);
        assert_eq!(
            work_tree_work::native_decode(nbits).unwrap(),
            difficulty,
            "independent Rust native difficulty decode"
        );
        assert!(anchors
            .insert(
                height,
                Anchor {
                    timestamp,
                    difficulty
                }
            )
            .is_none());
    }
    anchors
}

fn typed_inputs(map: &Map, owner: u64, anchors: &BTreeMap<u64, Anchor>) -> Inputs {
    let mut inputs = Inputs::default();
    for import in map.imports(owner).expect("typed Map imports") {
        let height = import.owner
            + match import.kind {
                Kind::Difficulty => 2,
                Kind::Timestamp => 1,
            };
        let anchor = anchors
            .get(&height)
            .unwrap_or_else(|| panic!("missing anchor {height}"));
        let word = match import.kind {
            Kind::Difficulty => BigInt::from(anchor.difficulty.clone()),
            Kind::Timestamp => BigInt::from(anchor.timestamp),
        };
        inputs.put(map, import, &word).expect("typed anchor import");
    }
    inputs
}

fn compare_bounds(actual: &[(u64, BigUint)], expected: &Value) -> Result<(), String> {
    let rows = get(expected, "legacy_bounds")
        .as_array()
        .ok_or("B result rows")?;
    if actual.len() != 822 || rows.len() != actual.len() {
        return Err("legacy B roster omission or addition".into());
    }
    for ((q, bound), row) in actual.iter().zip(rows) {
        if as_u64(get(row, "q")) != *q
            || *q == 407
            || as_u64(get(row, "endpoint")) != (q + 1) * 1024
            || as_u64(get(row, "map_owner")) != q * 1024 + 959
            || as_u64(get(row, "ell")) != (*q).min(8)
        {
            return Err(format!("legacy B source mismatch q={q}"));
        }
        if decimal(get(row, "bound")) != *bound {
            return Err(format!("legacy B value mismatch q={q}"));
        }
    }
    Ok(())
}

#[test]
#[ignore = "exact two-receipt H21 observed-arithmetic differential; prelaunch review required"]
fn h21_all_822_map_bounds_and_global_u_match_independent_diagnostic() {
    assert_eq!(sha256(include_bytes!("global_u_roster.rs")), ROSTER_SHA256);
    assert_eq!(
        sha256(include_bytes!("legacy_envelope_map.rs")),
        LEGACY_SHA256
    );
    let d = read_pinned("NIPOPOW_H21_D_CENSUS", D_RECEIPT_BYTES, D_RECEIPT_SHA256);
    let b = read_pinned("NIPOPOW_H21_B_DIAGNOSTIC", B_RESULT_BYTES, B_RESULT_SHA256);
    assert_eq!(as_str(get(&d, "format")), "H21-D-CENSUS-1");
    assert_eq!(as_str(get(&b, "format")), "H21-B-ENVELOPE-DIAGNOSTIC-1");
    assert!(as_str(get(&d, "scope")).starts_with("census-observed:"));
    assert_eq!(
        as_str(get(&b, "scope")),
        "observed-frame arithmetic only; no same-X authentication or proof"
    );
    assert_eq!(get(&d, "frame"), get(&b, "frame"));
    assert_eq!(as_u64(get(get(&d, "frame"), "bytes")), 1_321_781_831);
    assert_eq!(as_str(get(get(&d, "frame"), "sha256")), FRAME_SHA256);
    assert_eq!(
        as_str(get(get(&d, "source_pins_sha256"), "scan.py")),
        SCANNER_SHA256
    );
    assert_eq!(
        as_str(get(get(&d, "source_pins_sha256"), "global_u_roster.rs")),
        ROSTER_SHA256
    );
    assert_eq!(
        as_str(get(get(&d, "source_pins_sha256"), "legacy_envelope_map.rs")),
        LEGACY_SHA256
    );
    assert_eq!(as_str(get(&b, "source_receipt_sha256")), D_RECEIPT_SHA256);
    assert_eq!(as_u64(get(&b, "cut_height")), N);
    assert_eq!(as_u64(get(&d, "header_count")), N);
    assert_eq!(as_u64(get(&b, "legacy_count")), 822);
    assert_eq!(
        as_str(get(&get(&b, "legacy_bounds")[0], "bound")),
        Q1,
        "frozen q1 diagnostic before the Rust census"
    );
    assert_eq!(get(&b, "max_difficulty"), get(&d, "difficulty_max"));
    assert_eq!(
        as_str(get(
            get(get(&b, "diagnostic_source_pins"), "analyze.py"),
            "sha256"
        )),
        ANALYZER_SHA256
    );
    assert_eq!(
        as_u64(get(
            get(get(&b, "diagnostic_source_pins"), "analyze.py"),
            "bytes"
        )),
        23_466
    );
    for (name, digest, size) in [
        ("src/global_u_roster.rs", ROSTER_SHA256, 5_884),
        ("src/legacy_envelope_map.rs", LEGACY_SHA256, 55_708),
    ] {
        let pin = get(get(&b, "diagnostic_source_pins"), name);
        assert_eq!(as_str(get(pin, "sha256")), digest);
        assert_eq!(as_u64(get(pin, "bytes")), size);
    }

    let anchors = read_anchors(&d);
    let max_item = get(&d, "difficulty_max");
    let max_height = as_u64(get(max_item, "height"));
    let max_d = decimal(get(max_item, "difficulty"));
    let max_nbits = u32::from_str_radix(
        as_str(get(max_item, "n_bits"))
            .strip_prefix("0x")
            .expect("nBits hex"),
        16,
    )
    .expect("maximum nBits");
    assert_eq!(work_tree_work::native_decode(max_nbits).unwrap(), max_d);
    assert_eq!(max_height, 841_729);

    let global = get(&b, "global_u");
    let e = usize::try_from(as_u64(get(global, "exponent"))).unwrap();
    let map = Map::new_modern_global_u(N, H, e).expect("observed H21 Map");
    let schedule = Schedule::new(N).unwrap();
    let legacy_sources = schedule.legacy_items().collect::<Vec<_>>();
    assert_eq!(legacy_sources.len(), 822);
    let mut actual = Vec::with_capacity(822);
    for source in legacy_sources {
        let CandidateSource::LegacyBound {
            q,
            map_owner,
            endpoint,
            ell,
        } = source
        else {
            panic!("legacy schedule variant");
        };
        assert_eq!(
            (map_owner, endpoint, ell),
            (q * 1024 + 959, (q + 1) * 1024, q.min(8) as usize)
        );
        let inputs = typed_inputs(&map, map_owner, &anchors);
        let row = map
            .generate(map_owner, &inputs)
            .expect("Rust Map B generation");
        let bound = row
            .bound(&map)
            .unwrap()
            .to_biguint()
            .expect("nonnegative B");
        if matches!(q, 1 | 8 | 9 | 406 | 408 | 821 | 823) {
            assert!(
                map.failures(&row, &inputs).unwrap().is_empty(),
                "selected real-derived F residual at q={q}"
            );
        }
        actual.push((q, bound));
    }
    assert_eq!(actual[0].1.to_string(), Q1, "frozen q1 native projection");
    compare_bounds(&actual, &b).expect("all 822 independent Rust/Python B values");
    assert_eq!(as_u64(get(&b, "legacy_count")), actual.len() as u64);
    let (max_q, max_b) = actual
        .iter()
        .max_by(|left, right| left.1.cmp(&right.1).then_with(|| right.0.cmp(&left.0)))
        .unwrap();
    let reported_max = get(&b, "max_legacy_bound");
    assert_eq!(as_u64(get(reported_max, "q")), *max_q);
    assert_eq!(decimal(get(reported_max, "bound")), *max_b);

    let mut changed = b.clone();
    changed["legacy_bounds"][0]["bound"] = Value::String("0".into());
    assert!(
        compare_bounds(&actual, &changed)
            .unwrap_err()
            .contains("value mismatch"),
        "isolated B value mutant"
    );
    let mut omitted = b.clone();
    omitted["legacy_bounds"].as_array_mut().unwrap().remove(0);
    assert!(
        compare_bounds(&actual, &omitted)
            .unwrap_err()
            .contains("omission"),
        "isolated B omission mutant"
    );
    let q1_owner = 1024 + 959;
    assert!(
        map.generate(q1_owner, &Inputs::default()).is_err(),
        "missing typed inputs must not default to zero"
    );

    // This D stream preserves only the observed maximum and mandatory reset
    // children. It checks fold/roster aggregation, not every real D value.
    let b_by_q = actual.iter().cloned().collect::<BTreeMap<_, _>>();
    let supplied = Schedule::new(N).unwrap().iter().map(|source| {
        let value = match source {
            CandidateSource::HeaderDifficulty { height, .. } if height == max_height => {
                max_d.clone()
            }
            CandidateSource::HeaderDifficulty {
                height: 417_792 | 417_793,
                ..
            } => BigUint::from(roster::RESET_CHILD_417792),
            CandidateSource::HeaderDifficulty { .. } => BigUint::from(roster::INITIAL_I),
            CandidateSource::LegacyBound { q, .. } => b_by_q.get(&q).unwrap().clone(),
        };
        SuppliedCandidate { source, value }
    });
    let folded = roster::fold(N, supplied).expect("complete max-preserving H21 fold");
    assert_eq!((folded.header_count, folded.legacy_count), (N - 1, 822));
    assert_eq!(folded.max_difficulty, max_d);
    assert_eq!(folded.modern_floor, decimal(get(global, "modern_floor")));
    assert_eq!(
        folded.maximum_candidate,
        decimal(get(global, "maximum_candidate"))
    );
    assert_eq!(folded.exponent, e);
    assert_eq!(folded.u, decimal(get(global, "u")));

    let lower = get(global, "selected_lower_candidate");
    assert_eq!(as_str(get(lower, "kind")), "header_difficulty");
    assert_eq!(as_u64(get(lower, "height")), max_height);
    assert_eq!(as_u64(get(lower, "work_owner")), max_height - 2);
    assert_eq!(decimal(get(lower, "value")), max_d);
    assert_eq!(decimal(get(lower, "threshold")), (&folded.u + 4u8) / 3u8);
    assert_eq!(as_str(get(get(lower, "branch"), "kind")), "pivot");
    let pivot = usize::try_from(as_u64(get(get(lower, "branch"), "bit"))).unwrap();
    let selected = Map::new_modern_global_u_selected_lower(
        N,
        H,
        e,
        LowerSelector {
            source: LowerSource::HeaderDifficulty { height: max_height },
            branch: LowerBranch::Pivot(pivot),
        },
    )
    .expect("H21 selected lower D constructor");
    let owner = max_height - 2;
    let imported = selected.imports(owner).unwrap();
    assert_eq!(imported.len(), 1);
    assert_eq!(imported[0].kind, Kind::Difficulty);
    let mut inputs = Inputs::default();
    inputs
        .put(&selected, imported[0], &BigInt::from(max_d.clone()))
        .unwrap();
    let row = selected
        .generate(owner, &inputs)
        .expect("selected D owner row");
    assert!(
        selected.failures(&row, &inputs).unwrap().is_empty(),
        "selected lower D and upper guard residuals"
    );
    inputs.flip(imported[0], pivot).unwrap();
    let faults = selected.failures(&row, &inputs).unwrap();
    assert!(
        faults
            .iter()
            .any(|(index, _)| *index == owner as usize * (1 << 14) + 10_123),
        "single-bit lower-pivot mutant reaches its exact selected row"
    );

    println!("H21_GLOBAL_U_RUST_DIFFERENTIAL_PASS q=822 max_q={max_q} e={e} D_max_height={max_height} selected_pivot={pivot} D_fold=max_preserving_surrogate authentication=unclaimed proof=none");
}

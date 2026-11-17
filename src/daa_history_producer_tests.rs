//! Direct packed-owner tests for the native retarget writer.
// The independent scalar oracle below reads the writer's actual packed output;
// the older expected_native checks retain their existing, different scope.
use crate::{
    daa_count, daa_finish,
    daa_header_window::{self, Action},
    daa_history_producer::{
        write_fault_for_test, write_retarget, RawWindow, Receipt, MAX_EXTERNAL_CELLS,
        PACKED_OWNER_BYTES, PATCH_BYTES,
    },
    daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS, WIDTH},
    daa_integer::{Epoch, Inputs, ShortLegacyInputs, ShortLegacyProfile, TwoRatioInputs},
    daa_one_ratio_finish, serializer,
    short_daa_layout::Profile,
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};
use ergo_header_core::Header;
use num_bigint::BigUint;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    io::Write,
    path::PathBuf,
    sync::OnceLock,
};

const OWNER_ROWS: usize = 1 << 19;
const M1_IMAGE: std::ops::Range<usize> = 819_200..827_392;
const SENTINEL_START: usize = 125_000;

mod packed_numeric_oracle {
    use super::*;
    use crate::daa_history_producer::{numeric_probe::Observation, write_observed_for_test};
    use num_bigint::{BigInt, Sign};
    use num_traits::Signed;

    const PRECISION: i64 = 1_000_000_000;
    type Words = BTreeMap<String, BigInt>;

    // Byte-oriented compact codec, separate from all circuit/finish/decode helpers.
    fn decode_compact(raw: u32) -> BigUint {
        assert_eq!(raw & 0x0080_0000, 0, "negative compact in positive fixture");
        let bytes = raw.to_be_bytes();
        let exponent = usize::from(bytes[0]);
        let mantissa = BigUint::from_bytes_be(&bytes[1..]);
        if exponent <= 3 { mantissa >> (8 * (3 - exponent)) }
        else { mantissa << (8 * (exponent - 3)) }
    }
    fn compact_roundtrip(value: &BigUint) -> (u32, BigUint) {
        let mut bytes = value.to_bytes_be();
        if bytes.is_empty() { bytes.push(0); }
        if bytes[0] & 0x80 != 0 { bytes.insert(0, 0); }
        let size = bytes.len();
        assert!(size <= 255);
        let mut top = [0u8; 3];
        for (target, source) in top.iter_mut().zip(bytes.iter()) { *target = *source; }
        let raw = ((size as u32) << 24) | u32::from_be_bytes([0, top[0], top[1], top[2]]);
        (raw, decode_compact(raw))
    }
    fn signed(out: &mut Words, name: &str, value: &BigInt) {
        out.insert(format!("{name}_magnitude"), value.abs());
        out.insert(format!("{name}_negative"), BigInt::from(i32::from(value < &BigInt::zero())));
    }
    fn unsigned(out: &mut Words, name: &str, value: impl Into<BigInt>) {
        assert!(out.insert(name.into(), value.into()).is_none(), "oracle duplicate {name}");
    }
    fn gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
        while !b.is_zero() { let r = &a % &b; a = b; b = r; }
        a.abs()
    }
    fn initial() -> BigUint { BigUint::parse_bytes(b"011765000000", 16).unwrap() }

    fn expected(case: &FixtureCase) -> Words {
        let samples = case.samples.iter().map(|raw| fields_for(raw).0).collect::<Vec<_>>();
        let child = fields_for(&case.child).0;
        let m = samples.len() - 1;
        let epoch = if case.child_height >= 844673 { 128i64 } else { 1024i64 };
        let p = BigInt::from(PRECISION);
        let mut out = Words::new();
        let mut ys = Vec::with_capacity(m);
        let mut ds = Vec::with_capacity(m);
        for j in 0..m {
            let start = &samples[j]; let end = &samples[j + 1];
            let d = decode_compact(end.n_bits);
            assert!(!d.is_zero());
            let delta = end.timestamp.wrapping_sub(start.timestamp);
            assert_ne!(delta, 0);
            let n = BigInt::from(d.clone()) * BigInt::from(120_000 * epoch);
            let denominator = BigInt::from(delta);
            let quotient = &n / &denominator;
            let remainder = &n % denominator.abs();
            let prefix = format!("a1.{j}");
            unsigned(&mut out, &format!("{prefix}.nbits"), end.n_bits);
            unsigned(&mut out, &format!("{prefix}.start_timestamp"), start.timestamp as u64);
            unsigned(&mut out, &format!("{prefix}.end_timestamp"), end.timestamp as u64);
            unsigned(&mut out, &format!("{prefix}.decoded_difficulty"), d.clone());
            unsigned(&mut out, &format!("{prefix}.wrapped_delta"), delta as u64);
            unsigned(&mut out, &format!("{prefix}.denominator_magnitude"), denominator.abs());
            unsigned(&mut out, &format!("{prefix}.numerator"), n);
            signed(&mut out, &format!("{prefix}.quotient"), &quotient);
            signed(&mut out, &format!("{prefix}.remainder"), &remainder);
            ys.push(quotient); ds.push(d);
        }
        let prediction = if m == 1 {
            unsigned(&mut out, "finish.delta_nonzero", 1);
            ys[0].clone()
        } else {
            let xs = samples.iter().skip(1).map(|h| BigInt::from(h.height)).collect::<Vec<_>>();
            assert!(xs.windows(2).all(|pair| &pair[1] - &pair[0] == BigInt::from(epoch)));
            let count = BigInt::from(m);
            let sx: BigInt = xs.iter().cloned().sum();
            let sy: BigInt = ys.iter().cloned().sum();
            let sxx: BigInt = xs.iter().map(|x| x * x).sum();
            let sxy: BigInt = xs.iter().zip(&ys).map(|(x, y)| x * y).sum();
            let native_n = (&count * &sxy - &sx * &sy) * &p;
            let native_den = &count * &sxx - &sx * &sx;
            let native_b = &native_n / &native_den;
            // Derive the lowered fraction from the full native polynomial,
            // never from the circuit's reduced profile constants.
            let coefficients = xs.iter().map(|x| &count * x - &sx).collect::<Vec<_>>();
            let factor = if m == 8 { BigInt::from(epoch) } else {
                coefficients.iter().fold(native_den.clone(), |g, c| gcd(g, c.abs()))
            };
            let weights = coefficients.iter().map(|c| c / &factor).collect::<Vec<_>>();
            let mut positive = BigInt::zero(); let mut negative = BigInt::zero();
            for (j, (weight, y)) in weights.iter().zip(&ys).enumerate() {
                unsigned(&mut out, &format!("a2.alias.{j}.magnitude"), y.abs());
                unsigned(&mut out, &format!("a2.alias.{j}.negative"), i32::from(y < &BigInt::zero()));
                let term = weight * y;
                if term < BigInt::zero() { negative -= term; } else { positive += term; }
            }
            let sum = &positive - &negative;
            let n = if m == 8 { &sum * &p * BigInt::from(epoch) } else { &sum * &p };
            let den = if m == 8 { native_den.clone() } else { &native_den / &factor };
            let b = &n / &den;
            assert_eq!(b, native_b, "lowered/native slope quotient divergence");
            unsigned(&mut out, "a2.positive_sum", positive);
            unsigned(&mut out, "a2.negative_sum", negative);
            signed(&mut out, "a2.sum", &sum);
            unsigned(&mut out, "a2.numerator", n.abs());
            signed(&mut out, "a2.slope", &b);
            unsigned(&mut out, "a2.remainder", (&n % &den).abs());
            unsigned(&mut out, "a2.remainder_negative", i32::from((&n % &den) < BigInt::zero()));
            for (j, x) in xs.iter().enumerate() { unsigned(&mut out, &format!("a3.grid.{j}"), x.clone()); }
            unsigned(&mut out, "a3.x0", xs[0].clone());
            unsigned(&mut out, "a3.sum_x", sx.clone());
            signed(&mut out, "a3.b", &b);
            signed(&mut out, "a3.y", &sy);
            unsigned(&mut out, "a3.py_magnitude", sy.abs() * &p);
            unsigned(&mut out, "a3.b_sum_x_magnitude", b.abs() * &sx);
            let x = &sy * &p - &b * &sx;
            signed(&mut out, "a3.x", &x);
            let count_q = &x / &count;
            let a = &count_q / &p;
            assert_eq!(a, &x / (&count * &p), "successive positive denominators quotient identity");
            signed(&mut out, "a3.a", &a);
            let a_remainder = if m == 8 { &x % (&count * &p) } else { &count_q % &p };
            unsigned(&mut out, "a3.a_remainder", a_remainder.abs());
            unsigned(&mut out, "a3.a_remainder_negative", i32::from(a_remainder < BigInt::zero()));
            if (3..=7).contains(&m) {
                signed(&mut out, "a3.count.quotient", &count_q);
                signed(&mut out, "a3.count.remainder", &(&x % &count));
            }
            if m == 8 {
                assert_eq!((&x % (&count * &p)).abs(), (&x % &count).abs() + &count * (&count_q % &p).abs(),
                    "mature aggregated remainder identity");
            }
            let point = (samples.last().unwrap().height.wrapping_add(epoch as u32)) as i32;
            unsigned(&mut out, "a3.point_twos", point as u32);
            let point = BigInt::from(point);
            signed(&mut out, "a3.point", &point);
            let product = &b * &point;
            unsigned(&mut out, "a3.b_point_magnitude", product.abs());
            let term = &product / &p;
            signed(&mut out, "a3.term", &term);
            unsigned(&mut out, "a3.term_remainder", (&product % &p).abs());
            unsigned(&mut out, "a3.term_remainder_negative", i32::from((&product % &p) < BigInt::zero()));
            let prediction = a + term;
            signed(&mut out, "a3.prediction", &prediction);
            prediction
        };
        let use_prediction = prediction > BigInt::zero();
        unsigned(&mut out, "finish.use_prediction", i32::from(use_prediction));
        let selected = if use_prediction { prediction.to_biguint().unwrap() } else { initial() };
        let predictive = compact_roundtrip(&selected).1;
        let result = if m == 1 {
            unsigned(&mut out, "finish.selected", selected);
            predictive
        } else {
            unsigned(&mut out, "finish.predictive", predictive.clone());
            if epoch == 1024 { predictive } else {
                let last = ds.last().unwrap();
                let lower = last >> 1usize;
                let upper = last + &lower;
                let limited = predictive.max(lower.clone()).min(upper.clone());
                let average = (ys.last().unwrap() + BigInt::from(limited.clone())) / BigInt::from(2);
                let precompact = average.clone().max(BigInt::from(lower.clone())).min(BigInt::from(upper.clone())).to_biguint().unwrap();
                unsigned(&mut out, "finish.lower", lower);
                unsigned(&mut out, "finish.upper", upper);
                unsigned(&mut out, "finish.limited", limited);
                signed(&mut out, "finish.average", &average);
                unsigned(&mut out, "finish.precompact", precompact.clone());
                compact_roundtrip(&precompact).1
            }
        };
        assert_eq!(result, decode_compact(child.n_bits), "oracle native child numeric D");
        unsigned(&mut out, "finish.numeric_result", result);
        unsigned(&mut out, "finish.child_nbits", child.n_bits);
        out
    }
    fn read_word(bytes: &[u8], wires: &[usize]) -> BigInt {
        let mut packed = vec![0u8; wires.len().div_ceil(8)];
        for (j, &wire) in wires.iter().enumerate() {
            assert!(wire < WIDTH);
            if bit(bytes, wire) { packed[j / 8] |= 1 << (j % 8); }
        }
        BigInt::from_biguint(Sign::Plus, BigUint::from_bytes_le(&packed))
    }
    fn compare_word(name: &str, bytes: &[u8], observation: &Observation, expected: &Words) -> Result<(), String> {
        let wires = observation.words.get(name).ok_or_else(|| format!("numeric missing coordinate {name}"))?;
        let value = expected.get(name).ok_or_else(|| format!("numeric unexpected coordinate {name}"))?;
        if &read_word(bytes, wires) != value { return Err(format!("numeric packed mismatch {name}")); }
        Ok(())
    }
    fn compare_all(bytes: &[u8], observation: &Observation, expected: &Words) -> Result<(), String> {
        if observation.words.keys().ne(expected.keys()) { return Err("numeric coordinate census mismatch".into()); }
        for name in expected.keys() { compare_word(name, bytes, observation, expected)?; }
        Ok(())
    }
    fn produce(case: &FixtureCase) -> (Vec<u8>, Observation) {
        let roster = roster();
        let external = fixture_values(case);
        let refs = case.refs();
        let mut destination = vec![0u8; PACKED_OWNER_BYTES];
        seed_owner_serializer(&mut destination, &case.child);
        let (_, observation) = write_observed_for_test(&roster, case.owner, case.window(&refs), &mut destination,
            |wire| Ok(external.get(&wire).copied().unwrap_or(false))).unwrap();
        (destination, observation)
    }

    #[test]
    fn scalar_signed_divisions_odd_average_and_byte_compact() {
        let n = BigInt::from(-7); let d = BigInt::from(3);
        assert_eq!(&n / &d, BigInt::from(-2));
        assert_eq!(&n % &d, BigInt::from(-1));
        assert_ne!(&n / &d, BigInt::from(-3), "floor must not replace trunc0");
        assert_eq!((BigInt::from(-5) + BigInt::from(2)) / BigInt::from(2), BigInt::from(-1));
        let p = BigInt::from(10); let m = BigInt::from(2); let x = BigInt::from(19); let product = BigInt::from(11);
        let a = (&x / &m) / &p;
        assert_eq!(a, &x / (&m * &p));
        assert_ne!(&a + &product / &p, ((&x / &m) + &product) / &p,
            "fusing intercept and forecast truncations changes the result");
        assert_eq!((&x % (&m * &p)).abs(), (&x % &m).abs() + &m * ((&x / &m) % &p).abs());
        // Distinguish the reduced slope remainder from the native polynomial remainder.
        let ys = [BigInt::from(1),BigInt::from(1),BigInt::from(2)];
        let xs = [BigInt::from(2048),BigInt::from(3072),BigInt::from(4096)];
        let sy: BigInt = ys.iter().cloned().sum(); let sx: BigInt = xs.iter().cloned().sum();
        let sxy: BigInt = xs.iter().zip(&ys).map(|(x,y)| x*y).sum();
        let sxx: BigInt = xs.iter().map(|x| x*x).sum();
        let n = (BigInt::from(3)*sxy-&sx*sy)*BigInt::from(PRECISION);
        let den = BigInt::from(3)*sxx-&sx*&sx;
        assert_eq!(&n/&den, BigInt::from(488281));
        assert_eq!(&n%&den, BigInt::from(1572864));
        assert_eq!((&n/BigInt::from(3072))%(&den/BigInt::from(3072)), BigInt::from(512));
        let x = BigInt::from(-499997696); let count = BigInt::from(3); let p = BigInt::from(PRECISION);
        let c = &x/&count;
        assert_eq!(c, BigInt::from(-166665898));
        assert_eq!(&x%&count, BigInt::from(-2));
        assert_eq!(&c/&p, BigInt::zero());
        assert_eq!(&c%&p, BigInt::from(-166665898));
        // An EIP clamp can hide a wrong average, so inspect the average itself.
        let lower = BigInt::from(1); let upper = BigInt::from(4);
        let limited = BigInt::from(8).max(lower.clone()).min(upper.clone());
        assert_eq!(limited, BigInt::from(4));
        assert_eq!((limited+BigInt::from(1))/BigInt::from(2), BigInt::from(2));
        assert_eq!((BigInt::from(-2)+BigInt::from(1))/BigInt::from(2), BigInt::zero());
        assert_eq!(compact_roundtrip(&BigUint::from(0x7fffffu32)).0, 0x037fffff);
        assert_eq!(compact_roundtrip(&BigUint::from(0x800001u32)), (0x04008000, BigUint::from(0x800000u32)));
        assert_eq!(decode_compact(0x0101ffff), decode_compact(0x020001ff));
        // Wrap cases are scalar source checks, not an admission claim for these history profiles.
        assert_eq!(i64::MIN.wrapping_sub(i64::MAX), 1);
        assert_eq!(i32::MAX.wrapping_add(1), i32::MIN);
    }
    #[test]
    fn m3_actual_packed_outputs_and_isolated_numeric_mutants() {
        let case = fixture_case(4097);
        let expected = expected(&case);
        let (bytes, observation) = produce(&case);
        compare_all(&bytes, &observation, &expected).unwrap();
        for name in ["a1.0.quotient_magnitude", "a1.0.remainder_magnitude",
            "a3.prediction_magnitude", "finish.numeric_result", "a3.count.quotient_magnitude",
            "a3.count.remainder_magnitude"] {
            let mut changed = bytes.clone();
            let wire = observation.words[name][0];
            changed[wire / 8] ^= 1 << (wire % 8);
            assert_eq!(compare_word(name, &changed, &observation, &expected).unwrap_err(), format!("numeric packed mismatch {name}"));
            assert!(compare_all(&changed, &observation, &expected).is_err());
        }
        let name = "a1.0.nbits";
        let mut changed = bytes.clone();
        let wires = &observation.words[name];
        let (a, b) = wires.iter().flat_map(|&a| wires.iter().map(move |&b| (a, b)))
            .find(|&(a,b)| bit(&bytes,a) != bit(&bytes,b)).expect("distinct source compact bits");
        changed[a/8] ^= 1 << (a%8); changed[b/8] ^= 1 << (b%8);
        assert_eq!(compare_word(name, &changed, &observation, &expected).unwrap_err(), format!("numeric packed mismatch {name}"));
        let mut wrong_coordinates = observation.clone();
        let coordinates = wrong_coordinates.words.get_mut(name).unwrap();
        let i = coordinates.iter().position(|&w| w == a).unwrap();
        let j = coordinates.iter().position(|&w| w == b).unwrap();
        coordinates.swap(i, j);
        assert_eq!(compare_word(name, &bytes, &wrong_coordinates, &expected).unwrap_err(), format!("numeric packed mismatch {name}"));
    }
    #[test]
    fn all_ten_native_windows_match_independent_packed_numeric_oracle() {
        for child in [2049,3073,4097,5121,6145,7169,8193,9217,844673,844801] {
            let case = fixture_case(child);
            let expected = expected(&case);
            let (bytes, observation) = produce(&case);
            compare_all(&bytes, &observation, &expected).unwrap_or_else(|e| panic!("child {child}: {e}"));
        }
    }
}

fn sentinel_byte(index: usize) -> u8 {
    (index as u8).wrapping_mul(73) ^ 0xa5
}

fn parent() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(844_801, 20, [0x35; 32], [0x35; 28]).unwrap())
}

fn roster() -> DaaHistoryRoster<'static> {
    DaaHistoryRoster::compile(parent()).unwrap()
}

fn serializer() -> &'static serializer::Compiled {
    static SERIALIZER: OnceLock<serializer::Compiled> = OnceLock::new();
    SERIALIZER.get_or_init(|| serializer::build(None).unwrap())
}

fn decode_hex(text: &str) -> Vec<u8> {
    text.as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

fn fixture_headers() -> HashMap<u32, Vec<u8>> {
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("../fixtures/mainnet-daa-windows-v1.json")).unwrap();
    assert_eq!(
        fixture["source_frame"]["sha256"].as_str(),
        Some("A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E")
    );
    fixture["headers"]
        .as_array()
        .unwrap()
        .iter()
        .map(|header| {
            (
                header["height"].as_u64().unwrap() as u32,
                decode_hex(header["raw_hex"].as_str().unwrap()),
            )
        })
        .collect()
}

fn child_raw(height: u32, headers: &HashMap<u32, Vec<u8>>) -> Vec<u8> {
    match height {
        3073 => {
            let fixture: serde_json::Value =
                serde_json::from_str(include_str!("../fixtures/mainnet-daa-child-3073-v1.json"))
                    .unwrap();
            decode_hex(fixture["raw_hex"].as_str().unwrap())
        }
        4097 => include_bytes!("../fixtures/mainnet-daa-child-4097-v1.raw.bin").to_vec(),
        5121 => include_bytes!("../fixtures/mainnet-daa-child-5121-v1.raw.bin").to_vec(),
        6145 => include_bytes!("../fixtures/mainnet-daa-child-6145-v1.raw.bin").to_vec(),
        7169 => include_bytes!("../fixtures/mainnet-daa-child-7169-v1.raw.bin").to_vec(),
        _ => headers.get(&height).expect("pinned window child").clone(),
    }
}

fn sample_heights(child: u32) -> Vec<u32> {
    match child {
        2049 => vec![1024, 2048],
        3073 => vec![1024, 2048, 3072],
        4097 => vec![1024, 2048, 3072, 4096],
        5121 => vec![1024, 2048, 3072, 4096, 5120],
        6145 => vec![1024, 2048, 3072, 4096, 5120, 6144],
        7169 => vec![1024, 2048, 3072, 4096, 5120, 6144, 7168],
        8193 => vec![1024, 2048, 3072, 4096, 5120, 6144, 7168, 8192],
        9217 => vec![1024, 2048, 3072, 4096, 5120, 6144, 7168, 8192, 9216],
        844673 => vec![
            843648, 843776, 843904, 844032, 844160, 844288, 844416, 844544, 844672,
        ],
        844801 => vec![
            843776, 843904, 844032, 844160, 844288, 844416, 844544, 844672, 844800,
        ],
        _ => panic!("no pinned retarget fixture for child {child}"),
    }
}

struct FixtureCase {
    child_height: u32,
    owner: u64,
    parent: Vec<u8>,
    child: Vec<u8>,
    samples: Vec<Vec<u8>>,
}

impl FixtureCase {
    fn refs(&self) -> Vec<&[u8]> {
        self.samples.iter().map(Vec::as_slice).collect()
    }

    fn window<'a>(&'a self, samples: &'a [&'a [u8]]) -> RawWindow<'a> {
        RawWindow {
            parent: &self.parent,
            child: &self.child,
            samples,
        }
    }
}

fn fixture_case(child_height: u32) -> FixtureCase {
    let headers = fixture_headers();
    let child = child_raw(child_height, &headers);
    let parent_height = child_height - 1;
    let parent = headers
        .get(&parent_height)
        .expect("pinned parent RAW")
        .clone();
    let samples: Vec<Vec<u8>> = sample_heights(child_height)
        .into_iter()
        .map(|height| headers.get(&height).expect("pinned sample RAW").clone())
        .collect();
    assert_eq!(
        samples.last().unwrap(),
        &parent,
        "last sample is exact parent RAW"
    );
    FixtureCase {
        child_height,
        owner: u64::from(parent_height),
        parent,
        child,
        samples,
    }
}

fn expected_class_name(height: u32) -> &'static str {
    match height {
        2049 => "M1",
        3073 => "Short(M2)",
        4097 => "Short(M3)",
        5121 => "Short(M4)",
        6145 => "Short(M5)",
        7169 => "Short(M6)",
        8193 => "Short(M7)",
        9217 => "Mature(Legacy)",
        844673 | 844801 => "Mature(Eip)",
        _ => panic!("unknown expected class"),
    }
}

fn fields_for(raw: &[u8]) -> (Header, serializer::Fields) {
    let header = Header::decode(raw, None).unwrap();
    assert_eq!(
        header.encode().unwrap(),
        raw,
        "fixture RAW canonical round-trip"
    );
    let fields = serializer::Fields::from_header(&header).unwrap();
    (header, fields)
}

fn fixture_values(case: &FixtureCase) -> BTreeMap<usize, bool> {
    let mut values = BTreeMap::new();
    let inputs = serializer();
    for raw in case.samples.iter().chain(std::iter::once(&case.child)) {
        let (header, fields) = fields_for(raw);
        let assignment = inputs.assign(&fields);
        let base = (header.height as usize - 1) * WIDTH + crate::header_hash::SERIALIZER_OFFSET;
        for &wire in inputs
            .layout
            .fields
            .n_bits
            .iter()
            .chain(&inputs.layout.fields.timestamp)
            .chain(&inputs.layout.fields.height)
        {
            values.insert(base + wire, assignment[wire].is_one());
        }

        // The B1 header alias for this RAW may feed the B4 work leaf at h-2.
        // Keep those global coordinates distinct from the serializer owner h-1.
        let work_base = (header.height as usize - 2) * crate::work_tree_layout::WIDTH;
        let endpoints = &crate::work_tree_layout::shared_baseline()
            .unwrap()
            .endpoints;
        let work = crate::work_tree_work::native_decode(header.n_bits).unwrap();
        for (&wire, value) in endpoints
            .n_bits
            .iter()
            .zip(biguint_bits(&BigUint::from(header.n_bits), 32))
        {
            values.insert(work_base + wire, value);
        }
        let work_minus_one = &work - BigUint::one();
        for (wires, integer) in [
            (&endpoints.lower, BigUint::zero()),
            (&endpoints.upper, work.clone()),
            (&endpoints.work, work.clone()),
            (&endpoints.work_minus_one, work_minus_one),
        ] {
            for (&wire, value) in wires.iter().zip(biguint_bits(&integer, wires.len())) {
                values.insert(work_base + wire, value);
            }
        }
        for (index, &wire) in endpoints.exponent.iter().enumerate() {
            values.insert(work_base + wire, index == (header.n_bits >> 24) as usize);
        }
    }
    values
}

fn biguint_bits(value: &BigUint, width: usize) -> Vec<bool> {
    (0..width)
        .map(|bit| ((value >> bit) & BigUint::one()) == BigUint::one())
        .collect()
}

fn seed_owner_serializer(destination: &mut [u8], raw: &[u8]) {
    let (header, fields) = fields_for(raw);
    let assignment = serializer().assign(&fields);
    let base = crate::header_hash::SERIALIZER_OFFSET;
    for (wire, value) in assignment.iter().enumerate() {
        let local = base + wire;
        assert!(local < WIDTH);
        assert!(!BANKS
            .iter()
            .any(|&(start, end)| (start..end).contains(&local)));
        if value.is_one() {
            destination[local / 8] |= 1 << (local % 8);
        }
    }
    assert!(SENTINEL_START * 8 >= BANKS.last().unwrap().1);
    for (index, byte) in destination.iter_mut().enumerate().skip(SENTINEL_START) {
        *byte = sentinel_byte(index);
    }
}

struct NativeExpected {
    witness: Vec<Fr>,
    arithmetic_terms: usize,
}

fn expected_native(roster: &DaaHistoryRoster<'_>, case: &FixtureCase) -> NativeExpected {
    let child = Header::decode(&case.child, None).unwrap();
    let samples: Vec<Header> = case
        .samples
        .iter()
        .map(|raw| Header::decode(raw, None).unwrap())
        .collect();
    let child_nbits = child.n_bits;
    match case.child_height {
        2049 => {
            let compiled = daa_one_ratio_finish::compile(
                &daa_count::q(),
                Inputs {
                    nbits: samples[1].n_bits,
                    start_timestamp: samples[0].timestamp,
                    end_timestamp: samples[1].timestamp,
                },
                child_nbits,
                true,
            )
            .unwrap();
            let mapped = roster.admit_one(&compiled).unwrap();
            NativeExpected {
                witness: mapped.witness().to_vec(),
                arithmetic_terms: mapped.circuit().terms.len(),
            }
        }
        3073 => {
            let compiled = daa_finish::compile_two_finish_with_child(
                &daa_count::q(),
                TwoRatioInputs {
                    nbits: [samples[1].n_bits, samples[2].n_bits],
                    timestamps: [
                        samples[0].timestamp,
                        samples[1].timestamp,
                        samples[2].timestamp,
                    ],
                },
                child_nbits,
                true,
            )
            .unwrap();
            let mapped = roster.admit_short(Profile::M2, &compiled).unwrap();
            NativeExpected {
                witness: mapped.witness().to_vec(),
                arithmetic_terms: mapped.circuit().terms.len(),
            }
        }
        4097 | 5121 | 6145 | 7169 | 8193 => {
            let profile = match case.child_height {
                4097 => Profile::M3,
                5121 => Profile::M4,
                6145 => Profile::M5,
                7169 => Profile::M6,
                _ => Profile::M7,
            };
            let native_profile = match profile {
                Profile::M3 => ShortLegacyProfile::M3,
                Profile::M4 => ShortLegacyProfile::M4,
                Profile::M5 => ShortLegacyProfile::M5,
                Profile::M6 => ShortLegacyProfile::M6,
                Profile::M7 => ShortLegacyProfile::M7,
                Profile::M2 => unreachable!(),
            };
            let compiled = daa_finish::compile_short_legacy_with_child(
                &daa_count::q(),
                ShortLegacyInputs {
                    profile: native_profile,
                    nbits: samples.iter().skip(1).map(|h| h.n_bits).collect(),
                    timestamps: samples.iter().map(|h| h.timestamp).collect(),
                },
                child_nbits,
                true,
            )
            .unwrap();
            let mapped = roster.admit_short(profile, &compiled).unwrap();
            NativeExpected {
                witness: mapped.witness().to_vec(),
                arithmetic_terms: mapped.circuit().terms.len(),
            }
        }
        9217 | 844673 | 844801 => {
            let refs = case.refs();
            let selected =
                daa_header_window::select_window(&case.parent, &case.child, &refs).unwrap();
            assert!(matches!(
                selected.action(),
                Action::Retarget(Epoch::Legacy | Epoch::Eip)
            ));
            let compiled = daa_header_window::compile_selected_window(&selected).unwrap();
            let mapped = roster.admit_mature(&selected, &compiled).unwrap();
            NativeExpected {
                witness: mapped.witness().to_vec(),
                arithmetic_terms: mapped.circuit().terms.len(),
            }
        }
        _ => panic!("no native oracle for fixture"),
    }
}

fn bit(bytes: &[u8], wire: usize) -> bool {
    bytes[wire / 8] & (1 << (wire % 8)) != 0
}

fn hex_digest(bytes: impl AsRef<[u8]>) -> String {
    let digest = Blake2b::<U32>::digest(bytes.as_ref());
    digest.iter().map(|byte| format!("{byte:02X}")).collect()
}

fn update_term_digest(digest: &mut Blake2b<U32>, family: u8, term: &crate::sparse::Term) {
    digest.update([family]);
    digest.update((term.row as u64).to_le_bytes());
    digest.update((term.gate.left as u64).to_le_bytes());
    digest.update((term.gate.right as u64).to_le_bytes());
    for coefficient in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
        for limb in coefficient.into_bigint().0 {
            digest.update(limb.to_le_bytes());
        }
    }
}

fn assert_all_lane_residuals_zero(
    roster: &DaaHistoryRoster<'_>,
    case: &FixtureCase,
    destination: &[u8],
    external: &BTreeMap<usize, bool>,
) {
    let base = case.owner as usize * WIDTH;
    let row_base = case.owner as usize * OWNER_ROWS;
    let value = |wire: usize| {
        if (base..base + WIDTH).contains(&wire) {
            bit(destination, wire - base)
        } else {
            external.get(&wire).copied().unwrap_or(false)
        }
    };
    let mut residuals: [BTreeMap<usize, Fr>; 4] = std::array::from_fn(|_| BTreeMap::new());
    roster
        .visit_owner_terms(case.owner, |term| {
            let local_row = term
                .row
                .checked_sub(row_base)
                .ok_or("wrong oracle owner row")?;
            let lane = (local_row >> 17) & 3;
            let row = local_row & ((1 << 17) - 1);
            let x = Fr::from(value(term.gate.left) as u64);
            let y = Fr::from(value(term.gate.right) as u64);
            *residuals[lane].entry(row).or_insert_with(Fr::zero) +=
                term.gate.c0 + term.gate.c1 * x + term.gate.c2 * y + term.gate.c3 * x * y;
            Ok(())
        })
        .unwrap();
    for (lane, rows) in residuals.iter().enumerate() {
        assert!(
            rows.values().all(Zero::is_zero),
            "owner lane {lane}: {rows:?}"
        );
    }
}

fn exercise_positive_case(case_height: u32) -> Vec<u8> {
    exercise_positive_case_in_roster(case_height, roster())
}

fn exercise_positive_case_in_roster(
    case_height: u32,
    roster: DaaHistoryRoster<'_>,
) -> Vec<u8> {
    exercise_positive_case_in_roster_detailed(case_height, roster).0
}

fn exercise_positive_case_in_roster_detailed(
    case_height: u32,
    roster: DaaHistoryRoster<'_>,
) -> (Vec<u8>, Receipt, BTreeMap<usize, bool>) {
    let case = fixture_case(case_height);
    let expected = expected_native(&roster, &case);
    assert_eq!(expected.witness.len(), WIDTH);
    assert!(expected
        .witness
        .iter()
        .all(|value| value.is_zero() || value.is_one()));
    assert!(expected.witness.iter().enumerate().all(|(wire, value)| {
        BANKS
            .iter()
            .any(|&(start, end)| (start..end).contains(&wire))
            || value.is_zero()
    }));

    let external = fixture_values(&case);
    let sample_refs = case.refs();
    let raw = case.window(&sample_refs);
    let mut destination = vec![0u8; PACKED_OWNER_BYTES];
    seed_owner_serializer(&mut destination, &case.child);
    let before = destination.clone();
    assert_eq!(before[SENTINEL_START], sentinel_byte(SENTINEL_START));
    let owner_base = case.owner as usize * WIDTH;
    let mut calls = BTreeMap::<usize, usize>::new();
    let mut used_external = BTreeMap::<usize, bool>::new();
    let receipt = write_retarget(&roster, case.owner, raw, &mut destination, |wire| {
        assert!(
            !(owner_base..owner_base + WIDTH).contains(&wire),
            "owner-local wire must not reach outside callback"
        );
        let seen = calls.entry(wire).or_insert(0);
        let canonical = external.get(&wire).copied().unwrap_or(false);
        let answer = if *seen == 0 { canonical } else { !canonical };
        if *seen == 0 {
            used_external.insert(wire, answer);
        }
        *seen += 1;
        Ok(answer)
    })
    .unwrap();

    assert_eq!(receipt.owner, case.owner);
    assert_eq!(
        format!("{:?}", receipt.class),
        expected_class_name(case_height)
    );
    assert_eq!(receipt.patched_bytes, PATCH_BYTES);
    assert_eq!(receipt.counts.lanes[0], expected.arithmetic_terms);
    assert_eq!(receipt.counts.lanes[2], 0);
    assert_eq!(receipt.external_cells, calls.len());
    assert!(receipt.external_cells <= MAX_EXTERNAL_CELLS);
    assert!(
        calls.values().all(|count| *count == 1),
        "callback cache failed"
    );
    assert!(!calls.is_empty());

    let mut patched = 0usize;
    for &(start, end) in &BANKS {
        for wire in start..end {
            assert_eq!(
                bit(&destination, wire),
                expected.witness[wire].is_one(),
                "independent native patch at local wire {wire}"
            );
        }
        patched += (end - start) / 8;
    }
    assert_eq!(patched, PATCH_BYTES);
    for byte in 0..destination.len() {
        let in_patch = BANKS
            .iter()
            .any(|&(start, end)| (start / 8..end / 8).contains(&byte));
        if !in_patch {
            assert_eq!(destination[byte], before[byte], "non-bank byte {byte}");
        }
    }
    assert_all_lane_residuals_zero(&roster, &case, &destination, &external);
    (destination, receipt, used_external)
}

pub(super) fn mature_eip_844672_h21_case() -> (WorkTreeHistoryPlan, Vec<u8>) {
    let (plan, packed, _, _) = mature_eip_844672_h21_detailed_case();
    (plan, packed)
}

pub(super) fn mature_eip_844672_h21_detailed_case(
) -> (WorkTreeHistoryPlan, Vec<u8>, Receipt, BTreeMap<usize, bool>) {
    let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x35; 32], [0x35; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&plan).unwrap();
    assert_eq!(roster.owner_class(844_672).unwrap(), OwnerClass::Mature(Epoch::Eip));
    let (packed, receipt, external) = exercise_positive_case_in_roster_detailed(844_673, roster);
    (plan, packed, receipt, external)
}

#[test]
#[ignore = "requires a fresh directory in NIPOPOW_RETARGET_CENSUS_DIR"]
fn retarget_writer_m2_authentic_census_is_replayable() {
    let directory = PathBuf::from(
        std::env::var_os("NIPOPOW_RETARGET_CENSUS_DIR")
            .expect("runner supplies a fresh M2 census directory"),
    );
    assert!(directory.is_dir(), "census directory must exist");
    assert!(
        std::fs::read_dir(&directory).unwrap().next().is_none(),
        "census directory must be fresh"
    );

    let parent = WorkTreeHistoryPlan::compile(3073, 12, [0x35; 32], [0x35; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&parent).unwrap();
    let case = fixture_case(3073);
    assert_eq!(case.owner, 3072);
    assert_eq!(
        roster.owner_class(case.owner).unwrap(),
        OwnerClass::Short(Profile::M2)
    );
    let expected = expected_native(&roster, &case);
    let external = fixture_values(&case);
    let sample_refs = case.refs();
    let raw = case.window(&sample_refs);

    let mut destination = vec![0u8; PACKED_OWNER_BYTES];
    seed_owner_serializer(&mut destination, &case.child);
    let mut calls = BTreeMap::<usize, usize>::new();
    let receipt = write_retarget(&roster, case.owner, raw, &mut destination, |wire| {
        let count = calls.entry(wire).or_insert(0);
        *count += 1;
        external
            .get(&wire)
            .copied()
            .ok_or_else(|| format!("M2 census unsupported external wire {wire}"))
    })
    .unwrap();

    assert_eq!(receipt.owner, case.owner);
    assert_eq!(receipt.class, OwnerClass::Short(Profile::M2));
    assert_eq!(receipt.patched_bytes, PATCH_BYTES);
    assert_eq!(receipt.counts.lanes[0], expected.arithmetic_terms);
    assert_eq!(receipt.counts.lanes[2], 0);
    assert_eq!(receipt.external_cells, calls.len());
    assert!(receipt.external_cells <= MAX_EXTERNAL_CELLS);
    assert!(calls.values().all(|count| *count == 1));

    let mut owner_digest = Blake2b::<U32>::new();
    let mut owner_terms = 0usize;
    let mut owner_lanes = [0usize; 4];
    let mut owner_left = BTreeSet::new();
    let mut owner_right = BTreeSet::new();
    let mut owner_sources = BTreeSet::new();
    roster
        .visit_owner_terms(case.owner, |term| {
            let row_base = case.owner as usize * OWNER_ROWS;
            let local_row = term
                .row
                .checked_sub(row_base)
                .ok_or("M2 census owner row precedes owner")?;
            let lane = (local_row >> 17) & 3;
            assert!(lane < owner_lanes.len());
            owner_lanes[lane] += 1;
            owner_terms += 1;
            if !term.gate.c1.is_zero() || !term.gate.c3.is_zero() {
                owner_left.insert(term.gate.left);
                owner_sources.insert(term.gate.left / WIDTH);
            }
            if !term.gate.c2.is_zero() || !term.gate.c3.is_zero() {
                owner_right.insert(term.gate.right);
                owner_sources.insert(term.gate.right / WIDTH);
            }
            update_term_digest(&mut owner_digest, lane as u8, &term);
            Ok(())
        })
        .unwrap();

    let mut header_digest = Blake2b::<U32>::new();
    let mut header_terms = 0usize;
    let mut header_left = BTreeSet::new();
    let mut header_right = BTreeSet::new();
    let mut header_sources = BTreeSet::new();
    let header_counts = roster
        .visit_header_terms(case.owner, |term| {
            header_terms += 1;
            if !term.gate.c1.is_zero() || !term.gate.c3.is_zero() {
                header_left.insert(term.gate.left);
                header_sources.insert(term.gate.left / WIDTH);
            }
            if !term.gate.c2.is_zero() || !term.gate.c3.is_zero() {
                header_right.insert(term.gate.right);
                header_sources.insert(term.gate.right / WIDTH);
            }
            update_term_digest(&mut header_digest, 4, &term);
            Ok(())
        })
        .unwrap();
    assert_eq!(header_counts.emitted, header_terms);

    let baseline = crate::work_tree_layout::shared_baseline().unwrap();
    let serializer_end = crate::header_hash::SERIALIZER_OFFSET + serializer().circuit.input_len;
    let endpoint_start = crate::work_tree_layout::ENDPOINT_BASE;
    let endpoint_end = endpoint_start + crate::work_tree_layout::ENDPOINT_WIDTH;
    let mut namespace_counts = BTreeMap::<String, usize>::new();
    let mut external_sources = BTreeSet::new();
    for (&wire, &count) in &calls {
        assert_eq!(count, 1, "external callback cache duplicated wire {wire}");
        assert!(
            external.contains_key(&wire),
            "external producer missing wire {wire}"
        );
        let local = wire % WIDTH;
        let namespace = if (crate::header_hash::SERIALIZER_OFFSET..serializer_end).contains(&local)
        {
            "serializer"
        } else if (endpoint_start..endpoint_end).contains(&local) {
            "work_endpoint"
        } else {
            panic!("M2 census unsupported namespace at wire {wire}");
        };
        *namespace_counts.entry(namespace.to_owned()).or_default() += 1;
        external_sources.insert(wire / WIDTH);
        let _ = &baseline; // Keep the shared endpoint authority in this diagnostic's input closure.
    }

    let owner_digest = hex_digest(owner_digest.finalize());
    let header_digest = hex_digest(header_digest.finalize());
    let raw_digests: Vec<_> = case
        .samples
        .iter()
        .chain(std::iter::once(&case.child))
        .map(hex_digest)
        .collect();
    let report = serde_json::json!({
        "schema": "nipopow-v2-m2-owner-census-v1",
        "scope": "authentic M2 owner producer census only; no dense global witness, common commitment, PCS, sync, production or security claim",
        "source_frame_sha256": "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E",
        "test_source_blake2b256": hex_digest(include_bytes!("daa_history_producer_tests.rs")),
        "owner": case.owner,
        "child_height": case.child_height,
        "class": "Short(M2)",
        "sample_heights": [1024, 2048, 3072],
        "raw_blake2b256": raw_digests,
        "receipt": {
            "patched_bytes": receipt.patched_bytes,
            "external_cells": receipt.external_cells,
            "lane_terms": receipt.counts.lanes,
        },
        "owner_relation": {
            "terms": owner_terms,
            "lane_terms": owner_lanes,
            "left_coordinates": owner_left.len(),
            "right_coordinates": owner_right.len(),
            "source_owners": owner_sources.into_iter().collect::<Vec<_>>(),
            "term_digest_blake2b256": owner_digest,
        },
        "header_relation": {
            "terms": header_terms,
            "emitted": header_counts.emitted,
            "omitted_worktree": header_counts.omitted_worktree,
            "omitted_short_a4": header_counts.omitted_short_a4,
            "left_coordinates": header_left.len(),
            "right_coordinates": header_right.len(),
            "source_owners": header_sources.into_iter().collect::<Vec<_>>(),
            "term_digest_blake2b256": header_digest,
        },
        "external_imports": {
            "namespace_counts": namespace_counts,
            "source_owners": external_sources.into_iter().collect::<Vec<_>>(),
            "all_callback_wires_have_canonical_fixture_values": true,
        },
        "global_producer_registry": "HOLD",
    });
    let bytes = serde_json::to_vec_pretty(&report).unwrap();
    let path = directory.join("m2-owner-census.json");
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .unwrap();
    file.write_all(&bytes).unwrap();
    file.sync_all().unwrap();
    println!("{}", String::from_utf8(bytes).unwrap());
}

#[test]
fn retarget_writer_patches_m1_m2_m3_m4_from_native_raw() {
    for child in [2049, 3073, 4097, 5121] {
        exercise_positive_case(child);
    }
}

#[test]
fn retarget_writer_patches_m5_m6_m7_from_native_raw() {
    for child in [6145, 7169, 8193] {
        exercise_positive_case(child);
    }
}

#[test]
fn retarget_writer_patches_mature_legacy_and_both_eip_raw_cases() {
    for child in [9217, 844673, 844801] {
        exercise_positive_case(child);
    }
}

fn reject_each_nonempty_bank_before_mutation() {
    let roster = roster();
    let empty_window = RawWindow {
        parent: &[],
        child: &[],
        samples: &[],
    };
    for &(start, _) in &BANKS {
        let mut destination = vec![0u8; PACKED_OWNER_BYTES];
        destination[start / 8] |= 1 << (start % 8);
        let before = destination.clone();
        let error = write_retarget(&roster, 3072, empty_window, &mut destination, |_| {
            panic!("bank admission must precede RAW/callback access")
        })
        .unwrap_err();
        assert_eq!(error, format!("retarget producer nonempty bank at {start}"));
        assert_eq!(destination, before, "bank {start} changed on rejection");
    }
}

fn reject_bad_shape_owner_raw_and_samples_unchanged() {
    let roster = roster();
    let case = fixture_case(2049);
    let refs = case.refs();
    let raw = case.window(&refs);

    for len in [PACKED_OWNER_BYTES - 1, PACKED_OWNER_BYTES + 1] {
        let mut destination = vec![0u8; len];
        let before = destination.clone();
        let error = write_retarget(&roster, case.owner, raw, &mut destination, |_| {
            panic!("destination width must fail before callback")
        })
        .unwrap_err();
        assert_eq!(error, "retarget producer destination width");
        assert_eq!(destination, before);
    }

    let run_bad = |owner: u64, bad: RawWindow<'_>, expected: &str| {
        let mut destination = vec![0u8; PACKED_OWNER_BYTES];
        seed_owner_serializer(&mut destination, &case.child);
        let before = destination.clone();
        let error = write_retarget(&roster, owner, bad, &mut destination, |_| {
            panic!("structural RAW rejection precedes callback")
        })
        .unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert_eq!(destination, before);
    };

    run_bad(3072, raw, "child owner mismatch");
    run_bad(
        case.owner,
        RawWindow {
            parent: &[],
            child: &[],
            samples: &[],
        },
        "RAW length",
    );
    run_bad(
        case.owner,
        RawWindow {
            parent: &case.samples[0],
            child: &case.child,
            samples: &refs,
        },
        "parent height mismatch",
    );
    run_bad(
        case.owner,
        RawWindow {
            parent: &case.parent,
            child: &case.child,
            samples: &refs[..1],
        },
        "sample count mismatch",
    );
    let swapped = vec![refs[1], refs[0]];
    run_bad(
        case.owner,
        RawWindow {
            parent: &case.parent,
            child: &case.child,
            samples: &swapped,
        },
        "sample height mismatch",
    );

    let mut wrong_parent_id = Header::decode(&case.child, None).unwrap();
    wrong_parent_id.parent_id[0] ^= 1;
    let wrong_parent_id = wrong_parent_id.encode().unwrap();
    run_bad(
        case.owner,
        RawWindow {
            parent: &case.parent,
            child: &wrong_parent_id,
            samples: &refs,
        },
        "parent identity mismatch",
    );

    let mut altered_parent = Header::decode(&case.parent, None).unwrap();
    altered_parent.extension_root[0] ^= 1;
    let altered_parent = altered_parent.encode().unwrap();
    let mut altered_samples = case.refs();
    *altered_samples.last_mut().unwrap() = &altered_parent;
    run_bad(
        case.owner,
        RawWindow {
            parent: &case.parent,
            child: &case.child,
            samples: &altered_samples,
        },
        "last sample is not exact parent",
    );

    let oversized_raw = vec![0u8; 515];
    run_bad(
        case.owner,
        RawWindow {
            parent: &oversized_raw,
            child: &case.child,
            samples: &refs,
        },
        "RAW length",
    );

    let malformed_raw = [0xff];
    run_bad(
        case.owner,
        RawWindow {
            parent: &case.parent,
            child: &malformed_raw,
            samples: &refs,
        },
        "RAW decode",
    );

    // Extend the timestamp VLQ with a zero terminal group without changing its value.
    // The pinned native decoder rejects this before the producer's redundant re-encode.
    let mut noncanonical_raw = case.child.clone();
    let mut timestamp_end = 1 + 32 + 32 + 32 + 33;
    while noncanonical_raw[timestamp_end] & 0x80 != 0 {
        timestamp_end += 1;
    }
    noncanonical_raw[timestamp_end] |= 0x80;
    noncanonical_raw.insert(timestamp_end + 1, 0);
    assert!(matches!(
        Header::decode(&noncanonical_raw, None),
        Err(ergo_header_core::Error::NonMinimalVlq)
    ));
    run_bad(
        case.owner,
        RawWindow {
            parent: &case.parent,
            child: &noncanonical_raw,
            samples: &refs,
        },
        "RAW decode: NonMinimalVlq",
    );

    for (owner, expected) in [
        (0, "retarget producer unsupported owner class"),
        (1, "retarget producer unsupported owner class"),
        (2, "retarget producer unsupported owner class"),
        (417_791, "retarget producer unsupported owner class"),
        (1024, "retarget producer unsupported owner class"),
        (844_801, "retarget producer unsupported owner class"),
        (1 << 20, "DAA roster owner outside slot domain"),
    ] {
        let mut destination = vec![0u8; PACKED_OWNER_BYTES];
        let before = destination.clone();
        let error = write_retarget(
            &roster,
            owner,
            RawWindow {
                parent: &[],
                child: &[],
                samples: &[],
            },
            &mut destination,
            |_| panic!("owner class rejection precedes callback"),
        )
        .unwrap_err();
        assert_eq!(error, expected, "unexpected rejection for owner {owner}");
        assert_eq!(destination, before);
    }

    let start = Header::decode(&case.samples[0], None).unwrap();
    let mut zero_denominator_parent = Header::decode(&case.parent, None).unwrap();
    zero_denominator_parent.timestamp = start.timestamp;
    let zero_denominator_parent = zero_denominator_parent.encode().unwrap();
    let mut zero_denominator_child = Header::decode(&case.child, None).unwrap();
    zero_denominator_child.parent_id = Blake2b::<U32>::digest(&zero_denominator_parent).into();
    let zero_denominator_child = zero_denominator_child.encode().unwrap();
    let mut zero_denominator_samples = case.refs();
    *zero_denominator_samples.last_mut().unwrap() = &zero_denominator_parent;
    let mut destination = vec![0u8; PACKED_OWNER_BYTES];
    seed_owner_serializer(&mut destination, &zero_denominator_child);
    let before = destination.clone();
    let error = write_retarget(
        &roster,
        case.owner,
        RawWindow {
            parent: &zero_denominator_parent,
            child: &zero_denominator_child,
            samples: &zero_denominator_samples,
        },
        &mut destination,
        |_| panic!("native timestamp guard precedes callback"),
    )
    .unwrap_err();
    assert_eq!(
        error,
        "M1 requires nonnegative increasing signed timestamps"
    );
    assert_eq!(destination, before);
}

#[test]
fn retarget_writer_rejects_structural_guards_and_each_bank_unchanged() {
    reject_each_nonempty_bank_before_mutation();
    reject_bad_shape_owner_raw_and_samples_unchanged();
}

#[test]
fn retarget_writer_memoizes_external_cells_and_rejects_import_or_read_faults() {
    let roster = roster();
    let case = fixture_case(2049);
    let external = fixture_values(&case);
    let refs = case.refs();
    let raw = case.window(&refs);
    let mut destination = vec![0u8; PACKED_OWNER_BYTES];
    seed_owner_serializer(&mut destination, &case.child);
    let before = destination.clone();
    let layout = &serializer().layout.fields;
    let foreign_height = Header::decode(&case.samples[0], None).unwrap().height as usize;
    let foreign_base = (foreign_height - 1) * WIDTH + crate::header_hash::SERIALIZER_OFFSET;
    for imported in [
        foreign_base + layout.n_bits[0],
        foreign_base + layout.timestamp[0],
        foreign_base + layout.height[0],
    ] {
        let mut changed = external.clone();
        changed.insert(imported, !changed[&imported]);
        let error = write_retarget(&roster, case.owner, raw, &mut destination, |wire| {
            Ok(changed.get(&wire).copied().unwrap_or(false))
        })
        .unwrap_err();
        assert!(
            error.starts_with("retarget producer RAW port mismatch at "),
            "imported field {imported}: {error}"
        );
        assert_eq!(destination, before);
    }

    let local_port = crate::header_hash::SERIALIZER_OFFSET + layout.n_bits[0];
    let mut changed_owner = destination.clone();
    changed_owner[local_port / 8] ^= 1 << (local_port % 8);
    let changed_owner_before = changed_owner.clone();
    let error = write_retarget(&roster, case.owner, raw, &mut changed_owner, |wire| {
        Ok(external.get(&wire).copied().unwrap_or(false))
    })
    .unwrap_err();
    assert!(
        error.starts_with("retarget producer RAW port mismatch at "),
        "owner-local imported port should be checked against packed bytes: {error}"
    );
    assert_eq!(changed_owner, changed_owner_before);

    let samples: Vec<Header> = case
        .samples
        .iter()
        .map(|sample| Header::decode(sample, None).unwrap())
        .collect();
    let child = Header::decode(&case.child, None).unwrap();
    let alternate = daa_one_ratio_finish::compile(
        &daa_count::q(),
        Inputs {
            nbits: samples[1].n_bits,
            start_timestamp: samples[0].timestamp.checked_add(1).unwrap(),
            end_timestamp: samples[1].timestamp.checked_add(1).unwrap(),
        },
        child.n_bits,
        true,
    )
    .unwrap();
    let alternate = roster.admit_one(&alternate).unwrap();
    let alternate_witness = alternate.witness();
    assert_eq!(alternate_witness.len(), WIDTH);
    assert!(alternate_witness
        .iter()
        .all(|value| value.is_zero() || value.is_one()));
    assert!(alternate_witness.iter().enumerate().all(|(wire, value)| {
        BANKS
            .iter()
            .any(|&(start, end)| (start..end).contains(&wire))
            || value.is_zero()
    }));

    let owner_base = case.owner as usize * WIDTH;
    let row_base = case.owner as usize * OWNER_ROWS;
    let mut arithmetic_rows = BTreeMap::<usize, Fr>::new();
    roster
        .visit_owner_terms(case.owner, |term| {
            let local_row = term
                .row
                .checked_sub(row_base)
                .ok_or("wrong oracle owner row")?;
            if local_row >> 17 == 0 {
                let value = |wire: usize| {
                    wire.checked_sub(owner_base)
                        .and_then(|local| alternate_witness.get(local))
                        .map(|field| Fr::from(field.is_one() as u64))
                        .unwrap_or_else(Fr::zero)
                };
                let x = value(term.gate.left);
                let y = value(term.gate.right);
                *arithmetic_rows
                    .entry(local_row & ((1 << 17) - 1))
                    .or_insert_with(Fr::zero) +=
                    term.gate.c0 + term.gate.c1 * x + term.gate.c2 * y + term.gate.c3 * x * y;
            }
            Ok(())
        })
        .unwrap();
    assert!(
        arithmetic_rows.values().all(Zero::is_zero),
        "valid alternate native M1 witness must satisfy every arithmetic row"
    );

    let error = write_fault_for_test(
        &roster,
        case.owner,
        raw,
        &mut destination,
        |wire| Ok(external.get(&wire).copied().unwrap_or(false)),
        |prepared| {
            assert_eq!(prepared.len(), WIDTH);
            prepared.clone_from_slice(alternate_witness);
        },
    )
    .unwrap_err();
    assert!(
        error.starts_with("retarget producer nonzero residual lane 1 "),
        "valid alternate arithmetic witness should fail only the imported serializer alias lane: {error}"
    );
    assert_eq!(destination, before);

    let error = write_retarget(&roster, case.owner, raw, &mut destination, |_| {
        Err("injected outside read failure".to_string())
    })
    .unwrap_err();
    assert_eq!(error, "injected outside read failure");
    assert_eq!(destination, before);
}

#[test]
fn retarget_writer_test_only_mapped_faults_reject_without_mutation() {
    let roster = roster();
    let case = fixture_case(2049);
    let expected = expected_native(&roster, &case);
    let external = fixture_values(&case);
    let refs = case.refs();
    let raw = case.window(&refs);

    let run_fault = |wire: usize, value: Fr, expected_error: &str| {
        let mut destination = vec![0u8; PACKED_OWNER_BYTES];
        seed_owner_serializer(&mut destination, &case.child);
        let before = destination.clone();
        let error = write_fault_for_test(
            &roster,
            case.owner,
            raw,
            &mut destination,
            |index| Ok(external.get(&index).copied().unwrap_or(false)),
            |mapped| mapped[wire] = value,
        )
        .unwrap_err();
        assert!(error.contains(expected_error), "{error}");
        assert_eq!(destination, before);
    };

    run_fault(BANKS[0].0, Fr::from(2u64), "non-Boolean mapped cell");
    run_fault(0, Fr::one(), "nonzero outside bank");
    run_fault(M1_IMAGE.end, Fr::one(), "nonzero residual lane 3");

    let mut arithmetic_wire = None;
    roster
        .visit_owner_terms(case.owner, |term| {
            if ((term.row / (1 << 17)) & 3) != 0 {
                return Ok(());
            }
            for wire in [term.gate.left, term.gate.right] {
                let local = wire - case.owner as usize * WIDTH;
                if M1_IMAGE.contains(&local) && expected.witness[local].is_one() {
                    arithmetic_wire = Some(local);
                    return Ok(());
                }
            }
            Ok(())
        })
        .unwrap();
    let arithmetic_wire = arithmetic_wire.expect("active local arithmetic witness bit");
    run_fault(arithmetic_wire, Fr::zero(), "nonzero residual lane 0");
}

#[test]
#[ignore = "requires a fresh directory in NIPOPOW_RETARGET_PACKED_DIR"]
fn retarget_writer_roundtrips_patched_owner_through_packed_file() {
    let directory = PathBuf::from(
        std::env::var_os("NIPOPOW_RETARGET_PACKED_DIR")
            .expect("runner supplies a fresh packed artifact directory"),
    );
    assert!(directory.is_dir());
    let path = directory.join("retarget-owner-packed-v1.bin");
    assert!(!path.exists(), "fresh output path required");
    let packed_bytes = exercise_positive_case(2049);
    let mut writer = crate::packed::PackedFileWriter::create_new(&path, 20).unwrap();
    writer.write_bytes(&packed_bytes).unwrap();
    let packed = writer.finish().unwrap();
    let mut reconstructed = vec![Fr::zero(); WIDTH];
    for copy in 0..(WIDTH / (1 << 16)) {
        let bits = packed.read_copy(1 << 16, copy).unwrap();
        let start = copy * (1 << 16);
        reconstructed[start..start + bits.len()].copy_from_slice(&bits);
    }
    for wire in 0..WIDTH {
        assert_eq!(reconstructed[wire].is_one(), bit(&packed_bytes, wire));
    }
}

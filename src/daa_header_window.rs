//! Bounded Mainnet DAA header-window selection and A1-A4 input binding.
//!
//! This is a source join only. It checks canonical header bytes, the selected
//! height window, and the direct parent edge; it does not authenticate history,
//! verify proof of work, or establish consensus validity.
use blake2::{digest::consts::U32, Blake2b, Digest};
use ergo_header_core::Header;

use crate::daa_integer::Epoch;
use crate::daa_regression::PredictionInput;
use crate::{daa_count, daa_finish, daa_integer};

const MAX_HEADER_BYTES: usize = 514;
pub(crate) const MAX_CHILD_HEIGHT: u32 = i32::MAX as u32;
pub(crate) const EIP37_FIRST_CHILD: u32 = 844_673;
pub(crate) const V2_RESET_CHILDREN: [u32; 2] = [417_792, 417_793];
pub(crate) const MAINNET_LEGACY_EPOCH_LENGTH: u64 = 1024;
pub(crate) const MAINNET_EIP37_EPOCH_LENGTH: u64 = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Action {
    Carry,
    FixedV2,
    Retarget(Epoch),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChildPlan {
    action: Action,
    sample_heights: Vec<u32>,
}

impl ChildPlan {
    pub(crate) fn action(&self) -> Action {
        self.action
    }

    pub(crate) fn sample_heights(&self) -> &[u32] {
        &self.sample_heights
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SelectedWindow {
    action: Action,
    prediction: PredictionInput,
    child_nbits: u32,
    child_height: u32,
}

impl SelectedWindow {
    pub(crate) fn action(&self) -> Action {
        self.action
    }

    pub(crate) fn prediction(&self) -> PredictionInput {
        self.prediction
    }

    pub(crate) fn child_nbits(&self) -> u32 {
        self.child_nbits
    }

    pub(crate) fn child_height(&self) -> u32 {
        self.child_height
    }
}

/// Selects the Mainnet branch and exact positive sample heights for a child.
/// Only epoch boundaries produce a retarget window; other heights carry state.
pub(crate) fn for_child_height(child_height: u32) -> Result<ChildPlan, String> {
    if !(2..=MAX_CHILD_HEIGHT).contains(&child_height) {
        return Err("child height outside supported Mainnet range".into());
    }
    let action = if child_height == 2 {
        Action::Carry
    } else if V2_RESET_CHILDREN.contains(&child_height) {
        Action::FixedV2
    } else if child_height == EIP37_FIRST_CHILD {
        Action::Retarget(Epoch::Eip)
    } else if child_height > EIP37_FIRST_CHILD {
        if (child_height - 1) % Epoch::Eip.length() as u32 == 0 {
            Action::Retarget(Epoch::Eip)
        } else {
            Action::Carry
        }
    } else if (child_height - 1) % Epoch::Legacy.length() as u32 == 0 {
        Action::Retarget(Epoch::Legacy)
    } else {
        Action::Carry
    };

    let sample_heights = match action {
        Action::Retarget(epoch) => {
            let parent_height = child_height - 1;
            let epoch = u32::try_from(epoch.length()).map_err(|_| "epoch exceeds height width")?;
            (0..=8u32)
                .rev()
                .filter_map(|back| parent_height.checked_sub(back * epoch))
                .filter(|height| *height > 0)
                .collect()
        }
        Action::Carry | Action::FixedV2 => Vec::new(),
    };
    Ok(ChildPlan {
        action,
        sample_heights,
    })
}

/// Validates source headers and builds the mature regression input for a
/// retarget. Immature windows, carry children, and fixed-V2 resets fail closed.
pub(crate) fn select_window(
    parent_raw: &[u8],
    child_raw: &[u8],
    samples_raw: &[&[u8]],
) -> Result<SelectedWindow, String> {
    let parent = decode_header(parent_raw)?;
    let child = decode_header(child_raw)?;
    if child.decoded.height < 2 || child.decoded.height > MAX_CHILD_HEIGHT {
        return Err("child height outside supported Mainnet range".into());
    }
    if parent.decoded.height.checked_add(1) != Some(child.decoded.height) {
        return Err("parent and child heights are not adjacent".into());
    }
    let parent_id: [u8; 32] = Blake2b::<U32>::digest(parent_raw).into();
    if child.decoded.parent_id != parent_id {
        return Err("child parent id does not bind the exact parent bytes".into());
    }

    let plan = for_child_height(child.decoded.height)?;
    let epoch = match plan.action {
        Action::Retarget(epoch) => epoch,
        Action::Carry => return Err("child follows the Mainnet carry branch".into()),
        Action::FixedV2 => return Err("child follows the Mainnet fixed-V2 reset branch".into()),
    };
    if plan.sample_heights.len() != 9 {
        return Err(
            "retarget window is immature: exactly nine positive samples are required".into(),
        );
    }
    if samples_raw.len() != plan.sample_heights.len() {
        return Err("sample count does not match the Mainnet height plan".into());
    }

    let mut samples = Vec::with_capacity(9);
    for (raw, expected_height) in samples_raw.iter().zip(&plan.sample_heights) {
        let header = decode_header(raw)?;
        if header.decoded.height != *expected_height {
            return Err(format!(
                "sample height mismatch: expected {expected_height}, got {}",
                header.decoded.height
            ));
        }
        samples.push(header);
    }
    if samples.last().map(|sample| sample.raw.as_slice()) != Some(parent_raw) {
        return Err("final retarget sample must equal the exact parent header bytes".into());
    }
    if parent.decoded.timestamp <= samples[0].decoded.timestamp {
        return Err("mature window head must follow its first sample timestamp".into());
    }
    if samples
        .windows(2)
        .any(|pair| pair[0].decoded.timestamp == pair[1].decoded.timestamp)
    {
        return Err("adjacent sample timestamps produce a zero DAA denominator".into());
    }

    let mut nbits = [0u32; 8];
    let mut timestamps = [0i64; 9];
    for (index, sample) in samples.iter().enumerate() {
        timestamps[index] = sample.decoded.timestamp;
        if index > 0 {
            nbits[index - 1] = sample.decoded.n_bits;
        }
    }
    let x0 = samples[1].decoded.height;
    let prediction = PredictionInput {
        window: daa_integer::WindowInputs { nbits, timestamps },
        x0,
    };
    Ok(SelectedWindow {
        action: plan.action,
        prediction,
        child_nbits: child.decoded.n_bits,
        child_height: child.decoded.height,
    })
}

fn decode_header(raw: &[u8]) -> Result<DecodedHeader, String> {
    if raw.is_empty() || raw.len() > MAX_HEADER_BYTES {
        return Err("header length outside 1..=514 bytes".into());
    }
    let decoded =
        Header::decode(raw, None).map_err(|error| format!("invalid header: {error:?}"))?;
    let canonical = decoded
        .encode()
        .map_err(|error| format!("header encode failed: {error:?}"))?;
    if canonical.as_slice() != raw {
        return Err("header bytes are not canonical".into());
    }
    Ok(DecodedHeader {
        raw: raw.to_vec(),
        decoded,
    })
}

#[derive(Debug)]
struct DecodedHeader {
    raw: Vec<u8>,
    decoded: Header,
}

/// The direct source-to-arithmetic join consumed by the bounded tests and
/// prototype caller. The true child compact value remains an explicit A4 input.
pub(crate) fn compile_selected_window(
    window: &SelectedWindow,
) -> Result<daa_finish::CompiledFinish, String> {
    let Action::Retarget(epoch) = window.action() else {
        return Err("selected child is not a retarget".into());
    };
    daa_finish::compile_finish_with_child(
        epoch,
        &daa_count::q(),
        window.prediction(),
        window.child_nbits(),
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Zero;
    use serde::Deserialize;
    use std::collections::HashMap;

    const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");
    const CHILD_3073_FIXTURE: &str = include_str!("../fixtures/mainnet-daa-child-3073-v1.json");
    const SOURCE_FRAME_SHA256: &str =
        "A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E";

    #[derive(Deserialize)]
    struct Fixture {
        schema: u32,
        source_frame: SourceFrame,
        cases: Vec<Case>,
        headers: Vec<FixtureHeader>,
    }
    #[derive(Deserialize)]
    struct SourceFrame {
        sha256: String,
    }
    #[derive(Deserialize)]
    struct Case {
        child: u32,
        parent: u32,
        branch: String,
        samples: Vec<u32>,
    }
    #[derive(Clone, Deserialize)]
    struct FixtureHeader {
        height: u32,
        raw_hex: String,
    }

    fn fixture() -> (Fixture, HashMap<u32, Vec<u8>>) {
        let value: Fixture = serde_json::from_str(FIXTURE).unwrap();
        assert_eq!(value.schema, 1);
        assert_eq!(value.source_frame.sha256, SOURCE_FRAME_SHA256);
        let headers = index_headers(&value.headers).unwrap();
        (value, headers)
    }

    fn index_headers(headers: &[FixtureHeader]) -> Result<HashMap<u32, Vec<u8>>, String> {
        let mut indexed = HashMap::new();
        for entry in headers {
            let raw = decode_hex(&entry.raw_hex);
            let decoded = decode_header(&raw)?;
            if decoded.decoded.height != entry.height {
                return Err(format!("fixture height mismatch at {}", entry.height));
            }
            if indexed.insert(entry.height, raw).is_some() {
                return Err(format!("duplicate fixture height {}", entry.height));
            }
        }
        Ok(indexed)
    }

    fn decode_hex(value: &str) -> Vec<u8> {
        value
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }

    fn decode_numeric_difficulty(nbits: u32) -> num_bigint::BigUint {
        let exponent = (nbits >> 24) as usize;
        let mantissa = nbits & 0x007f_ffff;
        if exponent <= 3 {
            num_bigint::BigUint::from(mantissa) >> (8 * (3 - exponent))
        } else {
            num_bigint::BigUint::from(mantissa) << (8 * (exponent - 3))
        }
    }

    fn encode_mutated(raw: &[u8], f: impl FnOnce(&mut Header)) -> Vec<u8> {
        let mut header = Header::decode(raw, None).unwrap();
        f(&mut header);
        header.encode().unwrap()
    }

    fn branch_name(action: Action) -> &'static str {
        match action {
            Action::Carry => "carry",
            Action::FixedV2 => "fixed-v2-activation",
            Action::Retarget(Epoch::Legacy) => "legacy-1024",
            Action::Retarget(Epoch::Eip) => "eip37-128",
        }
    }

    #[test]
    fn exact_mainnet_child_plans_match_fixture_and_boundaries() {
        let (fixture, headers) = fixture();
        assert_eq!(fixture.cases.len(), 10);
        assert_eq!(fixture.headers.len(), 31);
        assert_eq!(headers.len(), 31);
        for entry in &fixture.headers {
            let raw = headers.get(&entry.height).unwrap();
            let decoded = decode_header(raw).unwrap();
            assert_eq!(decoded.decoded.height, entry.height);
            assert_eq!(decoded.decoded.encode().unwrap(), *raw);
        }
        let mut duplicated = fixture.headers.clone();
        duplicated.push(duplicated[0].clone());
        assert!(index_headers(&duplicated)
            .unwrap_err()
            .contains("duplicate"));
        for case in fixture.cases {
            assert_eq!(case.parent + 1, case.child);
            let plan = for_child_height(case.child).unwrap();
            assert_eq!(
                branch_name(plan.action()),
                case.branch,
                "child {}",
                case.child
            );
            assert_eq!(plan.sample_heights(), case.samples, "child {}", case.child);
        }
        assert_eq!(for_child_height(844_672).unwrap().action(), Action::Carry);
        assert_eq!(for_child_height(844_674).unwrap().action(), Action::Carry);
        for child in [3, 4] {
            assert_eq!(for_child_height(child).unwrap().action(), Action::Carry);
        }
        assert_eq!(
            for_child_height(844_801).unwrap().sample_heights().first(),
            Some(&843_776)
        );
        assert!(for_child_height(1).is_err());
        assert!(for_child_height(i32::MAX as u32 + 1).is_err());
    }

    #[test]
    fn early_legacy_2049_one_ratio_a1_matches_native_raw_fixture() {
        let (fixture, headers) = fixture();
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == 2_049)
            .unwrap();
        assert_eq!(case.parent, 2_048);
        assert_eq!(case.samples.as_slice(), &[1_024, 2_048]);
        let plan = for_child_height(case.child).unwrap();
        assert_eq!(plan.action(), Action::Retarget(Epoch::Legacy));
        assert_eq!(plan.sample_heights(), case.samples);

        let start = decode_header(headers.get(&1_024).unwrap()).unwrap();
        let end = decode_header(headers.get(&2_048).unwrap()).unwrap();
        let child = decode_header(headers.get(&2_049).unwrap()).unwrap();
        assert_eq!(start.decoded.n_bits, 0x0601_1765);
        assert_eq!(end.decoded.n_bits, 0x0601_1765);
        assert_eq!(start.decoded.timestamp, 1_561_986_131_991);
        assert_eq!(end.decoded.timestamp, 1_561_993_105_670);
        let delta = end.decoded.timestamp - start.decoded.timestamp;
        assert_eq!(delta, 6_973_679);

        // This checks the one-ratio arithmetic on selected RAW values only.
        // It does not authenticate those headers as a historical chain.
        let compiled = daa_integer::compile(
            Epoch::Legacy,
            &daa_count::q(),
            daa_integer::Inputs {
                nbits: end.decoded.n_bits,
                start_timestamp: start.decoded.timestamp,
                end_timestamp: end.decoded.timestamp,
            },
            true,
        )
        .unwrap();
        let read_bits = |bits: &[usize]| {
            let mut bytes = vec![0u8; bits.len().div_ceil(8)];
            for (i, &wire) in bits.iter().enumerate() {
                let bit = compiled.witness[wire];
                assert!(bit.is_zero() || bit == ark_bn254::Fr::from(1u64));
                if !bit.is_zero() {
                    bytes[i / 8] |= 1 << (i % 8);
                }
            }
            num_bigint::BigUint::from_bytes_le(&bytes)
        };
        let decoded = read_bits(&compiled.output.decoded_difficulty);
        let numerator = read_bits(&compiled.output.numerator);
        let denominator = read_bits(&compiled.output.denominator_magnitude);
        let quotient = read_bits(&compiled.output.quotient_magnitude);
        let remainder = read_bits(&compiled.output.remainder_magnitude);
        assert_eq!(decoded, num_bigint::BigUint::from(1_199_990_374_400u64));
        assert_eq!(denominator, num_bigint::BigUint::from(delta as u64));
        assert_eq!(
            numerator,
            num_bigint::BigUint::from(147_454_817_206_272_000_000u128)
        );
        assert_eq!(
            numerator,
            decoded.clone() * num_bigint::BigUint::from(Epoch::Legacy.multiplier())
        );
        assert_eq!(quotient, num_bigint::BigUint::from(21_144_480_152_624u64));
        assert_eq!(remainder, num_bigint::BigUint::from(1_216_304u64));
        assert_eq!(quotient.clone() * &denominator + &remainder, numerator);
        assert!(remainder < denominator);
        assert!(compiled.witness[compiled.output.quotient_negative].is_zero());
        assert!(compiled.witness[compiled.output.remainder_negative].is_zero());
        assert!(daa_integer::residuals(&compiled)
            .unwrap()
            .iter()
            .all(|residual| residual.is_zero()));

        // Scala's size-one interpolation returns this quotient directly.
        let (compact, rounded) = daa_finish::native_positive_compact_roundtrip(&quotient);
        assert_eq!(compact, 0x0613_3b15);
        assert_eq!(rounded, num_bigint::BigUint::from(21_144_476_319_744u64));
        assert_eq!(child.decoded.n_bits, compact);
        assert_eq!(decode_numeric_difficulty(child.decoded.n_bits), rounded);
        eprintln!(
            "{}",
            serde_json::json!({
                "child": 2049,
                "samples": [1024, 2048],
                "delta_ms": delta,
                "quotient": quotient.to_string(),
                "remainder": remainder.to_string(),
                "compact": format!("{compact:08x}"),
                "a1_terms": compiled.count.terms,
                "authority_ceiling": "selected RAW one-ratio arithmetic only; no history/hash/adjacency proof"
            })
        );
    }

    #[test]
    fn early_legacy_3073_two_ratios_match_native_raw_child() {
        let (fixture, headers) = fixture();
        let child_fixture: serde_json::Value = serde_json::from_str(CHILD_3073_FIXTURE).unwrap();
        assert_eq!(child_fixture["schema"], 1);
        assert_eq!(child_fixture["source_frame_sha256"], SOURCE_FRAME_SHA256);
        assert_eq!(
            child_fixture["base_fixture_sha256"],
            "E45A23753B39C4CFD415A8F91F1FFE2A994E4A2AE3B12DFAF83869F4C736AA9E"
        );
        assert_eq!(
            child_fixture["extraction_receipt_sha256"],
            "85F162CF1876A921CEA13A395EE6518F033DE7904C704D54F683E847E5AE1860"
        );
        assert_eq!(
            child_fixture["raw_sha256"],
            "2735A3D7A52AAAE6C3BEA4AFDB0262EB0CC222D64215D7E25FC9A5480A6A2CD5"
        );
        assert_eq!(child_fixture["height"], 3_073);
        let child_raw = decode_hex(child_fixture["raw_hex"].as_str().unwrap());
        assert_eq!(child_raw.len(), 279);
        let child = decode_header(&child_raw).unwrap();
        assert_eq!(child.decoded.height, 3_073);
        assert_eq!(child.decoded.n_bits, 0x0700_a8a7);

        let plan = for_child_height(child.decoded.height).unwrap();
        assert_eq!(plan.action(), Action::Retarget(Epoch::Legacy));
        assert_eq!(plan.sample_heights(), &[1_024, 2_048, 3_072]);
        assert!(!fixture.cases.iter().any(|case| case.child == 3_073));

        let selected = [1_024, 2_048, 3_072]
            .map(|height| decode_header(headers.get(&height).unwrap()).unwrap());
        let timestamps = selected.each_ref().map(|header| header.decoded.timestamp);
        let bits = selected.each_ref().map(|header| header.decoded.n_bits);
        assert_eq!(
            timestamps,
            [1_561_986_131_991, 1_561_993_105_670, 1_562_018_260_215]
        );
        assert_eq!(bits, [0x0601_1765, 0x0601_1765, 0x0613_3b15]);
        let dt = [timestamps[1] - timestamps[0], timestamps[2] - timestamps[1]];
        assert_eq!(dt, [6_973_679, 25_154_545]);
        assert!(timestamps[0] < timestamps[2]);

        // The source selector deliberately rejects this immature window after
        // checking the direct parent edge; this test does not supply fake samples.
        let sample_raw =
            [1_024, 2_048, 3_072].map(|height| headers.get(&height).unwrap().as_slice());
        assert!(select_window(sample_raw[2], &child_raw, &sample_raw)
            .unwrap_err()
            .contains("exactly nine positive samples"));

        // Exact Scala calculateFromSamples arithmetic: each division truncates
        // toward zero, followed by the two separate intercept divisions.
        let multiplier = num_bigint::BigInt::from(Epoch::Legacy.multiplier());
        let end_difficulty = [
            decode_numeric_difficulty(bits[1]),
            decode_numeric_difficulty(bits[2]),
        ];
        let numerators =
            end_difficulty.map(|difficulty| num_bigint::BigInt::from(difficulty) * &multiplier);
        let denominators = dt.map(num_bigint::BigInt::from);
        let y = [
            &numerators[0] / &denominators[0],
            &numerators[1] / &denominators[1],
        ];
        let remainders = [
            &numerators[0] % &denominators[0],
            &numerators[1] % &denominators[1],
        ];
        assert_eq!(y[0], num_bigint::BigInt::from(21_144_480_152_624u64));
        assert_eq!(y[1], num_bigint::BigInt::from(103_290_806_896_731u64));
        assert_eq!(remainders[0], num_bigint::BigInt::from(1_216_304u64));
        assert_eq!(remainders[1], num_bigint::BigInt::from(12_427_605u64));
        for i in 0..2 {
            assert_eq!(&y[i] * &denominators[i] + &remainders[i], numerators[i]);
            assert!(&remainders[i] >= &num_bigint::BigInt::from(0u8));
            assert!(&remainders[i] < &denominators[i]);
        }
        let x = [
            num_bigint::BigInt::from(2_048u32),
            num_bigint::BigInt::from(3_072u32),
        ];
        let two = num_bigint::BigInt::from(2u8);
        let precision = num_bigint::BigInt::from(1_000_000_000u64);
        let x_sum = &x[0] + &x[1];
        let y_sum = &y[0] + &y[1];
        let xy_sum = &x[0] * &y[0] + &x[1] * &y[1];
        let x2_sum = &x[0] * &x[0] + &x[1] * &x[1];
        let b =
            (&xy_sum * &two - &x_sum * &y_sum) * &precision / (&x2_sum * &two - &x_sum * &x_sum);
        let a = (&y_sum * &precision - &b * &x_sum) / &two / &precision;
        let point = num_bigint::BigInt::from(4_096u32);
        let prediction = &a + &b * &point / &precision;
        assert_eq!(b, num_bigint::BigInt::from(80_221_022_211_041_992_187u128));
        assert_eq!(a, num_bigint::BigInt::from(-143_148_173_335_589i64));
        assert_eq!(prediction, num_bigint::BigInt::from(185_437_133_640_838u64));
        let (compact, decoded) =
            daa_finish::native_positive_compact_roundtrip(&prediction.to_biguint().unwrap());
        assert_eq!(compact, 0x0700_a8a7);
        assert_eq!(decoded, num_bigint::BigUint::from(185_435_213_004_800u64));
        assert_eq!(child.decoded.n_bits, compact);
        assert_eq!(decode_numeric_difficulty(child.decoded.n_bits), decoded);
        eprintln!(
            "{}",
            serde_json::json!({
                "child": 3073,
                "samples": [1024, 2048, 3072],
                "deltas_ms": dt,
                "ratio_quotients": [y[0].to_string(), y[1].to_string()],
                "slope_scaled": b.to_string(),
                "intercept": a.to_string(),
                "prediction": prediction.to_string(),
                "compact": format!("{compact:08x}"),
                "authority_ceiling": "selected RAW two-ratio arithmetic and direct parent only; no authenticated history or compact proof"
            })
        );
    }

    #[test]
    fn early_legacy_3073_constrained_two_ratio_finish_matches_raw_child() {
        use ark_ff::{One, Zero};
        use crate::daa_regression;
        let (_, headers) = fixture();
        let samples = [1024, 2048, 3072].map(|h| decode_header(headers.get(&h).unwrap()).unwrap());
        let child_fixture: serde_json::Value = serde_json::from_str(CHILD_3073_FIXTURE).unwrap();
        let child_raw = decode_hex(child_fixture["raw_hex"].as_str().unwrap());
        let child = decode_header(&child_raw).unwrap();
        let input = daa_integer::TwoRatioInputs {
            nbits: [samples[1].decoded.n_bits, samples[2].decoded.n_bits],
            timestamps: samples.each_ref().map(|s| s.decoded.timestamp),
        };
        let mut c = daa_finish::compile_two_finish_with_child(&daa_count::q(), input,
            child.decoded.n_bits, true).unwrap();
        assert!(daa_finish::finish_residuals(&c).unwrap().iter().all(Zero::is_zero));
        let w = &c.joined.joined.joined.witness;
        let slope = &c.joined.joined.output;
        let prediction = &c.joined.output;
        assert_eq!(daa_regression::signed_value(w, &slope.slope_magnitude, slope.slope_negative),
            num_bigint::BigInt::from(80_221_022_211_041_992_187u128));
        assert_eq!(daa_regression::signed_value(w, &prediction.a_magnitude, prediction.a_negative),
            num_bigint::BigInt::from(-143_148_173_335_589i64));
        assert_eq!(daa_regression::signed_value(w, &prediction.prediction_magnitude, prediction.prediction_negative),
            num_bigint::BigInt::from(185_437_133_640_838u64));
        let read = |bits: &[usize]| bits.iter().enumerate().fold(num_bigint::BigUint::from(0u8),
            |v,(i,&wire)| if w[wire].is_one() {v+(num_bigint::BigUint::from(1u8)<<i)} else {v});
        assert_eq!(read(&c.output.numeric_result), num_bigint::BigUint::from(185_435_213_004_800u64));
        assert_eq!(c.joined.joined.joined.external.len(), 2);
        assert_eq!(w[c.output.use_prediction], ark_bn254::Fr::one());
        let child_wire = c.child_nbits.unwrap()[0];
        let original = w[child_wire];
        c.joined.joined.joined.witness[child_wire] = ark_bn254::Fr::one()-original;
        assert!(daa_finish::finish_residuals(&c).unwrap().iter().any(|r| !r.is_zero()));
        c.joined.joined.joined.witness[child_wire] = original;
        assert!(daa_finish::finish_residuals(&c).unwrap().iter().all(Zero::is_zero));
        let wrong = daa_finish::compile_two_finish_with_child(&daa_count::q(), input,
            child.decoded.n_bits ^ 1, true).unwrap();
        assert!(daa_finish::finish_residuals(&wrong).unwrap().iter().any(|r| !r.is_zero()));
        println!("{}",serde_json::json!({"profile":"LegacyTwoRatio3073",
            "terms":c.joined.joined.joined.count.terms,"rows":c.joined.joined.joined.count.padded_rows,
            "input_len":c.joined.joined.joined.count.padded_input_bits,
            "claim_ceiling":"local constrained arithmetic; RAW serializer and proof pending"}));
    }

    #[test]
    fn three_mature_mainnet_windows_join_true_child_nbits_through_a4() {
        let (fixture, headers) = fixture();
        for child_height in [9_217, 844_673, 844_801] {
            let case = fixture
                .cases
                .iter()
                .find(|case| case.child == child_height)
                .unwrap();
            let parent = headers.get(&case.parent).unwrap();
            let child = headers.get(&case.child).unwrap();
            let samples = case
                .samples
                .iter()
                .map(|height| headers.get(height).unwrap().as_slice())
                .collect::<Vec<_>>();
            let raw_child_before = child.as_slice().to_vec();
            let selected = select_window(parent, child, &samples).unwrap();
            assert!(matches!(selected.action(), Action::Retarget(_)));
            assert_eq!(selected.child_height(), child_height);
            assert_eq!(selected.prediction().x0, case.samples[1]);
            let epoch = match selected.action() {
                Action::Retarget(epoch) => epoch.length() as u32,
                Action::Carry | Action::FixedV2 => unreachable!(),
            };
            let forecast_height = selected.prediction().x0 + 8 * epoch;
            let expected_forecast = match child_height {
                9_217 => 10_240,
                844_673 => 844_800,
                844_801 => 844_928,
                _ => unreachable!(),
            };
            assert_eq!(forecast_height, expected_forecast);
            let compiled = compile_selected_window(&selected).unwrap();
            let residuals = daa_finish::finish_residuals(&compiled).unwrap();
            let nonzero_residual_count = residuals
                .iter()
                .filter(|residual| !residual.is_zero())
                .count();
            let count = &compiled.joined.joined.joined.count;
            eprintln!(
                "{}",
                serde_json::json!({
                    "child": child_height,
                    "epoch": epoch,
                    "x0": selected.prediction().x0,
                    "forecast_height": forecast_height,
                    "true_child_nbits": format!("{:08x}", selected.child_nbits()),
                    "numeric_difficulty": decode_numeric_difficulty(selected.child_nbits()).to_string(),
                    "padded_input_bits": count.padded_input_bits,
                    "padded_rows": count.padded_rows,
                    "terms": count.terms,
                    "nonzero_residual_count": nonzero_residual_count
                })
            );
            assert_eq!(nonzero_residual_count, 0);
            assert_eq!(headers.get(&child_height).unwrap(), &raw_child_before);
        }
    }

    #[test]
    fn carry_reset_immature_and_malformed_source_windows_fail_closed() {
        let (_, headers) = fixture();
        let child2 =
            select_window(headers.get(&1).unwrap(), headers.get(&2).unwrap(), &[]).unwrap_err();
        assert!(child2.contains("carry"));
        let fixed = select_window(
            headers.get(&417_791).unwrap(),
            headers.get(&417_792).unwrap(),
            &[],
        )
        .unwrap_err();
        assert!(fixed.contains("fixed-V2"));

        let case = for_child_height(8_193).unwrap();
        assert_eq!(case.sample_heights().len(), 8);
        let samples = case
            .sample_heights()
            .iter()
            .map(|height| headers.get(height).unwrap().as_slice())
            .collect::<Vec<_>>();
        assert!(select_window(
            headers.get(&8_192).unwrap(),
            headers.get(&8_193).unwrap(),
            &samples
        )
        .unwrap_err()
        .contains("immature"));

        let parent = headers.get(&9_216).unwrap();
        let child = headers.get(&9_217).unwrap();
        let case = fixture()
            .0
            .cases
            .into_iter()
            .find(|case| case.child == 9_217)
            .unwrap();
        let valid = case
            .samples
            .iter()
            .map(|height| headers.get(height).unwrap().as_slice())
            .collect::<Vec<_>>();
        let mut short = valid.clone();
        short.pop();
        assert!(select_window(parent, child, &short)
            .unwrap_err()
            .contains("sample count"));
        let mut reordered = valid.clone();
        reordered.swap(0, 1);
        assert!(select_window(parent, child, &reordered)
            .unwrap_err()
            .contains("height mismatch"));
        let mut bad_height = valid.clone();
        let changed = encode_mutated(bad_height[0], |header| header.height += 1);
        bad_height[0] = &changed;
        assert!(select_window(parent, child, &bad_height)
            .unwrap_err()
            .contains("height mismatch"));
        let mut surplus = valid.clone();
        surplus.push(valid[0]);
        assert!(select_window(parent, child, &surplus)
            .unwrap_err()
            .contains("sample count"));
        let mut malformed = valid.clone();
        malformed[3] = &[0];
        assert!(select_window(parent, child, &malformed)
            .unwrap_err()
            .contains("invalid header"));
        assert!(decode_header(&[]).unwrap_err().contains("length"));
        assert!(decode_header(&vec![0; MAX_HEADER_BYTES + 1])
            .unwrap_err()
            .contains("length"));
        let mut trailing = child.to_vec();
        trailing.push(0);
        assert!(decode_header(&trailing)
            .unwrap_err()
            .contains("invalid header"));

        let bad_child = encode_mutated(child, |header| header.parent_id = [0; 32]);
        assert!(select_window(parent, &bad_child, &valid)
            .unwrap_err()
            .contains("parent id"));
        let bad_parent_height = encode_mutated(parent, |header| header.height -= 1);
        assert!(select_window(&bad_parent_height, child, &valid)
            .unwrap_err()
            .contains("adjacent"));

        let different_parent_sample = encode_mutated(valid[8], |header| header.n_bits ^= 1);
        let mut different_last = valid.clone();
        different_last[8] = &different_parent_sample;
        assert!(select_window(parent, child, &different_last)
            .unwrap_err()
            .contains("exact parent"));

        let parent_timestamp = Header::decode(parent, None).unwrap().timestamp;
        let equal_first = encode_mutated(valid[0], |header| header.timestamp = parent_timestamp);
        let mut equal = valid.clone();
        equal[0] = &equal_first;
        assert!(select_window(parent, child, &equal)
            .unwrap_err()
            .contains("must follow"));
        let descending_first = encode_mutated(valid[0], |header| {
            header.timestamp = parent_timestamp.saturating_add(1)
        });
        let mut descending = valid.clone();
        descending[0] = &descending_first;
        assert!(select_window(parent, child, &descending)
            .unwrap_err()
            .contains("must follow"));

        let prior_timestamp = Header::decode(valid[3], None).unwrap().timestamp;
        let repeated_interior =
            encode_mutated(valid[4], |header| header.timestamp = prior_timestamp);
        let mut zero_delta = valid.clone();
        zero_delta[4] = &repeated_interior;
        assert!(select_window(parent, child, &zero_delta)
            .unwrap_err()
            .contains("zero DAA denominator"));
    }

    #[test]
    fn changed_true_child_nbits_breaks_the_a4_residual() {
        let (fixture, headers) = fixture();
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == 844_801)
            .unwrap();
        let parent = headers.get(&case.parent).unwrap();
        let child = headers.get(&case.child).unwrap();
        let samples = case
            .samples
            .iter()
            .map(|height| headers.get(height).unwrap().as_slice())
            .collect::<Vec<_>>();
        let child_before = child.as_slice().to_vec();
        let changed_child = encode_mutated(child, |header| header.n_bits ^= 1);
        assert_ne!(changed_child, child_before);
        assert_ne!(
            decode_numeric_difficulty(Header::decode(&changed_child, None).unwrap().n_bits),
            decode_numeric_difficulty(Header::decode(child, None).unwrap().n_bits)
        );
        let selected = select_window(parent, &changed_child, &samples).unwrap();
        let compiled = compile_selected_window(&selected).unwrap();
        assert!(daa_finish::finish_residuals(&compiled)
            .unwrap()
            .iter()
            .any(|residual| !residual.is_zero()));
    }
}

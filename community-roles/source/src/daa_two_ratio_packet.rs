//! Bounded exact-RAW Legacy m=2 packet: one composite GKR and one PCS.
//! The caller owns the expected RAW roster and admitted diagnostic key. This
//! profile does not prove historical inclusion, PoW or mainnet security.
use crate::{
    daa_two_ratio_join::{Plan, INPUT_LOG, LOCAL_LOG, ROW_LOCAL_LOG, ROW_LOG, SLOT_LOG, WIDTH},
    gkr::{self, InputClaim},
    packed::{self, PackedCommitted, PackedFile},
    pcs::{self, Setup},
    sparse_stream_roster,
    transcript::Transcript,
    verifier_key::AdmittedVerifierKey,
};
use ark_bn254::Fr;
use serde::{Deserialize, Serialize};

const PROFILE: &str = "legacy-two-ratio-3073-exact-raw-one-gkr-pcs-v1";
const DOMAIN: &[u8] = b"nipopow-legacy-two-ratio-3073-packet-v1";
const MAGIC: &[u8; 8] = b"M2DAAP01";
const VERSION: u8 = 1;
const EXPECTED_CAP: usize = 16_384;
const SECTION_BYTES: [usize; 3] = [4_576, 26_829, 32];
pub(crate) const PACKET_BYTES: usize = 8 + 1 + 3 * 5 + 4_576 + 26_829 + 32;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExpectedStatement {
    version: u8,
    profile: String,
    input_log: u8,
    sample_heights: [u32; 4],
    ratio_count: u8,
    setup_id: [u8; 32],
    commitment_hex: String,
    raw_headers_hex: [String; 4],
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn unhex(text: &str) -> Result<Vec<u8>, String> {
    if text.len() % 2 != 0
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("noncanonical lowercase hex".into());
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}
impl ExpectedStatement {
    pub(crate) fn new(
        raw: &[Vec<u8>; 4],
        setup: &Setup,
        committed: &PackedCommitted,
    ) -> Result<Self, String> {
        let value = Self {
            version: VERSION,
            profile: PROFILE.into(),
            input_log: INPUT_LOG as u8,
            sample_heights: [1024, 2048, 3072, 3073],
            ratio_count: 2,
            setup_id: setup.id,
            commitment_hex: hex(&pcs::encode_commitment(&committed.commitment)?),
            raw_headers_hex: raw.each_ref().map(|r| hex(r)),
        };
        value.validate()?;
        Ok(value)
    }
    fn validate(&self) -> Result<(), String> {
        if self.version != VERSION
            || self.profile != PROFILE
            || self.input_log as usize != INPUT_LOG
            || self.sample_heights != [1024, 2048, 3072, 3073]
            || self.ratio_count != 2
        {
            return Err("m2 code-owned profile/count/order rejected".into());
        }
        pcs::decode_commitment(&unhex(&self.commitment_hex)?)?;
        for raw in &self.raw_headers_hex {
            if raw.is_empty() || raw.len() > 2 * 514 {
                return Err("m2 RAW cap rejected".into());
            }
            unhex(raw)?;
        }
        Ok(())
    }
    fn raws(&self) -> Result<[Vec<u8>; 4], String> {
        self.raw_headers_hex
            .iter()
            .map(|s| unhex(s))
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|_| "m2 RAW roster".into())
    }
}
pub(crate) fn encode_expected(expected: &ExpectedStatement) -> Result<Vec<u8>, String> {
    expected.validate()?;
    let bytes = serde_json::to_vec_pretty(expected).map_err(|e| e.to_string())?;
    if bytes.len() > EXPECTED_CAP {
        return Err("m2 expected cap".into());
    }
    Ok(bytes)
}
fn decode_expected(bytes: &[u8]) -> Result<ExpectedStatement, String> {
    if bytes.is_empty() || bytes.len() > EXPECTED_CAP {
        return Err("m2 expected length".into());
    }
    let expected: ExpectedStatement = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    if encode_expected(&expected)? != bytes {
        return Err("noncanonical m2 expected".into());
    }
    Ok(expected)
}

#[derive(Clone)]
pub(crate) struct Packet {
    gkr: Vec<u8>,
    pcs: Vec<u8>,
    post_pcs: Vec<u8>,
}
pub(crate) fn encode_packet(packet: &Packet) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::with_capacity(PACKET_BYTES);
    bytes.extend_from_slice(MAGIC);
    bytes.push(VERSION);
    for (i, section) in [&packet.gkr, &packet.pcs, &packet.post_pcs]
        .into_iter()
        .enumerate()
    {
        if section.len() != SECTION_BYTES[i] {
            return Err(format!("m2 section {i} length"));
        }
        bytes.push(i as u8);
        bytes.extend_from_slice(&(section.len() as u32).to_le_bytes());
        bytes.extend_from_slice(section);
    }
    if bytes.len() != PACKET_BYTES {
        return Err("m2 packet size drift".into());
    }
    Ok(bytes)
}
fn decode_packet(bytes: &[u8]) -> Result<Packet, String> {
    if bytes.len() != PACKET_BYTES {
        return Err("m2 packet length/EOF".into());
    }
    if &bytes[..8] != MAGIC || bytes[8] != VERSION {
        return Err("m2 packet profile".into());
    }
    let mut at = 9;
    let mut ranges = [(0, 0); 3];
    for i in 0..3 {
        if bytes[at] as usize != i {
            return Err("m2 component order".into());
        }
        let size = u32::from_le_bytes(bytes[at + 1..at + 5].try_into().unwrap()) as usize;
        if size != SECTION_BYTES[i] {
            return Err("m2 component size before allocation".into());
        }
        at += 5;
        ranges[i] = (at, at + size);
        at += size;
    }
    if at != bytes.len() {
        return Err("m2 trailing bytes".into());
    }
    let section = |i: usize| bytes[ranges[i].0..ranges[i].1].to_vec();
    Ok(Packet {
        gkr: section(0),
        pcs: section(1),
        post_pcs: section(2),
    })
}
fn bind(plan: &Plan, expected: &ExpectedStatement, t: &mut Transcript) {
    t.append_bytes(b"packet-profile", PROFILE.as_bytes());
    t.append_bytes(b"packet-magic", MAGIC);
    t.append_u64(b"packet-version", VERSION as u64);
    t.append_u64(b"mandatory-gkr", 1);
    t.append_u64(b"mandatory-pcs", 1);
    // Lowercase hex was admitted; decoding is deterministic and infallible here.
    plan.bind(
        t,
        &expected.setup_id,
        &unhex(&expected.commitment_hex).expect("admitted commitment"),
    );
}
fn verify_gkr(
    plan: &Plan,
    expected: &ExpectedStatement,
    packet: &Packet,
) -> Result<(InputClaim, Transcript), String> {
    let proof = gkr::decode_dimensions(&[INPUT_LOG], &packet.gkr)?;
    let mut t = Transcript::new(DOMAIN);
    let claim = gkr::verify_with_wiring(
        &[INPUT_LOG],
        1 << ROW_LOG,
        &proof,
        &mut t,
        |t| bind(plan, expected, t),
        |_, r, u, v| {
            plan.coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        },
    )
    .map_err(|e| format!("m2 GKR: {e}"))?;
    Ok((claim, t))
}

/// No proof-supplied profile, role roster, claim point or opening value is accepted.
pub(crate) fn verify_with_key(
    expected_bytes: &[u8],
    packet_bytes: &[u8],
    key: &AdmittedVerifierKey,
) -> Result<serde_json::Value, String> {
    let started = std::time::Instant::now();
    let expected = decode_expected(expected_bytes)?;
    let packet = decode_packet(packet_bytes)?;
    if key.log_n() != INPUT_LOG || key.id() != &expected.setup_id {
        return Err("m2 admitted key mismatch".into());
    }
    let plan = Plan::build(&expected.raws()?)?;
    let (claim, mut t) = verify_gkr(&plan, &expected, &packet)?;
    let proof = pcs::decode_proof(&packet.pcs, INPUT_LOG)?;
    pcs::verify_admitted(
        pcs::decode_commitment(&unhex(&expected.commitment_hex)?)?,
        claim.value,
        &claim.point,
        &proof,
        key,
        &mut t,
    )
    .map_err(|e| format!("m2 PCS: {e}"))?;
    if pcs::encode(&t.challenge_scalar(b"m2-post-pcs"))? != packet.post_pcs {
        return Err("m2 post-PCS artifact mismatch".into());
    }
    Ok(
        serde_json::json!({"profile":PROFILE,"gkr_proofs":1,"pcs_openings":1,
        "proof_bytes":packet_bytes.len(),"verify_seconds":started.elapsed().as_secs_f64(),
        "claim_ceiling":"four verifier-selected exact RAW headers and local Legacy m2 arithmetic/direct edge; no authenticated history or PoW; diagnostic BN254"}),
    )
}

fn read_owner(source: &PackedFile, slot: usize) -> Result<Vec<Fr>, String> {
    if source.input_len() != 1 << INPUT_LOG || slot >= 1 << SLOT_LOG {
        return Err("m2 packed owner bounds invalid".into());
    }
    // PackedFile retains its reviewed 2^16-coordinate read cap. Each owner
    // occupies two adjacent capped copies in the same LSB-first input order.
    let mut values = source.read_copy(WIDTH / 2, 2 * slot)?;
    values.extend(source.read_copy(WIDTH / 2, 2 * slot + 1)?);
    Ok(values)
}

pub(crate) fn prove(
    expected: &ExpectedStatement,
    source: &PackedFile,
    setup: &Setup,
    committed: &PackedCommitted,
) -> Result<(Packet, serde_json::Value), String> {
    expected.validate()?;
    if setup.log_n != INPUT_LOG
        || source.input_len() != 1 << INPUT_LOG
        || setup.id != expected.setup_id
        || committed.nu != INPUT_LOG / 2
        || committed.sigma != INPUT_LOG.div_ceil(2)
        || pcs::encode_commitment(&committed.commitment)? != unhex(&expected.commitment_hex)?
    {
        return Err("m2 producer setup/commitment mismatch".into());
    }
    let plan = Plan::build(&expected.raws()?)?;
    let mut t = Transcript::new(DOMAIN);
    let mark = std::time::Instant::now();
    let (proof, claim, incremental_u, incremental_v) = sparse_stream_roster::prove_edge_terms(
        LOCAL_LOG,
        SLOT_LOG,
        ROW_LOCAL_LOG,
        0,
        &[ROW_LOCAL_LOG],
        |left, slot, sink| plan.visit_endpoint(left, slot, sink),
        |slot| read_owner(source, slot),
        &mut t,
        |t| bind(&plan, expected, t),
        |r, u, v| plan.coefficients(r, u, v),
    )?;
    let gkr_seconds = mark.elapsed().as_secs_f64();
    if source.evaluate(&claim.point)? != claim.value {
        return Err("m2 common witness claim mismatch".into());
    }
    let mark = std::time::Instant::now();
    let opening = packed::open(committed, source, &claim.point, setup, &mut t)?;
    let pcs_seconds = mark.elapsed().as_secs_f64();
    let packet = Packet {
        gkr: gkr::encode_proof(&proof)?,
        pcs: pcs::encode_proof(&opening)?,
        post_pcs: pcs::encode(&t.challenge_scalar(b"m2-post-pcs"))?,
    };
    encode_packet(&packet)?;
    Ok((
        packet,
        serde_json::json!({"gkr_seconds":gkr_seconds,"pcs_seconds":pcs_seconds,
        "terms":plan.term_count(),"input_log":INPUT_LOG,"row_log":ROW_LOG,
        "incremental_u":incremental_u,"incremental_v":incremental_v}),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{One, Zero};
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    use std::{
        io::Write,
        path::{Path, PathBuf},
    };
    fn directory() -> PathBuf {
        let root = std::env::var_os("NIPOPOW_M2_PACKET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                std::env::temp_dir().join(format!(
                    "nipopow-m2-{}-{}",
                    std::process::id(),
                    std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_nanos()
                ))
            });
        std::fs::create_dir_all(&root).unwrap();
        root
    }
    fn create(path: &Path, bytes: &[u8]) {
        let mut f = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .unwrap();
        f.write_all(bytes).unwrap();
        f.sync_all().unwrap();
    }
    fn key(setup: &Setup) -> AdmittedVerifierKey {
        let bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
        crate::verifier_key::admit_generated_test_key(INPUT_LOG, &bytes, setup.id).unwrap()
    }
    fn raw_field_faults(
        expected: &ExpectedStatement,
        packet: &[u8],
        key: &AdmittedVerifierKey,
    ) -> usize {
        let mut count = 0;
        for slot in 0..4 {
            for field in ["height", "timestamp", "nbits"] {
                let raw = unhex(&expected.raw_headers_hex[slot]).unwrap();
                let mut header = ergo_header_core::Header::decode(&raw, None).unwrap();
                match field {
                    "height" => header.height += 1,
                    "timestamp" => header.timestamp += 1,
                    "nbits" => header.n_bits ^= 1,
                    _ => unreachable!(),
                }
                let changed_raw = header.encode().unwrap();
                assert_ne!(raw, changed_raw);
                let mut changed = expected.clone();
                changed.raw_headers_hex[slot] = hex(&changed_raw);
                assert!(
                    verify_with_key(&encode_expected(&changed).unwrap(), packet, key).is_err(),
                    "fresh expected RAW slot{slot} {field}"
                );
                count += 1;
            }
        }
        for slot in [2, 3] {
            let raw = unhex(&expected.raw_headers_hex[slot]).unwrap();
            let mut header = ergo_header_core::Header::decode(&raw, None).unwrap();
            header.parent_id[0] ^= 1;
            let mut changed = expected.clone();
            changed.raw_headers_hex[slot] = hex(&header.encode().unwrap());
            assert!(
                verify_with_key(&encode_expected(&changed).unwrap(), packet, key).is_err(),
                "fresh expected RAW parentId slot{slot}"
            );
            count += 1;
        }
        count
    }
    #[test]
    fn m2_packed_owner_reader_preserves_coordinates_and_bounds() {
        let dir = directory();
        let bytes = (0..(1 << INPUT_LOG) / 8)
            .map(|i| ((i * 37 + (i >> 8) * 13 + (i >> 13) * 59) % 256) as u8)
            .collect::<Vec<_>>();
        let mut writer =
            packed::PackedFileWriter::create_new(&dir.join("owner-reader.bits"), INPUT_LOG)
                .unwrap();
        writer.write_bytes(&bytes).unwrap();
        let source = writer.finish().unwrap();
        assert!(source.read_copy(WIDTH, 0).is_err());
        for slot in 0..1 << SLOT_LOG {
            let values = read_owner(&source, slot).unwrap();
            assert_eq!(values.len(), WIDTH);
            for (local, actual) in values.iter().enumerate() {
                let bit = slot * WIDTH + local;
                assert_eq!(
                    *actual,
                    Fr::from(((bytes[bit / 8] >> (bit % 8)) & 1) as u64)
                );
            }
        }
        assert!(read_owner(&source, 1 << SLOT_LOG)
            .unwrap_err()
            .contains("owner bounds"));
        let mut wrong_writer = packed::PackedFileWriter::create_new(
            &dir.join("wrong-owner-shape.bits"),
            INPUT_LOG - 1,
        )
        .unwrap();
        wrong_writer.write_bytes(&bytes[..bytes.len() / 2]).unwrap();
        let wrong_source = wrong_writer.finish().unwrap();
        assert!(read_owner(&wrong_source, 0)
            .unwrap_err()
            .contains("owner bounds"));
    }
    #[test]
    fn m2_one_gkr_one_pcs_producer_and_packet_faults() {
        let whole = std::time::Instant::now();
        let dir = directory();
        let raws = crate::daa_two_ratio_join::fixture_raws();
        let plan = Plan::build(&raws).unwrap();
        let witness = plan.materialize_witness().unwrap();
        plan.check_residuals(&witness).unwrap();
        let bytes = witness
            .chunks_exact(8)
            .map(|bits| {
                bits.iter().enumerate().fold(0u8, |n, (i, x)| {
                    assert!(x.is_zero() || x.is_one());
                    n | ((x.is_one() as u8) << i)
                })
            })
            .collect::<Vec<_>>();
        let path = dir.join("witness.bits");
        let mut writer = packed::PackedFileWriter::create_new(&path, INPUT_LOG).unwrap();
        writer.write_bytes(&bytes).unwrap();
        let source = writer.finish().unwrap();
        drop(witness);
        let mark = std::time::Instant::now();
        let setup = pcs::generate_setup(INPUT_LOG).unwrap();
        let setup_seconds = mark.elapsed().as_secs_f64();
        let admitted = key(&setup);
        let mark = std::time::Instant::now();
        let committed = packed::commit(&source, &setup).unwrap();
        let commit_seconds = mark.elapsed().as_secs_f64();
        let expected = ExpectedStatement::new(&raws, &setup, &committed).unwrap();
        let expected_bytes = encode_expected(&expected).unwrap();
        let (packet, metrics) = prove(&expected, &source, &setup, &committed).unwrap();
        let packet_bytes = encode_packet(&packet).unwrap();
        let report = verify_with_key(&expected_bytes, &packet_bytes, &admitted).unwrap();
        // Each fixture below changes a single independently admitted boundary.
        let mut negatives = 0;
        for field in ["version", "count", "profile", "dimension", "setup"] {
            let mut changed = expected.clone();
            match field {
                "version" => changed.version ^= 1,
                "count" => changed.ratio_count = 3,
                "profile" => changed.profile.push('x'),
                "dimension" => changed.input_log += 1,
                "setup" => changed.setup_id[0] ^= 1,
                _ => unreachable!(),
            }
            let input = serde_json::to_vec_pretty(&changed).unwrap();
            assert!(
                verify_with_key(&input, &packet_bytes, &admitted).is_err(),
                "{field}"
            );
            negatives += 1;
        }
        let mut swapped = expected.clone();
        swapped.raw_headers_hex.swap(1, 2);
        assert!(verify_with_key(
            &encode_expected(&swapped).unwrap(),
            &packet_bytes,
            &admitted
        )
        .is_err());
        negatives += 1;
        let mut wrong_commitment = expected.clone();
        let mut commitment =
            pcs::decode_commitment(&unhex(&expected.commitment_hex).unwrap()).unwrap();
        let delta = commitment.0;
        commitment.0 += delta;
        wrong_commitment.commitment_hex = hex(&pcs::encode_commitment(&commitment).unwrap());
        assert_ne!(wrong_commitment.commitment_hex, expected.commitment_hex);
        assert!(verify_with_key(
            &encode_expected(&wrong_commitment).unwrap(),
            &packet_bytes,
            &admitted
        )
        .unwrap_err()
        .contains("GKR"));
        negatives += 1;
        // Canonical scalar alteration reaches the GKR checks rather than the codec.
        let mut changed = packet.clone();
        let mut g = gkr::decode_dimensions(&[INPUT_LOG], &changed.gkr).unwrap();
        g.layers[0].rounds[0][0] += Fr::one();
        changed.gkr = gkr::encode_proof(&g).unwrap();
        assert!(verify_with_key(
            &expected_bytes,
            &encode_packet(&changed).unwrap(),
            &admitted
        )
        .unwrap_err()
        .contains("GKR"));
        negatives += 1;
        // t*(t-1) preserves both line endpoints and every sumcheck message.
        // GKR consequently derives a different terminal point/value, whose
        // unchanged PCS opening must fail at the opening boundary.
        let mut changed = packet.clone();
        let mut g = gkr::decode_dimensions(&[INPUT_LOG], &changed.gkr).unwrap();
        g.layers[0].line_coefficients[1] -= Fr::one();
        g.layers[0].line_coefficients[2] += Fr::one();
        changed.gkr = gkr::encode_proof(&g).unwrap();
        assert!(verify_with_key(
            &expected_bytes,
            &encode_packet(&changed).unwrap(),
            &admitted
        )
        .unwrap_err()
        .contains("PCS"));
        negatives += 1;
        let mut changed = packet.clone();
        let mut p = pcs::decode_proof(&changed.pcs, INPUT_LOG).unwrap();
        let delta = p.first_messages[0].d1_left.0;
        p.first_messages[0].d1_left.0 += delta;
        changed.pcs = pcs::encode_proof(&p).unwrap();
        assert_ne!(changed.pcs, packet.pcs, "PCS mutation must change bytes");
        assert!(verify_with_key(
            &expected_bytes,
            &encode_packet(&changed).unwrap(),
            &admitted
        )
        .unwrap_err()
        .contains("PCS"));
        negatives += 1;
        let mut changed = packet.clone();
        changed.post_pcs[0] ^= 1;
        assert!(verify_with_key(
            &expected_bytes,
            &encode_packet(&changed).unwrap(),
            &admitted
        )
        .unwrap_err()
        .contains("post-PCS"));
        negatives += 1;
        for size in [0, 14, PACKET_BYTES - 1] {
            assert!(verify_with_key(&expected_bytes, &packet_bytes[..size], &admitted).is_err());
            negatives += 1;
        }
        let mut trailing = packet_bytes.clone();
        trailing.push(0);
        assert!(verify_with_key(&expected_bytes, &trailing, &admitted).is_err());
        negatives += 1;
        let mut changed = packet_bytes.clone();
        changed[9] = 1;
        assert!(verify_with_key(&expected_bytes, &changed, &admitted)
            .unwrap_err()
            .contains("order"));
        negatives += 1;
        let mut section_at = 9;
        for (index, size) in SECTION_BYTES.into_iter().enumerate() {
            let mut omitted = packet_bytes.clone();
            omitted.drain(section_at..section_at + 5 + size);
            assert!(
                verify_with_key(&expected_bytes, &omitted, &admitted)
                    .unwrap_err()
                    .contains("length/EOF"),
                "omitted component {index}"
            );
            negatives += 1;
            let mut changed = packet_bytes.clone();
            changed[section_at + 1..section_at + 5].copy_from_slice(&0u32.to_le_bytes());
            assert!(
                verify_with_key(&expected_bytes, &changed, &admitted)
                    .unwrap_err()
                    .contains("component size"),
                "component length {index}"
            );
            negatives += 1;
            section_at += 5 + size;
        }
        assert_eq!(section_at, PACKET_BYTES);
        create(&dir.join("expected.json"), &expected_bytes);
        create(&dir.join("packet.bin"), &packet_bytes);
        create(&dir.join("post-pcs.bin"), &packet.post_pcs);
        let receipt = serde_json::json!({"setup_seconds":setup_seconds,"commit_seconds":commit_seconds,
            "producer":metrics,"consumer":report,"isolated_packet_negatives":negatives,
            "whole_seconds":whole.elapsed().as_secs_f64(),"key_admission":"independently generated diagnostic test key; no released log20 pin"});
        create(
            &dir.join("producer.json"),
            &serde_json::to_vec_pretty(&receipt).unwrap(),
        );
        println!("{receipt}");
    }
    #[test]
    #[ignore = "separate fresh consumer requires NIPOPOW_M2_PACKET_INPUT_DIR"]
    fn m2_fresh_serialized_consumer() {
        let dir = PathBuf::from(
            std::env::var_os("NIPOPOW_M2_PACKET_INPUT_DIR")
                .expect("fresh consumer inputs required"),
        );
        let expected = std::fs::read(dir.join("expected.json")).unwrap();
        let packet = std::fs::read(dir.join("packet.bin")).unwrap();
        let setup = pcs::generate_setup(INPUT_LOG).unwrap();
        let admitted = key(&setup);
        let report = verify_with_key(&expected, &packet, &admitted).unwrap();
        let expected = decode_expected(&expected).unwrap();
        let negative_count = raw_field_faults(&expected, &packet, &admitted);
        assert_eq!(negative_count, 14);
        println!(
            "{}",
            serde_json::json!({"consumer":report,"isolated_expected_raw_negatives":negative_count,
            "scope":"fresh process verifies serialized producer output; RAW changes test expected-statement binding; coherent changed-witness/alias negatives are separate relation tests"})
        );
    }
}

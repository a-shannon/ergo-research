use super::*;
use crate::native_prefix_auth_plan::{Role4EndpointAdapter, Role4EndpointScope};
use ark_serialize::CanonicalSerialize;
use dory_pcs::{backends::arkworks::ArkFr, primitives::arithmetic::Group};
use serde_json::json;
use std::{cell::RefCell, fs, path::PathBuf};

const GKR_BYTES: usize = (7 * 22 + 3) * 32;
const OUTPUT_LIMIT: usize = 2 * 1024 * 1024;
const OUTPUT_NAMES: [&str; 6] = [
    "witness.bits", "statement.bin", "commitment.bin", "role4.gkr", "opening.pcs", "summary.json",
];

fn counters(t: &Transcript) -> [u64; 3] {
    [t.challenges(), t.raw_queries(), t.bytes_absorbed()]
}

fn same_continuation(a: &Transcript, b: &Transcript) {
    let before_a = counters(a);
    let before_b = counters(b);
    assert_eq!(before_a, before_b, "actual continuation counters");
    let mut probe_a = a.clone();
    let mut probe_b = b.clone();
    assert_eq!(
        probe_a.challenge_scalar(b"role4-streaming-join-continuation"),
        probe_b.challenge_scalar(b"role4-streaming-join-continuation"),
        "cloned continuation probes",
    );
    assert_eq!(counters(&probe_a), counters(&probe_b));
    assert_eq!(counters(a), before_a, "producer continuation untouched");
    assert_eq!(counters(b), before_b, "consumer continuation untouched");
}

fn phase_event(started: Instant, phase: &str, edge: &str) {
    if phase == "witness" && edge == "begin" {
        println!(); // Separate the first marker from libtest's test-name prefix.
    }
    println!("role4_streaming_phase {}", json!({
        "phase": phase, "edge": edge, "seconds": started.elapsed().as_secs_f64(),
    }));
    std::io::stdout().flush().unwrap();
}

fn resolved_directory(path: &Path) -> PathBuf {
    assert!(path.is_absolute(), "absolute controlled directory required");
    for ancestor in path.ancestors() {
        let metadata = fs::symlink_metadata(ancestor).unwrap();
        assert!(metadata.is_dir() && !metadata.file_type().is_symlink());
        #[cfg(windows)] {
            use std::os::windows::fs::MetadataExt;
            assert_eq!(metadata.file_attributes() & 0x400, 0, "reparse directory rejected");
        }
    }
    fs::canonicalize(path).unwrap()
}

struct Outputs {
    dir: PathBuf,
    bytes: usize,
    names: Vec<&'static str>,
}
impl Outputs {
    fn new() -> Self {
        let path = std::env::var_os("NIPOPOW_ROLE4_STREAMING_DIR")
            .expect("fresh role4 streaming output directory required");
        let dir = resolved_directory(Path::new(&path));
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 0, "output directory must be empty");
        Self { dir, bytes: 0, names: Vec::new() }
    }
    fn write(&mut self, name: &'static str, bytes: &[u8]) {
        assert!(OUTPUT_NAMES.contains(&name) && !self.names.contains(&name));
        let next = self.bytes.checked_add(bytes.len()).unwrap();
        assert!(next <= OUTPUT_LIMIT, "role4 retained outputs exceed 2MiB");
        let mut file = OpenOptions::new().write(true).create_new(true)
            .open(self.dir.join(name)).unwrap();
        file.write_all(bytes).unwrap();
        file.sync_all().unwrap();
        assert_eq!(file.metadata().unwrap().len(), bytes.len() as u64);
        self.bytes = next;
        self.names.push(name);
    }
    fn verify_inventory(&self) {
        let mut bytes = 0usize;
        let mut names = Vec::new();
        for entry in fs::read_dir(&self.dir).unwrap() {
            let entry = entry.unwrap();
            let metadata = fs::symlink_metadata(entry.path()).unwrap();
            assert!(metadata.is_file() && !metadata.file_type().is_symlink());
            #[cfg(windows)] {
                use std::os::windows::fs::MetadataExt;
                assert_eq!(metadata.file_attributes() & 0x400, 0);
            }
            let name = entry.file_name().into_string().unwrap();
            assert!(self.names.iter().any(|expected| *expected == name));
            names.push(name);
            bytes = bytes.checked_add(usize::try_from(metadata.len()).unwrap()).unwrap();
        }
        assert_eq!(names.len(), self.names.len());
        assert_eq!(bytes, self.bytes);
        assert!(bytes <= OUTPUT_LIMIT);
    }
}

fn consume_role4(
    context: &ProofContext<'_>,
    key: &verifier_key::AdmittedVerifierKey,
    commitment: &[u8],
    bytes: &[u8],
) -> Result<(InputClaim, Transcript), Reject> {
    if key.log_n() != 22 || bytes.len() != GKR_BYTES {
        return Err(Reject::Shape);
    }
    pcs::decode_commitment(commitment).map_err(|_| Reject::Commitment)?;
    let proof = gkr::decode_dimensions(&[22], bytes).map_err(|_| Reject::Role(4))?;
    let mut transcript = context.transcript(4, key, commitment);
    let claim = context.verify_role4(&proof, &mut transcript).map_err(|_| Reject::Role(4))?;
    if claim.point.len() != 22 {
        return Err(Reject::Role(4));
    }
    Ok((claim, transcript))
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |weight, (bit, coordinate)| {
        weight * if index >> bit & 1 == 0 { Fr::one() - coordinate } else { *coordinate }
    })
}

fn term_channels(term: &Term, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let weight = eq_index(r, term.row) * eq_index(u, term.gate.left) * eq_index(v, term.gate.right);
    [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3].map(|coefficient| weight * coefficient)
}

fn complete_s2_endpoint_constructor_preflight(context: &ProofContext<'_>) {
    let mut role_before = context.base.clone();
    context.bind_role(4, &mut role_before);
    let mut expected_height = Transcript::new(b"role4-constructor-preflight-height");
    HeightWork::new(&context.consumer.parent).unwrap().bind(&mut expected_height);
    let mut actual_height = Transcript::new(b"role4-constructor-preflight-height");
    context.height.bind(&mut actual_height);
    same_continuation(&actual_height, &expected_height);

    let legacy = Role4EndpointAdapter::new(
        &context.height, &context.daa, Role4EndpointScope::CompleteS2,
    ).unwrap();
    let mut legacy_calls = 0;
    let rejected = legacy.visit_endpoint(&legacy.binding(), true, 0, |_| {
        legacy_calls += 1;
        Ok(())
    });
    assert_eq!(rejected, Err("height endpoint complete S2 scope rejected".into()));
    assert_eq!(legacy_calls, 0, "legacy height must reject before the sink");

    let endpoint_height = role4_complete_s2_endpoint_height(context).unwrap();
    let adapter = Role4EndpointAdapter::new(
        &endpoint_height, &context.daa, Role4EndpointScope::CompleteS2,
    ).unwrap();
    let binding = adapter.binding();
    let mut generic_calls = 0;
    let admitted = adapter.visit_endpoint(&binding, true, 0, |edge| {
        adapter.check_edge(true, 0, &edge)?;
        generic_calls += 1;
        Err("role4 constructor preflight first edge".into())
    });
    assert_eq!(admitted, Err("role4 constructor preflight first edge".into()));
    assert_eq!(generic_calls, 1, "generic visitor must reach one checked edge");

    let r: Vec<_> = (0..22).map(|i| Fr::from((i + 5) as u64)).collect();
    let u: Vec<_> = (0..22).map(|i| Fr::from((2 * i + 13) as u64)).collect();
    let v: Vec<_> = (0..22).map(|i| Fr::from((3 * i + 29) as u64)).collect();
    assert_eq!(adapter.coefficients(&r, &u, &v).unwrap(),
        context.coefficients(4, &r, &u, &v).unwrap());
    let mut height_after = Transcript::new(b"role4-constructor-preflight-height");
    context.height.bind(&mut height_after);
    same_continuation(&actual_height, &height_after);
    let mut role_after = context.base.clone();
    context.bind_role(4, &mut role_after);
    same_continuation(&role_before, &role_after);
}

fn foreign_owner_control(context: &ProofContext<'_>) {
    let endpoint_height = role4_complete_s2_endpoint_height(context).unwrap();
    let adapter = Role4EndpointAdapter::new(
        &endpoint_height, &context.daa, Role4EndpointScope::CompleteS2,
    ).unwrap();
    let binding = adapter.binding();
    let mut selected = None;
    for owner in 0..4 {
        adapter.visit_endpoint(&binding, true, owner, |edge| {
            if selected.is_none() && edge.term.gate.left / layout::WIDTH != edge.term.gate.right / layout::WIDTH
                && !edge.term.gate.c1.is_zero() {
                selected = Some((owner, edge));
            }
            Ok(())
        }).unwrap();
    }
    let (owner, original) = selected.expect("native CompleteS2 must contain a foreign endpoint");
    let mut mutant = original.clone();
    mutant.term.gate.right = owner * layout::WIDTH + original.term.gate.right % layout::WIDTH;
    assert_ne!(mutant.term.gate.right, original.term.gate.right);
    assert_eq!(mutant.term.gate.right % layout::WIDTH, original.term.gate.right % layout::WIDTH);
    adapter.check_edge(true, owner, &original).unwrap();
    adapter.check_edge(true, owner, &mutant).unwrap(); // Geometry and selected endpoint remain valid.
    let r: Vec<_> = (0..22).map(|i| Fr::from((i + 5) as u64)).collect();
    let u: Vec<_> = (0..22).map(|i| Fr::from((2 * i + 13) as u64)).collect();
    let v: Vec<_> = (0..22).map(|i| Fr::from((3 * i + 29) as u64)).collect();
    let canonical = adapter.coefficients(&r, &u, &v).unwrap();
    assert_eq!(canonical, context.coefficients(4, &r, &u, &v).unwrap());
    let original_channels = term_channels(&original.term, &r, &u, &v);
    let mutant_channels = term_channels(&mutant.term, &r, &u, &v);
    assert_ne!(original_channels, mutant_channels, "foreign-owner control must be observable");
    let forged: [Fr; 4] = std::array::from_fn(|i| canonical[i] - original_channels[i] + mutant_channels[i]);
    assert_ne!(forged, canonical, "unchanged analytic coefficients reject the isolated source substitution");
}

fn gkr_controls(
    context: &ProofContext<'_>, key: &verifier_key::AdmittedVerifierKey,
    commitment: &[u8], proof: &GkrProof, encoded: &[u8], expected: &InputClaim,
) {
    let verify = |proof: &GkrProof| {
        context.verify_role4(proof, &mut context.transcript(4, key, commitment))
    };
    assert_eq!(verify(proof).unwrap(), *expected);
    let mut mutant = proof.clone();
    mutant.layers[0].rounds[0][0] += Fr::one();
    assert_eq!(verify(&mutant), Err(GkrError::SumcheckIdentity));

    let coefficients = RefCell::new(None);
    let positive = gkr::verify_with_wiring(
        &[context.geometry.input_bits[4]], 1 << context.geometry.row_bits[4], proof, &mut context.transcript(4, key, commitment),
        |t| context.bind_role(4, t),
        |_, r, u, v| {
            let value = context.coefficients(4, r, u, v).map_err(|_| GkrError::InvalidWireIndex)?;
            *coefficients.borrow_mut() = Some(value);
            Ok(value)
        },
    ).unwrap();
    assert_eq!(positive, *expected);
    let coefficients = coefficients.into_inner().unwrap();
    let multiplier = coefficients[1] + coefficients[3] * proof.layers[0].right_value;
    assert!(!multiplier.is_zero(), "left-value terminal control needs a nonzero multiplier");
    let mut mutant = proof.clone();
    mutant.layers[0].left_value += Fr::one();
    assert_eq!(verify(&mutant), Err(GkrError::TerminalExpression));
    let mut mutant = proof.clone();
    mutant.layers[0].line_coefficients[0] += Fr::one();
    assert_eq!(verify(&mutant), Err(GkrError::LineEndpoints));

    let mut trailing = encoded.to_vec();
    trailing.push(0);
    assert!(gkr::decode_dimensions(&[22], &trailing).is_err());
    assert!(gkr::decode_dimensions(&[22], &encoded[..encoded.len() - 1]).is_err());
    foreign_owner_control(context);
}

fn run_join() {
    let mut outputs = Outputs::new();
    let tmp = resolved_directory(Path::new(&std::env::var_os("TMP").expect("controlled TMP required")));
    let temp = resolved_directory(Path::new(&std::env::var_os("TEMP").expect("controlled TEMP required")));
    assert_eq!(tmp, temp);
    assert_ne!(tmp, outputs.dir);
    assert_eq!(fs::read_dir(&tmp).unwrap().count(), 0, "controlled temp must be empty");
    let started = Instant::now();
    phase_event(started, "witness", "begin");
    let public = Public::native(3).unwrap();
    let w = witness::build(&witness::retained_headers_n(3).unwrap()).unwrap();
    assert_eq!(w.root, public.root);
    assert_eq!(w.total, public.total);
    assert_eq!(w.tip, public.tip);
    assert_eq!(w.tip_time, public.tip_time);
    assert_eq!(w.values.len(), 1 << 22);
    let mut bits = vec![0u8; (1 << 22) / 8];
    for (i, value) in w.values.iter().enumerate() {
        if value.is_one() { bits[i / 8] |= 1 << (i % 8); }
        else { assert!(value.is_zero(), "native witness must be Boolean"); }
    }
    drop(w);
    outputs.write("witness.bits", &bits);
    drop(bits);
    let source = PackedFile::open(outputs.dir.join("witness.bits"), 22).unwrap();
    let consumer = Consumer::new(&public).unwrap();
    let context = ProofContext::new(&consumer).unwrap();
    complete_s2_endpoint_constructor_preflight(&context);
    let statement_bytes = public.bytes_with_geometry(&context.geometry).unwrap();
    assert_eq!(statement_bytes.len(), 568);
    outputs.write("statement.bin", &statement_bytes);
    phase_event(started, "witness", "end");

    phase_event(started, "setup", "begin");
    let setup = pcs::generate_setup(22).unwrap();
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
    assert_eq!(setup.id, *key.id());
    phase_event(started, "setup", "end");
    phase_event(started, "commit", "begin");
    let committed = packed::commit(&source, &setup).unwrap();
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    assert_eq!(commitment.len(), 384);
    outputs.write("commitment.bin", &commitment);
    phase_event(started, "commit", "end");

    phase_event(started, "dense_reference", "begin");
    let mut dense_t = context.transcript(4, &key, &commitment);
    let (dense_bytes, dense_claim) = {
        let circuit = context.small_circuit(4).unwrap();
        let input = read_all(&source, &context.geometry).unwrap();
        let (proof, claim) = sparse::prove_with_binding(
            &circuit, &input, 0, &mut dense_t, |t| context.bind_role(4, t),
        ).unwrap();
        (gkr::encode_proof(&proof).unwrap(), claim)
    };
    assert_eq!(dense_bytes.len(), GKR_BYTES);
    phase_event(started, "dense_reference", "end");
    phase_event(started, "stream_candidate", "begin");
    let mut producer_t = context.transcript(4, &key, &commitment);
    let (proof, claim, incremental_u, incremental_v) =
        prove_role4_complete_s2_streaming(&context, &source, 0, &mut producer_t).unwrap();
    assert!(!incremental_u, "explicit zero cache limit must select U fallback");
    assert!(!incremental_v, "explicit zero cache limit must select V fallback");
    let encoded = gkr::encode_proof(&proof).unwrap();
    assert_eq!(encoded.len(), GKR_BYTES);
    assert_eq!(encoded, dense_bytes, "first deciding producer differential");
    assert_eq!(claim, dense_claim);
    same_continuation(&producer_t, &dense_t);
    drop(dense_bytes);
    drop(dense_claim);
    drop(dense_t);
    outputs.write("role4.gkr", &encoded);
    phase_event(started, "stream_candidate", "end");

    phase_event(started, "gkr_consumer", "begin");
    let (derived, mut consumer_t) = consume_role4(&context, &key, &commitment, &encoded).unwrap();
    assert_eq!(derived, claim);
    same_continuation(&producer_t, &consumer_t);
    let post_gkr_counters = counters(&producer_t);
    let pre_pcs = consumer_t.clone();
    phase_event(started, "gkr_consumer", "end");
    phase_event(started, "single_opening", "begin");
    let opening = packed::open(&committed, &source, &derived.point, &setup, &mut producer_t).unwrap();
    let pcs_bytes = pcs::encode_proof(&opening).unwrap();
    assert_eq!(pcs_bytes.len(), 29421);
    let decoded_opening = pcs::decode_proof(&pcs_bytes, 22).unwrap();
    outputs.write("opening.pcs", &pcs_bytes);
    phase_event(started, "single_opening", "end");
    phase_event(started, "pcs_consumer", "begin");
    pcs::verify_admitted(
        committed.commitment.clone(), derived.value, &derived.point,
        &decoded_opening, &key, &mut consumer_t,
    ).unwrap();
    same_continuation(&producer_t, &consumer_t);
    let post_pcs_counters = counters(&producer_t);
    phase_event(started, "pcs_consumer", "end");

    phase_event(started, "negatives", "begin");
    let decoded_gkr = gkr::decode_dimensions(&[22], &encoded).unwrap();
    gkr_controls(&context, &key, &commitment, &decoded_gkr, &encoded, &derived);
    assert!(pcs::verify_admitted(
        committed.commitment.clone(), derived.value + Fr::one(), &derived.point,
        &decoded_opening, &key, &mut pre_pcs.clone(),
    ).is_err());
    let mut wrong_point = derived.point.clone();
    wrong_point[0] += Fr::one();
    assert!(pcs::verify_admitted(
        committed.commitment.clone(), derived.value, &wrong_point,
        &decoded_opening, &key, &mut pre_pcs.clone(),
    ).is_err());
    let wrong_commitment = committed.commitment.scale(&ArkFr(Fr::from(2u64)));
    assert_ne!(pcs::encode_commitment(&wrong_commitment).unwrap(), commitment);
    assert!(pcs::verify_admitted(
        wrong_commitment, derived.value, &derived.point,
        &decoded_opening, &key, &mut pre_pcs.clone(),
    ).is_err());
    let mut wrong_prefix = pre_pcs.clone();
    wrong_prefix.append_bytes(b"role4-streaming-prefix-control", b"changed");
    assert!(pcs::verify_admitted(
        committed.commitment.clone(), derived.value, &derived.point,
        &decoded_opening, &key, &mut wrong_prefix,
    ).is_err());
    let mut trailing_pcs = pcs_bytes.clone();
    trailing_pcs.push(0);
    assert!(pcs::decode_proof(&trailing_pcs, 22).is_err());
    let mut wrong_rounds = pcs_bytes.clone();
    let rounds_offset = 2 * committed.commitment.0.compressed_size()
        + ark_bn254::G1Projective::zero().compressed_size();
    wrong_rounds[rounds_offset..rounds_offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(pcs::decode_proof(&wrong_rounds, 22).is_err());
    same_continuation(&producer_t, &consumer_t);
    assert_eq!(fs::read_dir(&tmp).unwrap().count(), 0, "controlled temp must remain empty");
    outputs.verify_inventory();
    phase_event(started, "negatives", "end");

    phase_event(started, "final_report", "begin");
    let mut report = json!({
        "schema": "role4-complete-s2-streaming-join-v1", "result": "PASS",
        "headers": 3, "owners": 4, "role": 4, "input_log": 22, "row_log": 22,
        "terms_per_side": 329122, "witness_bytes": 524288, "gkr_bytes": GKR_BYTES,
        "pcs_bytes": pcs_bytes.len(), "incremental_u": incremental_u, "incremental_v": incremental_v,
        "exact_gkr_bytes": true, "claim_equal": true, "post_gkr_continuation_equal": true,
        "post_pcs_continuation_equal": true, "role4_gkr_verified": true, "single_pcs_verified": true,
        "seven_role_packet_verified": false, "full_s12_equivalence": false, "gkr32_fit": false,
        "post_gkr_counters": post_gkr_counters, "post_pcs_counters": post_pcs_counters,
        "negatives": {"gkr_sumcheck": 1, "gkr_terminal": 1, "gkr_line": 1, "foreign_owner": 1,
            "gkr_codec": 2, "pcs_inputs": 4, "pcs_codec": 2},
        "output_bytes_total": 0,
    });
    let mut final_bytes = None;
    for _ in 0..8 {
        let bytes = serde_json::to_vec(&report).unwrap();
        let total = outputs.bytes.checked_add(bytes.len()).unwrap();
        if report["output_bytes_total"].as_u64() == Some(total as u64) {
            final_bytes = Some(bytes);
            break;
        }
        report["output_bytes_total"] = json!(total);
    }
    let report_bytes = final_bytes.expect("bounded report size must reach a fixed point");
    outputs.write("summary.json", &report_bytes);
    outputs.verify_inventory();
    assert_eq!(outputs.names.len(), OUTPUT_NAMES.len());
    assert_eq!(report["output_bytes_total"].as_u64().unwrap(), outputs.bytes as u64);
    println!("role4_streaming_join {}", std::str::from_utf8(&report_bytes).unwrap());
    std::io::stdout().flush().unwrap();
    phase_event(started, "final_report", "end");
}

#[test]
fn n3_complete_s2_endpoint_constructor_preflight() {
    let public = Public::native(3).unwrap();
    let consumer = Consumer::new(&public).unwrap();
    let context = ProofContext::new(&consumer).unwrap();
    complete_s2_endpoint_constructor_preflight(&context);
}

#[test]
#[ignore = "bounded native N3 role4 differential and admitted single opening; separate ROOT runtime GO"]
fn n3_complete_s2_edge_matches_dense_and_single_opening() {
    run_join();
}

use super::*;
use ark_ff::{One, Zero};
use num_bigint::BigUint;
use std::{collections::BTreeMap, path::{Path, PathBuf}};
use crate::{sparse::{Circuit, Term}, verifier_key, work_tree_layout::{Endpoints, WIDTH}};

fn key22() -> AdmittedVerifierKey {
    verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap()
}
fn total(headers: usize) -> [u8; 28] {
    let d = crate::work_tree_work::native_decode(0x0601_1765).unwrap();
    let bytes = (d * BigUint::from((headers - 1) as u64)).to_bytes_be();
    let mut out = [0; 28]; out[28 - bytes.len()..].copy_from_slice(&bytes); out
}
fn parent(headers: usize) -> WorkTreeHistoryPlan {
    WorkTreeHistoryPlan::compile(headers as u64,
        headers.next_power_of_two().trailing_zeros() as usize, [7; 32], total(headers)).unwrap()
}
fn circuit(p: &WorkTreeHistoryPlan) -> Circuit {
    let relation = NativeWorkRelation::new(p).unwrap();
    work_circuit(&relation, WORK_PRODUCER_COUNTS[p.headers() as usize - 3]).unwrap()
}
fn assign(map: &mut BTreeMap<usize, Fr>, wire: usize, value: Fr) {
    assert!(value.is_zero() || value.is_one());
    if let Some(old) = map.insert(wire, value) { assert_eq!(old, value, "wire{wire}"); }
}
fn integer(map: &mut BTreeMap<usize, Fr>, base: usize, wires: &[usize], value: &BigUint) {
    assert!(value.bits() <= wires.len() as u64);
    for (bit, wire) in wires.iter().enumerate() {
        assign(map, base + *wire, Fr::from(value.bit(bit as u64) as u64));
    }
}
// Copy of C554's bounded fixture semantics, not a canonical RAW witness.
// The free coordinate7 remains a bit here so the same fixture can be packed.
fn fixture_input(headers: usize) -> Vec<Fr> {
    let p = parent(headers);
    let base = work_tree_layout::shared_baseline().unwrap(); let e = &base.endpoints;
    let d = crate::work_tree_work::native_decode(0x0601_1765).unwrap();
    let mut map = BTreeMap::new();
    for owner in 0..headers - 1 {
        let offset = owner * WIDTH;
        let lower = &d * BigUint::from(owner as u64); let upper = &lower + &d;
        integer(&mut map, offset, &e.n_bits, &BigUint::from(0x0601_1765u32));
        integer(&mut map, offset, &e.height, &BigUint::from((owner + 2) as u64));
        integer(&mut map, offset, &e.lower, &lower);
        integer(&mut map, offset, &e.upper, &upper);
        integer(&mut map, offset, &e.work, &d);
        integer(&mut map, offset, &e.work_minus_one, &(&d - BigUint::from(1u8)));
        for (exp, wire) in e.exponent.iter().enumerate() {
            assign(&mut map, offset + *wire, Fr::from((exp == 6) as u64));
        }
    }
    // Work padding uses tree.leaves, NOT the count of physical HEADER owners.
    for owner in p.descriptor().genuine..p.descriptor().leaves {
        for wires in [&e.lower, &e.upper, &e.work, &e.work_minus_one, &e.exponent] {
            for wire in wires { assign(&mut map, owner * WIDTH + *wire, Fr::zero()); }
        }
    }
    let destination = e.header_aliases();
    for header_owner in 1..headers {
        let mut envelope = vec![Fr::zero(); 514 * 8];
        for (width, number) in [(10, 514u64), (32, 0x0601_1765u64), (32, (header_owner + 1) as u64)] {
            envelope.extend((0..width).map(|bit| Fr::from((number >> bit) & 1)));
        }
        assert_eq!(envelope.len(), 4186);
        for ((source, dest), value) in base.header_alias_wires.iter().zip(&destination).zip(envelope) {
            assign(&mut map, header_owner * WIDTH + *source, value);
            assign(&mut map, (header_owner - 1) * WIDTH + *dest, value);
        }
    }
    let mut input = Vec::new(); input.try_reserve_exact(WORK_PRODUCER_INPUT).unwrap();
    input.resize(WORK_PRODUCER_INPUT, Fr::zero());
    for (wire, value) in map { input[wire] = value; } input
}
fn eq(point: &[Fr], mut index: usize) -> Fr {
    let mut out = Fr::one();
    for z in point { out *= if index & 1 == 0 { Fr::one() - z } else { *z }; index >>= 1; }
    assert_eq!(index, 0); out
}
fn direct(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for t in terms {
        let weight = eq(r, t.row) * eq(u, t.gate.left) * eq(v, t.gate.right);
        for (a, b) in out.iter_mut().zip([t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3]) { *a += weight * b; }
    } out
}
fn output_path(leaf: &str) -> PathBuf {
    let dir = PathBuf::from(std::env::var_os("C569_OUTPUT_DIR")
        .expect("controller supplies C569_OUTPUT_DIR"));
    assert!(dir.is_absolute() && dir.is_dir());
    let dir = dir.canonicalize().unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).canonicalize().unwrap();
    assert!(!dir.starts_with(&source), "controller outputs must stay outside source");
    assert!(!dir.ancestors().any(|ancestor| ancestor.join("Cargo.toml").is_file()),
        "controller output directory must not be inside any Cargo source tree");
    let path = dir.join(leaf); assert!(!path.exists(), "create-only output"); path
}
fn write_bits(path: &Path, input: &[Fr]) {
    assert_eq!(input.len(), WORK_PRODUCER_INPUT);
    let mut writer = crate::packed::PackedFileWriter::create_new(path, 22).unwrap();
    let mut bytes = vec![0u8; WORK_PRODUCER_INPUT / 8];
    for (index, value) in input.iter().enumerate() {
        assert!(value.is_zero() || value.is_one());
        if value.is_one() { bytes[index / 8] |= 1 << (index % 8); }
    }
    writer.write_bytes(&bytes).unwrap(); drop(writer.finish().unwrap());
}

#[test]
fn c569_geometry_and_foreign_key_fail_before_source_or_relation() {
    let poison = Path::new("Z:/c569-poison-must-never-open.bits");
    for p in [parent(5), WorkTreeHistoryPlan::compile(1_827_840, 21, [7; 32], [9; 28]).unwrap()] {
        let mut audit = WorkPreparationAudit::default();
        let error = match prepare_work_source(&p, poison, key22(), Some(&mut audit)) {
            Err(e) => e, Ok(_) => panic!("unsupported geometry admitted"),
        };
        assert_eq!(error, "C569 cheap geometry/key dimension"); assert_eq!(audit, WorkPreparationAudit::default());
    }
    let p = parent(3); let mut audit = WorkPreparationAudit::default();
    let key18 = verifier_key::admit(18, include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert!(prepare_work_source(&p, poison, key18, Some(&mut audit)).is_err());
    assert_eq!(audit, WorkPreparationAudit::default());
    let key = key22(); let mut foreign = key.verifier().clone(); foreign.chi.swap(0, 1);
    let bytes = pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(foreign)).unwrap();
    assert_ne!(bytes.as_slice(), include_bytes!("../fixtures/verifier-keys-v1/log22.vk"));
    let foreign = verifier_key::admit_generated_test_key(22, &bytes, *key.id()).unwrap();
    let error = match prepare_work_source(&p, poison, foreign, Some(&mut audit)) {
        Err(e) => e, Ok(_) => panic!("foreign same-ID key admitted"),
    };
    assert_eq!(error, "C569 pinned key22 identity/bytes"); assert_eq!(audit, WorkPreparationAudit::default());
}

#[test]
fn c569_exact_geometry_census_and_collection_cap() {
    for n in [3usize, 4] {
        let p = parent(n); assert_eq!(work_geometry(&p, &key22()).unwrap(), WORK_PRODUCER_COUNTS[n - 3]);
        let c = circuit(&p); let mut counts = [0; 6];
        for t in &c.terms { counts[t.row >> 15] += 1; }
        assert_eq!(counts, WORK_PRODUCER_COUNTS[n - 3]);
        assert_eq!(c.terms.len(), if n == 3 { 16247 } else { 25522 });
    }
    let c = circuit(&parent(3)); let term = c.terms[0].clone();
    let mut terms = Vec::new(); terms.try_reserve_exact(WORK_PRODUCER_TERM_CAP).unwrap();
    let mut counts = [0; 6];
    for _ in 0..WORK_PRODUCER_TERM_CAP { push_work_term(&mut terms, &mut counts, term.clone()).unwrap(); }
    assert_eq!(push_work_term(&mut terms, &mut counts, term.clone()).unwrap_err(), "C569 term cap before push");
    assert_eq!(terms.len(), WORK_PRODUCER_TERM_CAP);
    for fault in 0..3 {
        let mut bad = term.clone();
        match fault { 0 => bad.row = 6 << 15, 1 => bad.gate.left = WORK_PRODUCER_INPUT, _ => bad.gate.right = WORK_PRODUCER_INPUT }
        let mut out = Vec::new(); let mut count = [0; 6];
        assert_eq!(push_work_term(&mut out, &mut count, bad).unwrap_err(), "C569 term domain");
        assert!(out.is_empty()); assert_eq!(count, [0; 6]);
    }
}

#[test]
fn c569_six_family_faults_and_inactive_work_scope() {
    for n in [3usize, 4] {
        let p = parent(n); let c = circuit(&p); let mut input = fixture_input(n);
        check_work_rows(&c, &input).unwrap();
        for tag in 0..6 {
            let selected: Vec<_> = c.terms.iter().filter(|t| t.row >> 15 == tag).cloned().collect();
            let subset = Circuit { input_len: c.input_len, row_count: c.row_count, terms: selected };
            check_work_rows(&subset, &input).unwrap();
            let first = &subset.terms[0]; let wire = first.gate.left;
            let old = input[wire]; input[wire] += Fr::from(2u64);
            let error = check_work_rows(&subset, &input).unwrap_err();
            assert!(error.starts_with(&format!("C569 residual family{tag} ")), "{error}");
            // Isolated whole-family omission witness, not a global-history attack.
            let omitted = Circuit { input_len: c.input_len, row_count: c.row_count, terms: vec![] };
            check_work_rows(&omitted, &input).unwrap(); input[wire] = old;
        }
        input[7] = Fr::from(2u64); assert!(!c.terms.iter().any(|t| t.gate.left == 7 || t.gate.right == 7));
        check_work_rows(&c, &input).unwrap(); input[7] = Fr::zero();
        let e = Endpoints::new();
        if n == 3 {
            for owner in [2, 3] {
                let wire = owner * WIDTH + e.lower[0];
                assert!(!c.terms.iter().any(|t| t.gate.left == wire || t.gate.right == wire));
                input[wire] = Fr::from(2u64); check_work_rows(&c, &input).unwrap(); input[wire] = Fr::zero();
            }
            // Tree's inactive writer and B1 inactive_tree_endpoints, not Work,
            // own the separate zero predicate at these physical owners.
        } else {
            input[3 * WIDTH + e.lower[0]] = Fr::from(2u64);
            assert!(check_work_rows(&c, &input).unwrap_err().starts_with("C569 residual family1 "));
        }
    }
}

#[test]
fn c569_header_alias_four_field_single_faults() {
    let p = parent(3); let c = circuit(&p); let mut input = fixture_input(3);
    let base = work_tree_layout::shared_baseline().unwrap();
    for index in [0, 4112, 4122, 4154] {
        let wire = WIDTH + base.header_alias_wires[index]; let old = input[wire];
        input[wire] += Fr::from(2u64);
        let error = check_work_rows(&c, &input).unwrap_err();
        assert!(error.starts_with("C569 residual family5 "), "{error}");
        let matches: Vec<_> = c.terms.iter().enumerate().filter(|(_, t)| t.row >> 15 == 5
            && (t.gate.left == wire || t.gate.right == wire)).collect();
        assert_eq!(matches.len(), 1);
        let mut omitted = c.clone(); omitted.terms.remove(matches[0].0);
        check_work_rows(&omitted, &input).unwrap(); input[wire] = old;
    }
}

#[test]
fn c569_arbitrary_field_coefficient_identity_preserves_operands() {
    for n in [3usize, 4] {
        let p = parent(n); let r = NativeWorkRelation::new(&p).unwrap(); let c = circuit(&p);
        let point = |len, seed| (0..len).map(|i| Fr::from(seed + 17 * i as u64)).collect::<Vec<_>>();
        let (a, u, v) = (point(18, 2u64), point(22, 43u64), point(22, 97u64));
        let expected = r.coefficients(&a, &u, &v).unwrap();
        assert_eq!(direct(&c.terms, &a, &u, &v), expected);
        for tag in 0..6 {
            let index = c.terms.iter().position(|t| t.row >> 15 == tag).unwrap();
            let mut changed = c.terms.clone(); changed[index].gate.c0 += Fr::one();
            assert_ne!(direct(&changed, &a, &u, &v), expected);
            let mut changed = c.terms.clone(); changed[index].gate.left ^= 1;
            assert_ne!(direct(&changed, &a, &u, &v), expected);
            let mut changed = c.terms.clone(); changed[index].gate.right ^= 1;
            assert_ne!(direct(&changed, &a, &u, &v), expected);
            let mut changed = c.terms.clone();
            assert!(!changed[index].gate.c1.is_zero(), "nonvacuous sign mutant");
            changed[index].gate.c1 = -changed[index].gate.c1;
            assert_ne!(direct(&changed, &a, &u, &v), expected);
        }
    }
}

#[test]
fn c569_public_decoders_fail_without_proof_or_setup() {
    let p = parent(3); let key = key22();
    let commitment = pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(
        ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap();
    let verifier = NativeWorkVerifier::new(&p, &key, &commitment).unwrap();
    assert!(verifier.verify(&[], &[]).unwrap_err().contains("extent"));
    assert!(verifier.verify(&vec![0; (7 * 22 + 3) * 32], &[]).unwrap_err().contains("PCS encoding"));
    assert!(NativeWorkVerifier::new(&p, &key, &[0]).is_err());
}

#[test]
#[ignore = "first C569 retained real-source residual gate; controller pins C569_RETAINED_SOURCE; no setup/commit"]
fn c569_retained_source_residual_before_crypto() {
    let path = PathBuf::from(std::env::var_os("C569_RETAINED_SOURCE").expect("controller supplies retained source"));
    assert!(path.is_absolute()); let meta = std::fs::metadata(&path).unwrap();
    assert_eq!(meta.len(), 524288); assert!(meta.permissions().readonly());
    let headers = crate::historical_prefix_witness::retained_headers().unwrap();
    let native = crate::packed_owner_assembly::NativePrefix::from_raw_iter(3,
        headers.iter().map(|h| Ok(h.encode().unwrap()))).unwrap();
    let p = WorkTreeHistoryPlan::compile(3, 2, native.root(), native.total_be28()).unwrap();
    let mut audit = WorkPreparationAudit::default();
    let prepared = prepare_work_source(&p, &path, key22(), Some(&mut audit)).unwrap();
    assert_eq!(prepared.circuit.terms.len(), 16247);
    assert_eq!(audit, WorkPreparationAudit { relations: 1, opens: 1, chunks: 64, residuals: 1, setups: 0, commits: 0 });
    println!("C569_RETAINED_RESIDUAL_PASS terms=16247 chunks=64 setups=0 commits=0");
}

#[test]
#[ignore = "C569 synthetic N4 packed preparation; controller-owned C569_OUTPUT_DIR; no setup/commit"]
fn c569_n4_packed_preparation_without_crypto() {
    let path = output_path("n4-source.bits"); let input = fixture_input(4); write_bits(&path, &input);
    drop(input); let p = parent(4); let mut audit = WorkPreparationAudit::default();
    let prepared = prepare_work_source(&p, &path, key22(), Some(&mut audit)).unwrap();
    assert_eq!(prepared.circuit.terms.len(), 25522);
    assert_eq!(audit, WorkPreparationAudit { relations: 1, opens: 1, chunks: 64, residuals: 1, setups: 0, commits: 0 });
    drop(prepared);
    let mut bad_input = fixture_input(4);
    let base = work_tree_layout::shared_baseline().unwrap();
    bad_input[WIDTH + base.header_alias_wires[0]] = Fr::one();
    let expected = check_work_rows(&circuit(&p), &bad_input).unwrap_err();
    assert!(expected.starts_with("C569 residual family5 "));
    let bad_path = output_path("n4-invalid-source.bits"); write_bits(&bad_path, &bad_input); drop(bad_input);
    let mut bad_audit = WorkPreparationAudit::default();
    let error = match NativeWorkProducer::create(&p, &bad_path, key22(), Some(&mut bad_audit)) {
        Err(e) => e, Ok(_) => panic!("invalid source reached setup/commit"),
    };
    assert_eq!(error, expected);
    assert_eq!(bad_audit, WorkPreparationAudit { relations: 1, opens: 1, chunks: 64, residuals: 1, setups: 0, commits: 0 });
}

#[test]
#[ignore = "C569 genuine retained-key22 Work+POINT+HEADER; separate controller and fresh C569_OUTPUT_DIR required"]
fn c569_real_retained_key22_work_point_header_same_x() {
    use crate::packed_owner_assembly::{NativePrefix, NativeOwnerProducer, NativePcsSource};
    use crate::point_role::{PointProducer, PointPublicStatement, PointPublicVerifier};
    use crate::global_producer_endpoint_plan::{GlobalProducerEndpointPlan, NativeReleasedHeaderAdmission,
        NativeHeaderPublicStatement, NativeHeaderPublicVerifier};
    let path = output_path("real-source.bits");
    let headers = crate::historical_prefix_witness::retained_headers().unwrap();
    let native = NativePrefix::from_raw_iter(3, headers.iter().map(|h| Ok(h.encode().unwrap()))).unwrap();
    let p = WorkTreeHistoryPlan::compile(3, 2, native.root(), native.total_be28()).unwrap();
    let native_producer = NativeOwnerProducer::new_for_history(&p, &native).unwrap();
    let source = NativePcsSource::new(&native_producer).unwrap();
    let mut writer = crate::packed::PackedFileWriter::create_new(&path, 22).unwrap();
    for owner in 0..4 { writer.write_bytes(source.read_owner(owner).unwrap().packed_bytes()).unwrap(); }
    drop(writer.finish().unwrap());
    println!("C569_REAL_STAGE|real_source_ready");
    println!("C569_REAL_STAGE|work_prepare_begin");
    let work = NativeWorkProducer::new(&p, &path, key22()).unwrap();
    println!("C569_REAL_STAGE|work_ready");
    println!("C569_REAL_STAGE|work_proof_begin");
    let proof = work.prove().unwrap();
    let verifier = NativeWorkVerifier::new(&p, &work.prepared.key, work.commitment_bytes()).unwrap();
    verifier.verify(proof.gkr_bytes(), proof.pcs_bytes()).unwrap();
    println!("C569_REAL_STAGE|work_verified");
    println!("C569_REAL_STAGE|point_begin");
    let point = PointProducer::new(&p, &path).unwrap();
    let statement = PointPublicStatement::new(&p, &work.prepared.key, work.commitment_bytes()).unwrap();
    let public_point = PointPublicVerifier::new(statement, &work.prepared.key).unwrap();
    let mut pt = Transcript::new(b"c569-POINT-semantic"); let pp = point.prove_on(&mut pt).unwrap();
    let mut pv = Transcript::new(b"c569-POINT-semantic"); public_point.verify_on(&pp.gkr, &pp.opening, &mut pv).unwrap();
    assert_eq!(pt.clone().try_challenge_scalar(b"continuation").unwrap(), pv.try_challenge_scalar(b"continuation").unwrap());
    println!("C569_REAL_STAGE|point_verified");
    println!("C569_REAL_STAGE|header_begin");
    let plan = GlobalProducerEndpointPlan::new(&p).unwrap();
    let header = NativeReleasedHeaderAdmission::new(&plan, &source).unwrap();
    let context = header.prepare_context(&work.setup, &work.prepared.key).unwrap();
    assert_eq!(context.commitment_bytes(), work.commitment_bytes());
    let mut ht = Transcript::new(b"c569-HEADER-semantic");
    let (hp, claim, _, _) = header.prove_on(&context, &mut ht).unwrap();
    let opening = crate::packed::open_native(&source, context.committed(), &work.setup, &claim.point, &mut ht).unwrap();
    let statement = NativeHeaderPublicStatement::new(native.root(), native.total_be28(),
        &work.prepared.key, work.commitment_bytes()).unwrap();
    let public_header = NativeHeaderPublicVerifier::new(&p, statement, &work.prepared.key).unwrap();
    let mut hv = Transcript::new(b"c569-HEADER-semantic");
    assert_eq!(public_header.verify_on(&hp, &opening, &mut hv).unwrap(), claim);
    assert_eq!(ht.try_challenge_scalar(b"continuation").unwrap(), hv.try_challenge_scalar(b"continuation").unwrap());
    println!("C569_REAL_STAGE|header_verified");
    let mut bad = gkr::decode_dimensions(&[22], proof.gkr_bytes()).unwrap();
    bad.layers[0].rounds[0][0] += Fr::one();
    assert!(verifier.verify(&gkr::encode_proof(&bad).unwrap(), proof.pcs_bytes()).is_err());
    let mut bad = gkr::decode_dimensions(&[22], proof.gkr_bytes()).unwrap();
    bad.layers[0].line_coefficients[1] += Fr::one();
    assert!(verifier.verify(&gkr::encode_proof(&bad).unwrap(), proof.pcs_bytes()).is_err());
    for gkr_side in [true, false] {
        let mut g = proof.gkr_bytes().to_vec(); let mut opening = proof.pcs_bytes().to_vec();
        if gkr_side { g.push(0); } else { opening.push(0); }
        assert!(verifier.verify(&g, &opening).is_err());
    }
    assert!(verifier.verify(&proof.gkr_bytes()[..proof.gkr_bytes().len() - 1], proof.pcs_bytes()).is_err());
    assert!(verifier.verify(proof.gkr_bytes(), &proof.pcs_bytes()[..proof.pcs_bytes().len() - 1]).is_err());
    let identity = pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(
        ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap();
    assert_ne!(identity.as_slice(), work.commitment_bytes());
    assert!(NativeWorkVerifier::new(&p, &work.prepared.key, &identity).unwrap()
        .verify(proof.gkr_bytes(), proof.pcs_bytes()).is_err());
    for field in 0..3 {
        let (mut root, mut total, mut n) = (native.root(), native.total_be28(), 3);
        match field { 0 => root[0] ^= 1, 1 => total[0] ^= 1, _ => n = 4 }
        let alternative = WorkTreeHistoryPlan::compile(n, 2, root, total).unwrap();
        assert!(NativeWorkVerifier::new(&alternative, &work.prepared.key, work.commitment_bytes()).unwrap()
            .verify(proof.gkr_bytes(), proof.pcs_bytes()).is_err());
    }
    let (claim, mut continuation) = verifier.replay_gkr(proof.gkr_bytes()).unwrap();
    native_work_pcs_separator(&mut continuation);
    let opened = pcs::decode_proof(proof.pcs_bytes(), 22).unwrap();
    for field in 0..2 {
        let mut q = claim.point.clone(); let mut value = claim.value;
        if field == 0 { q[0] += Fr::one(); } else { value += Fr::one(); }
        assert!(pcs::verify_admitted(work.committed.commitment.clone(), value, &q, &opened,
            &work.prepared.key, &mut continuation.clone()).is_err());
    }
    assert!(verifier.verify(proof.gkr_bytes(), &pcs::encode_proof(&pp.opening).unwrap()).is_err());
    println!("C569_REAL_STAGE|controls_done");
}


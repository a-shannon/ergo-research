use crate::{
    gkr,
    packed::{self, PackedFile, PackedFileWriter},
    pcs,
    short_common_owner::{
        self as common, Plan, BASE_ROWS, COPY_BITS, DOMAIN, FAMILY_BITS, INPUT_BITS, LOCAL_BITS,
        MEMBER_ROWS, ROW_BITS, TOTAL_TERMS,
    },
    short_common_owner_fixture_tests::materialize,
    sparse_stream_roster::{self, EdgeTerm},
    transcript::Transcript,
    verifier_key,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use std::{path::PathBuf, time::Instant};

fn row(edge: &EdgeTerm) -> usize {
    sparse_stream_roster::global_edge_row(
        edge.source_slot,
        edge.family_row,
        COPY_BITS,
        BASE_ROWS,
        FAMILY_BITS,
        &MEMBER_ROWS,
    )
    .unwrap()
}
fn finite(plan: &Plan, left: bool, r: &[Fr], u: &[Fr], v: &[Fr]) -> ([Fr; 4], usize) {
    let rw = gkr::eq_weights(r);
    let uw = gkr::eq_weights(u);
    let vw = gkr::eq_weights(v);
    let mut out = [Fr::zero(); 4];
    let mut count = 0;
    for copy in 0..4 {
        plan.visit_endpoint(left, copy, |edge| {
            let weight = rw[row(&edge)] * uw[edge.term.gate.left] * vw[edge.term.gate.right];
            for (out, c) in out.iter_mut().zip([
                edge.term.gate.c0,
                edge.term.gate.c1,
                edge.term.gate.c2,
                edge.term.gate.c3,
            ]) {
                if !c.is_zero() {
                    *out += weight * c;
                }
            }
            count += 1;
            Ok(())
        })
        .unwrap();
    }
    (out, count)
}
fn mixed(bits: usize, seed: usize) -> Vec<Fr> {
    (0..bits)
        .map(|i| Fr::from((seed + 11 * i) as u64))
        .collect()
}

#[test]
fn mixed_coefficients_match_both_endpoint_streams_and_family_omissions() {
    let plan = Plan::new().unwrap();
    let r = mixed(ROW_BITS, 7);
    let u = mixed(INPUT_BITS, 13);
    let v = mixed(INPUT_BITS, 19);
    let (expected, count) = finite(&plan, true, &r, &u, &v);
    let (right, right_count) = finite(&plan, false, &r, &u, &v);
    assert_eq!(count, TOTAL_TERMS);
    assert_eq!(right_count, TOTAL_TERMS);
    assert_eq!(expected, right);
    assert_eq!(plan.coefficients(&r, &u, &v).unwrap(), expected);
    let parts = plan.parts(&r, &u, &v).unwrap();
    for family in 0..3 {
        assert_ne!(parts[family], [Fr::zero(); 4]);
        let omitted: [Fr; 4] = std::array::from_fn(|i| expected[i] - parts[family][i]);
        assert_ne!(omitted, expected, "omitted family{family}");
    }
    let mut wrong = r.clone();
    wrong[10] = Fr::one() - wrong[10];
    let alias_wrong_owner = plan.parts(&wrong, &u, &v).unwrap()[2];
    assert_ne!(alias_wrong_owner, parts[2]);
    let mut single_edge_delta = [Fr::zero(); 4];
    plan.visit_endpoint(true, 0, |edge| {
        if edge.family_row == 2 << BASE_ROWS {
            let weight = common::eq(&r, row(&edge))
                * common::eq(&u, edge.term.gate.left)
                * common::eq(&v, edge.term.gate.right);
            single_edge_delta[1] += weight;
            single_edge_delta[2] -= weight;
        }
        Ok(())
    })
    .unwrap();
    assert_ne!(single_edge_delta, [Fr::zero(); 4]);
    println!(
        "mixed physical input22/row23: left={count} right={right_count}, three families distinct"
    );
}

#[test]
fn selected_family_copy_padding_endpoint_and_dimension_gates() {
    let plan = Plan::new().unwrap();
    for (family, owner, source_copy) in [(0, 3, 3), (1, 3, 3), (2, 3, 0), (2, 3, 3)] {
        let low = MEMBER_ROWS[family];
        let mut r = vec![Fr::zero(); ROW_BITS];
        r[..low].copy_from_slice(&mixed(low, 7));
        r[low..low + COPY_BITS].copy_from_slice(&common::boolean(owner, COPY_BITS));
        r[21..].copy_from_slice(&common::boolean(family, FAMILY_BITS));
        let mut u = mixed(INPUT_BITS, 13);
        let mut v = mixed(INPUT_BITS, 19);
        u[20..].copy_from_slice(&common::boolean(source_copy, COPY_BITS));
        v[20..].copy_from_slice(&common::boolean(owner, COPY_BITS));
        let (expected, count) = finite(&plan, true, &r, &u, &v);
        assert_eq!(count, TOTAL_TERMS);
        assert_ne!(expected, [Fr::zero(); 4]);
        assert_eq!(plan.coefficients(&r, &u, &v).unwrap(), expected);
        for bit in low..low + COPY_BITS {
            let mut bad = r.clone();
            bad[bit] = Fr::one() - bad[bit];
            assert_eq!(
                plan.coefficients(&bad, &u, &v).unwrap(),
                [Fr::zero(); 4],
                "row owner bit{bit}"
            );
        }
        for bit in low + COPY_BITS..21 {
            let mut bad = r.clone();
            bad[bit] = Fr::one();
            assert_eq!(
                plan.coefficients(&bad, &u, &v).unwrap(),
                [Fr::zero(); 4],
                "row padding bit{bit}"
            );
        }
        let mut unused = r.clone();
        unused[21] = Fr::one();
        unused[22] = Fr::one();
        assert_eq!(plan.coefficients(&unused, &u, &v).unwrap(), [Fr::zero(); 4]);
        for bit in 21..ROW_BITS {
            let mut bad = r.clone();
            bad[bit] = Fr::one() - bad[bit];
            assert_eq!(
                plan.coefficients(&bad, &u, &v).unwrap(),
                [Fr::zero(); 4],
                "family tag bit{bit}"
            );
        }
        // Header and arithmetic both require the same owner at both endpoints.
        // For aliases all four sources are legitimate; use a noncanonical right owner.
        for bit in 20..INPUT_BITS {
            let mut bad = v.clone();
            bad[bit] = Fr::one() - bad[bit];
            assert_eq!(
                plan.coefficients(&r, &u, &bad).unwrap(),
                [Fr::zero(); 4],
                "right copy bit{bit}"
            );
            if family < 2 {
                let mut bad = u.clone();
                bad[bit] = Fr::one() - bad[bit];
                assert_eq!(
                    plan.coefficients(&r, &bad, &v).unwrap(),
                    [Fr::zero(); 4],
                    "left copy bit{bit}"
                );
            }
        }
        for (br, bu, bv) in [
            (&r[..ROW_BITS - 1], u.as_slice(), v.as_slice()),
            (r.as_slice(), &u[..INPUT_BITS - 1], v.as_slice()),
            (r.as_slice(), u.as_slice(), &v[..INPUT_BITS - 1]),
        ] {
            assert!(plan.coefficients(br, bu, bv).is_err());
        }
    }
    let mut calls = 0;
    assert!(plan
        .visit_endpoint(true, 4, |_| {
            calls += 1;
            Ok(())
        })
        .is_err());
    assert_eq!(calls, 0);
    assert_eq!(
        plan.visit_endpoint(false, 0, |_| Err("sink sentinel".into()))
            .err()
            .as_deref(),
        Some("sink sentinel")
    );
}

fn artifact(kind: &str) -> PathBuf {
    let root = PathBuf::from(
        std::env::var_os("NIPOPOW_SHORT_COMMON_DIR")
            .expect("explicit machine-local artifact directory"),
    );
    assert!(root.is_dir());
    root.join(format!(
        "selected-m2-{kind}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}
fn pack(plan: &Plan) -> PackedFile {
    let copies = materialize(plan, false);
    let mut writer = PackedFileWriter::create_new(artifact("packed.bin"), INPUT_BITS).unwrap();
    for copy in copies {
        let mut bytes = vec![0u8; copy.len() / 8];
        for (wire, value) in copy.iter().enumerate() {
            assert!(value.is_zero() || value.is_one());
            if value.is_one() {
                bytes[wire / 8] |= 1 << (wire % 8);
            }
        }
        writer.write_bytes(&bytes).unwrap();
    }
    writer.finish().unwrap()
}
fn load(source: &PackedFile, copy: usize) -> Result<Vec<Fr>, String> {
    let mut values = Vec::with_capacity(1 << LOCAL_BITS);
    for chunk in 0..16 {
        values.extend(source.read_copy(1 << 16, copy * 16 + chunk)?);
    }
    Ok(values)
}

#[test]
fn actual_selected_m2_proof_and_one_pcs22_reject_consumer_substitutions() {
    let whole = Instant::now();
    let plan = Plan::new().unwrap();
    let source = pack(&plan);
    let setup = pcs::generate_setup(INPUT_BITS).unwrap();
    let key = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let admitted = verifier_key::admit_generated_test_key(INPUT_BITS, &key, setup.id).unwrap();
    let committed = packed::commit(&source, &setup).unwrap();
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    println!(
        "prepared selected M2 at {:.3}s",
        whole.elapsed().as_secs_f64()
    );
    let mut t = Transcript::new(DOMAIN);
    let mark = Instant::now();
    let (proof, claim, incremental_u, incremental_v) = sparse_stream_roster::prove_edge_terms(
        LOCAL_BITS,
        COPY_BITS,
        BASE_ROWS,
        FAMILY_BITS,
        &MEMBER_ROWS,
        |left, copy, sink| plan.visit_endpoint(left, copy, sink),
        |copy| load(&source, copy),
        &mut t,
        |t| plan.bind(t, &setup.id, &commitment),
        |r, u, v| plan.coefficients(r, u, v),
    )
    .unwrap();
    let prover_seconds = mark.elapsed().as_secs_f64();
    let gkr_bytes = gkr::encode_proof(&proof).unwrap();
    let decoded = gkr::decode_dimensions(&[INPUT_BITS], &gkr_bytes).unwrap();
    assert_eq!(decoded, proof);
    assert_eq!(decoded.layers[0].rounds.len(), 2 * INPUT_BITS);
    assert_eq!(decoded.layers[0].line_coefficients.len(), INPUT_BITS + 1);
    let mut crossed_dimensions = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[ROW_BITS],
            1 << INPUT_BITS,
            &decoded,
            &mut crossed_dimensions,
            |t| plan.bind(t, &setup.id, &commitment),
            |_layer, r, u, v| plan
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::SumcheckRoundCount
    );
    drop(plan);
    let expected = Plan::new().unwrap();
    let mark = Instant::now();
    let (verified, mut consumer) = expected
        .verify_gkr(&decoded, &setup.id, &commitment)
        .unwrap();
    let relation_verify_seconds = mark.elapsed().as_secs_f64();
    assert_eq!(verified, claim);
    assert_eq!(source.evaluate(&claim.point).unwrap(), claim.value);
    assert_eq!(
        t.clone().challenge_scalar(b"post-gkr"),
        consumer.clone().challenge_scalar(b"post-gkr")
    );
    let pre_pcs = consumer.clone();
    let mark = Instant::now();
    let opening = packed::open(&committed, &source, &claim.point, &setup, &mut t).unwrap();
    let opening_seconds = mark.elapsed().as_secs_f64();
    let opening_bytes = pcs::encode_proof(&opening).unwrap();
    let opening = pcs::decode_proof(&opening_bytes, INPUT_BITS).unwrap();
    let mark = Instant::now();
    pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value,
        &claim.point,
        &opening,
        &admitted,
        &mut consumer,
    )
    .unwrap();
    let pcs_verify_seconds = mark.elapsed().as_secs_f64();
    assert_eq!(
        t.challenge_scalar(b"post-pcs"),
        consumer.challenge_scalar(b"post-pcs")
    );
    assert!(pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value + Fr::one(),
        &claim.point,
        &opening,
        &admitted,
        &mut pre_pcs.clone()
    )
    .is_err());
    for fault in 0..2 {
        let mut rejected = Transcript::new(DOMAIN);
        let outcome = gkr::verify_with_wiring(
            &[INPUT_BITS],
            1 << ROW_BITS,
            &decoded,
            &mut rejected,
            |t| expected.bind(t, &setup.id, &commitment),
            |_layer, r, u, v| {
                let parts = expected
                    .parts(r, u, v)
                    .map_err(|_| gkr::GkrError::PointDimension)?;
                let alias = if fault == 0 {
                    [Fr::zero(); 4]
                } else {
                    let mut wrong = r.to_vec();
                    wrong[10] = Fr::one() - wrong[10];
                    expected
                        .parts(&wrong, u, v)
                        .map_err(|_| gkr::GkrError::PointDimension)?[2]
                };
                Ok(std::array::from_fn(|i| {
                    parts[0][i] + parts[1][i] + alias[i]
                }))
            },
        );
        assert_eq!(outcome.unwrap_err(), gkr::GkrError::TerminalExpression);
    }
    let mut wrong_setup = setup.id;
    wrong_setup[0] ^= 1;
    assert!(expected
        .verify_gkr(&decoded, &wrong_setup, &commitment)
        .is_err());
    let mut wrong_commitment = commitment.clone();
    wrong_commitment[0] ^= 1;
    assert!(expected
        .verify_gkr(&decoded, &setup.id, &wrong_commitment)
        .is_err());
    std::fs::write(artifact("gkr.bin"), &gkr_bytes).unwrap();
    std::fs::write(artifact("pcs.bin"), &opening_bytes).unwrap();
    println!(
        "{}",
        serde_json::json!({"kind":"selected-m2-common-proof", "physicalInputBits":INPUT_BITS,
        "rowBits":ROW_BITS,"logicalSlots":common::LOGICAL_SLOTS,"terms":TOTAL_TERMS,
        "gkrBytes":gkr_bytes.len(),"pcsBytes":opening_bytes.len(),"proverSeconds":prover_seconds,
        "relationVerifySeconds":relation_verify_seconds,"openingSeconds":opening_seconds,
        "pcsVerifySeconds":pcs_verify_seconds,"incrementalU":incremental_u,"incrementalV":incremental_v,
        "wholeSeconds":whole.elapsed().as_secs_f64(),"scope":"selected relations only; no ancestry/core/points/PoW qualification"})
    );
}

#[test]
fn rebuilt_timestamp_corpus_is_rejected_at_the_common_zero_claim() {
    let plan = Plan::new().unwrap();
    let copies = materialize(&plan, true);
    let mut t = Transcript::new(DOMAIN);
    let outcome = sparse_stream_roster::prove_edge_terms(
        LOCAL_BITS,
        COPY_BITS,
        BASE_ROWS,
        FAMILY_BITS,
        &MEMBER_ROWS,
        |left, copy, sink| plan.visit_endpoint(left, copy, sink),
        |copy| Ok(copies[copy].clone()),
        &mut t,
        |t| plan.bind(t, &[0; 32], b"diagnostic-invalid-corpus"),
        |r, u, v| plan.coefficients(r, u, v),
    );
    assert_eq!(
        outcome.err().as_deref(),
        Some(gkr::GkrError::SumcheckIdentity.to_string().as_str())
    );
}

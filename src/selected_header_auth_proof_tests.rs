use crate::{
    core_pool_boolean,
    gkr::{self, GkrProof, InputClaim},
    packed::{self, PackedFile, PackedFileWriter},
    pcs, segment_points,
    selected_header_auth::{Artifact, Plan, Reject, CORE_BANKS, INPUT_BITS},
    selected_header_auth_tests::expected_ids,
    short_common_owner::{BASE_ROWS, COPY_BITS, FAMILY_BITS, LOCAL_BITS, MEMBER_ROWS},
    short_common_owner_fixture_tests::materialize,
    sparse, sparse_stream_boolean, sparse_stream_roster,
    transcript::Transcript,
    verifier_key,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use std::{
    fs::OpenOptions,
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

fn path(name: &str) -> PathBuf {
    PathBuf::from(
        std::env::var_os("NIPOPOW_SELECTED_AUTH_DIR")
            .expect("fresh selected authentication artifact directory"),
    )
    .join(name)
}
fn write(name: &str, bytes: &[u8]) {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path(name))
        .unwrap();
    file.write_all(bytes).unwrap();
    file.sync_all().unwrap();
}
fn pack(plan: &Plan) -> PackedFile {
    let mut writer = PackedFileWriter::create_new(path("selected-m2.packed"), 22).unwrap();
    for copy in materialize(plan.common(), false) {
        let mut bytes = vec![0; copy.len() / 8];
        for (i, x) in copy.iter().enumerate() {
            assert!(x.is_zero() || x.is_one());
            if x.is_one() {
                bytes[i / 8] |= 1 << (i % 8);
            }
        }
        writer.write_bytes(&bytes).unwrap();
    }
    writer.finish().unwrap()
}
fn load(source: &PackedFile, copy: usize) -> Result<Vec<Fr>, String> {
    if copy >= 4 || source.input_len() != 1 << 22 {
        return Err("selected copy dimension".into());
    }
    let mut values = Vec::with_capacity(1 << 20);
    for bank in 0..16 {
        values.extend(source.read_copy(1 << 16, copy * 16 + bank)?);
    }
    Ok(values)
}
fn all(source: &PackedFile) -> Result<Vec<Fr>, String> {
    let mut values = Vec::with_capacity(1 << 22);
    for copy in 0..4 {
        values.extend(load(source, copy)?);
    }
    Ok(values)
}
fn produce(
    plan: &Plan,
    source: &PackedFile,
    role: usize,
    setup_id: &[u8; 32],
    commitment: &[u8],
) -> (GkrProof, InputClaim, Transcript) {
    let mut t = plan.transcript(role, setup_id, commitment).unwrap();
    let (proof, mut claim) = match role {
        0 => core_pool_boolean::prove_with_copy_bits_for_test(
            plan.core(),
            4,
            &CORE_BANKS,
            2,
            |copy| load(source, copy),
            &mut t,
            |t| plan.bind_role(0, t, setup_id, commitment),
            |r, u, v| plan.core_coefficients(r, u, v).map_err(|e| e.to_string()),
        )
        .unwrap(),
        1 => {
            let (proof, claim, _, _) = sparse_stream_roster::prove_edge_terms(
                LOCAL_BITS,
                COPY_BITS,
                BASE_ROWS,
                FAMILY_BITS,
                &MEMBER_ROWS,
                |left, copy, sink| plan.common().visit_endpoint(left, copy, sink),
                |copy| load(source, copy),
                &mut t,
                |t| plan.bind_role(1, t, setup_id, commitment),
                |r, u, v| plan.common().coefficients(r, u, v),
            )
            .unwrap();
            (proof, claim)
        }
        2 => sparse_stream_boolean::prove(
            &plan.points().circuit,
            2,
            |copy| {
                segment_points::load_copy(source, 3, 4, copy)
                    .map_err(|_| gkr::GkrError::InvalidInputWidth)
            },
            &mut t,
        )
        .unwrap(),
        3 => sparse::prove_with_binding(plan.ids(), &all(source).unwrap(), 0, &mut t, |t| {
            plan.bind_role(3, t, setup_id, commitment)
        })
        .unwrap(),
        _ => unreachable!(),
    };
    if role == 2 {
        claim.point = segment_points::embed(3, 2, &claim.point).unwrap();
    }
    (proof, claim, t)
}

#[test]
fn four_actual_selected_headers_authenticate_under_one_commitment_and_reject_substitutions() {
    let whole = Instant::now();
    let ids = expected_ids();
    let plan = Plan::new(ids).unwrap();
    let source = pack(&plan);
    let setup = pcs::generate_setup(22).unwrap();
    let key_bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let key = verifier_key::admit_generated_test_key(22, &key_bytes, setup.id).unwrap();
    let committed = packed::commit(&source, &setup).unwrap();
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    println!(
        "prepared selected authentication {:.3}s",
        whole.elapsed().as_secs_f64()
    );
    let mut artifact = Artifact {
        commitment: commitment.clone(),
        roles: std::array::from_fn(|_| Vec::new()),
        openings: std::array::from_fn(|_| Vec::new()),
    };
    let mut claims = Vec::new();
    let mut gkr_seconds = [0.0; 4];
    let mut opening_seconds = [0.0; 4];
    let mut gkr_verify_seconds = [0.0; 4];
    let mut pcs_verify_seconds = [0.0; 4];
    for role in 0..4 {
        let mark = Instant::now();
        let (proof, claim, mut t) = produce(&plan, &source, role, &setup.id, &commitment);
        gkr_seconds[role] = mark.elapsed().as_secs_f64();
        artifact.roles[role] = gkr::encode_proof(&proof).unwrap();
        let decoded = gkr::decode_dimensions(&[INPUT_BITS[role]], &artifact.roles[role]).unwrap();
        assert_eq!(decoded, proof);
        assert_eq!(decoded.layers[0].rounds.len(), 2 * INPUT_BITS[role]);
        assert_eq!(
            decoded.layers[0].line_coefficients.len(),
            INPUT_BITS[role] + 1
        );
        let mark = Instant::now();
        let (verified, mut consumer) = plan
            .verify_role(role, &decoded, &setup.id, &commitment)
            .unwrap();
        gkr_verify_seconds[role] = mark.elapsed().as_secs_f64();
        assert_eq!(verified, claim);
        assert_eq!(source.evaluate(&claim.point).unwrap(), claim.value);
        assert_eq!(
            t.clone().challenge_scalar(b"post-gkr"),
            consumer.clone().challenge_scalar(b"post-gkr")
        );
        let pre_pcs = consumer.clone();
        let mark = Instant::now();
        let opening = packed::open(&committed, &source, &claim.point, &setup, &mut t).unwrap();
        opening_seconds[role] = mark.elapsed().as_secs_f64();
        artifact.openings[role] = pcs::encode_proof(&opening).unwrap();
        let opening = pcs::decode_proof(&artifact.openings[role], 22).unwrap();
        let mark = Instant::now();
        pcs::verify_admitted(
            committed.commitment.clone(),
            claim.value,
            &claim.point,
            &opening,
            &key,
            &mut consumer,
        )
        .unwrap();
        pcs_verify_seconds[role] = mark.elapsed().as_secs_f64();
        assert_eq!(
            t.challenge_scalar(b"post-pcs"),
            consumer.challenge_scalar(b"post-pcs")
        );
        assert!(pcs::verify_admitted(
            committed.commitment.clone(),
            claim.value + Fr::one(),
            &claim.point,
            &opening,
            &key,
            &mut pre_pcs.clone()
        )
        .is_err());
        if role == 2 {
            for bit in [13, 20] {
                let mut wrong = claim.point.clone();
                wrong[bit] = Fr::one() - wrong[bit];
                assert_ne!(
                    source.evaluate(&wrong).unwrap(),
                    claim.value,
                    "point bank/owner bit{bit}"
                );
                assert!(pcs::verify_admitted(
                    committed.commitment.clone(),
                    claim.value,
                    &wrong,
                    &opening,
                    &key,
                    &mut pre_pcs.clone()
                )
                .is_err());
            }
        }
        if role == 3 {
            let mut crossed = plan.transcript(3, &setup.id, &commitment).unwrap();
            assert_eq!(
                gkr::verify_with_wiring(
                    &[11],
                    1 << 22,
                    &decoded,
                    &mut crossed,
                    |t| plan.bind_role(3, t, &setup.id, &commitment),
                    |_, _, _, _| Ok([Fr::zero(); 4])
                )
                .unwrap_err(),
                gkr::GkrError::SumcheckRoundCount
            );
        }
        claims.push(claim);
        write(&format!("role-{role}.gkr"), &artifact.roles[role]);
        write(&format!("role-{role}.pcs"), &artifact.openings[role]);
        println!(
            "role{role} GKR {:.3}s opening {:.3}s",
            gkr_seconds[role], opening_seconds[role]
        );
    }
    drop(plan);
    let expected = Plan::new(ids).unwrap();
    assert_eq!(expected.verify(&artifact, &key).unwrap().to_vec(), claims);
    for role in 0..4 {
        let mut changed = artifact.clone();
        changed.roles[role].clear();
        assert_eq!(expected.verify(&changed, &key).unwrap_err(), Reject::Shape);
        let mut changed = artifact.clone();
        changed.openings[role].clear();
        assert_eq!(
            expected.verify(&changed, &key).unwrap_err(),
            Reject::Opening(role)
        );
        let mut changed = artifact.clone();
        changed.openings[role][0] ^= 1;
        assert_eq!(
            expected.verify(&changed, &key).unwrap_err(),
            Reject::Opening(role)
        );
        let mut wrong_ids = ids;
        wrong_ids[role][0] ^= 1;
        // A reused proof under changed expected IDs must fail its new context.
        // Direct causal ID residual tests separately establish field ownership.
        assert_eq!(
            Plan::new(wrong_ids)
                .unwrap()
                .verify(&artifact, &key)
                .unwrap_err(),
            Reject::Role(0)
        );
    }
    let mut reordered = artifact.clone();
    reordered.roles.swap(0, 1);
    assert_eq!(
        expected.verify(&reordered, &key).unwrap_err(),
        Reject::Role(0)
    );
    let mut duplicated = artifact.clone();
    duplicated.roles[1] = artifact.roles[0].clone();
    assert_eq!(
        expected.verify(&duplicated, &key).unwrap_err(),
        Reject::Role(1)
    );
    let mut swapped_openings = artifact.clone();
    swapped_openings.openings.swap(0, 1);
    assert_eq!(
        expected.verify(&swapped_openings, &key).unwrap_err(),
        Reject::Opening(0)
    );
    let proof = gkr::decode_dimensions(&[22], &artifact.roles[0]).unwrap();
    let mut wrong_setup = setup.id;
    wrong_setup[0] ^= 1;
    assert_eq!(
        expected
            .verify_role(0, &proof, &wrong_setup, &commitment)
            .err(),
        Some(Reject::Role(0))
    );
    let mut malformed = artifact.clone();
    malformed.commitment.push(0);
    assert_eq!(
        expected.verify(&malformed, &key).unwrap_err(),
        Reject::Commitment
    );
    let mut alternate_bytes = std::fs::read(path("selected-m2.packed")).unwrap();
    alternate_bytes[0] ^= 1;
    let mut alternate = PackedFileWriter::create_new(path("alternate.packed"), 22).unwrap();
    alternate.write_bytes(&alternate_bytes).unwrap();
    let alternate = alternate.finish().unwrap();
    let alternate = packed::commit(&alternate, &setup).unwrap();
    let mut different_corpus = artifact.clone();
    different_corpus.commitment = pcs::encode_commitment(&alternate.commitment).unwrap();
    assert_ne!(different_corpus.commitment, commitment);
    assert_eq!(
        expected.verify(&different_corpus, &key).unwrap_err(),
        Reject::Role(0)
    );
    write("expected-statement.json", &serde_json::to_vec_pretty(&serde_json::json!({
        "profile":"selected-m2-four-header-authentication-v1", "expectedIds":ids,
        "logicalSlots":crate::short_common_owner::LOGICAL_SLOTS, "physicalCopies":[0,1,2,3],
        "inputBits":INPUT_BITS, "rowBits":crate::selected_header_auth::ROW_BITS,
        "setupId":setup.id, "scope":"selected header IDs and relations; no ancestry/PoW/full-history/backend qualification"
    })).unwrap());
    write("verifier-key.bin", &key_bytes);
    write("commitment.bin", &commitment);
    println!(
        "{}",
        serde_json::json!({"kind":"selected-m2-four-role-authentication",
        "gkrBytes":artifact.roles.iter().map(Vec::len).collect::<Vec<_>>(),
        "pcsBytes":artifact.openings.iter().map(Vec::len).collect::<Vec<_>>(),
        "gkrSeconds":gkr_seconds, "openingSeconds":opening_seconds,
        "gkrVerifySeconds":gkr_verify_seconds, "pcsVerifySeconds":pcs_verify_seconds,
        "wholeSeconds":whole.elapsed().as_secs_f64(),
        "fullHistory":false, "production":false,
        "artifactScope":"diagnostic files; no standalone replay claim"})
    );
    assert!(Path::new(&path("expected-statement.json")).is_file());
}

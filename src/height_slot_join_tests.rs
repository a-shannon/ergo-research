//! Height owners in the bounded common GKR/PCS24 witness.
//! Sample hashes and historical inclusion remain outside this join.
use super::{Context as Base, CHUNK, MEMBER_ROWS, N, SLOT_LOG, WIDTH};
use crate::{
    gkr::{self, GkrProof, InputClaim},
    header_height_layout::HeaderHeightLayout,
    header_history_boundary::HeaderHistoryBoundary,
    packed::{self, PackedFile},
    pcs,
    sparse::Term,
    sparse_stream_roster::{self, EdgeTerm},
    transcript::Transcript,
    verifier_key,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use std::time::Instant;
const HEIGHT_START: usize = (1 << 19) | (1 << 17) | 1024;
const TOTAL: usize = super::TOTAL_TERMS + 352;
const DOMAIN: &[u8] = b"native-common-header-daa-height-v1";
fn eq(point: &[Fr], index: usize) -> Fr {
    super::super::eq_at(point, index)
}
fn boolean(index: usize, bits: usize) -> Vec<Fr> {
    super::boolean(index, bits)
}
fn value(input: &[Fr], slot: u64, term: &Term) -> Fr {
    let base = slot as usize * WIDTH;
    let x = input[term.gate.left - base];
    let y = input[term.gate.right - base];
    term.gate.c0 + term.gate.c1 * x + term.gate.c2 * y + term.gate.c3 * x * y
}
struct Context {
    base: Base,
    height: HeaderHeightLayout,
}
impl Context {
    fn new() -> Result<Self, String> {
        Ok(Self {
            base: Base::new()?,
            height: HeaderHeightLayout::compile(N, SLOT_LOG)?,
        })
    }
    fn bind(&self, t: &mut Transcript, key: &[u8; 32], commitment: &[u8], height_count: u64) {
        self.base.bind(t, key, commitment, N);
        t.append_bytes(b"height-profile", DOMAIN);
        t.append_bytes(b"height-fingerprint", self.height.fingerprint().as_bytes());
        t.append_u64(b"height-owner-count", height_count);
        t.append_u64(b"height-row-start", HEIGHT_START as u64);
        t.append_u64(b"height-joined-term-count", TOTAL as u64);
    }
    fn visit_height(
        &self,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if copy >= 16 {
            return Err("height copy outside common domain".into());
        }
        if copy >= 11 {
            return Ok(());
        }
        let slot = u64::from(self.base.heights[copy] - 1);
        let count = self.height.visit_slot_terms(slot, |mut term| {
            let bit = term
                .row
                .checked_sub(slot as usize * 32)
                .ok_or("height row underflow")?;
            if bit >= 32 {
                return Err("height row escaped bit bank".into());
            }
            for wire in [&mut term.gate.left, &mut term.gate.right] {
                let local = wire
                    .checked_sub(slot as usize * WIDTH)
                    .ok_or("height endpoint underflow")?;
                if local >= WIDTH {
                    return Err("height endpoint escaped local input".into());
                }
                *wire = copy * WIDTH + local;
            }
            let row = HEIGHT_START + bit;
            term.row = row;
            sink(EdgeTerm {
                source_slot: copy,
                family_row: row,
                term,
            })
        })?;
        if count != 32 {
            return Err("height term count changed".into());
        }
        Ok(())
    }
    fn visit(
        &self,
        left: bool,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        self.base.visit_endpoint(left, copy, &mut sink)?;
        self.visit_height(copy, sink)
    }
    fn height_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != 24 || u.len() != 24 || v.len() != 24 {
            return Err("height common dimensions rejected".into());
        }
        let weight = r[23]
            * (Fr::one() - r[22])
            * r[17]
            * r[10]
            * (5..10)
                .chain(11..17)
                .fold(Fr::one(), |a, i| a * (Fr::one() - r[i]));
        let mut result = [Fr::zero(); 4];
        for copy in 0..11 {
            let fixed = boolean(self.base.heights[copy] as usize - 1, SLOT_LOG);
            let mut row = r[..5].to_vec();
            row.extend_from_slice(&fixed);
            let mut left = u[..20].to_vec();
            left.extend_from_slice(&fixed);
            let mut right = v[..20].to_vec();
            right.extend_from_slice(&fixed);
            let coefficients = self.height.coefficients(&row, &left, &right)?;
            let mask = weight * eq(&r[18..22], copy) * eq(&u[20..], copy) * eq(&v[20..], copy);
            for i in 0..4 {
                result[i] += mask * coefficients[i];
            }
        }
        Ok(result)
    }
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let old = self.base.coefficients(r, u, v)?;
        let height = self.height_coefficients(r, u, v)?;
        Ok(std::array::from_fn(|i| old[i] + height[i]))
    }
}

#[test]
fn canonical_relocation_and_common_height_owner_references_are_causal() {
    let height = HeaderHeightLayout::compile(N + 1, SLOT_LOG).unwrap();
    let header = HeaderHistoryBoundary::compile(N + 1, SLOT_LOG).unwrap();
    let (fixture, headers) = crate::header_history_boundary::tests::fixture();
    let canonical =
        crate::header_history_boundary::tests::assignment_for_child(844_674, &fixture, &headers);
    for slot in [844_673u64, 844_674] {
        let mut previous = None;
        let mut residual = Fr::zero();
        let mut terms = 0;
        header
            .visit_slot_terms(slot, |term| {
                if previous.is_some_and(|row| row != term.row) {
                    assert!(
                        residual.is_zero(),
                        "old header row {:?} slot{slot}",
                        previous
                    );
                    assert!(previous.unwrap() < term.row);
                    residual = Fr::zero();
                }
                previous = Some(term.row);
                residual += value(&canonical, slot, &term);
                terms += 1;
                Ok(())
            })
            .unwrap();
        assert!(residual.is_zero());
        assert_eq!(terms, 474_755);
        let mut failing = Vec::new();
        height
            .visit_slot_terms(slot, |term| {
                let residual = value(&canonical, slot, &term);
                if !residual.is_zero() {
                    failing.push((term.row - slot as usize * 32, residual));
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(
            failing,
            if slot == 844_673 {
                vec![]
            } else {
                vec![(0, -Fr::one())]
            }
        );
    }
    let context = Context::new().unwrap();
    let r = (0..24)
        .map(|i| Fr::from((13 + i * 7) as u64))
        .collect::<Vec<_>>();
    let u = (0..24)
        .map(|i| Fr::from((29 + i * 11) as u64))
        .collect::<Vec<_>>();
    let v = (0..24)
        .map(|i| Fr::from((41 + i * 17) as u64))
        .collect::<Vec<_>>();
    let mut reference = [Fr::zero(); 4];
    let mut count = 0;
    for copy in 0..16 {
        context
            .visit_height(copy, |edge| {
                let row = sparse_stream_roster::global_edge_row(
                    copy,
                    edge.family_row,
                    4,
                    19,
                    1,
                    &MEMBER_ROWS,
                )?;
                let weight =
                    eq(&r, row) * eq(&u, edge.term.gate.left) * eq(&v, edge.term.gate.right);
                for (out, c) in reference.iter_mut().zip([
                    edge.term.gate.c0,
                    edge.term.gate.c1,
                    edge.term.gate.c2,
                    edge.term.gate.c3,
                ]) {
                    *out += weight * c;
                }
                count += 1;
                Ok(())
            })
            .unwrap();
    }
    assert_eq!(count, 352);
    assert_eq!(context.height_coefficients(&r, &u, &v).unwrap(), reference);
    assert_ne!(reference, [Fr::zero(); 4]);
    assert_ne!(
        context.coefficients(&r, &u, &v).unwrap(),
        context.base.coefficients(&r, &u, &v).unwrap()
    );
    for copy in 0..11 {
        let mut rr = r.clone();
        let mut uu = u.clone();
        let mut vv = v.clone();
        for i in 5..24 {
            rr[i] = Fr::zero();
        }
        rr[10] = Fr::one();
        rr[17] = Fr::one();
        rr[23] = Fr::one();
        rr[18..22].copy_from_slice(&boolean(copy, 4));
        uu[20..].copy_from_slice(&boolean(copy, 4));
        vv[20..].copy_from_slice(&boolean(copy, 4));
        let mut expected = [Fr::zero(); 4];
        context
            .visit_height(copy, |edge| {
                let row = sparse_stream_roster::global_edge_row(
                    copy,
                    edge.family_row,
                    4,
                    19,
                    1,
                    &MEMBER_ROWS,
                )?;
                let weight =
                    eq(&rr, row) * eq(&uu, edge.term.gate.left) * eq(&vv, edge.term.gate.right);
                for (out, c) in expected.iter_mut().zip([
                    edge.term.gate.c0,
                    edge.term.gate.c1,
                    edge.term.gate.c2,
                    edge.term.gate.c3,
                ]) {
                    *out += weight * c;
                }
                Ok(())
            })
            .unwrap();
        assert_ne!(expected, [Fr::zero(); 4]);
        assert_eq!(
            context.height_coefficients(&rr, &uu, &vv).unwrap(),
            expected
        );
        let mask = eq(&r[18..22], copy);
        let mut asym_row = r.clone();
        asym_row[18..22].copy_from_slice(&boolean(copy, 4));
        let isolated = context.height_coefficients(&asym_row, &u, &v).unwrap();
        assert_ne!(
            std::array::from_fn::<_, 4, _>(|i| isolated[i] * mask),
            isolated,
            "duplicate copymask"
        );
        for bit in 0..32 {
            let row = sparse_stream_roster::global_edge_row(
                copy,
                HEIGHT_START + bit,
                4,
                19,
                1,
                &MEMBER_ROWS,
            )
            .unwrap();
            let left = copy * WIDTH + context.height.height_wire(bit).unwrap();
            let right = copy * WIDTH;
            let rb = boolean(row, 24);
            let ub = boolean(left, 24);
            let vb = boolean(right, 24);
            let expected = [
                -Fr::from((u64::from(context.base.heights[copy]) >> bit) & 1),
                Fr::one(),
                Fr::zero(),
                Fr::zero(),
            ];
            assert_eq!(
                context.height_coefficients(&rb, &ub, &vb).unwrap(),
                expected
            );
            let mut wrong = rb.clone();
            wrong[22] = Fr::one();
            assert_eq!(
                context.height_coefficients(&wrong, &ub, &vb).unwrap(),
                [Fr::zero(); 4]
            );
            wrong = rb.clone();
            wrong[10] = Fr::zero();
            assert_eq!(
                context.height_coefficients(&wrong, &ub, &vb).unwrap(),
                [Fr::zero(); 4]
            );
            wrong = rb.clone();
            wrong[18] = Fr::one() - wrong[18];
            assert_eq!(
                context.height_coefficients(&wrong, &ub, &vb).unwrap(),
                [Fr::zero(); 4]
            );
            if bit == 0 {
                assert_ne!(
                    expected[0],
                    -Fr::from((u64::from(context.base.heights[copy]) - 1) & 1)
                );
            }
        }
    }
    for copy in 11..16 {
        let row = sparse_stream_roster::global_edge_row(copy, HEIGHT_START, 4, 19, 1, &MEMBER_ROWS)
            .unwrap();
        assert_eq!(
            context
                .height_coefficients(
                    &boolean(row, 24),
                    &boolean(copy * WIDTH + context.height.height_wire(0).unwrap(), 24),
                    &boolean(copy * WIDTH, 24)
                )
                .unwrap(),
            [Fr::zero(); 4]
        );
    }
    assert!(context.height_coefficients(&r[..23], &u, &v).is_err());
    println!("relocated canonical carry old rows zero/new bit0=-1;352 emitted heights mixedcopy/32bits/guards passed");
}
fn load(source: &PackedFile, copy: usize) -> Result<Vec<Fr>, String> {
    let mut input = Vec::with_capacity(WIDTH);
    for chunk in 0..16 {
        input.extend(source.read_copy(CHUNK, copy * 16 + chunk)?);
    }
    Ok(input)
}
fn verify(
    proof: &GkrProof,
    key: &[u8; 32],
    commitment: &[u8],
) -> Result<(InputClaim, Transcript), String> {
    let expected = Context::new()?;
    let mut t = Transcript::new(DOMAIN);
    let claim = gkr::verify_with_wiring(
        &[24],
        1 << 24,
        proof,
        &mut t,
        |t| expected.bind(t, key, commitment, 11),
        |_, r, u, v| {
            expected
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        },
    )
    .map_err(|e| e.to_string())?;
    Ok((claim, t))
}
#[test]
fn native_common_height_witness_one_gkr_pcs_and_single_causal_fault() {
    let whole = Instant::now();
    let mark = Instant::now();
    let context = Context::new().unwrap();
    let context_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    let source = super::pack_native(&context.base);
    let packing_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    let setup = pcs::generate_setup(24).unwrap();
    let setup_ms = mark.elapsed().as_millis();
    let key = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let admitted = verifier_key::admit_generated_test_key(24, &key, setup.id).unwrap();
    let mark = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commit_ms = mark.elapsed().as_millis();
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    let mut t = Transcript::new(DOMAIN);
    let mut loads = 0;
    let mut visits = 0;
    let mut passes = 0;
    source.reset_io_metrics();
    let mark = Instant::now();
    let (proof, claim, inc_u, inc_v) = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            passes += 1;
            context.visit(left, copy, |edge| {
                visits += 1;
                sink(edge)
            })
        },
        |copy| {
            loads += 1;
            load(&source, copy)
        },
        &mut t,
        |t| context.bind(t, &setup.id, &commitment, 11),
        |r, u, v| context.coefficients(r, u, v),
    )
    .unwrap();
    let gkr_ms = mark.elapsed().as_millis();
    let io = source.io_metrics_snapshot();
    assert_eq!(loads, 48);
    assert_eq!(passes, 64);
    assert_eq!(visits, 4 * TOTAL);
    assert_eq!(io.read_calls, 768);
    assert_eq!(io.read_bytes, 6291456);
    assert!(inc_u && inc_v);
    let mark = Instant::now();
    let (verified, mut consumer) = verify(&proof, &setup.id, &commitment).unwrap();
    let consumer_ms = mark.elapsed().as_millis();
    assert_eq!(claim, verified);
    assert_eq!(
        t.clone().challenge_scalar(b"post-gkr"),
        consumer.clone().challenge_scalar(b"post-gkr")
    );
    let mark = Instant::now();
    assert_eq!(source.evaluate(&claim.point).unwrap(), claim.value);
    let mle_ms = mark.elapsed().as_millis();
    let pre_pcs = consumer.clone();
    let mut opening_t = t.clone();
    let mark = Instant::now();
    let opening = packed::open(&committed, &source, &claim.point, &setup, &mut opening_t).unwrap();
    let opening_ms = mark.elapsed().as_millis();
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
    let pcs_verify_ms = mark.elapsed().as_millis();
    assert_eq!(
        opening_t.challenge_scalar(b"post-pcs"),
        consumer.challenge_scalar(b"post-pcs")
    );
    let mut wrong_value = pre_pcs;
    assert!(pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value + Fr::one(),
        &claim.point,
        &opening,
        &admitted,
        &mut wrong_value
    )
    .is_err());
    let mut omitted = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut omitted,
            |t| context.bind(t, &setup.id, &commitment, 11),
            |_, r, u, v| context
                .base
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::TerminalExpression
    );
    let mut wrong_context = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut wrong_context,
            |t| context.bind(t, &setup.id, &commitment, 10),
            |_, r, u, v| context
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::SumcheckIdentity
    );
    let mut causal = None;
    context
        .visit_height(10, |edge| {
            if edge.family_row == HEIGHT_START {
                causal = Some(edge);
            }
            Ok(())
        })
        .unwrap();
    let causal = causal.unwrap();
    let x = source
        .read_copy(CHUNK, causal.term.gate.left / CHUNK)
        .unwrap()[causal.term.gate.left % CHUNK];
    assert!(x.is_zero());
    assert!(causal.term.gate.c0.is_zero());
    assert_eq!(causal.term.gate.c1, Fr::one());
    assert!(causal.term.gate.c2.is_zero());
    assert!(causal.term.gate.c3.is_zero());
    assert!((causal.term.gate.c0 + causal.term.gate.c1 * x).is_zero());
    let false_constant = -Fr::one();
    assert_eq!(false_constant + causal.term.gate.c1 * x, -Fr::one());
    let mut false_t = Transcript::new(DOMAIN);
    let false_edge = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            context.visit(left, copy, |mut edge| {
                if edge.source_slot == 10 && edge.family_row == HEIGHT_START {
                    edge.term.gate.c0 = false_constant;
                }
                sink(edge)
            })
        },
        |copy| load(&source, copy),
        &mut false_t,
        |t| context.bind(t, &setup.id, &commitment, 11),
        |r, u, v| context.coefficients(r, u, v),
    );
    assert_eq!(
        false_edge.unwrap_err(),
        gkr::GkrError::SumcheckIdentity.to_string()
    );
    let proof_bytes = gkr::encode_proof(&proof).unwrap();
    let pcs_bytes = pcs::encode_proof(&opening).unwrap();
    super::super::write_create_new(&super::artifact("height-gkr", "bin"), &proof_bytes);
    super::super::write_create_new(&super::artifact("height-pcs", "bin"), &pcs_bytes);
    super::super::write_create_new(&super::artifact("height-test-key", "bin"), &key);
    let receipt = serde_json::json!({"profile":"common headers+DAA+aliases+11heightowners","N":N,"terms":TOTAL,"height_terms":352,"height_fingerprint":context.height.fingerprint(),"input_bits":24,"row_bits":24,"copies":16,"active_copies":11,"context_ms":context_ms,"packing_ms":packing_ms,"setup_ms":setup_ms,"commit_ms":commit_ms,"gkr_ms":gkr_ms,"full_consumer_ms":consumer_ms,"mle_ms":mle_ms,"opening_ms":opening_ms,"pcs_verify_ms":pcs_verify_ms,"whole_ms":whole.elapsed().as_millis(),"loader_calls":loads,"endpoint_passes":passes,"term_visits":visits,"packed_reads":io.read_calls,"packed_read_bytes":io.read_bytes,"incremental_u":inc_u,"incremental_v":inc_v,"gkr_bytes":proof_bytes.len(),"pcs_bytes":pcs_bytes.len(),"setup_id":setup.id.iter().map(|b|format!("{b:02x}")).collect::<String>(),"authority_ceiling":"bounded heights; sample serializer/hash validity and history inclusion, carryDAA, fullchain/finalparameters not proven"});
    println!("{receipt}");
    super::super::write_create_new(
        &super::artifact("height-receipt", "json"),
        receipt.to_string().as_bytes(),
    );
}

#[path = "carry_numeric_join_tests.rs"]
mod carry_numeric_join_tests;

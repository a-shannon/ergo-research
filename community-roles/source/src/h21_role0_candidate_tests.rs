//! Source/shape/admission controls. No test fabricates a complete H21 source,
//! a full-history proof, or native verification authority.
use super::*;
use core_pool_boolean::{H21Role0DiagnosticBudget, H21Role0ResourcePreflight};
use dory_pcs::{backends::arkworks::ArkGT, primitives::arithmetic::Group};

const KEY41: &[u8] = include_bytes!("../fixtures/verifier-keys-v1/log41.vk");
fn banks() -> [usize; 11] { layout::CORE_OFFSETS.map(|offset| offset / layout::CORE) }
fn budget() -> H21Role0DiagnosticBudget {
    H21Role0DiagnosticBudget { limit_bytes:8usize << 30,
        caller_graph_reservation_bytes:1usize << 30, unmeasured_reservation_bytes:256usize << 20 }
}
fn resources(b: H21Role0DiagnosticBudget) -> Result<H21Role0ResourcePreflight,String> {
    core_pool_boolean::h21_role0_resource_preflight(21,&banks(),16 * (1 << 21),b)
}
fn commitment() -> Vec<u8> { pcs::encode_commitment(&ArkGT::identity()).unwrap() }
fn parameters() -> [PublicMapParameters;2] {
    use crate::legacy_envelope_map::{LowerSelector,LowerSource,LowerBranch};
    crate::bank53_map::CutDescriptor::eligible08().terminals().map(|terminal|PublicMapParameters {
        terminal,exponent:55,lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},
            branch:LowerBranch::Pivot(54)} })
}
fn state(t: &Transcript) -> (u64,u64,u64) { (t.challenges(),t.raw_queries(),t.bytes_absorbed()) }

#[test]
fn c592_h21_role0_exact_shape_preserves_legacy_admissions() -> Result<(),String> {
    let h21 = crate::core_pool::Plan::new(21)?;
    h21.require_h21_role0_candidate_shape()?;
    assert_eq!((h21.input_log(),h21.row_log(),h21.input_len(),h21.row_count()),
        (16+4+21,17+21+4,1usize << 41,1usize << 42));
    assert_eq!(h21.term_count(),172_480usize * banks().len() * (1 << 21));
    assert!(h21.require_native_role0_shape().is_err());
    let h12 = crate::core_pool::Plan::new(12)?;
    h12.require_native_role0_shape()?;
    assert!(h12.require_h21_role0_candidate_shape().is_err());
    for h in [0,2,20] { assert!(crate::core_pool::Plan::new(h)?.require_h21_role0_candidate_shape().is_err()); }
    assert!(crate::core_pool::Plan::new(22).is_err());
    Ok(())
}

#[test]
fn c592_h21_role0_preflight_requires_all_sixteen_physical_banks() -> Result<(),String> {
    let baseline = resources(budget())?;
    assert_eq!(baseline.copies,1 << 21);
    assert_eq!(baseline.high_records,16 * baseline.copies);
    assert!(core_pool_boolean::h21_role0_resource_preflight(21,&banks(),11 * (1 << 21),budget()).is_err());
    let mut changed = banks(); changed.swap(0,1);
    assert!(core_pool_boolean::h21_role0_resource_preflight(21,&changed,baseline.high_records,budget()).is_err());
    changed = banks(); changed[10] = changed[0];
    assert!(core_pool_boolean::h21_role0_resource_preflight(21,&changed,baseline.high_records,budget()).is_err());
    assert!(core_pool_boolean::h21_role0_resource_preflight(21,&banks()[..10],baseline.high_records,budget()).is_err());
    for h in [12,20,22,usize::BITS as usize-1,usize::MAX] {
        assert!(core_pool_boolean::h21_role0_resource_preflight(h,&banks(),baseline.high_records,budget()).is_err());
    }
    Ok(())
}

#[test]
fn c592_h21_role0_resource_phases_refuse_floor_shortfall_and_overflow() -> Result<(),String> {
    let actual = resources(budget())?;
    assert_eq!(actual.dense_high_fold_payload_bytes,4usize << 30);
    assert_eq!(actual.tau_payload_bytes,704usize << 20);
    assert_eq!(actual.persistent_weights_payload_bytes,(64usize << 20)+(4usize << 20)+16*32);
    assert_eq!(actual.known_peak_lower_bound_bytes,
        actual.dense_high_fold_payload_bytes+actual.persistent_weights_payload_bytes);
    assert!(actual.v_high_materialization_payload_bytes < actual.known_peak_lower_bound_bytes,
        "tau and cloned X do not coexist");
    assert!(actual.u_high_materialization_reservation_bytes < actual.known_peak_lower_bound_bytes);
    assert!(actual.local_phase_reservation_bytes < actual.known_peak_lower_bound_bytes);
    for limit in [0,4usize << 30,actual.known_peak_lower_bound_bytes,actual.required_reservation_bytes-1] {
        assert!(resources(H21Role0DiagnosticBudget {limit_bytes:limit,..budget()}).is_err());
    }
    let exact = resources(H21Role0DiagnosticBudget {limit_bytes:actual.required_reservation_bytes,..budget()})?;
    assert_eq!(exact.required_reservation_bytes,actual.required_reservation_bytes);
    assert!(resources(H21Role0DiagnosticBudget {caller_graph_reservation_bytes:usize::MAX,..budget()}).is_err());
    assert!(resources(H21Role0DiagnosticBudget {unmeasured_reservation_bytes:usize::MAX,..budget()}).is_err());
    assert!(resources(H21Role0DiagnosticBudget {caller_graph_reservation_bytes:0,..budget()}).is_err());
    assert!(resources(H21Role0DiagnosticBudget {unmeasured_reservation_bytes:0,..budget()}).is_err());
    Ok(())
}

#[test]
fn c592_h21_role0_candidate_signature_requires_native_borrowed_view() {
    type Bind = fn(&mut Transcript)->Result<(),String>;
    type Wiring = fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>;
    // A wrapper resolves impl-Trait inference without calling the producer or
    // constructing a fake native source/view. Removing the typed borrow breaks
    // this ordinary positive call site at compile time.
    fn entry(plan:&crate::core_pool::Plan,view:&packed::PackedH21Role0View<'_>,
        b:H21Role0DiagnosticBudget,t:&mut Transcript,bind:Bind,wiring:Wiring)
        ->Result<core_pool_boolean::CandidateRole0Proof,String> {
        core_pool_boolean::prove_packed_h21_role0_candidate(plan,view,b,t,bind,wiring)
    }
    let _entry:fn(&crate::core_pool::Plan,&packed::PackedH21Role0View<'_>,
        H21Role0DiagnosticBudget,&mut Transcript,Bind,Wiring)
        ->Result<core_pool_boolean::CandidateRole0Proof,String> = entry;
}

#[test]
fn c592_h21_role0_admission_uses_exact_key_bytes_not_a_generated_id() -> Result<(),String> {
    assert_eq!(KEY41.len(),42_864);
    let inputs = H21Role0DiagnosticInputs::new(b"prefix-binding-only",KEY41,&commitment())?;
    require_h21_role0_diagnostic_key(&inputs.key)?;
    assert_eq!(inputs.key.log_n(),41);
    let wrong_id = verifier_key::admit_generated_test_key(41,KEY41,[0x99;32])?;
    assert!(require_h21_role0_diagnostic_key(&wrong_id).is_err());
    let wrong_log = verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    assert!(require_h21_role0_diagnostic_key(&wrong_log).is_err());
    assert!(verifier_key::admit(32,KEY41).is_err());
    assert!(H21Role0DiagnosticInputs::new(b"prefix-binding-only",
        include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),&commitment()).is_err());
    let mut changed = KEY41.to_vec();
    // Keep valid group encodings and framing while violating the exact key pin.
    changed[8..392].copy_from_slice(&KEY41[392..776]);
    assert!(H21Role0DiagnosticInputs::new(b"prefix-binding-only",&changed,&commitment()).is_err());
    for framed in [KEY41[..KEY41.len()-1].to_vec(),[KEY41,&[0u8]].concat()] {
        assert!(H21Role0DiagnosticInputs::new(b"prefix-binding-only",&framed,&commitment()).is_err());
    }
    changed = KEY41.to_vec(); changed[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(H21Role0DiagnosticInputs::new(b"prefix-binding-only",&changed,&commitment()).is_err());
    changed = KEY41.to_vec(); let at=5*(8+384*22)+576;
    changed[at..at+8].copy_from_slice(&32u64.to_le_bytes());
    assert!(H21Role0DiagnosticInputs::new(b"prefix-binding-only",&changed,&commitment()).is_err());
    Ok(())
}

#[test]
fn c592_h21_role0_canonical_commitment_and_fresh_prefix_controls() -> Result<(),String> {
    let c = commitment();
    for invalid in [vec![0xff;c.len()],c[..c.len()-1].to_vec(),[c.as_slice(),&[0u8]].concat()] {
        assert!(H21Role0DiagnosticInputs::new(b"prefix-binding-only",KEY41,&invalid).is_err());
    }
    let inputs = H21Role0DiagnosticInputs::new(b"prefix-binding-only",KEY41,&c)?;
    let mut t = Transcript::new(H21_ROLE0_DIAGNOSTIC_DOMAIN); let before=state(&t);
    assert!(inputs.bind_prefix(1,&mut t).is_err()); assert_eq!(state(&t),before);
    t.challenge_scalar(b"already-queried"); let before=state(&t);
    assert!(inputs.bind_prefix(0,&mut t).is_err()); assert_eq!(state(&t),before);
    let mut bad_key = H21Role0DiagnosticInputs::new(b"prefix-binding-only",KEY41,&c)?;
    bad_key.key = verifier_key::admit_generated_test_key(41,KEY41,[0x99;32])?;
    let mut pristine=Transcript::new(H21_ROLE0_DIAGNOSTIC_DOMAIN); let before=state(&pristine);
    assert!(bad_key.bind_prefix(0,&mut pristine).is_err()); assert_eq!(state(&pristine),before);
    let mut a=inputs.fresh_transcript()?; let mut b=inputs.fresh_transcript()?;
    assert_eq!((a.challenges(),a.raw_queries()),(0,0));
    assert_eq!(a.challenge_scalar(b"first"),b.challenge_scalar(b"first"));
    let mut legacy=Transcript::new(b"historical51"); inputs.bind_prefix(0,&mut legacy)?;
    assert_ne!(legacy.challenge_scalar(b"first"),inputs.fresh_transcript()?.challenge_scalar(b"first"));
    Ok(())
}

#[test]
fn c592_h21_role0_expected_maps_are_derived_from_both_public_parameter_sets() -> Result<(),String> {
    use crate::legacy_envelope_map::LowerBranch;
    let p=parameters(); let actual=h21_role0_expected_maps(p)?;
    for index in 0..2 {
        assert_eq!(actual[index],crate::legacy_envelope_map::Map::new_modern_global_u_selected_lower(
            p[index].terminal as u64,21,p[index].exponent,p[index].lower)?.binding());
        assert!(actual[index].parent_root.is_none());
        let mut exponent_only=p; exponent_only[index].exponent=54;
        let mut pivot_only=p; pivot_only[index].lower.branch=LowerBranch::Pivot(56);
        for (field,changed) in [("exponent",exponent_only),("pivot",pivot_only)] {
            let different=h21_role0_expected_maps(changed)?;
            assert_ne!(different[index],actual[index],"context {index}, isolated {field}");
            assert_eq!(different[1-index],actual[1-index],"other context, isolated {field}");
        }
    }
    assert_ne!(actual[0],actual[1]);
    Ok(())
}

#[test]
fn c592_h21_role0_raw_codec_rejects_other_dimension_and_framing() -> Result<(),String> {
    let expected=(7*41+3)*32;
    for bytes in [vec![],vec![0;(7*32+3)*32],vec![0;expected-1],vec![0;expected+1]] {
        assert!(gkr::decode_dimensions(&[41],&bytes).is_err());
    }
    let zeros=vec![0;expected]; let decoded=gkr::decode_dimensions(&[41],&zeros)?;
    assert_eq!(decoded.layers[0].rounds.len(),82);
    assert_eq!(decoded.layers[0].line_coefficients.len(),42);
    assert_eq!(gkr::encode_proof(&decoded)?,zeros);
    let mut noncanonical=zeros; noncanonical[..32].fill(0xff);
    assert!(gkr::decode_dimensions(&[41],&noncanonical).is_err());
    // A valid scalar stream alone is not a valid H21 proof or wiring check.
    Ok(())
}

#[test]
#[ignore="one actual H21 public context; separately capped 2 GiB diagnostic Job required"]
fn c592_h21_role0_actual_public_context_binds_statement_maps_template_and_c() -> Result<(),String> {
    use ark_ec::{PrimeGroup as ArkGroup,pairing::Pairing};
    let p=parameters(); let owned=H21StructuralDiagnostic::compile([0x31;32],[0x42;28],[0x52;32],1,p)?;
    let context=owned.context()?; // Exactly one full public context in this test.
    let c=commitment(); let admission=context.admit_role0_diagnostic(KEY41,&c)?;
    let first=|a:&H21Role0DiagnosticAdmission<'_, '_>|->Result<Fr,String> {
        let mut t=a.inputs.fresh_transcript()?; a.bind_role0(&mut t)?;
        assert_eq!((t.challenges(),t.raw_queries()),(0,0)); Ok(t.challenge_scalar(b"first"))
    };
    let original=first(&admission)?;
    let mut expected=admission.inputs.fresh_transcript()?;
    context.bind_role(0,&mut expected)?; context.layouts.parent.core_pool().bind(&mut expected);
    assert_eq!(original,expected.challenge_scalar(b"first"));
    let root_at=b"historical-prefix-h21-eligible08-structural-diagnostic-v1".len()+32;
    let tip_at=root_at+32+28;
    // Byte mutants isolate the exact public prefix, not alternate accepted
    // contexts. The owning admission rejects each detached identity below.
    let map_at=context.public_bytes.len()-7*16-2*34;
    for at in [root_at,tip_at,map_at,map_at+34] {
        let mut changed=H21Role0DiagnosticInputs::new(context.public_bytes,KEY41,&c)?;
        changed.public_identity[at]^=1;
        assert_ne!(changed.fresh_transcript()?.challenge_scalar(b"first"),
            admission.inputs.fresh_transcript()?.challenge_scalar(b"first"));
        let mutant=H21Role0DiagnosticAdmission {context:&context,inputs:changed};
        let mut t=mutant.inputs.fresh_transcript()?; let before=state(&t);
        assert!(mutant.bind_role0(&mut t).is_err()); assert_eq!(state(&t),before);
    }
    let other_c=pcs::encode_commitment(&ArkGT(ark_bn254::Bn254::pairing(
        ark_bn254::G1Projective::generator(),ark_bn254::G2Projective::generator())))?;
    assert_ne!(other_c,c);
    assert_ne!(original,first(&context.admit_role0_diagnostic(KEY41,&other_c)?)?);
    let mut used=admission.inputs.fresh_transcript()?; used.challenge_scalar(b"already-queried");
    assert!(admission.bind_role0(&mut used).is_err());
    // This is an early dimension/codec negative, not a claimed wiring negative.
    assert!(admission.verify(&vec![0;(7*32+3)*32]).is_err());
    // Canonical 41-dimensional messages preserve every zero sumcheck identity
    // and both line endpoints. The real public callback must reject their
    // inconsistent terminal value before the line checks can accept it.
    let mut inconsistent=gkr::decode_dimensions(&[41],&vec![0;(7*41+3)*32])?;
    inconsistent.layers[0].left_value=Fr::one();
    inconsistent.layers[0].line_coefficients[0]=Fr::one();
    inconsistent.layers[0].line_coefficients[1]=-Fr::one();
    let inconsistent=gkr::encode_proof(&inconsistent)?;
    let terminal=GkrError::TerminalExpression.to_string();
    assert_eq!(admission.verify(&inconsistent),Err(terminal.clone()));
    let callbacks=std::cell::Cell::new(0usize);
    assert_eq!(admission.verify_with_counter(&inconsistent,Some(&callbacks)),Err(terminal));
    assert_eq!(callbacks.get(),1,"one successful real public role0 callback");
    assert!(context.coefficients(0,&[Fr::zero();41],&[Fr::zero();41],&[Fr::zero();41]).is_err());
    Ok(())
}

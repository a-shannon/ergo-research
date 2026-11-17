use super::*;
use crate::pcs;

fn domain()->Transcript {Transcript::new(b"c589-role0-candidate-independent-consumer-v1")}
fn bind(public:&Circuit,commitment:&[u8],setup:&pcs::Setup,t:&mut Transcript) {
    sparse::bind(public,0,t);
    t.append_bytes(b"c589-input-key",&setup.id);
    t.append_bytes(b"c589-original-input-commitment",commitment);
}

#[test]
fn c589_candidate_preserves_checked_proof_and_boolean_preflight()->Result<(),String> {
    let core=super::tests::fixture();let shape=sparse::validate(&core,0).map_err(|e|e.to_string())?;
    let input=vec![Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()];
    let binding=|t:&mut Transcript|sparse::bind(&core,0,t);
    let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|sparse::wiring(&core,&shape,r,u,v).map_err(|e|e.to_string());
    let mut checked_t=domain();
    let checked=prove_tensor(&core,0,&[0],0,|_|Ok(input.clone()),&mut checked_t,binding,wiring)?;
    let mut candidate_t=domain();
    let candidate=prove_tensor_with_policy(&core,0,&[0],0,
        |_|Ok(DenseBooleanCopy {values:input.clone()}),&mut candidate_t,
        |t|{binding(t);Ok(())},wiring,&mut DenseHigh,0,1,ResidualPolicy::Candidate)?;
    assert_eq!(gkr::encode_proof(&checked.0)?,gkr::encode_proof(&candidate.0)?);
    assert_eq!(checked.1,candidate.1);
    assert_eq!((checked_t.challenges(),checked_t.raw_queries(),checked_t.bytes_absorbed()),
        (candidate_t.challenges(),candidate_t.raw_queries(),candidate_t.bytes_absorbed()));
    let bound=std::cell::Cell::new(false);let mut invalid=input;invalid[2]=Fr::from(2u64);
    let mut t=domain();let before=(t.challenges(),t.raw_queries(),t.bytes_absorbed());
    let error=prove_tensor_with_policy(&core,0,&[0],0,|_|Ok(DenseBooleanCopy {values:invalid.clone()}),
        &mut t,|_|{bound.set(true);Ok(())},wiring,&mut DenseHigh,0,1,ResidualPolicy::Candidate).unwrap_err();
    assert!(error.contains("non-Boolean input"));assert!(!bound.get());
    assert_eq!((t.challenges(),t.raw_queries(),t.bytes_absorbed()),before);Ok(())
}

#[test]
fn c589_self_consistent_changed_commitment_and_proof_reach_public_consumer_rejection()->Result<(),String> {
    let public=super::tests::fixture();let public_shape=sparse::validate(&public,0).map_err(|e|e.to_string())?;
    let original=vec![Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()];
    let mut changed=original.clone();changed[2]=Fr::one();
    // The sole changed witness bit creates residual +1 at P's row2. Prove
    // P'=P-1 at that row, while the transcript still binds PUBLIC P and C'.
    let mut altered=public.clone();
    altered.terms.iter_mut().find(|term|term.row==2).ok_or("fixture row2")?.gate.c0-=Fr::one();
    let altered_shape=sparse::validate(&altered,0).map_err(|e|e.to_string())?;
    let setup=pcs::generate_setup(2)?;
    let committed_original=pcs::commit(&original,&setup)?;
    let committed_changed=pcs::commit(&changed,&setup)?;
    let c=pcs::encode_commitment(&committed_changed.commitment)?;
    assert_ne!(pcs::encode_commitment(&committed_original.commitment)?,c);
    let original_wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|sparse::wiring(&public,&public_shape,r,u,v).map_err(|e|e.to_string());
    let altered_wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|sparse::wiring(&altered,&altered_shape,r,u,v).map_err(|e|e.to_string());
    let mut preflight_t=domain();
    assert_eq!(prove_tensor(&public,0,&[0],0,|_|Ok(changed.clone()),&mut preflight_t,
        |t|bind(&public,&c,&setup,t),original_wiring).unwrap_err(),GkrError::NonzeroOutput.to_string());
    let mut prover_t=domain();
    let(proof,claim)=prove_tensor_with_policy(&altered,0,&[0],0,
        |_|Ok(DenseBooleanCopy {values:changed.clone()}),&mut prover_t,
        |t|{bind(&public,&c,&setup,t);Ok(())},altered_wiring,&mut DenseHigh,0,1,ResidualPolicy::Candidate)?;
    let encoded=gkr::encode_proof(&proof)?;let proof=gkr::decode_dimensions(&[2],&encoded)?;
    // The adversarial packet is well formed and proves its deliberately
    // altered relation. This is not a malformed/preflight-only rejection.
    let mut altered_t=domain();
    let derived=gkr::verify_with_wiring(&[2],4,&proof,&mut altered_t,
        |t|bind(&public,&c,&setup,t),|_,r,u,v|sparse::wiring(&altered,&altered_shape,r,u,v))
        .map_err(|e|e.to_string())?;
    assert_eq!(derived,claim);
    let mut open_t=prover_t.clone();open_t.append_bytes(b"c589-boundary",b"input-PCS");
    let opening=pcs::open(&committed_changed,&claim.point,&setup,&mut open_t)?;
    let opening_bytes=pcs::encode_proof(&opening)?;
    let opening=pcs::decode_proof(&opening_bytes,2)?;
    let mut pcs_t=altered_t;pcs_t.append_bytes(b"c589-boundary",b"input-PCS");
    pcs::verify(committed_changed.commitment,claim.value,&claim.point,&opening,&setup,&mut pcs_t)?;
    let entered=std::cell::Cell::new(0usize);let mut consumer_t=domain();
    let result=gkr::verify_with_wiring(&[2],4,&proof,&mut consumer_t,
        |t|bind(&public,&c,&setup,t),|_,r,u,v|{entered.set(entered.get()+1);sparse::wiring(&public,&public_shape,r,u,v)});
    assert_eq!(entered.get(),1);
    assert_eq!(result,Err(GkrError::TerminalExpression));Ok(())
}

#[test]
fn c590_u0_four_boolean_cases_match_generic_with_arbitrary_fr_coefficients()->Result<(),String> {
    let mut all_x=Vec::new();let mut all_a=Vec::new();let mut all_b=Vec::new();
    let mut sum=vec![Fr::zero();3];
    for (j,(x0,x1)) in [(false,false),(false,true),(true,false),(true,true)].into_iter().enumerate() {
        let a=vec![-Fr::from((3+j)as u64),Fr::from((11+2*j)as u64)];
        let b=vec![Fr::from((5+3*j)as u64),-Fr::from((17+j)as u64)];
        let x=vec![Fr::from(x0 as u64),Fr::from(x1 as u64)];
        let checked=read_local_copy(&mut |_|Ok(DenseBooleanCopy {values:x.clone()}),0,2,&ResidualPolicy::Candidate)?;
        let span=checked.candidate_u0_span(&[],0,2)?.ok_or("missing validated candidate span")?;
        let actual=candidate_u0_message(&a,&b,&span)?;
        let expected=gkr::quadratic_message(&a,&b,&x);
        assert_eq!(actual,expected,"pair{x0:?}/{x1:?}");assert_eq!(actual.len(),3);
        if x0==x1 {assert_eq!(actual[2],Fr::zero());}
        for (total,value) in sum.iter_mut().zip(actual) {*total+=value;}
        all_x.extend(x);all_a.extend(a);all_b.extend(b);
    }
    let checked=read_local_copy(&mut |_|Ok(DenseBooleanCopy {values:all_x.clone()}),0,8,&ResidualPolicy::Candidate)?;
    let span=checked.candidate_u0_span(&[],0,8)?.unwrap();
    assert_eq!(candidate_u0_message(&all_a,&all_b,&span)?,sum);
    assert_eq!(sum,gkr::quadratic_message(&all_a,&all_b,&all_x));
    assert!(candidate_u0_message(&all_a[..7],&all_b,&span).is_err());
    assert!(checked.candidate_u0_span(&[],usize::MAX,8).is_err());
    assert!(checked.candidate_u0_span(&[],1,2).is_err());
    assert!(checked.candidate_u0_span(&[],0,3).is_err());
    assert!(checked.candidate_u0_span(&[Fr::from(2u64)],0,8)?.is_none());
    let legacy=read_local_copy(&mut |_|Ok(DenseBooleanCopy {values:all_x.clone()}),0,8,&ResidualPolicy::Checked)?;
    assert!(legacy.candidate_u0_span(&[],0,8)?.is_none());
    Ok(())
}

#[test]
fn c590_u0_original_dense_fr2_and_raw_spans_refuse_before_binding()->Result<(),String> {
    let core=super::tests::fixture();let width=core.input_len*4;
    for index in 0..width {
        let mut values=vec![Fr::zero();width];values[index]=Fr::from(2u64);
        let bound=std::cell::Cell::new(false);let mut transcript=domain();
        let before=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
        let result=prove_tensor_with_policy(&core,2,&[0,2,3],0,
            |_|Ok(DenseBooleanCopy {values:values.clone()}),&mut transcript,
            |_|{bound.set(true);Ok(())},|_,_,_|panic!("invalid original input reached wiring"),
            &mut DenseHigh,0,4,ResidualPolicy::Candidate);
        assert!(result.unwrap_err().contains("non-Boolean input"),"position{index}");
        assert!(!bound.get());
        assert_eq!((transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()),before);
    }
    // BooleanSpan's bit() alone would hide this Fr=2. A raw span has no
    // whole-copy validation constructor, even when its geometry is correct.
    let raw=DenseBooleanCopy {values:vec![Fr::from(2u64),Fr::zero(),Fr::one(),Fr::zero()]};
    let result=read_local_copy(&mut |_|bank_span(&raw,0,4),0,4,&ResidualPolicy::Candidate);
    assert!(matches!(result,Err(error) if error=="candidate requires a complete original Boolean copy"));
    Ok(())
}

#[test]
fn c590_u0_optimized_proof_claim_and_transcript_match_generic_reference()->Result<(),String> {
    let core=Circuit {input_len:8,row_count:8,terms:(0..8).map(|wire|Term {row:wire,
        gate:crate::gkr::Gate {left:wire,right:wire,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()}}).collect()};
    let shape=sparse::validate(&core,0).map_err(|e|e.to_string())?;
    let values=[false,false,false,true,true,false,true,true].map(|value|Fr::from(value as u64)).to_vec();
    let mut reference_t=domain();let mut candidate_t=domain();
    let binding=|t:&mut Transcript|sparse::bind(&core,0,t);
    let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|sparse::wiring(&core,&shape,r,u,v).map_err(|e|e.to_string());
    let reference=prove_tensor(&core,0,&[0],0,|_|Ok(values.clone()),&mut reference_t,binding,wiring)?;
    let candidate=prove_tensor_with_policy(&core,0,&[0],0,
        |_|Ok(DenseBooleanCopy {values:values.clone()}),&mut candidate_t,
        |t|{binding(t);Ok(())},wiring,&mut DenseHigh,0,1,ResidualPolicy::Candidate)?;
    assert_eq!(gkr::encode_proof(&reference.0)?,gkr::encode_proof(&candidate.0)?);
    assert_eq!(reference.1,candidate.1);
    assert_eq!((reference_t.challenges(),reference_t.raw_queries(),reference_t.bytes_absorbed()),
        (candidate_t.challenges(),candidate_t.raw_queries(),candidate_t.bytes_absorbed()));
    assert_eq!(reference_t.challenge_scalar(b"c590-next"),candidate_t.challenge_scalar(b"c590-next"));
    let proof=gkr::decode_dimensions(&[3],&gkr::encode_proof(&candidate.0)?)?;
    let mut independent=domain();
    let claim=gkr::verify_with_wiring(&[3],8,&proof,&mut independent,binding,
        |_,r,u,v|sparse::wiring(&core,&shape,r,u,v)).map_err(|e|e.to_string())?;
    assert_eq!(claim,candidate.1);Ok(())
}

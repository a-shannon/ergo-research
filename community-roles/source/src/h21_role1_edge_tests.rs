//! Role1 admission controls and a projected canonical import-edge fixture.
//! The small GKR fixture is not an H21 role proof or a PCS/history result.
use super::*;
use ark_ff::{One,Zero};
use crate::sparse_stream_roster as edge;

fn budget() -> edge::H21Role1Budget {
    edge::H21Role1Budget {limit_bytes:4usize<<30,caller_context_bytes:1600usize<<20,
        visitor_scratch_bytes:32usize<<20,unmeasured_bytes:128usize<<20}
}
fn preflight(budget:edge::H21Role1Budget) -> Result<edge::H21Role1ResourcePlan,String> {
    edge::h21_role1_resource_preflight(20,21,19,0,&[19],512,budget)
}
fn state(t:&Transcript) -> (u64,u64,u64) {(t.challenges(),t.raw_queries(),t.bytes_absorbed())}

#[test]
fn c596_h21_role1_resource_phases_refuse_short_budget_and_overflow() -> Result<(),String> {
    let plan=preflight(budget())?;
    assert_eq!(plan.census_bytes,32usize<<20);assert_eq!(plan.cache_bytes,(512usize<<10)+512);
    assert_eq!(plan.u_weights_bytes,96usize<<20);
    assert_eq!(plan.high_accumulation_bytes,192usize<<20);assert_eq!(plan.high_fold_bytes,256usize<<20);
    assert_eq!(plan.replay_banks_bytes,64usize<<20);assert_eq!(plan.expanded_owner_bytes,32usize<<20);
    assert_eq!(plan.line_work_bytes,96usize<<20);
    assert!(plan.known_peak_bytes>(416usize<<20));
    assert!(plan.known_peak_bytes-(416usize<<20)>=plan.cache_bytes);
    assert_eq!(plan.required_bytes,plan.known_peak_bytes+budget().caller_context_bytes+budget().unmeasured_bytes);
    let small=preflight(edge::H21Role1Budget {visitor_scratch_bytes:1,..budget()})?;
    assert_eq!(small.required_bytes,plan.required_bytes,"visitor and expanded X are not live together");
    let larger=preflight(edge::H21Role1Budget {visitor_scratch_bytes:64usize<<20,..budget()})?;
    assert_eq!(larger.required_bytes-plan.required_bytes,32usize<<20);
    assert_eq!(preflight(edge::H21Role1Budget {limit_bytes:plan.required_bytes,..budget()})?,plan);
    for limit in [0,416usize<<20,plan.required_bytes-1] {
        assert!(preflight(edge::H21Role1Budget {limit_bytes:limit,..budget()}).is_err());
    }
    for invalid in [edge::H21Role1Budget {caller_context_bytes:0,..budget()},
        edge::H21Role1Budget {visitor_scratch_bytes:0,..budget()},
        edge::H21Role1Budget {unmeasured_bytes:0,..budget()},
        edge::H21Role1Budget {caller_context_bytes:usize::MAX,..budget()},
        edge::H21Role1Budget {visitor_scratch_bytes:usize::MAX,..budget()},
        edge::H21Role1Budget {unmeasured_bytes:usize::MAX,..budget()}] {
        assert!(preflight(invalid).is_err());
    }
    assert!(edge::h21_role1_resource_preflight(20,21,19,0,&[19],usize::MAX,budget()).is_err());
    for (input,slots,rows,family) in [(19,21,19,0),(20,20,19,0),(20,21,18,0),(20,21,19,1),
        (usize::MAX,21,19,0),(20,usize::MAX,19,0)] {
        assert!(edge::h21_role1_resource_preflight(input,slots,rows,family,&[19],512,budget()).is_err());
    }
    for members in [&[][..],&[18][..],&[19,19][..]] {
        assert!(edge::h21_role1_resource_preflight(20,21,19,0,members,512,budget()).is_err());
    }
    Ok(())
}

#[test]
fn c596_h21_role1_identity_and_typed_entry_preserve_legacy_guards() -> Result<(),String> {
    let loads=std::cell::Cell::new(0usize);let work=std::cell::Cell::new(0usize);
    let mut t=Transcript::new(b"c596-admission-order-test-only");let before=state(&t);
    let refused=with_matching_h21_requested_identity(b"requested-A",b"requested-B",|| {
        work.set(work.get()+1);preflight(budget())?;
        loads.set(loads.get()+1);Ok(t.challenge_scalar(b"must-not-query"))
    });
    assert!(refused.is_err());assert_eq!((work.get(),loads.get()),(0,0));assert_eq!(state(&t),before);
    let refused=with_matching_h21_requested_identity(b"same",b"same",|| {
        work.set(work.get()+1);preflight(edge::H21Role1Budget {limit_bytes:1,..budget()})?;
        loads.set(loads.get()+1);Ok(t.challenge_scalar(b"must-not-query"))
    });
    assert!(refused.is_err());assert_eq!((work.get(),loads.get()),(1,0));assert_eq!(state(&t),before);
    fn typed_entry(context:&H21StructuralDiagnosticContext<'_>,key:&[u8],c:&[u8],
        candidate:&packed::UntrustedH21CandidateFile,budget:edge::H21Role1Budget)
        ->Result<(Vec<u8>,InputClaim),String> {
        context.prove_role1_untrusted_candidate(key,c,candidate,budget)
    }
    let _entry:fn(&H21StructuralDiagnosticContext<'_>,&[u8],&[u8],
        &packed::UntrustedH21CandidateFile,edge::H21Role1Budget)->Result<(Vec<u8>,InputClaim),String>=typed_entry;
    assert!(edge::PackedEdgeInput::new(1<<20,4096,|_| {loads.set(loads.get()+1);Ok(vec![0;1<<17])}).is_ok());
    assert!(edge::PackedEdgeInput::new(1<<20,1<<21,|_| {loads.set(loads.get()+1);Ok(vec![0;1<<17])}).is_err());
    assert!(edge::PackedEdgeInput::new(1<<21,4096,|_| {loads.set(loads.get()+1);Ok(vec![0;1<<18])}).is_err());
    assert_eq!((1usize<<20)*4096,1usize<<32);assert_eq!(loads.get(),0);
    Ok(())
}

// The fixture's row owner is independent of either endpoint owner. This
// adapter rejects bad metadata before the generic engine can consume it.
fn projected_edge(term:Term,source_slot:usize) -> Result<edge::EdgeTerm,String> {
    let row=edge::global_edge_row(source_slot,0,2,0,0,&[0])?;
    if row!=term.row {return Err("projected edge global ROW metadata mismatch".into());}
    Ok(edge::EdgeTerm {source_slot,family_row:0,term})
}

#[test]
fn c596_h21_role1_row_metadata_preserves_the_canonical_row_owner() -> Result<(),String> {
    for row in [0usize,(1<<19)-1,1<<19,(1usize<<40)-1,1_810_841*(1<<19)+506_925+17] {
        let (owner,local)=edge::h21_role1_edge_metadata(row)?;
        assert_eq!(owner,row/(1<<19));assert_eq!(local,row%(1<<19));
        assert_eq!(edge::global_edge_row(owner,local,21,19,0,&[19])?,row);
    }
    assert!(edge::h21_role1_edge_metadata(1usize<<40).is_err());
    assert!(edge::h21_role1_edge_metadata(usize::MAX).is_err());
    let term=Term {row:2,gate:gkr::Gate {left:9,right:0,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
    assert_eq!(projected_edge(term.clone(),2)?.source_slot,2);
    assert_eq!(edge::global_edge_row(1,0,2,0,0,&[0])?,1);
    assert_eq!(projected_edge(term,1).err().as_deref(),Some("projected edge global ROW metadata mismatch"));
    Ok(())
}

fn fixture_parameters() -> [PublicMapParameters;2] {
    use crate::legacy_envelope_map::{LowerSource,LowerBranch,LowerSelector};
    crate::bank53_map::CutDescriptor::eligible08().terminals().map(|terminal|PublicMapParameters {
        terminal,exponent:55,lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},branch:LowerBranch::Pivot(54)}
    })
}
fn physical_projection(wire:usize) -> Result<usize,String> {
    let owner=match wire/(1<<20) {0=>0,1_810_840=>1,1_810_841=>2,_=>return Err("fixture physical owner".into())};
    let local=match wire%(1<<20) {0=>0,987_467=>1,685_710=>2,_=>return Err("fixture physical local coordinate".into())};
    Ok(owner*8+local)
}
const TEST_DOMAIN:&[u8]=b"c596-h21-upper-score-projected-edge-test-scope-v1";
fn bind_scope(identity:&[u8],public:&Circuit,t:&mut Transcript) {
    t.append_bytes(b"test-scope-H21-public-identity",identity);
    for (physical,projected) in [(0,0),(1_810_840,1),(1_810_841,2)] {
        t.append_u64(b"test-scope-physical-owner",physical);t.append_u64(b"test-scope-projected-owner",projected);
    }
    for (physical,projected) in [(0,0),(987_467,1),(685_710,2)] {
        t.append_u64(b"test-scope-physical-local",physical);t.append_u64(b"test-scope-projected-local",projected);
    }
    t.append_u64(b"test-scope-physical-row",1_810_841*(1<<19)+506_925+17);
    t.append_u64(b"test-scope-projected-row",2);
    sparse::bind(public,0,t);
}
fn visit_projected(terms:&[Term],left:bool,owner:usize,
    sink:&mut dyn FnMut(edge::EdgeTerm)->Result<(),String>) -> Result<(),String> {
    for term in terms {
        if (if left {term.gate.left}else{term.gate.right})/8==owner {
            sink(projected_edge(term.clone(),term.row)?)?;
        }
    }
    Ok(())
}
fn prove_packed_scope(identity:&[u8],public:&Circuit,producer:&Circuit,values:&[Fr])
    ->Result<(GkrProof,InputClaim,edge::EdgeFullStats),String> {
    if values.len()!=32 || values.iter().any(|x|!x.is_zero()&&!x.is_one()) {return Err("Boolean fixture width/value".into());}
    let shape=sparse::validate(producer,0).map_err(|e|e.to_string())?;
    let mut input=edge::PackedEdgeInput::new(8,4,|owner| {
        let mut byte=0u8;for bit in 0..8 {if values[owner*8+bit].is_one() {byte|=1<<bit;}}Ok(vec![byte])
    })?;
    let mut t=Transcript::new(TEST_DOMAIN);
    let (proof,claim,u,v,stats)=edge::prove_edge_terms_strategy_for_test(3,2,0,0,&[0],false,true,true,0,&mut input,
        |left,owner,sink|visit_projected(&producer.terms,left,owner,sink),&mut t,
        |t|bind_scope(identity,public,t),|r,u,v|sparse::wiring(producer,&shape,r,u,v).map_err(|e|e.to_string()),&mut |_|Ok(()))?;
    assert!(!u&&!v);assert_eq!(stats.input_vector_clones,0);
    Ok((proof,claim,stats))
}
fn prove_dense_scope(identity:&[u8],public:&Circuit,producer:&Circuit,values:&[Fr])
    ->Result<(GkrProof,InputClaim),String> {
    let shape=sparse::validate(producer,0).map_err(|e|e.to_string())?;
    let mut t=Transcript::new(TEST_DOMAIN);
    let (proof,claim,u,v)=edge::prove_edge_terms_with_cache_limit_for_test(3,2,0,0,&[0],0,
        |left,owner,sink|visit_projected(&producer.terms,left,owner,sink),
        |owner|Ok(values[owner*8..(owner+1)*8].to_vec()),&mut t,|t|bind_scope(identity,public,t),
        |r,u,v|sparse::wiring(producer,&shape,r,u,v).map_err(|e|e.to_string()))?;
    assert!(!u&&!v);Ok((proof,claim))
}
fn verify_scope(identity:&[u8],binding:&Circuit,wiring:&Circuit,proof:&GkrProof) -> Result<InputClaim,GkrError> {
    let shape=sparse::validate(wiring,0)?;let mut t=Transcript::new(TEST_DOMAIN);
    gkr::verify_with_wiring(&[5],4,proof,&mut t,|t|bind_scope(identity,binding,t),
        |_,r,u,v|sparse::wiring(wiring,&shape,r,u,v))
}

#[test]
#[ignore="one canonical H21 public context; separate 2 GiB/120 s diagnostic trial required"]
fn c596_actual_upper_score_edge_projects_and_rejects_independent_mutants() -> Result<(),String> {
    let (identity,physical)={
        let owned=H21StructuralDiagnostic::compile([0x31;32],[0x42;28],[0x52;32],1,fixture_parameters())?;
        let context=owned.context()?;
        (context.public_bytes.to_vec(),context.roster.upper_score_edge_fixture()?)
    }; // The sole large public context is dropped before the small proof runs.
    let mut terms=Vec::new();
    for term in physical {
        assert_eq!(term.row,1_810_841*(1<<19)+506_925+17);assert_eq!(term.gate.right,0);
        let mut projected=term;projected.row=2;
        projected.gate.left=physical_projection(projected.gate.left)?;
        projected.gate.right=physical_projection(projected.gate.right)?;terms.push(projected);
    }
    terms.sort_by_key(|term|std::cmp::Reverse(term.gate.left));
    let public=Circuit {input_len:32,row_count:4,terms};
    assert_eq!(public.terms.len(),2);
    for (term,left,coefficient) in [(&public.terms[0],18,Fr::one()),(&public.terms[1],9,-Fr::one())] {
        assert_eq!(term.row,2);assert_eq!(term.gate.left,left);assert_eq!(term.gate.right,0);
        assert_eq!([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3],
            [Fr::zero(),coefficient,Fr::zero(),Fr::zero()]);
    }
    let mut values=vec![Fr::zero();32];values[0]=Fr::one();values[9]=Fr::one();values[18]=Fr::one();
    assert_eq!((values[8],values[16]),(Fr::zero(),Fr::zero()));
    let (proof,claim,stats)=prove_packed_scope(&identity,&public,&public,&values)?;
    assert_eq!(stats.left_counts,[0,1,1,0]);assert_eq!(stats.right_counts,[2,0,0,0]);
    let encoded=gkr::encode_proof(&proof)?;assert_eq!(encoded.len(),1216);
    let proof=gkr::decode_dimensions(&[5],&encoded)?;
    assert_eq!(verify_scope(&identity,&public,&public,&proof).map_err(|e|e.to_string())?,claim);
    assert_eq!(gkr::mle(&values,&claim.point).map_err(|e|e.to_string())?,claim.value);
    let mut flipped=proof.clone();flipped.layers[0].rounds[0][0]+=Fr::one();
    assert_eq!(verify_scope(&identity,&public,&public,&flipped),Err(GkrError::SumcheckIdentity));
    let mut omitted=public.clone();omitted.terms.retain(|term|term.gate.left!=9);
    let mut omitted_x=values.clone();omitted_x[18]=Fr::zero();
    let (omitted_proof,omitted_claim,_)=prove_packed_scope(&identity,&public,&omitted,&omitted_x)?;
    assert_eq!(verify_scope(&identity,&public,&omitted,&omitted_proof).map_err(|e|e.to_string())?,omitted_claim);
    assert_eq!(verify_scope(&identity,&public,&public,&omitted_proof),Err(GkrError::TerminalExpression));
    let mut normalized=public.clone();for term in &mut normalized.terms {term.gate.right=16;}
    let (normalized_proof,normalized_claim,_)=prove_packed_scope(&identity,&public,&normalized,&values)?;
    assert_eq!(verify_scope(&identity,&public,&normalized,&normalized_proof).map_err(|e|e.to_string())?,normalized_claim);
    assert_eq!(verify_scope(&identity,&public,&public,&normalized_proof),Err(GkrError::TerminalExpression));
    let mut coefficient=public.clone();coefficient.terms.iter_mut().find(|term|term.gate.left==9)
        .ok_or("projected Upper term")?.gate.c1=-Fr::from(2u64);
    let mut dense=values;dense[18]=Fr::from(2u64);
    let (coefficient_proof,coefficient_claim)=prove_dense_scope(&identity,&public,&coefficient,&dense)?;
    assert_eq!(verify_scope(&identity,&public,&coefficient,&coefficient_proof).map_err(|e|e.to_string())?,coefficient_claim);
    assert_eq!(gkr::mle(&dense,&coefficient_claim.point).map_err(|e|e.to_string())?,coefficient_claim.value);
    assert_eq!(verify_scope(&identity,&public,&public,&coefficient_proof),Err(GkrError::TerminalExpression));
    println!("C596_PROJECTED_CANONICAL_EDGE scope=two_terms projection_only=true gkr_bytes=1216 pcs_verified=false history_token=false");
    Ok(())
}

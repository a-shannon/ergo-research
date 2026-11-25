//! Integration admission and canonical-address controls. No projected proof,
//! replacement full-X fixture, or verifier-success capability is constructed.
use super::*;
use std::sync::OnceLock;
use dory_pcs::{backends::arkworks::ArkGT,primitives::arithmetic::Group};

fn public()->Result<&'static H21StructuralDiagnostic,String>{
    static PUBLIC:OnceLock<Result<H21StructuralDiagnostic,String>>=OnceLock::new();
    PUBLIC.get_or_init(|| {
        use crate::legacy_envelope_map::{LowerSelector,LowerSource,LowerBranch};
        let p=crate::bank53_map::CutDescriptor::eligible08().terminals().map(|terminal|PublicMapParameters {
            terminal,exponent:55,lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},branch:LowerBranch::Pivot(54)}});
        H21StructuralDiagnostic::compile([0x31;32],[0x42;28],[0x52;32],1,p)
    }).as_ref().map_err(Clone::clone)
}
fn roles()->[H21CandidateRole;4]{[H21CandidateRole::Tree,H21CandidateRole::Point,H21CandidateRole::HeightDaa,H21CandidateRole::Metadata]}
fn shape(role:H21CandidateRole)->Result<H21CandidateShape,String>{H21CandidateShape::for_parent(role,&public()?.layouts.parent)}
fn budget()->H21CandidateBudget {H21CandidateBudget {limit_bytes:8usize<<30,
    caller_context_bytes:2usize<<30,visitor_scratch_bytes:128usize<<20,unmeasured_bytes:256usize<<20}}
fn term(row:usize)->Term {Term {row,gate:gkr::Gate {left:0,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}}

#[test]
fn h21_e2e1_candidate_roles_keep_exact_consumer_shapes_and_row_padding()->Result<(),String>{
    for role in roles() {
        let s=shape(role)?;let index=role.index();
        assert_eq!(s.input_log(),codec::INPUT_BITS[index]as usize);
        assert_eq!(s.row_log(),codec::ROW_BITS[index]as usize);
        let rows=1usize<<s.row_log();assert!(s.edge_metadata(rows).is_err());
        for (family,&bits) in s.member_row_bits().iter().enumerate() {
            let base=family<<(s.base_row_bits()+21);
            for row in [base,base+((1usize<<21)-1)*(1usize<<bits)+(1usize<<bits)-1] {
                let (owner,local)=s.edge_metadata(row)?;
                assert_eq!(edge::global_edge_row(owner,local,21,s.base_row_bits(),s.family_bits(),s.member_row_bits())?,row);
                let correct=EdgeTerm {source_slot:owner,family_row:local,term:term(row)};s.check_edge(&correct)?;
                let mut wrong=correct.clone();wrong.source_slot^=1;assert!(s.check_edge(&wrong).is_err());
                let mut wrong=correct;wrong.family_row^=1;assert!(s.check_edge(&wrong).is_err());
            }
            if bits<s.base_row_bits() {
                assert!(s.edge_metadata(base+(1usize<<(bits+21))).is_err(),"member {family} zero extension");
            }
        }
    }
    let tree=shape(H21CandidateRole::Tree)?;
    assert_eq!((tree.base_row_bits(),tree.family_bits(),tree.member_row_bits().len()),(14,6,58));
    for unused in 58..64 {assert!(tree.edge_metadata(unused<<(14+21)).is_err());}
    let composite=shape(H21CandidateRole::HeightDaa)?;
    assert_eq!(composite.member_row_bits(),[6,19]);
    // HeightWork already has a tagged numeric range. Its ROW partition is
    // decoded from that canonical range, not guessed from the input owner.
    let numeric=(1usize<<26)+1001;let (owner,local)=composite.edge_metadata(numeric)?;
    assert_eq!(edge::global_edge_row(owner,local,21,19,1,&[6,19])?,numeric);
    assert!(composite.edge_metadata(1usize<<27).is_err());
    let daa=(1usize<<40)+(1001usize<<19)+393_216;
    let (owner,local)=composite.edge_metadata(daa)?;assert_eq!(owner,1001);
    assert_eq!(edge::global_edge_row(owner,local,21,19,1,&[6,19])?,daa);
    for owner in [0usize,1,crate::h21_snapshot::N,(1<<21)-1] {
        assert_eq!(H21CandidateShape::physical_point_row(owner)?,owner*128+96);
        assert!(H21CandidateShape::physical_point_row(owner)?<(1usize<<28));
    }
    assert!(H21CandidateShape::physical_point_row(1<<21).is_err());
    Ok(())
}

#[test]
fn h21_e2e1_candidate_phase_reservations_are_role_specific_and_checked()->Result<(),String>{
    for role in roles() {
        let s=shape(role)?;let p=edge::h21_candidate_resource_preflight(&s,512,budget())?;
        assert_eq!(p.census_bytes,32usize<<20);assert_eq!(p.high_fold_bytes,256usize<<20);
        assert_eq!(p.expanded_owner_bytes,(1usize<<s.input_bits())*32);
        assert_eq!(p.cache_bytes,4*(1usize<<s.input_bits())/8+512);
        assert_eq!(p.u_weights_bytes,((1usize<<s.input_bits())+(1usize<<21))*32);
        assert!(p.known_peak_bytes>p.high_fold_bytes);
        assert!(edge::h21_candidate_resource_preflight(&s,512,H21CandidateBudget {limit_bytes:p.required_bytes-1,..budget()}).is_err());
        for bad in [H21CandidateBudget {caller_context_bytes:0,..budget()},H21CandidateBudget {visitor_scratch_bytes:0,..budget()},
            H21CandidateBudget {unmeasured_bytes:0,..budget()},H21CandidateBudget {caller_context_bytes:usize::MAX,..budget()},
            H21CandidateBudget {visitor_scratch_bytes:usize::MAX,..budget()},H21CandidateBudget {unmeasured_bytes:usize::MAX,..budget()}] {
            assert!(edge::h21_candidate_resource_preflight(&s,512,bad).is_err());
        }
        assert!(edge::h21_candidate_resource_preflight(&s,usize::MAX,budget()).is_err());
    }
    Ok(())
}

#[test]
fn h21_e2e1_remaining_admission_uses_actual_key_c_and_requested_identity()->Result<(),String>{
    let key=include_bytes!("../fixtures/verifier-keys-v1/log41.vk");
    let c=pcs::encode_commitment(&ArkGT::identity())?;
    let admitted=admit_remaining_public_inputs(b"expected",b"expected",key,&c)?;
    require_h21_role0_diagnostic_key(&admitted)?;
    assert!(admit_remaining_public_inputs(b"wrong",b"expected",&[],&[]).err().ok_or("identity admitted")?.contains("identity"));
    let mut bad=key.to_vec();bad[100]^=1;
    assert!(admit_remaining_public_inputs(b"same",b"same",&bad,&c).is_err());
    assert!(admit_remaining_public_inputs(b"same",b"same",include_bytes!("../fixtures/verifier-keys-v1/log22.vk"),&c).is_err());
    assert!(admit_remaining_public_inputs(b"same",b"same",key,&vec![0xff;384]).is_err());
    fn typed(context:&H21StructuralDiagnosticContext<'_>,role:H21CandidateRole,key:&[u8],c:&[u8],
        source:&packed::UntrustedH21CandidateFile,budget:H21CandidateBudget)->Result<(Vec<u8>,InputClaim),String>{
        context.prove_remaining_untrusted_candidate(role,key,c,source,budget)
    }
    let _entry:fn(&H21StructuralDiagnosticContext<'_>,H21CandidateRole,&[u8],&[u8],&packed::UntrustedH21CandidateFile,H21CandidateBudget)
        ->Result<(Vec<u8>,InputClaim),String>=typed;
    assert!(edge::PackedEdgeInput::new(1<<20,1<<21,|_|Ok(vec![0;1<<17])).is_err());
    Ok(())
}

#[test]
#[ignore="one full public H21 context; canonical endpoint gates only, no proof or witness"]
fn h21_e2e1_actual_remaining_endpoints_keep_canonical_rows_and_fail_closed()->Result<(),String>{
    let context=public()?.context()?;
    for role in roles() {
        let s=context.candidate_role_shape(role)?;
        for (left,owner) in [(true,1001usize),(false,1001),(true,crate::h21_snapshot::N)] {
            let mut count=0usize;
            let result=context.visit_remaining_endpoint(&s,left,owner,&mut |e|{
                s.check_edge(&e)?;let endpoint=if left{e.term.gate.left}else{e.term.gate.right};
                assert_eq!(endpoint/(1usize<<s.input_bits()),owner);
                if role == H21CandidateRole::Point {
                    // First x² term uses the low bit of the last encoded x byte.
                    let wire = (owner << 13) + 1 + 32 * 8;
                    assert_eq!(e.term, Term { row: owner << 14, gate: gkr::Gate {
                        left: wire, right: wire, c0: Fr::zero(), c1: Fr::zero(),
                        c2: Fr::zero(), c3: Fr::one(),
                    }});
                }
                count+=1;Err("isolated canonical endpoint sink".into())
            });
            if role == H21CandidateRole::Point || (role == H21CandidateRole::Metadata && owner == 1001) {
                assert_eq!(count, 1, "active canonical role must reach its sink");
            }
            if role == H21CandidateRole::Metadata && owner == crate::h21_snapshot::N {
                assert_eq!(count, 0, "metadata padding has no endpoints");
            }
            if count==0 {assert!(result.is_ok());}else{assert_eq!(count,1);assert_eq!(result.err().as_deref(),Some("isolated canonical endpoint sink"));}
        }
        let mut calls=0usize;
        assert!(context.visit_remaining_endpoint(&s,true,1<<21,&mut |_|{calls+=1;Ok(())}).is_err());
        assert_eq!(calls,0);
    }
    let s=context.candidate_role_shape(H21CandidateRole::Metadata)?;
    // At an interior owner, the left index consumes its successor's link,
    // while the right index consumes its own. Check a nonzero bit independently.
    for left in [true, false] {
        let requested = 1001usize;
        let link_owner = requested + usize::from(left);
        let bit = 17;
        let bank = crate::header_order::ORDER_OFFSET;
        let expected = Term { row: (link_owner << 12) + (1 << 11) + bit, gate: gkr::Gate {
            left: ((link_owner - 1) << 20) + bank + 256 + bit,
            right: (link_owner << 20) + bank + bit,
            c0: Fr::zero(), c1: Fr::one(), c2: -Fr::one(), c3: Fr::zero(),
        }};
        let (mut count, mut hits) = (0usize, 0usize);
        context.visit_remaining_endpoint(&s, left, requested, &mut |edge| {
            if edge.term == expected {
                assert_eq!((edge.source_slot, edge.family_row), (link_owner, (1 << 11) + bit));
                hits += 1;
            }
            count += 1;
            Ok(())
        })?;
        assert_eq!((count, hits), (2081 + 256, 1));
    }
    // The metadata Global0 inverse is bounded to the genesis/last sources.
    let mut last=false;
    context.visit_remaining_endpoint(&s,false,0,&mut |e|{s.check_edge(&e)?;if e.source_slot==crate::h21_snapshot::N-1 {last=true;}Ok(())})?;
    assert!(last);
    Ok(())
}

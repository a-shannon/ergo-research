//! H21 role5 descriptor, admission and allocation-free resource controls.
//! Existing N3/H50 arithmetic evidence is reused; no new GKR fixture is made.
use super::*;
use crate::{header_adjacency_layout::HeaderAdjacencyLayout,
    segment_adjacency::linear_for_test as linear};
use dory_pcs::{backends::arkworks::ArkGT,primitives::arithmetic::Group};
use std::sync::OnceLock;

const KEY41:&[u8]=include_bytes!("../fixtures/verifier-keys-v1/log41.vk");
fn layout() -> Result<&'static HeaderAdjacencyLayout,String> {
    static LAYOUT:OnceLock<Result<HeaderAdjacencyLayout,String>>=OnceLock::new();
    LAYOUT.get_or_init(||HeaderAdjacencyLayout::compile(1_827_840,21,[0;32],[0x52;32]))
        .as_ref().map_err(Clone::clone)
}
fn budget() -> linear::H21Role5Budget {
    linear::H21Role5Budget {limit_bytes:8usize<<30,caller_context_bytes:1600usize<<20,unmeasured_bytes:128usize<<20}
}
fn commitment() -> Vec<u8> {pcs::encode_commitment(&ArkGT::identity()).unwrap()}
fn error<T>(result:Result<T,String>) -> String {match result {Ok(_)=>panic!("expected rejection"),Err(error)=>error}}
fn state(t:&Transcript) -> (u64,u64,u64) {(t.challenges(),t.raw_queries(),t.bytes_absorbed())}

#[test]
fn c597_h21_role5_descriptor_binds_canonical_layout_and_keeps_old_admissions() -> Result<(),String> {
    let layout=layout()?;let descriptor=layout.h21_role5_descriptor_for_test()?;
    descriptor.validate_h21(1usize<<41)?;descriptor.require_h21_layout(layout)?;
    assert_eq!((descriptor.active(),descriptor.padded(),descriptor.local_input(),descriptor.local_row()),
        (1_827_840,1<<21,20,9));
    assert_eq!((descriptor.ids(),descriptor.chunk_bits(),descriptor.input_log(),descriptor.row_log()),(256,16,41,30));
    assert_eq!((descriptor.input_len(),descriptor.row_count()),(1usize<<41,1usize<<30));
    assert_eq!(layout.term_count(),(1_827_840+1)*256);
    assert_eq!(descriptor.parent().len(),256);assert_eq!(descriptor.digest().len(),256);
    let mut wires=descriptor.parent().to_vec();wires.extend_from_slice(descriptor.digest());
    assert!(wires.iter().all(|wire|*wire<1<<20));wires.sort_unstable();assert!(!wires.windows(2).any(|p|p[0]==p[1]));
    for bit in 0..256 {
        assert_eq!(descriptor.start_bit(bit),Fr::from(0u64));
        assert_eq!(descriptor.tip_bit(bit),Fr::from(((0x52u8>>(bit%8))&1)as u64));
    }
    assert!(descriptor.validate_h21(1usize<<32).is_err());
    assert!(descriptor.validate_h21((1usize<<41)-1).is_err());
    assert!(descriptor.validate_h21(usize::MAX).is_err());
    let detached=(*layout).clone();assert!(descriptor.require_h21_layout(&detached).is_err());
    assert!(descriptor.validate(descriptor.input_len(),16).is_err());
    assert!(linear::preflight_for_test(&descriptor,0).is_err());
    let small=HeaderAdjacencyLayout::compile(3,2,[0;32],[0x52;32])?;
    let old=small.linear_descriptor_for_test()?;old.validate(old.input_len(),old.chunk_bits())?;
    assert!(small.h21_role5_descriptor_for_test().is_err());assert!(old.validate_h21(1usize<<41).is_err());
    drop(old);drop(small);
    let historical=HeaderAdjacencyLayout::compile(3073,12,[0;32],[0x52;32])?;
    assert!(historical.h21_role5_descriptor_for_test().is_err());drop(historical);
    let wrong_start=HeaderAdjacencyLayout::compile(1_827_840,21,[1;32],[0x52;32])?;
    assert!(wrong_start.h21_role5_descriptor_for_test().is_err());
    Ok(())
}

#[test]
fn c597_h21_role5_phase_plan_checks_exact_payloads_budget_and_overflow() -> Result<(),String> {
    let descriptor=layout()?.h21_role5_descriptor_for_test()?;
    let plan=linear::h21_role5_resource_preflight(&descriptor,1usize<<41,budget())?;
    assert_eq!(plan.chunks,1usize<<25);assert_eq!(plan.chunk_bytes,2usize<<20);
    assert_eq!(plan.parent_cache_bytes,1_827_840*32);
    assert_eq!(plan.owner_weights_bytes,((1usize<<9)+(1usize<<21))*32);
    assert_eq!(plan.high_vectors_bytes,3usize<<30);
    assert_eq!(plan.control_bytes,256);
    assert_eq!(plan.known_peak_bytes,*plan.phase_bounds.iter().max().unwrap());
    assert!(plan.known_peak_bytes>plan.high_vectors_bytes);
    assert_eq!(plan.phase_bounds[1]-plan.phase_bounds[2],plan.parent_cache_bytes,
        "the parent cache is dropped before V");
    assert!(plan.phase_bounds[0]<plan.phase_bounds[1]);assert!(plan.phase_bounds[3]<plan.phase_bounds[2]);
    assert_eq!(plan.required_bytes,plan.known_peak_bytes+budget().caller_context_bytes+budget().unmeasured_bytes+plan.control_bytes);
    let exact=linear::h21_role5_resource_preflight(&descriptor,1usize<<41,
        linear::H21Role5Budget {limit_bytes:plan.required_bytes,..budget()})?;
    assert_eq!(exact,plan);
    let extra=linear::h21_role5_resource_preflight(&descriptor,1usize<<41,
        linear::H21Role5Budget {caller_context_bytes:budget().caller_context_bytes+1,..budget()})?;
    assert_eq!(extra.required_bytes,plan.required_bytes+1);assert_eq!(extra.known_peak_bytes,plan.known_peak_bytes);
    for limit in [0,3usize<<30,plan.required_bytes-1] {
        assert!(linear::h21_role5_resource_preflight(&descriptor,1usize<<41,
            linear::H21Role5Budget {limit_bytes:limit,..budget()}).is_err());
    }
    for invalid in [linear::H21Role5Budget {caller_context_bytes:0,..budget()},
        linear::H21Role5Budget {unmeasured_bytes:0,..budget()},
        linear::H21Role5Budget {caller_context_bytes:usize::MAX,..budget()},
        linear::H21Role5Budget {unmeasured_bytes:usize::MAX,..budget()}] {
        assert!(linear::h21_role5_resource_preflight(&descriptor,1usize<<41,invalid).is_err());
    }
    assert!(linear::h21_role5_resource_preflight(&descriptor,1usize<<32,budget()).is_err());
    // These phase payloads and declared margins qualify no process RSS/cap.
    Ok(())
}

#[test]
fn c597_h21_role5_actual_public_input_admission_is_strict_before_activity() -> Result<(),String> {
    let c=commitment();let key=admit_h21_role5_public_inputs(b"requested",b"requested",KEY41,&c)?;
    require_h21_role0_diagnostic_key(&key)?;assert_eq!(key.log_n(),41);
    let operations=std::cell::Cell::new(0usize);
    let caller=Transcript::new(b"c597-role5-admission-order-only");let before=state(&caller);
    let refused=|requested:&[u8],expected:&[u8],key:&[u8],c:&[u8]| {
        let result=(|| {let admitted=admit_h21_role5_public_inputs(requested,expected,key,c)?;
            operations.set(operations.get()+1);Ok(admitted)})();
        let message=error(result);assert_eq!(operations.get(),0);assert_eq!(state(&caller),before);message
    };
    let identity=refused(b"requested-A",b"requested-B",&[],&[]);
    assert!(identity.contains("identity"),"identity must reject before invalid key/C: {identity}");
    let mut wrong=KEY41.to_vec();wrong[100]^=1;
    for bytes in [wrong,KEY41[..KEY41.len()-1].to_vec(),[KEY41,&[0u8]].concat(),
        include_bytes!("../fixtures/verifier-keys-v1/log22.vk").to_vec()] {
        assert_eq!(refused(b"same",b"same",&bytes,&c),error(verifier_key::admit(41,&bytes)));
    }
    for bytes in [vec![0xff;384],c[..c.len()-1].to_vec(),[c.as_slice(),&[0u8]].concat()] {
        assert_eq!(refused(b"same",b"same",KEY41,&bytes),error(pcs::decode_commitment(&bytes)));
    }
    fn typed_entry(context:&H21StructuralDiagnosticContext<'_>,key:&[u8],commitment:&[u8],
        candidate:&packed::UntrustedH21CandidateFile,budget:linear::H21Role5Budget)
        ->Result<(Vec<u8>,InputClaim),String> {
        context.prove_role5_untrusted_candidate(key,commitment,candidate,budget)
    }
    let _entry:fn(&H21StructuralDiagnosticContext<'_>,&[u8],&[u8],&packed::UntrustedH21CandidateFile,
        linear::H21Role5Budget)->Result<(Vec<u8>,InputClaim),String>=typed_entry;
    Ok(())
}

#[test]
fn c597_h21_role5_actual_audit_boundary_and_legacy_512_guard_are_distinct() -> Result<(),String> {
    let descriptor=layout()?.h21_role5_descriptor_for_test()?;
    let plan=linear::h21_role5_resource_preflight(&descriptor,1usize<<41,budget())?;
    // The helper exercises the actual Audit observer at exact room, then
    // checks a one-byte excess; it allocates none of the phase payloads.
    let stats=linear::h21_role5_audit_controls_for_test(&descriptor,budget())?;
    assert_eq!(stats.scoped_limit_bytes,budget().limit_bytes);
    assert_eq!(stats.preflight_bound_bytes,plan.required_bytes);
    assert_eq!(stats.retained_capacity_bytes,budget().caller_context_bytes+budget().unmeasured_bytes+plan.control_bytes);
    assert_eq!(stats.fixed_typed_bound_bytes,65_536);
    assert_eq!(stats.combined_bound_peak_bytes[1],plan.required_bytes);
    assert_eq!(stats.read_calls,[0;4]);assert_eq!(stats.reconstructed_fields,[0;4]);
    assert!(!stats.helper_bounds_measured);
    assert_eq!(linear::LIMIT,512usize<<20);
    linear::historical50_resource_controls_for_test()?;
    Ok(())
}

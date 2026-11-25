//! Small real packed-producer fixtures only. These tests execute no native
//! H21 frame and establish no owner845759 runtime or shared PCS evidence.
use super::*;
use crate::h21_work_local_source::{self as local,LocalPublisher,NativeWorkLocalPublisher,Role};
use std::sync::OnceLock;

pub(super) fn fixture()->(&'static WorkTreeHistoryPlan,&'static NativePrefix) {
    static INPUT:OnceLock<NativePrefix>=OnceLock::new();
    static PLAN:OnceLock<WorkTreeHistoryPlan>=OnceLock::new();
    let input=INPUT.get_or_init(||{
        let pack:serde_json::Value=serde_json::from_str(include_str!(
            "../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let raws=(0..3).map(|i|{
            let hex=pack["networks"]["mainnet"]["source_headers_hex"][i].as_str().unwrap();
            Ok(hex.as_bytes().chunks_exact(2).map(|p|u8::from_str_radix(
                std::str::from_utf8(p).unwrap(),16).unwrap()).collect())
        });
        NativePrefix::from_raw_iter(3,raws).unwrap()
    });
    let plan=PLAN.get_or_init(||WorkTreeHistoryPlan::compile(3,2,input.root(),input.total_be28()).unwrap());
    (plan,input)
}

#[test]
fn c203_upper_publication_is_the_real_packed_operand_and_retains_canonical_local_custody() {
    let (plan,input)=fixture();let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    for owner in [0,1] {
        let lease=producer.work_local_lease(owner).unwrap();
        let token=producer.work_upper_publication(owner,&lease).unwrap();
        assert_eq!(token.retained_counts(),(3265,1184));
        assert_eq!(token.terms,lease.terms);assert_eq!(token.operands,lease.operands);
        let actual=token.checked_upper(input.root(),input.total_be28(),input.profile(),&lease.parent.cut,owner).unwrap();
        assert_eq!(actual.len(),224);
        for &(wire,value) in actual {
            let local=wire%WIDTH;
            assert_eq!(value,Fr::from(((lease.row.bytes[local/8]>>(local%8))&1)as u64));
            assert_eq!(value,Fr::from(producer.exports.bit(wire).unwrap()as u64));
        }
        assert!(producer.native_work_local_lease_for_owner(owner).is_err(),"no small-fixture native authority");
    }
}
fn copy<'a>(x:&WorkLocalLease<'a>)->WorkLocalLease<'a>{
    WorkLocalLease{source:x.source,parent:x.parent.clone(),owner:x.owner,height:x.height,
        row:x.row.clone(),terms:x.terms.clone(),operands:x.operands.clone(),d:x.d.clone()}
}
fn rejected(producer:&NativeOwnerProducer<'_>,owner:usize,lease:&WorkLocalLease<'_>,needle:&str){
    let mut publisher=LocalPublisher::new(producer,owner).unwrap();
    let error=publisher.publish(lease).unwrap_err();assert!(error.contains(needle),"{error}");
    assert_eq!(publisher.state_counts(),(false,0,0),"failure must leave publication empty");
}

#[test]
fn c195_work_local_small_packed_source_census_and_strict_h21_gate(){
    let (plan,input)=fixture();let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    for owner in [0,1]{
        let lease=producer.work_local_lease(owner).unwrap();
        assert_eq!(lease.terms.len(),3265);assert_eq!(lease.operands.len(),1184);assert_eq!(lease.d.len(),224);
        assert_eq!(lease.parent.root,input.root());assert_eq!(lease.parent.total,input.total_be28());
        assert_eq!(lease.parent.profile,input.profile());assert_eq!(lease.height,owner+2);
        for &(wire,value) in &lease.operands{
            let w=wire%WIDTH;assert_eq!(value,Fr::from(((lease.row.bytes[w/8]>>(w%8))&1)as u64));
        }
        let mut publisher=LocalPublisher::new(&producer,owner).unwrap();
        assert_eq!(publisher.publish(&lease).unwrap(),(3265,1435));
        assert_eq!(publisher.state_counts(),(true,3265,1184));
        assert!(publisher.publish(&lease).unwrap_err().contains("replay"));
        assert_eq!(publisher.state_counts(),(true,3265,1184));
    }
    assert!(producer.work_local_lease(plan.descriptor().genuine).is_err());
    assert!(producer.work_local_lease(plan.slots()).is_err());
    assert!(LocalPublisher::new(&producer,plan.descriptor().genuine).is_err());
    assert!(producer.native_work_local_lease().is_err(),"small fixture grants no native lease");
    assert!(NativeWorkLocalPublisher::new(&producer).is_err(),"small fixture grants no H21 publication");
}

#[test]
fn c195_work_local_every_canonical_term_field_and_occurrence_is_exact(){
    let (plan,input)=fixture();let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    let good=producer.work_local_lease(0).unwrap();
    for kind in 0..13 {
        let mut bad=copy(&good);
        match kind {
            0=>{bad.terms.remove(0);},
            1=>bad.terms.push(bad.terms[0].clone()),
            2=>{let row=bad.terms[0].term.row;bad.terms.retain(|t|t.term.row!=row);},
            3=>{let row=bad.terms[0].term.row;let extra=bad.terms.iter().filter(|t|t.term.row==row).cloned().collect::<Vec<_>>();bad.terms.extend(extra);},
            4=>bad.terms[0].term.row+=1,
            5=>bad.terms[0].term.gate.left+=1,
            6=>bad.terms[0].term.gate.right+=1,
            7=>bad.terms[0].term.gate.c0+=Fr::one(),
            8=>bad.terms[0].term.gate.c1+=Fr::one(),
            9=>bad.terms[0].term.gate.c2+=Fr::one(),
            10=>bad.terms[0].term.gate.c3+=Fr::one(),
            11=>bad.terms[0].role=Role::WorkLocal{owner:1,height:2},
            12=>bad.terms[0].role=Role::WorkLocal{owner:0,height:3},
            _=>unreachable!(),
        }
        rejected(&producer,0,&bad,"canonical tagged term occurrences");
    }
    // Removing a term whose evaluated contribution is zero still fails census.
    let mut bad=copy(&good);let i=bad.terms.iter().position(|t|{
        let g=&t.term.gate;g.c0.is_zero()&&g.c2.is_zero()&&g.c3.is_zero()
            && good.operands.iter().any(|&(w,v)|w==g.left&&v.is_zero())
    }).unwrap();bad.terms.remove(i);
    rejected(&producer,0,&bad,"canonical tagged term occurrences");
}

#[test]
fn c195_work_local_parent_owner_and_source_row_identity_are_atomic(){
    let (plan,input)=fixture();let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    let good=producer.work_local_lease(0).unwrap();
    for kind in 0..8{
        let mut bad=copy(&good);match kind {
            0=>bad.parent.root[0]^=1,1=>bad.parent.total[0]^=1,2=>bad.parent.profile[0]^=1,
            3=>bad.parent.cut=crate::bank53_map::CutDescriptor::diagnostic08().canonical_identity(),
            4=>bad.parent.headers+=1,5=>bad.parent.slots+=1,6=>bad.owner+=1,7=>bad.height+=1,_=>unreachable!(),
        }rejected(&producer,0,&bad,"parent/cut/owner/height");
    }
    let map=crate::legacy_envelope_map::Map::new(plan.headers(),plan.slot_log(),64).unwrap();
    for kind in 0..8{
        let mut bad=copy(&good);match kind {
            0=>bad.row.owner+=1,1=>bad.row.root[0]^=1,2=>bad.row.total[0]^=1,
            3=>{bad.row.bytes.pop();},4=>bad.row.map_context=Some(0),
            5=>bad.row.class=crate::daa_history_roster::OwnerClass::Padding,
            6=>bad.row.max_binding=Some([0x51;32]),
            7=>{assert!(bad.row.map_context.is_none());bad.row.map_binding=Some(map.binding());},
            _=>unreachable!(),
        }rejected(&producer,0,&bad,"packed source row identity");
    }
    let mut bad=copy(&good);bad.row.legacy_binding=Some([0x61;32]);
    rejected(&producer,0,&bad,"legacy packed source");
}

#[test]
fn c195_work_local_valid_max_adapted_source_rejected_before_mint_or_publication(){
    let (plan,input)=fixture();
    let adapter=crate::max_header_adapter::MaxHeaderAdapter::compile(plan).unwrap();
    adapter.check_parent(plan).unwrap();
    let adapted=NativeOwnerProducer::new_for_max_history(plan,input,&adapter).unwrap();
    assert!(0<plan.descriptor().genuine);
    let error=adapted.work_local_parent(0).unwrap_err();
    assert_eq!(error,"Work LOCAL genuine unadapted source");
    let error=match adapted.work_local_lease(0){Err(error)=>error,Ok(_)=>panic!("adapted source minted local lease")};
    assert_eq!(error,"Work LOCAL genuine unadapted source");
    // Constructor failure leaves no destination to mutate; no unchecked stage
    // or adapted lease is introduced to test a state that this API excludes.
    let error=match LocalPublisher::new(&adapted,0){Err(error)=>error,Ok(_)=>panic!("adapted source created publisher")};
    assert_eq!(error,"Work LOCAL genuine unadapted source");
    let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    let empty=LocalPublisher::new(&producer,0).unwrap();
    let mut rebound=producer.work_local_lease(0).unwrap();rebound.source=&adapted;
    let error=adapted.require_work_local_lease(0,&rebound).unwrap_err();
    assert_eq!(error,"Work LOCAL genuine unadapted source");
    assert_eq!(empty.state_counts(),(false,0,0));
    // A real legacy-adapted source cannot be constructed from this bounded
    // fixture: the unchanged adapter requires N3073/S12 before construction.
    let error=match crate::legacy_native_adapter::LegacyNativeAdapter::compile(plan,input){
        Err(error)=>error,Ok(_)=>panic!("small fixture constructed legacy adapter")};
    assert_eq!(error,"legacy native adapter requires N3073/S12");
    assert_eq!(empty.state_counts(),(false,0,0));
}

#[test]
fn c195_work_local_complete_active_operands_and_d_are_bound_to_packed_native_source(){
    let (plan,input)=fixture();let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    let good=producer.work_local_lease(0).unwrap();
    let mut bad=copy(&good);bad.operands.pop();rejected(&producer,0,&bad,"complete operand census");
    let mut bad=copy(&good);bad.operands.push(bad.operands[0]);rejected(&producer,0,&bad,"complete operand census");
    let mut bad=copy(&good);bad.operands[1]=bad.operands[0];rejected(&producer,0,&bad,"active operand");
    for i in [0,31,32,255,256,479,480,703,704,927,928,1183]{
        let mut bad=copy(&good);bad.operands[i].1=Fr::one()-bad.operands[i].1;
        rejected(&producer,0,&bad,"active operand");
    }
    let mut bad=copy(&good);let wire=bad.operands[0].0%WIDTH;bad.row.bytes[wire/8]^=1<<(wire%8);
    bad.operands[0].1=Fr::one()-bad.operands[0].1;
    rejected(&producer,0,&bad,"active operand"); // coordinated packed+projection mutation
    for kind in 0..3{
        let mut bad=copy(&good);match kind{0=>bad.d[0].1=Fr::one()-bad.d[0].1,
            1=>bad.d[0].0+=1,2=>{bad.d.pop();},_=>unreachable!()};
        rejected(&producer,0,&bad,"native D projection");
    }
}

#[test]
fn c195_work_local_same_values_different_source_rejected_and_failure_retry_is_clean(){
    let (plan,input)=fixture();let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    let other=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    let good=producer.work_local_lease(0).unwrap();let identical=other.work_local_lease(0).unwrap();
    assert_eq!(good.row.bytes,identical.row.bytes);assert_eq!(good.terms,identical.terms);
    rejected(&producer,0,&identical,"exact producer source identity");
    let raw=(1..=3).map(|h|Ok(input.raw(h).unwrap().to_vec()));
    let distinct=NativePrefix::from_raw_iter(3,raw).unwrap();
    let another=NativeOwnerProducer::new_for_history(plan,&distinct).unwrap();
    rejected(&producer,0,&another.work_local_lease(0).unwrap(),"exact producer source identity");
    let mut publisher=LocalPublisher::new(&producer,0).unwrap();
    let mut bad=copy(&good);bad.terms.pop();assert!(publisher.publish(&bad).is_err());
    assert_eq!(publisher.state_counts(),(false,0,0));assert!(publisher.publish(&good).is_ok());
    assert!(publisher.publish(&good).is_err());
}

#[test]
fn c195_work_local_residual_checker_rejects_missing_nonboolean_duplicate_and_false_rows(){
    let (plan,input)=fixture();let producer=NativeOwnerProducer::new_for_history(plan,input).unwrap();
    let good=producer.work_local_lease(0).unwrap();
    assert_eq!(local::require_zero_residual(&good.terms,&good.operands).unwrap(),1435);
    let mut missing=good.operands.clone();missing.remove(0);
    assert!(local::require_zero_residual(&good.terms,&missing).unwrap_err().contains("missing active operand"));
    let mut duplicate=good.operands.clone();duplicate.push(duplicate[0]);
    assert!(local::require_zero_residual(&good.terms,&duplicate).unwrap_err().contains("duplicate/nonboolean"));
    let mut nonboolean=good.operands.clone();nonboolean[0].1=Fr::from(2u64);
    assert!(local::require_zero_residual(&good.terms,&nonboolean).unwrap_err().contains("duplicate/nonboolean"));
    let mut changed=good.operands.clone();changed[32].1=Fr::one()-changed[32].1;
    assert!(local::require_zero_residual(&good.terms,&changed).unwrap_err().contains("nonzero per-row"));
}

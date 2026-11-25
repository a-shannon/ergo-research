use super::*;
use std::{fs,path::PathBuf,io::Write,time::Instant};

fn fixture()->(&'static WorkTreeHistoryPlan,&'static NativePrefix,VerifiedBundleIdentity){
    let dir=PathBuf::from(std::env::var_os("NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR").expect("pinned fixture directory"));
    let native=crate::packed_owner_assembly_tests::legacy_prefix_for_test();
    let parent=crate::packed_owner_assembly_tests::legacy_assembly_plan_for_test();
    let id=VerifiedBundleIdentity::from_bundle(parent,native,&fs::read(dir.join("mainnet-prefix-first-3073-u32le-v1.bin")).unwrap(),
        &fs::read(dir.join("manifest.json")).unwrap()).unwrap();
    (parent,native,id)
}
fn source<'a>(p:&'a WorkTreeHistoryPlan,n:&'a NativePrefix,id:VerifiedBundleIdentity,c:usize)->CutMapSource<'a>{
    CutMapSource::new(p,n,id,SealedCutProfile::Bounded,c).unwrap()
}
fn oracle(n:&NativePrefix,i:Import)->BigInt{
    match i.kind {
        Kind::Difficulty=>BigInt::from(crate::work_tree_work::native_decode(n.compact_n_bits(i.owner as usize+2).unwrap()).unwrap()),
        Kind::Timestamp=>BigInt::from(n.timestamp(i.owner as usize+1).unwrap()),
    }
}
fn integer(b:&OwnerMapBatch,i:Import)->BigInt{
    (0..i.width).fold(BigInt::from(0u8),|n,k|if b.reads[&(i.owner as usize*WIDTH+i.local+k)].is_one(){n+(BigInt::from(1u8)<<k)}else{n})
}
fn atomic_reject(s:&CutMapSource,b:OwnerMapBatch){let mut d=Destination::default();let old=d.clone();
    assert!(s.publish(&mut d,b).is_err());assert_eq!(d,old);}

#[test]
fn bounded_q2_e48_profile_matches_real_native_map(){
    let (p,n,id)=fixture();let s=source(p,n,id,0);let b=s.stage_owner(3007).unwrap();
    let expected=BigInt::from(199576266412041u64);
    let bound=(0..92).fold(BigInt::from(0u8),|v,k|{
        if b.helpers[&(3007*WIDTH+677223+k)].is_one(){v+(BigInt::from(1u8)<<k)}else{v}
    });
    assert_eq!(bound,expected);assert!(bound>(BigInt::from(1u8)<<47usize));
    assert!(bound<(BigInt::from(1u8)<<48usize));
    assert!(b.helpers[&(3007*WIDTH+677223+45)].is_one());
    assert!(!b.helpers[&(3007*WIDTH+677223+46)].is_one());
    assert!(b.helpers[&(3007*WIDTH+677223+47)].is_one());
    let parameters=SealedCutProfile::Bounded.parameters(0).unwrap();
    assert_eq!(parameters.e,48);assert_eq!(parameters.lower,LowerSelector{
        source:LowerSource::LegacyBound{q:2},branch:LowerBranch::Pivot(45)});
    let pivot_row=3007*524288+477074+10123;
    assert!(b.terms.iter().any(|t|t.row==pivot_row&&t.gate.left==3007*WIDTH+677223+45&&t.gate.c1.is_one()));
    assert!(residuals(&b).unwrap().values().all(|v|v.is_zero()));s.validate(&b).unwrap();
    let mut destination=Destination::default();s.publish(&mut destination,b).unwrap();
    println!("C129B_Q2_PASS owner=3007 context=0 B=199576266412041 e=48 lower_q=2 pivot=45 residuals=zero");
}

#[test]
fn actual_native_parent_two_cuts_real_map_owners(){
    let (p,n,id)=fixture();let mut d=Destination::default();
    for c in 0..2 {let s=source(p,n,id.clone(),c);assert_eq!(s.binding().source.root,p.descriptor().root);
        assert_eq!(s.binding().cut(),[3073,3072][c]);assert_eq!(s.binding().source_headers(),3073);
        assert_eq!(s.binding().source_root(),n.root());assert_eq!(s.binding().source_total(),n.total_be28());
        assert_eq!(s.binding().map_binding(),&s.map.binding());assert_eq!(s.binding().context(),c);
        for owner in [0,959,1983,3007,3070,3071,3072,4095] {
            let b=s.stage_owner(owner).unwrap();s.validate(&b).unwrap();
            for imp in &b.imports{assert_eq!(integer(&b,*imp),oracle(n,*imp),"context{c} owner{owner} {imp:?}");}
            let (inputs,_)=s.imports(owner,&b.imports).unwrap();let direct=s.map.generate(owner as u64,&inputs).unwrap();
            for k in 0..5757{assert_eq!(b.helpers[&(owner*WIDTH+671744+c*8192+k)].is_one(),direct.bits[k]);}
            let before=bank53_map::map_owner_terms(&s.map,owner as u64,c).unwrap();assert_eq!(before.len(),b.terms.len());
            for (a,z) in before.iter().zip(&b.terms){assert_eq!(a.gate,z.gate);assert_eq!(*z,relocate(Family::Map(c),owner,a).unwrap());}
            println!("C129A_OWNER context={c} owner={owner} imports={} terms={} helpers={}",b.imports.len(),b.terms.len(),b.helpers.len());
            s.publish(&mut d,b).unwrap();let old=d.clone();assert!(s.publish_owner(&mut d,owner).is_err());assert_eq!(d,old);
        }
        let b=s.stage_owner(3071).unwrap();assert_eq!(b.imports.iter().any(|i|i.kind==Kind::Difficulty),c==0);
    }assert_eq!(d.owners.len(),16);
}

#[test]
fn exact_import_membership_offsets_and_active_foreign_faults(){
    let (p,n,id)=fixture();let s=source(p,n,id,1);let b=s.stage_owner(3007).unwrap();s.validate(&b).unwrap();
    let ds=b.imports.iter().filter(|i|i.kind==Kind::Difficulty).map(|i|i.owner).collect::<Vec<_>>();
    let ts=b.imports.iter().filter(|i|i.kind==Kind::Timestamp).map(|i|i.owner).collect::<Vec<_>>();
    assert_eq!(ds,vec![2046,3006,3007]);assert_eq!(ts,vec![1023,2047,3007]);
    let timestamp=*b.imports.iter().find(|i|i.kind==Kind::Timestamp&&i.owner==3007).unwrap();
    for foreign in [3071,3072] {let mut imports=b.imports.clone();let i=imports.iter_mut().find(|i|**i==timestamp).unwrap();i.owner=foreign;
        // Both coordinates exist in the source parent; cut-valid alone is insufficient.
        assert!(s.exports.bit(foreign as usize*WIDTH+timestamp.local).is_ok());
        assert_eq!(s.imports(3007,&imports).err().unwrap(),"exact destination import census");
        let index=b.terms.iter().position(|t|t.gate.left==3007*WIDTH+timestamp.local
            &&(!t.gate.c1.is_zero()||!t.gate.c3.is_zero())).expect("active timestamp operand");
        let mut bad=b.clone();bad.terms[index].gate.left=foreign as usize*WIDTH+timestamp.local;atomic_reject(&s,bad);
    }
    // Numeric perturbation of a real read, using an equation with an active coefficient.
    let mut bad=b.clone();let address=3007*WIDTH+timestamp.local;
    let old=bad.reads[&address];*bad.reads.get_mut(&address).unwrap()=Fr::one()-old;
    assert!(residuals(&bad).unwrap().values().any(|r|!r.is_zero()));atomic_reject(&s,bad);
    for imp in &b.imports {
        let expected=imp.owner+if imp.kind==Kind::Difficulty{2}else{1};
        let wrong=imp.owner+if imp.kind==Kind::Difficulty{1}else{2};
        assert_ne!(expected,wrong);assert_eq!(integer(&b,*imp),oracle(n,*imp));
        // Wrong height maps back to a different typed physical owner, even if D is equal.
        let mut mutant=*imp;mutant.owner=wrong-if imp.kind==Kind::Difficulty{2}else{1};
        assert_ne!(s.map.input_index(*imp,0).unwrap(),s.map.input_index(mutant,0).unwrap());
        let mut imports=b.imports.clone();*imports.iter_mut().find(|x|**x==*imp).unwrap()=mutant;
        assert!(s.imports(3007,&imports).is_err());
    }
    let mut duplicate=b.imports.clone();duplicate.push(timestamp);assert!(s.imports(3007,&duplicate).is_err());
    let mut missing=b.imports.clone();missing.pop();assert!(s.imports(3007,&missing).is_err());
    for axis in 0..3 {let mut imports=b.imports.clone();match axis{0=>imports[0].local+=1,1=>imports[0].width-=1,
        _=>imports[0].kind=if imports[0].kind==Kind::Timestamp{Kind::Difficulty}else{Kind::Timestamp}};
        assert_ne!(imports,b.imports);assert!(s.imports(3007,&imports).is_err());}
}

#[test]
fn sealed_identity_profiles_and_native_plan_boundaries(){
    let (p,n,id)=fixture();
    for field in 0..5 {let mut bad=id.clone();match field{0=>bad.root[0]^=1,1=>bad.total[0]^=1,2=>bad.headers-=1,
        3=>bad.profiles.push(0),_=>bad.native_profile[0]^=1};assert!(CutMapSource::new(p,n,bad,SealedCutProfile::Bounded,1).is_err());}
    assert!(CutMapSource::new_checked(p,n,id.clone(),SealedCutProfile::Bounded,1,3071).is_err());
    assert!(CutMapSource::new_checked(p,n,id.clone(),SealedCutProfile::Bounded,1,3074).is_err());
    assert!(CutMapSource::new(p,n,id.clone(),SealedCutProfile::Bounded,2).is_err());
    let h=SealedCutProfile::H21Metadata.parameters(1).unwrap();assert_eq!((h.source_n,h.h,h.cut,h.e),(1827840,21,1827775,55));
    assert!(CutMapSource::new(p,n,id.clone(),SealedCutProfile::H21Metadata,1).is_err());
    let mut s=source(p,n,id.clone(),1);let expected=s.map.clone();
    s.map=Map::new_modern_global_u(3072,12,48).unwrap();assert!(s.stage_owner(3007).is_err());s.map=expected;
    let expected=s.map.clone();s.map=Map::new_modern_global_u_selected_lower(3072,12,48,LowerSelector{
        source:LowerSource::LegacyBound{q:2},branch:LowerBranch::Pivot(46)}).unwrap();assert!(s.stage_owner(3007).is_err());s.map=expected;
    // Old packed guards are unchanged source evidence. Their N3073 dispatch
    // rejection precedes the cut comparison, so no packed-producer claim here.
    let dir=PathBuf::from(std::env::var_os("NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR").unwrap());
    let bytes=fs::read(dir.join("mainnet-prefix-first-3073-u32le-v1.bin")).unwrap();let manifest=fs::read(dir.join("manifest.json")).unwrap();
    let mut corrupt=bytes.clone();corrupt[10]^=1;assert!(VerifiedBundleIdentity::from_bundle(p,n,&corrupt,&manifest).is_err());
    let mut corrupt=manifest.clone();corrupt[10]^=1;assert!(VerifiedBundleIdentity::from_bundle(p,n,&bytes,&corrupt).is_err());
}

#[derive(Clone,Copy)]
enum ActualPlanFault {Root,Total,Count}

fn reject_actual_plan(fault:ActualPlanFault){
    // One authentic fixture and one deliberately changed plan in this test.
    // No NativeOwnerProducer, DAA roster, or second invalid plan is built.
    let (parent,native,_)=fixture();validate_native_plan_input(parent,native).unwrap();
    let dir=PathBuf::from(std::env::var_os("NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR").unwrap());
    let bytes=fs::read(dir.join("mainnet-prefix-first-3073-u32le-v1.bin")).unwrap();
    let manifest=fs::read(dir.join("manifest.json")).unwrap();
    let mut headers=3073;let mut root=native.root();let mut total=native.total_be28();
    let (field,expected)=match fault{
        ActualPlanFault::Root=>{root=[13;32];("root","native history plan/input root, total or profile mismatch")},
        ActualPlanFault::Total=>{total[27]^=1;("total","native history plan/input root, total or profile mismatch")},
        ActualPlanFault::Count=>{headers=3072;("count","native history plan/input count mismatch")},
    };
    assert_eq!([headers!=3073,root!=native.root(),total!=native.total_be28()].iter().filter(|v|**v).count(),1);
    println!("C129C_PLAN_START field={field}");std::io::stdout().flush().unwrap();let started=Instant::now();
    let changed=WorkTreeHistoryPlan::compile(headers,12,root,total).unwrap();
    println!("C129C_PLAN_READY field={field} elapsed_s={:.6}",started.elapsed().as_secs_f64());std::io::stdout().flush().unwrap();
    assert_eq!(changed.headers(),headers);assert_eq!(changed.slot_log(),12);
    assert_eq!(changed.descriptor().root,root);assert_eq!(changed.work_profile().total_be28,total);
    assert_eq!(VerifiedBundleIdentity::from_bundle(&changed,native,&bytes,&manifest).unwrap_err(),expected);
    drop(changed);
    println!("C129C_PLAN_REJECT_PASS field={field}");std::io::stdout().flush().unwrap();
}

#[test]
fn actual_wrong_root_plan_rejected_by_bundle_factory(){reject_actual_plan(ActualPlanFault::Root);}

#[test]
fn actual_wrong_total_plan_rejected_by_bundle_factory(){reject_actual_plan(ActualPlanFault::Total);}

#[test]
fn actual_wrong_count_plan_rejected_by_bundle_factory(){reject_actual_plan(ActualPlanFault::Count);}

#[test]
fn omissions_duplicates_and_row_collision_are_atomic(){
    let (p,n,id)=fixture();let s=source(p,n,id,1);let b=s.stage_owner(3007).unwrap();s.validate(&b).unwrap();
    for fault in 0..8 {let mut bad=b.clone();match fault{
        0=>{bad.terms.pop();},1=>bad.terms.clear(),2=>{let q=*bad.helpers.keys().next().unwrap();bad.helpers.remove(&q);},
        3=>{let q=*bad.reads.keys().next().unwrap();bad.reads.remove(&q);},4=>bad.terms.push(bad.terms[0].clone()),
        5=>bad.binding.cut+=1,6=>{let q=*bad.helpers.keys().next().unwrap();bad.helpers.insert(q,Fr::from(2u8));},
        _=>bad.imports.clear(),
    }atomic_reject(&s,bad);}
    // Existing equal-valued writer and cross-writer ROW must both fail without mutation.
    let address=*b.helpers.keys().next().unwrap();let value=b.helpers[&address];
    let mut d=Destination::default();d.cells.insert(address,((1,3007),value));let before=d.clone();
    assert!(s.publish(&mut d,b.clone()).is_err());assert_eq!(d,before);
    let mut d=Destination::default();d.rows.insert(b.terms[0].row,(0,3007));let before=d.clone();
    assert!(s.publish(&mut d,b.clone()).is_err());assert_eq!(d,before);
    let mut d=Destination::default();s.publish(&mut d,b.clone()).unwrap();let before=d.clone();
    assert!(s.publish(&mut d,b).is_err());assert_eq!(d,before);
}

#[test]
fn coherent_foreign_d_and_helpers_cannot_forge_native_reads(){
    let (p,n,id)=fixture();let s=source(p,n,id,1);
    let honest=s.stage_owner(0).unwrap();s.validate(&honest).unwrap();
    let d=*honest.imports.iter().find(|i|i.kind==Kind::Difficulty).unwrap();
    assert_eq!((d.owner,d.local,d.width),(0,987674,224));
    let mut forged=honest.clone();let address=d.owner as usize*WIDTH+d.local;
    let old=forged.reads[&address];*forged.reads.get_mut(&address).unwrap()=Fr::one()-old;
    // Deliberately bypass the source adapter in this adversarial fixture only:
    // use the real Map producer to make all helper equations coherent with D'.
    let (mut inputs,_)=s.imports(0,&honest.imports).unwrap();
    inputs.put(&s.map,d,&integer(&forged,d)).unwrap();
    let replacement=s.map.generate(0,&inputs).unwrap();s.map.check_row(&replacement).unwrap();
    for k in 0..5757{*forged.helpers.get_mut(&(671744+8192+k)).unwrap()=Fr::from(u64::from(replacement.bits[k]));}
    assert_eq!(forged.binding,honest.binding);assert_eq!(forged.imports,honest.imports);
    assert_eq!(forged.terms,honest.terms);assert_ne!(forged.reads,honest.reads);
    assert!(residuals(&forged).unwrap().values().all(|v|v.is_zero()),"coherent forged Map witness");
    assert_eq!(s.validate(&forged).unwrap_err(),"native READ values/source binding");
    let mut destination=Destination::default();s.publish(&mut destination,honest).unwrap();
    let frozen=destination.clone();
    assert_eq!(s.publish(&mut destination,forged).unwrap_err(),"native READ values/source binding");
    assert_eq!(destination,frozen);
}

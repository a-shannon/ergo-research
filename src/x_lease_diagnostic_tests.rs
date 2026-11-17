use super::*;
use std::{collections::BTreeMap,sync::OnceLock};
use crate::{daa_integer::Epoch,short_daa_layout::Profile};

fn source()->(&'static WorkTreeHistoryPlan,&'static DaaHistoryRoster<'static>) {
    static P:OnceLock<WorkTreeHistoryPlan>=OnceLock::new();
    static R:OnceLock<DaaHistoryRoster<'static>>=OnceLock::new();
    let p=P.get_or_init(||WorkTreeHistoryPlan::compile(1827840,21,[0;32],[0;28]).unwrap());
    (p,R.get_or_init(||DaaHistoryRoster::compile(p).unwrap()))
}
fn count(p:&Policy,w:Writer)->usize {p.leases.iter().filter(|&&tag|tag==w as u8).count()}
fn decode_hex(s:&str)->Vec<u8>{assert_eq!(s.len()%2,0);s.as_bytes().chunks_exact(2)
    .map(|x|u8::from_str_radix(std::str::from_utf8(x).unwrap(),16).unwrap()).collect()}
fn fixture()->BTreeMap<u32,Vec<u8>> {
    let json:serde_json::Value=serde_json::from_str(include_str!("../fixtures/mainnet-daa-windows-v1.json")).unwrap();
    assert_eq!(json["source_frame"]["sha256"].as_str(),Some("A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E"));
    json["headers"].as_array().unwrap().iter().map(|x|
        (x["height"].as_u64().unwrap()as u32,decode_hex(x["raw_hex"].as_str().unwrap()))).collect()
}
fn m1_exports(raws:&BTreeMap<u32,Vec<u8>>)->BTreeMap<usize,bool> {
    // Fixture-local native serializer ports only; absence is an error, never false.
    let serializer=serializer::build(None).unwrap();let mut out=BTreeMap::new();
    for h in [1024,2048,2049] {
        let header=Header::decode(&raws[&h],None).unwrap();
        let fields=serializer::Fields::from_header(&header).unwrap();
        let values=serializer.assign(&fields);let base=(h as usize-1)*WIDTH+crate::header_hash::SERIALIZER_OFFSET;
        for &wire in serializer.layout.fields.timestamp.iter().chain(&serializer.layout.fields.n_bits)
            .chain(&serializer.layout.fields.height) {
            assert!(out.insert(base+wire,values[wire].is_one()).is_none());
        }
    }out
}

#[test]
fn immutable_domains_classify_real_mask_banks_and_scheduled_writers() {
    let (parent,roster)=source();
    for (owner,class) in [(0,OwnerClass::Genesis),(1,OwnerClass::Initial),(2,OwnerClass::Carry),
        (1024,OwnerClass::Singleton),(2048,OwnerClass::M1),(3072,OwnerClass::Short(Profile::M2)),
        (4096,OwnerClass::Short(Profile::M3)),(5120,OwnerClass::Short(Profile::M4)),
        (6144,OwnerClass::Short(Profile::M5)),(7168,OwnerClass::Short(Profile::M6)),
        (8192,OwnerClass::Short(Profile::M7)),(9216,OwnerClass::Mature(Epoch::Legacy)),
        (417792,OwnerClass::FixedV2),(844670,OwnerClass::Carry),
        (844672,OwnerClass::Mature(Epoch::Eip)),(845759,OwnerClass::Carry),
        (1827840,OwnerClass::Padding),(2097151,OwnerClass::Padding)] {
        let p=Policy::new(parent,roster,owner).unwrap();assert_eq!(p.class,class);
        let bank_writer=if retarget(class){Writer::DaaRetarget}else{Writer::AssemblyInactiveZero};
        assert_eq!(count(&p,bank_writer),81920);
        assert_eq!(count(&p,if retarget(class){Writer::AssemblyInactiveZero}else{Writer::DaaRetarget}),0);
        assert_eq!(p.leases.iter().filter(|&&x|x==0).count(),401362);
        for (a,b) in BANKS {assert!(p.leases[a..b].iter().all(|&x|x==bank_writer as u8));}
        assert!(p.leases[989658..989730].iter().all(|&x|x==Writer::Header as u8));
        assert!(p.leases[991232..999424].iter().all(|&x|x==bank_writer as u8));
        let scheduled=Scheduled::new().visit_owner(owner,|_,_|Ok(())).unwrap();
        for (w,active,len) in [(Writer::Max0,scheduled.max[0]>0,673),(Writer::Max1,scheduled.max[1]>0,673),
            (Writer::Cap0,scheduled.cap[0]>0,2048),(Writer::Cap1,scheduled.cap[1]>0,2048)] {
            assert_eq!(count(&p,w),if active{len}else{0});
        }
        if owner==2048 {assert_eq!(count(&p,Writer::Header),565294);}
    }
    assert!(Policy::new(parent,roster,OWNERS).is_err());
    let mask=parent.physical_assignment_replacement_mask(2048).unwrap();
    let reserved=mask.iter().position(|&x|x).unwrap();
    for (cell,error) in [(989658,"X lease protected endpoint release"),(989729,"X lease protected endpoint release"),
        (991232,"X lease A4 parent release"),(999423,"X lease A4 parent release")] {
        let mut mutant=mask.clone();assert!(!mutant[cell]);mutant[cell]=true;mutant[reserved]=false;
        assert_eq!(mutant.iter().filter(|&&x|x).count(),401362,"isolate authority, not count");
        assert_eq!(validate_replacement_mask(&mutant).unwrap_err(),error);
    }
}

#[test]
fn native_m1_stage_duplicate_zero_and_atomic_publish_negatives() {
    let (parent,roster)=source();let policy=Policy::new(parent,roster,2048).unwrap();
    let template=HeaderAssignmentTemplate::new().unwrap();let raws=fixture();let external=m1_exports(&raws);
    let samples=[raws[&1024].as_slice(),raws[&2048].as_slice()];
    let raw=RawWindow{parent:&raws[&2048],child:&raws[&2049],samples:&samples};
    let mut scratch=Scratch::new(&policy);
    assert!(scratch.stage_retarget(roster,raw,|_|Err("missing export".into())).unwrap_err().contains("staged HEADER"));
    scratch.stage_header(&template,&raws[&2049],Some(&raws[&2048])).unwrap();
    scratch.stage_retarget(roster,raw,|index|external.get(&index).copied().ok_or_else(||format!("missing export {index}"))).unwrap();
    assert_eq!(scratch.packed[991232/8],0,"M1 A4 zero is already produced by retarget");
    assert!(scratch.claimed[991232]);
    assert!(scratch.packed[819200/8..827392/8].iter().any(|&x|x!=0),"real M1 values, not a zero stand-in");
    let packed=scratch.packed.clone();let claims=scratch.claimed.clone();
    assert_eq!(scratch.stage_values(Writer::DaaRetarget,2048,OwnerClass::M1,[(991232,Fr::zero())]).unwrap_err(),"X stage duplicate claim");
    assert!(scratch.stage_assembly_inactive_zero().is_err());
    assert_eq!(scratch.stage_values(Writer::Header,2048,OwnerClass::M1,[(991232,Fr::zero())]).unwrap_err(),"X stage outside lease");
    assert_eq!(scratch.stage_values(Writer::Header,2049,OwnerClass::M1,[(0,Fr::zero())]).unwrap_err(),"X stage owner/class");
    assert_eq!(scratch.stage_values(Writer::Header,2048,OwnerClass::Carry,[(0,Fr::zero())]).unwrap_err(),"X stage owner/class");
    assert_eq!(scratch.stage_values(Writer::DaaRetarget,2048,OwnerClass::M1,[(991232,Fr::from(2u64))]).unwrap_err(),"X stage nonboolean");
    assert_eq!(scratch.packed,packed);assert_eq!(scratch.claimed,claims);
    let mut destination=vec![0xA5;PACKED_OWNER_BYTES];let before=destination.clone();
    assert!(scratch.publish(2049,OwnerClass::M1,&mut destination).is_err());assert_eq!(destination,before);
    assert!(scratch.publish(2048,OwnerClass::Carry,&mut destination).is_err());assert_eq!(destination,before);
    // Omit the last participant cell: validation reaches the end without publishing earlier values.
    assert_eq!(policy.leases[WIDTH-1],Writer::Header as u8);scratch.claimed[WIDTH-1]=false;
    assert_eq!(scratch.publish(2048,OwnerClass::M1,&mut destination).unwrap_err(),"X publish incomplete claims");
    assert_eq!(destination,before);scratch.claimed[WIDTH-1]=true;
    scratch.publish(2048,OwnerClass::M1,&mut destination).unwrap();
    for cell in 0..WIDTH {
        let bit=|bytes:&[u8]|(bytes[cell/8]>>(cell%8))&1;
        assert_eq!(bit(&destination),if policy.leases[cell]==0{bit(&before)}else{bit(&scratch.packed)});
    }
    // Complete restaging fails even for equal values and cannot alter the validated scratch.
    assert!(scratch.stage_header(&template,&raws[&2049],Some(&raws[&2048])).unwrap_err().contains("duplicate"));
    assert_eq!(scratch.packed,packed);assert_eq!(scratch.claimed,claims);
}

#[test]
fn carry_has_assembly_zero_not_a_false_retarget_claim() {
    let (parent,roster)=source();let policy=Policy::new(parent,roster,844670).unwrap();
    let mut scratch=Scratch::new(&policy);let packed=scratch.packed.clone();let claims=scratch.claimed.clone();
    let raw=RawWindow{parent:&[],child:&[],samples:&[]};
    assert_eq!(scratch.stage_retarget(roster,raw,|_|panic!("class failure precedes exports")).unwrap_err(),"X retarget class/roster");
    assert_eq!(scratch.stage_values(Writer::DaaRetarget,844670,OwnerClass::Carry,[(991232,Fr::zero())]).unwrap_err(),"X stage outside lease");
    assert_eq!(scratch.packed,packed);assert_eq!(scratch.claimed,claims);
    scratch.stage_assembly_inactive_zero().unwrap();
    for (a,b) in BANKS {assert!(scratch.claimed[a..b].iter().all(|&x|x));assert!(scratch.packed[a/8..b/8].iter().all(|&x|x==0));}
    assert!(scratch.stage_assembly_inactive_zero().unwrap_err().contains("duplicate"));
    let mut destination=vec![0x5A;PACKED_OWNER_BYTES];let before=destination.clone();
    assert!(scratch.publish(844670,OwnerClass::Carry,&mut destination).is_err());assert_eq!(destination,before);
}

#[test]
fn typed_scheduled_staging_preserves_its_conditional_d_contract_and_domain() {
    let (parent,roster)=source();
    // Explicitly conditional D fixture; this is not NativePrefix provenance.
    let prepared=Prepared::from_d_iter((844672..=1827840).map(|h|(h,num_bigint::BigUint::from(1u8)))).unwrap();
    for owner in [844670,845759,1827773,1827774,1827837,1827838] {
        let policy=Policy::new(parent,roster,owner).unwrap();let mut scratch=Scratch::new(&policy);
        scratch.stage_scheduled(&prepared).unwrap();
        let expected:usize=[Writer::Max0,Writer::Max1,Writer::Cap0,Writer::Cap1].into_iter().map(|w|count(&policy,w)).sum();
        assert_eq!(scratch.claimed.iter().filter(|&&x|x).count(),expected);
        for cell in 0..WIDTH {if scratch.claimed[cell]{assert!((Writer::Max0 as u8..=Writer::Cap1 as u8).contains(&policy.leases[cell]));}}
        let packed=scratch.packed.clone();let claims=scratch.claimed.clone();
        if expected>0 {assert!(scratch.stage_scheduled(&prepared).unwrap_err().contains("duplicate"));}
        assert_eq!(scratch.packed,packed);assert_eq!(scratch.claimed,claims);
    }
}

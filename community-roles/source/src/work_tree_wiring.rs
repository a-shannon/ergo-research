//! B1 topology equalities only. No work arithmetic or full hash boundary is implied.
use std::collections::BTreeMap;

/// Literal endpoint partition of the full roster. Local B2 GLOBAL0 endpoints
/// retain their original row source; unused endpoints are never normalized.
#[cfg(test)]
pub(crate) fn check_role2_endpoint_edge(e:&crate::sparse_stream_roster::EdgeTerm,left:bool,owner:usize,
    slot_bits:usize,strides:&[usize])->Result<usize,String>{
    let tag=e.family_row>>14;let slots=1usize.checked_shl(slot_bits as u32).ok_or("role2 endpoint slots overflow")?;
    if tag>=strides.len()||e.source_slot>=slots{return Err("endpoint member/source".into());}
    let family_bits=strides.len().next_power_of_two().trailing_zeros() as usize;
    if crate::sparse_stream_roster::global_edge_row(e.source_slot,e.family_row,slot_bits,14,family_bits,strides)?!=e.term.row{
        return Err("endpoint exact canonical row".into());}
    if e.term.gate.left>=WIDTH*slots||e.term.gate.right>=WIDTH*slots{return Err("endpoint domain".into());}
    if (if left{e.term.gate.left}else{e.term.gate.right})/WIDTH!=owner{return Err("endpoint owner mismatch".into());}
    Ok(tag)
}
#[cfg(test)]
pub(crate) fn visit_full_roster_endpoint(
    topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed:&crate::work_tree_fixed_hash::FixedProfile,leaf:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,left:bool,owner:usize,
    sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>,
)->Result<(),String>{
    use crate::sparse_stream_roster::{EdgeTerm,global_edge_row};
    validate_full_split_inputs(topology,fixed,leaf,work)?;
    let d=&topology.descriptor;let h=d.slot_log();
    if owner>=d.slots{return Err("role2 endpoint owner".into());}
    let members=topology.families.len()+6;let family_bits=members.next_power_of_two().trailing_zeros() as usize;
    let mut strides=[0usize;64];
    if members>64{return Err("role2 endpoint member extent".into());}
    for (i,f) in topology.families.iter().enumerate(){strides[i]=f.count(d)?.row_log-h;}
    let b2=topology.families.len();strides[b2..b2+3].copy_from_slice(&[11,14,11]);
    for(i,f)in work.links().iter().enumerate(){strides[b2+3+i]=f.count(d)?.row_log-h;}
    let mut emit=|tag:usize,source:usize,t:Term|->Result<(),String>{
        let stride=strides[tag];let local=t.row.checked_sub(source.checked_shl(stride as u32).ok_or("role2 endpoint source shift")?)
            .ok_or("role2 endpoint source row")?;
        if local>=1usize<<stride{return Err("role2 endpoint local row".into());}
        let family_row=(tag<<14)|local;let mut term=t;
        term.row=term.row.checked_add(tag.checked_shl((14+h) as u32).ok_or("role2 endpoint tag shift")?).ok_or("role2 endpoint row overflow")?;
        if global_edge_row(source,family_row,h,14,family_bits,&strides[..members])?!=term.row{
            return Err("role2 endpoint exact row".into());}
        let endpoint=if left{term.gate.left}else{term.gate.right};
        if term.gate.left>=WIDTH*d.slots||term.gate.right>=WIDTH*d.slots||endpoint/WIDTH!=owner{
            return Err("role2 endpoint selected wire".into());}
        let edge=EdgeTerm{source_slot:source,family_row,term};
        check_role2_endpoint_edge(&edge,left,owner,h,&strides[..members])?;sink(edge)
    };
    for(tag,f)in topology.families.iter().enumerate(){
        f.emit_endpoint_terms(d,left,owner,|s,_,t|emit(tag,s,t))?;
    }
    let mut local=|tag:usize,source:usize,filter:bool|->Result<(),String>{
        let mut error=None;
        let mut cb=|t:Term|{if error.is_some(){return;}
            if tag==b2&&(t.gate.right!=0||!(t.gate.left/WIDTH==0||t.gate.left/WIDTH==source)){
                error=Some("role2 B2 endpoint invariant".into());return;}
            if tag!=b2&&(t.gate.left/WIDTH!=source||t.gate.right/WIDTH!=source){
                error=Some("role2 local endpoint invariant".into());return;}
            if !filter||(if left{t.gate.left}else{t.gate.right})/WIDTH==owner{
                if let Err(e)=emit(tag,source,t){error=Some(e);}
            }
        };
        match tag-b2 {0=>crate::work_tree_fixed_hash::emit_slot(engine,fixed,source,&mut cb)?,
            1=>leaf.emit_slot(source,&mut cb)?,2=>work.emit_slot(source,&mut cb)?,_=>return Err("role2 local tag".into())}
        if let Some(e)=error{return Err(e);}Ok(())
    };
    if left{if owner==0{for source in 0..d.slots{local(b2,source,true)?;}}
        else{local(b2,owner,true)?;}}
    else if owner==0{for source in 0..d.slots{local(b2,source,false)?;}}
    local(b2+1,owner,false)?;local(b2+2,owner,false)?;drop(local);
    for(i,f)in work.links().iter().enumerate(){f.emit_endpoint_terms(d,left,owner,|s,_,t|emit(b2+3+i,s,t))?;}
    Ok(())
}

/// Canonical full-roster order and per-member ROW owner strides for H21.
/// This is the original 58-member roster, never the reordered split roster.
#[cfg(test)]
pub(crate) fn h21_full_roster_member_bits(
    topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,leaf:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,
)->Result<Vec<usize>,String>{
    validate_full_split_inputs(topology,fixed_profile,leaf,work)?;
    let d=&topology.descriptor;let h=d.slot_log();
    let shape=full_roster_shape(topology)?;
    if usize::BITS!=64 || d.headers!=crate::h21_snapshot::N || d.slots!=1usize<<21 || h!=21
        ||shape!=(35,6,41,41)||topology.families.len()!=52||work.links().len()!=3
        ||!std::ptr::eq(engine,crate::work_tree_fixed_hash::engine()?){
        return Err("H21 full roster canonical geometry/engine".into());
    }
    let mut bits=Vec::with_capacity(58);
    for family in &topology.families {
        bits.push(family.count(d)?.row_log.checked_sub(h).ok_or("H21 full roster B1 row stride")?);
    }
    bits.extend([11,14,11]);
    for family in work.links() {
        bits.push(family.count(d)?.row_log.checked_sub(h).ok_or("H21 full roster work-link row stride")?);
    }
    if bits.len()!=58||bits.iter().any(|stride|*stride>14){
        return Err("H21 full roster member stride coverage".into());
    }
    Ok(bits)
}

/// Physical-input-owner inverse of the canonical H21 full roster. Original
/// term endpoints and coefficients survive unchanged; ROW owners come from
/// each canonical emitter, independently of the requested input owner.
#[cfg(test)]
pub(crate) fn h21_full_roster_endpoint(
    topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,leaf:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,left:bool,source_owner:usize,
    sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>,
)->Result<(),String>{
    h21_full_roster_member_bits(topology,engine,fixed_profile,leaf,work)?;
    visit_full_roster_endpoint(topology,engine,fixed_profile,leaf,work,left,source_owner,sink)
}

#[cfg(test)]
pub(crate) fn role2_endpoint_ordinary_controls()->Result<(),String>{
    use crate::{work_tree_fixed_hash as fixed,work_tree_leaf_hash as leaf,work_tree_work as work,
        sparse_stream_roster::global_edge_row};
    fn same(expected:&[Term],actual:&[Term])->Result<(),String>{
        if expected==actual{Ok(())}else{Err("role2 exact occurrence mismatch".into())}
    }
    let engine=fixed::engine()?;let base=layout::shared_baseline()?;
    // N3 literal occurrence oracle plus N6 genuine/padding/position-mask coverage.
    for n in [3usize,6]{
        let topology=Topology::new(base,n,[0x5a;32])?;let fp=fixed::FixedProfile::new(n,[0x5a;32])?;
        let lb=leaf::compile(engine,leaf::LeafProfile::new(n,[0x5a;32])?)?;
        let wb=work::compile(base,work::WorkProfile::new(n,[0x5a;32],[0;28])?)?;
        let circuit=full_roster_circuit(&topology,engine,&fp,&lb,&wb)?;
        if circuit.terms.len()>1<<20{return Err("role2 ordinary literal bound".into());}
        let d=&topology.descriptor;let h=d.slot_log();let count=topology.families.len()+6;
        let bits=count.next_power_of_two().trailing_zeros() as usize;let mut strides=Vec::with_capacity(count);
        for f in &topology.families{strides.push(f.count(d)?.row_log-h);}strides.extend([11,14,11]);
        for f in wb.links(){strides.push(f.count(d)?.row_log-h);}
        for left in [true,false]{
            for owner in 0..d.slots{
                let mut expected=circuit.terms.iter().filter(|t|(if left{t.gate.left}else{t.gate.right})/WIDTH==owner)
                    .cloned().collect::<Vec<_>>();
                let mut actual=Vec::new();
                visit_full_roster_endpoint(&topology,engine,&fp,&lb,&wb,left,owner,&mut |e|{
                    if global_edge_row(e.source_slot,e.family_row,h,14,bits,&strides)?!=e.term.row{
                        return Err("role2 ordinary row identity".into());}actual.push(e.term);Ok(())})?;
                let key=|t:&Term|(t.row,t.gate.left,t.gate.right);
                expected.sort_by_key(key);actual.sort_by_key(key);
                same(&expected,&actual)?;
                if !actual.is_empty(){let original=actual.clone();actual.remove(0);
                    if same(&original,&actual).unwrap_err()!="role2 exact occurrence mismatch"{return Err("role2 omitted occurrence accepted".into());}
                    actual=original.clone();actual.push(original[0].clone());
                    if same(&original,&actual).unwrap_err()!="role2 exact occurrence mismatch"{return Err("role2 duplicate occurrence accepted".into());}
                    actual=original.clone();actual[0].gate.c0+=Fr::one();
                    if same(&original,&actual).unwrap_err()!="role2 exact occurrence mismatch"{return Err("role2 coefficient substitution accepted".into());}
                    actual=original.clone();actual[0].gate.left^=1;
                    if same(&original,&actual).unwrap_err()!="role2 exact occurrence mismatch"{return Err("role2 wire substitution accepted".into());}
                    if owner==0{
                        let b2=topology.families.len();
                        let position=original.iter().position(|t|t.row>>(14+h)==b2&&
                            ((t.row&((1usize<<(14+h))-1))>>11)>0&&t.gate.left==0&&!t.gate.c0.is_zero())
                            .ok_or("role2 B2 foreign GLOBAL0 control absent")?;
                        actual=original.clone();actual.remove(position);
                        if same(&original,&actual).unwrap_err()!="role2 exact occurrence mismatch"{return Err("role2 B2 omitted foreign constant accepted".into());}
                        actual=original.clone();actual.push(original[position].clone());
                        if same(&original,&actual).unwrap_err()!="role2 exact occurrence mismatch"{return Err("role2 B2 duplicate foreign constant accepted".into());}
                        let own=original.iter().find(|t|t.row>>(14+h)==b2&&((t.row&((1usize<<(14+h))-1))>>11)==0)
                            .ok_or("role2 B2 source0 control absent")?;
                        actual=original.clone();actual.push(own.clone());
                        if same(&original,&actual).unwrap_err()!="role2 exact occurrence mismatch"{return Err("role2 B2 source0 double emission accepted".into());}
                    }
                }
            }
        }
        let error=visit_full_roster_endpoint(&topology,engine,&fp,&lb,&wb,true,1,&mut |_|Err("role2 isolated sink".into()));
        if error.unwrap_err()!="role2 isolated sink"{return Err("role2 sink propagation".into());}
    }
    // All native Child levels/branches, including nonzero positions and both ends.
    let d=Descriptor::new(3073,[0;32])?;
    for level in 1..=12{let (lo,n)=d.level(level)?;
        for branch in 0..2{let f=equal("inverse",Mapping::Child{level,branch},vec![1],vec![2]);
            for ordinal in [0,n/2,n-1]{let source=lo+ordinal;
                let child_base=if level==1{0}else{d.leaves-4*(d.leaves>>level)};let child=child_base+2*ordinal+branch;
                let mut got=Vec::new();f.emit_endpoint_terms(&d,false,child,|s,_,t|{got.push((s,t.gate.right/WIDTH));Ok(())})?;
                if got!=[(source,child)]{return Err("role2 child inverse".into());}
                let mut wrong=0;f.emit_endpoint_terms(&d,false,child^1,|_,_,_|{wrong+=1;Ok(())})?;
                if wrong!=0{return Err("role2 child branch inverse".into());}
            }
        }
    }
    for (mapping,source,right) in [(Mapping::Same{lo:2,hi:5},3,3),
        (Mapping::HeaderSuccessor{lo:2,hi:5},3,2),(Mapping::FixedRight{lo:2,hi:5,target:7},3,7)]{
        let f=equal("inverse",mapping,vec![1],vec![2]);let mut selected=Vec::new();
        f.emit_endpoint_terms(&d,true,source,|s,_,t|{selected.push((s,t.gate.right/WIDTH));Ok(())})?;
        if selected!=[(source,right)]{return Err("role2 inverse forward fixture".into());}
        selected.clear();f.emit_endpoint_terms(&d,false,right,|s,_,_|{selected.push((s,right));Ok(())})?;
        let expected=if matches!(f.mapping,Mapping::FixedRight{..}){vec![(2,right),(3,right),(4,right)]}else{vec![(source,right)]};
        if selected!=expected{return Err("role2 inverse reverse fixture".into());}
        let mut calls=0;f.emit_endpoint_terms(&d,true,1,|_,_,_|{calls+=1;Ok(())})?;
        if calls!=0{return Err("role2 inverse lower boundary".into());}
        if f.emit_endpoint_terms(&d,true,d.slots,|_,_,_|Ok(())).unwrap_err()!="endpoint slot outside descriptor"{
            return Err("role2 inverse owner range".into());}
    }
    let zero=Term{row:0,gate:Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}};
    if same(&[zero.clone()],&[zero.clone(),zero]).unwrap_err()!="role2 exact occurrence mismatch"{
        return Err("role2 all-zero duplicate accepted".into());}
    // Native padding positions have only bits0..11. Higher PaddingBit masks
    // cannot select any owner; preserve this exclusion explicitly for all32 masks.
    for bit in 0..32{let count=(3072usize..4096).filter(|s|(*s>>bit)&1!=0).count();
        let expected=if bit<10{512}else if bit<12{1024}else{0};
        if count!=expected{return Err("role2 native padding-bit boundary".into());}
    }
    // Inspect actual compiled PaddingBit contributions at native boundary slots,
    // independently locating their message rows and expected position bits.
    let lb=leaf::compile(engine,leaf::LeafProfile::new(3073,[0;32])?)?;
    let rows=lb.family("padding_message_0")?;
    for owner in [3072usize,3073,4095]{let mut occurrences=[0usize;32];let mut constants=[Fr::zero();32];
        lb.emit_slot(owner,|t|{let local=t.row-owner*leaf::ROW_WIDTH;
            if(rows.start+37*8..rows.start+41*8).contains(&local){
                let absolute=(local-rows.start)/8;let bit=(local-rows.start)%8;let position_bit=(40-absolute)*8+bit;
                occurrences[position_bit]+=1;constants[position_bit]+=t.gate.c0;
            }})?;
        for bit in 0..32{let one=(owner>>bit)&1;
            if occurrences[bit]!=1+one||constants[bit]!=-Fr::from(one as u64){return Err("role2 compiled PaddingBit selection".into());}
        }
    }
    Ok(())
}
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use serde::{Deserialize,Serialize};
use crate::{gkr::Gate,sparse::{Circuit,Term},wiring::{evaluate_shift,RightIndex},
    work_tree_layout::{self as layout,Baseline,WIDTH,ENDPOINT_BASE,ENDPOINT_WIDTH}};

#[cfg(test)]
mod cross_endpoint_falsifier {
    use super::*;
    use crate::{gkr::{self,GkrError,GkrProof,InputClaim},sparse,
        sparse_stream_roster::{self as edge,EdgeTerm},transcript::Transcript,
        work_tree_fixed_hash::{self as fixed,Engine,FixedProfile},
        work_tree_leaf_hash::{self as leaf,LeafProfile},work_tree_work::{self as work,WorkProfile}};
    use ark_serialize::CanonicalSerialize;
    use ark_ff::{One,Zero};
    use std::{cell::{Cell,RefCell},mem::size_of,time::{Duration,Instant}};

    const TERMS:usize=33228;
    const OWNERS:usize=4;
    const BASE:usize=13;
    const FAMILY:usize=4;
    const ROW_BITS:usize=19;
    const INPUT_BITS:usize=22;
    const MIB:usize=1024*1024;
    const SCOPED:usize=512*MIB;
    const JOB:usize=2*1024*MIB;
    const MAP_KEYS:usize=46352;
    const REFERENCE:usize=16*MIB;
    const BUCKET:usize=4*MIB;
    const DOMAIN:&[u8]=b"role2-cross-endpoint-n3-falsifier-v1";
    const CONTINUE:&[u8]=b"role2-cross-endpoint-falsifier-continuation";

    fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or_else(||"role2 inventory overflow".into())}
    fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or_else(||"role2 inventory overflow".into())}
    fn need(ok:bool,message:&str)->Result<(),String>{if ok{Ok(())}else{Err(message.into())}}
    fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
    fn continuation(t:&Transcript)->Fr{t.clone().challenge_scalar(CONTINUE)}
    fn unchanged(a:&Transcript,b:&Transcript){assert_eq!(counters(a),counters(b));assert_eq!(continuation(a),continuation(b));}

    #[derive(Clone)]
    struct Ledger {scoped:usize,map_model:usize,parent_retained:usize,buckets:[usize;4]}
    impl Ledger {
        fn preflight(extra:usize)->Result<Self,String>{
            need(size_of::<Fr>()==32&&size_of::<Term>()==152&&size_of::<usize>()==8,
                "role2 ledger requires reviewed x64 layout")?;
            let map_model=mul(add(MAP_KEYS,32)?,1024)?;
            let scoped=add(add(add(add(mul(9,mul(WIDTH,32)?)?,128)?,map_model)?,REFERENCE)?,4*BUCKET)?;
            need(scoped==383041664,"role2 source-model ledger changed")?;
            need(add(scoped,extra)?<=SCOPED,"role2 scoped preflight exceeds512MiB")?;
            // The immutable parent construction precedes all proof/map/reference buffers.
            // It is an explicit model reservation, not a measured private-heap census.
            need(1536*MIB<=JOB&&add(scoped,512*MIB)?<=JOB,"role2 parent/Job preflight")?;
            Ok(Self{scoped,map_model,parent_retained:0,buckets:[0;4]})
        }
        fn bucket(&mut self,index:usize,bytes:usize)->Result<(),String>{
            need(index<4&&bytes<=BUCKET,"role2 auxiliary bucket exceeds4MiB")?;
            self.buckets[index]=self.buckets[index].max(bytes);Ok(())
        }
        fn fixture_model(&mut self)->Result<(),String>{
            // Buffers in native_endpoint_assignment: aliases, tags/layers/records,
            // small temporary vectors and the BTreeMap inline/iterator overlap.
            self.bucket(0,256*1024)?;
            // full_split_circuit may overlap old/new terms and its largest family.
            let construction=mul(32768+65536+16384,size_of::<Term>())?;
            self.bucket(1,add(construction.saturating_sub(REFERENCE),256*1024)?)?;
            self.bucket(2,256*1024)?;
            // Canonical N3 topology/profile validation JSON and fixed strings only.
            // 42000 seven-digit wire indices plus punctuation is below400KiB.
            self.bucket(3,2*MIB)?;Ok(())
        }
        fn observed_parent(&mut self,base:&Baseline,engine:&Engine,topology:&Topology,
            leaf:&leaf::Boundary,work:&work::Boundary)->Result<(),String>{
            let inspected=base.inventory.inspected_template_peak_capacity_bytes;
            need(add(mul(2,inspected)?,64*MIB)?<=1536*MIB,"role2 parent construction model exceeded")?;
            let leaf_report=leaf::count(engine,leaf)?;
            let work_report=work::count(work)?;
            let value=|report:&serde_json::Value,key:&str|->Result<usize,String>{
                usize::try_from(report.get(key).and_then(serde_json::Value::as_u64)
                    .ok_or_else(||format!("role2 parent count missing {key}"))?)
                    .map_err(|_|"role2 parent count overflow".into())
            };
            let mut observed=add(base.inventory.retained_capacity_bytes,
                mul(engine.core.terms.capacity(),size_of::<Term>())?)?;
            observed=add(observed,value(&leaf_report,"retained_local_boundary_capacity_bytes")?)?;
            observed=add(observed,value(&work_report,"retained_local_term_capacity_bytes")?)?;
            observed=add(observed,value(&work_report,"retained_link_wire_capacity_bytes")?)?;
            observed=add(observed,mul(topology.families.capacity(),size_of::<Family>())?)?;
            for family in &topology.families{
                observed=add(observed,add(family.name.capacity(),mul(add(family.left_wires.capacity(),
                    family.right_wires.capacity())?,size_of::<usize>())?)?)?;
                observed=add(observed,family.constants.as_ref().map_or(0,Vec::capacity))?;
            }
            // Profiles, inventory strings, private boundary-group metadata and
            // their typed headers are explicitly modeled, not called observed.
            self.parent_retained=add(observed,16*MIB)?;
            need(self.parent_retained<=512*MIB&&add(self.scoped,self.parent_retained)?<=JOB,
                "role2 retained parents exceedJob reservation")?;Ok(())
        }
    }

    struct Fixture {
        base:&'static Baseline,engine:&'static Engine,topology:Topology,fixed:FixedProfile,
        leaf:leaf::Boundary,work:work::Boundary,circuit:Circuit,members:Vec<usize>,
        values:BTreeMap<usize,Fr>,ledger:Ledger,initial:Transcript,prepared:Transcript,
    }
    fn decode_row(row:usize,members:&[usize])->Result<(usize,usize),String>{
        let family=row>>(BASE+2);
        let bits=*members.get(family).ok_or("role2 reference family outside roster")?;
        let allocated=row&((1usize<<(BASE+2))-1);
        let source=allocated>>bits;let local=allocated&((1usize<<bits)-1);
        need(source<OWNERS,"role2 reference row occupies family padding")?;
        Ok((source,(family<<BASE)|local))
    }
    impl Fixture {
        fn new()->Result<Self,String>{
            let mut ledger=Ledger::preflight(0)?;ledger.fixture_model()?;
            let base=layout::shared_baseline()?;let engine=fixed::engine()?;
            let root=[0x5a;32];let topology=Topology::new(base,3,root)?;
            let fixed=FixedProfile::new(3,root)?;
            let leaf=leaf::compile(engine,LeafProfile::new(3,root)?)?;
            let work=work::compile(base,WorkProfile::new(3,root,[0;28])?)?;
            ledger.observed_parent(base,engine,&topology,&leaf,&work)?;
            need((topology.descriptor.genuine,topology.descriptor.leaves,topology.descriptor.slots)==(2,2,4)
                &&base.endpoints.used==6690,"role2 canonical N3 geometry")?;
            need(full_split_cross_tensor_dimensions(&topology,&work)?==(20,2,13,4),"role2 dimensions")?;
            let members=full_split_cross_tensor_member_row_bits(&topology,&work)?;
            need(members.len()==12&&members.capacity()*size_of::<usize>()<=1024,"role2 member roster")?;
            // Count the actual canonical families before allocating the reference.
            let mut family_terms=Vec::with_capacity(12);
            for family in &topology.families {if !matches!(family.mapping,Mapping::Same{..}){
                family_terms.push(usize::try_from(family.count(&topology.descriptor)?.terms)
                    .map_err(|_|"role2 family term count overflow")?);
            }}
            for family in work.links(){family_terms.push(usize::try_from(family.count(&topology.descriptor)?.terms)
                .map_err(|_|"role2 work term count overflow")?);}
            need(family_terms==[8372usize,512,256,256,256,16384,0,512,6008,224,224,224]
                &&family_terms.iter().sum::<usize>()==TERMS,"role2 source-derived family census")?;
            let circuit=full_split_circuit(&topology,engine,&fixed,&leaf,&work,false)?;
            need(circuit.terms.len()==TERMS&&circuit.terms.capacity()<=65536
                &&mul(circuit.terms.capacity(),size_of::<Term>())?<=REFERENCE
                &&circuit.input_len==1usize<<INPUT_BITS&&circuit.row_count==1usize<<ROW_BITS,
                "role2 reference capacity/shape")?;
            need(circuit.terms.windows(2).all(|w|w[0].row<w[1].row),"role2 reference rows must be unique and ordered")?;
            sparse::validate(&circuit,0).map_err(|e|e.to_string())?;
            let mut values=native_endpoint_assignment(base,&topology.descriptor)?;
            for bit in 0..224 {let q=Fr::from((1000+bit)as u64);
                values.insert(base.endpoints.lower[bit],Fr::zero());values.insert(base.endpoints.upper[bit],q);
                values.insert(WIDTH+base.endpoints.lower[bit],q);values.insert(WIDTH+base.endpoints.upper[bit],Fr::zero());
            }
            values.insert(3*WIDTH,Fr::from(73u64));
            need(values.len()<=MAP_KEYS&&ledger.map_model==47497216,"role2 map model/census")?;
            need(values[&base.endpoints.upper[0]]==values[&(WIDTH+base.endpoints.lower[0])]
                &&values[&base.endpoints.upper[0]]!=values[&base.endpoints.upper[1]]
                &&values[&(3*WIDTH)]!=Fr::zero(),"role2 witness discrimination")?;
            for term in &circuit.terms{
                let x=values.get(&term.gate.left).copied().unwrap_or_else(Fr::zero);
                let y=values.get(&term.gate.right).copied().unwrap_or_else(Fr::zero);
                need((term.gate.c0+term.gate.c1*x+term.gate.c2*y+term.gate.c3*x*y).is_zero(),
                    "role2 partial witness residual nonzero")?;
                let(source,local)=decode_row(term.row,&members)?;
                need(edge::global_edge_row(source,local,2,BASE,FAMILY,&members)?==term.row,
                    "role2 independent row decoding")?;
            }
            let initial=Transcript::new(DOMAIN);let mut prepared=initial.clone();
            sparse::bind(&circuit,0,&mut prepared);
            Ok(Self{base,engine,topology,fixed,leaf,work,circuit,members,values,ledger,initial,prepared})
        }
        fn canonical(&self,left:bool,owner:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
            full_split_visit_cross_endpoint_terms(&self.topology,&self.work,left,owner,&mut |source,local,mut term|{
                term.row=edge::global_edge_row(source,local,2,BASE,FAMILY,&self.members)?;
                sink(EdgeTerm{source_slot:source,family_row:local,term})
            })
        }
        fn reference(&self,left:bool,owner:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
            need(owner<OWNERS,"role2 reference endpoint outside domain")?;
            for term in &self.circuit.terms{if (if left{term.gate.left}else{term.gate.right})/WIDTH==owner{
                let(source_slot,family_row)=decode_row(term.row,&self.members)?;
                sink(EdgeTerm{source_slot,family_row,term:term.clone()})?;
            }}Ok(())
        }
        fn compare_sources(&mut self)->Result<(),String>{
            self.ledger.bucket(1,TERMS+1024)?;
            let mut seen=Vec::new();seen.try_reserve_exact(TERMS).map_err(|_|"role2 seen reservation")?;
            need(seen.capacity()==TERMS,"role2 seen capacity")?;seen.resize(TERMS,0u8);
            for left in [true,false]{seen.fill(0);
                let mut total=0usize;let mut cross_owner=false;
                for owner in 0..OWNERS{
                    let expected=self.circuit.terms.iter().filter(|term|
                        (if left{term.gate.left}else{term.gate.right})/WIDTH==owner).count();
                    let mut count=0usize;
                    self.canonical(left,owner,&mut |edge|{
                        let index=self.circuit.terms.binary_search_by_key(&edge.term.row,|t|t.row)
                            .map_err(|_|"role2 canonical row absent from reference")?;
                        need(seen[index]==0&&self.circuit.terms[index]==edge.term,"role2 exact endpoint multiset differs")?;
                        let(source,local)=decode_row(edge.term.row,&self.members)?;
                        need((source,local)==(edge.source_slot,edge.family_row),"role2 row owner/tag differs")?;
                        if !left&&source!=owner{cross_owner=true;}seen[index]=1;count+=1;Ok(())
                    })?;
                    need(count==expected,"role2 per-endpoint census differs")?;total+=count;
                }
                need(total==TERMS&&seen.iter().all(|n|*n==1),"role2 endpoint coverage differs")?;
                if !left{need(cross_owner,"role2 fixture lost cross-owner endpoint")?;}
            }
            for seed in [3u64,97u64]{
                let point=|bits:usize,offset:u64|(0..bits).map(|bit|Fr::from(seed+offset+37*(bit as u64+1))).collect::<Vec<_>>();
                let r=point(ROW_BITS,0);let u=point(INPUT_BITS,101);let v=point(INPUT_BITS,211);
                need(direct_coefficients(&self.circuit,&r,&u,&v)==full_split_coefficients(&self.topology,self.engine,
                    &self.fixed,&self.leaf,&self.work,false,&r,&u,&v)?,"role2 analytic/materialized coefficients differ")?;
            }Ok(())
        }
        fn source_mle(&self,point:&[Fr],changed:Option<usize>)->Fr{
            self.values.iter().fold(Fr::zero(),|sum,(index,value)|sum+*value*eq_index(point,*index))
                +changed.map_or_else(Fr::zero,|index|eq_index(point,index))
        }
        fn load(&self,owner:usize,short:bool,capacity_fault:bool)->Result<Vec<Fr>,String>{
            need(owner<OWNERS,"role2 loader owner outside domain")?;
            let capacity=if capacity_fault{WIDTH+1}else{WIDTH};
            // The loader destination is one cache slot, not an additional full source.
            need(mul(capacity,size_of::<Fr>())?<=mul(WIDTH+1,32)?,"role2 loader preflight")?;
            let mut out=Vec::new();out.try_reserve_exact(capacity).map_err(|_|"role2 loader allocation")?;
            need(out.capacity()==WIDTH,"role2 loader capacity differs")?;
            out.resize(if short{WIDTH-1}else{WIDTH},Fr::zero());
            for(index,value)in self.values.range(owner*WIDTH..(owner+1)*WIDTH){
                if let Some(slot)=out.get_mut(index-owner*WIDTH){*slot=*value;}
            }Ok(out)
        }
    }

    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    enum Fault {None,Budget,Overflow,SourceSlot,Endpoint,Member,CountDrift,Read(usize),Short,Capacity,LateVisit}
    #[derive(Debug)]
    struct Failure {error:String,loads:usize,visits:usize,hits:usize,binds:usize,wires:usize,observed:[u64;3]}
    struct Produced {proof:GkrProof,packet:Vec<u8>,claim:InputClaim,transcript:Transcript,loads:usize,terms:usize}
    fn proof_capacity(proof:&GkrProof)->Result<usize,String>{
        let mut bytes=add(size_of::<GkrProof>(),mul(proof.layers.capacity(),size_of::<gkr::LayerProof>())?)?;
        for layer in &proof.layers{
            bytes=add(bytes,mul(layer.rounds.capacity(),size_of::<Vec<Fr>>())?)?;
            bytes=add(bytes,mul(layer.line_coefficients.capacity(),32)?)?;
            for round in &layer.rounds{bytes=add(bytes,mul(round.capacity(),32)?)?;}
        }Ok(bytes)
    }
    fn returned_capacity(out:&Produced)->Result<usize,String>{
        add(add(add(proof_capacity(&out.proof)?,out.packet.capacity())?,mul(out.claim.point.capacity(),32)?)?,size_of::<Produced>())
    }
    fn produce(f:&Fixture,canonical:bool,fault:Fault,caller:&mut Transcript,retained:usize)->Result<Produced,Failure>{
        let loads=Cell::new(0usize);let visits=Cell::new(0usize);let hits=Cell::new(0usize);
        let binds=Cell::new(0usize);let wires=Cell::new(0usize);let terms=Cell::new(0usize);
        let mut working=caller.clone();
        let extra=if fault==Fault::Budget{SCOPED-f.ledger.scoped+1}else if fault==Fault::Overflow{usize::MAX}else{0};
        if let Err(error)=Ledger::preflight(extra){return Err(Failure{error,loads:0,visits:0,hits:1,binds:0,wires:0,observed:counters(&working)});}
        if let Err(error)=need(retained<=BUCKET,"role2 retained first return exceeds bucket"){
            return Err(Failure{error,loads:0,visits:0,hits:1,binds:0,wires:0,observed:counters(&working)});
        }
        let result=edge::prove_edge_terms_with_cache_limit_for_test(20,2,BASE,FAMILY,&f.members,0,
            |left,owner,sink|{
                visits.set(visits.get()+1);let visit=visits.get();let mut first=true;
                if fault==Fault::LateVisit&&visit==13{hits.set(hits.get()+1);return Err("role2 isolated second-U visitor failure".into());}
                let mut forward=|mut item:EdgeTerm|{
                    if first{
                        first=false;
                        match fault{
                            Fault::SourceSlot if visit==1=>{item.source_slot=OWNERS;hits.set(hits.get()+1);},
                            Fault::Endpoint if visit==1=>{item.term.gate.left=OWNERS*WIDTH;hits.set(hits.get()+1);},
                            Fault::Member if visit==1=>{item.family_row=16usize<<BASE;hits.set(hits.get()+1);},
                            Fault::CountDrift if visit==9=>{hits.set(hits.get()+1);return Ok(());},
                            _=>{}
                        }
                    }
                    terms.set(terms.get()+1);sink(item)
                };
                if canonical{f.canonical(left,owner,&mut forward)}else{f.reference(left,owner,&mut forward)}
            },
            |owner|{
                loads.set(loads.get()+1);let call=loads.get();
                if fault==Fault::Read(call){hits.set(hits.get()+1);return Err("role2 isolated loader failure".into());}
                if call==1&&matches!(fault,Fault::Short|Fault::Capacity){hits.set(hits.get()+1);}
                f.load(owner,call==1&&fault==Fault::Short,call==1&&fault==Fault::Capacity)
            },&mut working,|t|{binds.set(binds.get()+1);*t=f.prepared.clone();},
            |r,u,v|{wires.set(wires.get()+1);Ok(direct_coefficients(&f.circuit,r,u,v))});
        let fail=|error:String,working:&Transcript|Failure{error,loads:loads.get(),visits:visits.get(),hits:hits.get(),
            binds:binds.get(),wires:wires.get(),observed:counters(working)};
        let(proof,claim,used_u,used_v)=result.map_err(|error|fail(error,&working))?;
        need(!used_u&&!used_v,"role2 incremental cache0 was not honored").map_err(|e|fail(e,&working))?;
        need(proof.layers.len()==1&&proof.layers[0].rounds.len()==44&&proof.layers[0].line_coefficients.len()==23
            &&working.challenges()==64,"role2 proof ABI differs").map_err(|e|fail(e,&working))?;
        // Codec/consumer allocation is reserved before producer dispatch and remains
        // in bucket3 with the first arm's observed retained capacities.
        need(add(retained,add(proof_capacity(&proof).map_err(|e|fail(e,&working))?,256*1024)
            .map_err(|e|fail(e,&working))?).map_err(|e|fail(e,&working))?<=BUCKET,
            "role2 proof/codec retained capacity").map_err(|e|fail(e,&working))?;
        let packet=gkr::encode_proof(&proof).map_err(|e|fail(e,&working))?;
        let bytes=mul(7*INPUT_BITS+3,Fr::zero().compressed_size()).map_err(|e|fail(e,&working))?;
        need(bytes==5024&&packet.len()==bytes&&packet.capacity()<=16384,"role2 packet ABI/capacity")
            .map_err(|e|fail(e,&working))?;
        let decoded=gkr::decode_dimensions(&[INPUT_BITS],&packet).map_err(|e|fail(e,&working))?;
        need(decoded==proof&&gkr::encode_proof(&decoded).map_err(|e|fail(e,&working))?==packet,
            "role2 codec not canonical").map_err(|e|fail(e,&working))?;
        let mut verifier=caller.clone();
        let consumed=gkr::verify_with_wiring(&[INPUT_BITS],1usize<<ROW_BITS,&decoded,&mut verifier,
            |t|*t=f.prepared.clone(),|_,r,u,v|Ok(direct_coefficients(&f.circuit,r,u,v)))
            .map_err(|e|fail(e.to_string(),&working))?;
        need(consumed==claim&&f.source_mle(&claim.point,None)==claim.value&&counters(&verifier)==counters(&working)
            &&continuation(&verifier)==continuation(&working),"role2 independent consumer/source differs")
            .map_err(|e|fail(e,&working))?;
        need(loads.get()==4&&visits.get()==176&&terms.get()==44*TERMS&&binds.get()==1&&wires.get()==1,
            "role2 actual fallback census differs").map_err(|e|fail(e,&working))?;
        *caller=working.clone();
        Ok(Produced{proof,packet,claim,transcript:working,loads:loads.get(),terms:terms.get()})
    }

    #[derive(Clone,Copy,Debug)]
    enum Semantic {RowOwner,Tag,Stride,Swap,Dummy,Endpoint}
    fn changed_term(f:&Fixture,term:&Term,kind:Semantic)->Option<Term>{
        let(source,local)=decode_row(term.row,&f.members).ok()?;
        let family=local>>BASE;let low=local&((1usize<<BASE)-1);let mut changed=term.clone();
        match kind{
            Semantic::RowOwner=>{
                if source==term.gate.right/WIDTH{return None;}
                changed.row=(family<<(BASE+2))|((term.gate.right/WIDTH)<<f.members[family])|low;
            },
            Semantic::Tag=>changed.row^=1usize<<(BASE+2),
            Semantic::Stride=>{
                if source==0||f.members[family]==BASE{return None;}
                changed.row=(family<<(BASE+2))|(source<<BASE)|low;
            },
            Semantic::Swap=>{if term.gate.c2.is_zero()||term.gate.left==term.gate.right{return None;}
                std::mem::swap(&mut changed.gate.left,&mut changed.gate.right);},
            Semantic::Dummy=>{if source==0||!term.gate.c2.is_zero()||term.gate.right!=0{return None;}
                changed.gate.right=source*WIDTH;},
            Semantic::Endpoint=>changed.gate.left^=1,
        }
        if changed==*term{None}else{Some(changed)}
    }
    fn one_coeff(term:&Term,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
        let w=eq_index(r,term.row)*eq_index(u,term.gate.left)*eq_index(v,term.gate.right);
        [term.gate.c0*w,term.gate.c1*w,term.gate.c2*w,term.gate.c3*w]
    }
    fn expression(c:[Fr;4],out:&Produced)->Fr{
        let layer=&out.proof.layers[0];c[0]+c[1]*layer.left_value+c[2]*layer.right_value+c[3]*layer.left_value*layer.right_value
    }
    // Reconstruct the reached prefix without invoking a producer or verifier.
    // Explicit framing also compares bytes absorbed and rejection-sampler queries.
    fn expected_prefix(prepared:&Transcript,proof:&GkrProof,rounds:usize,line:bool)->Transcript{
        assert!(rounds<=44&&(!line||rounds==44));
        let mut expected=prepared.clone();
        for _ in 0..ROW_BITS{expected.challenge_scalar(b"gkr-output-coordinate");}
        expected.append_bytes(b"gkr-layer-index",&0u64.to_le_bytes());
        for polynomial in proof.layers[0].rounds.iter().take(rounds){
            expected.append_bytes(b"gkr-sumcheck-polynomial",&3u64.to_le_bytes());
            for coefficient in polynomial{expected.append_scalar(b"gkr-polynomial-coefficient",coefficient);}
            expected.challenge_scalar(b"gkr-sumcheck-challenge");
        }
        if line{
            let layer=&proof.layers[0];
            expected.append_scalar(b"gkr-left-value",&layer.left_value);
            expected.append_scalar(b"gkr-right-value",&layer.right_value);
            expected.append_bytes(b"gkr-line-polynomial",&(layer.line_coefficients.len()as u64).to_le_bytes());
            for coefficient in &layer.line_coefficients{expected.append_scalar(b"gkr-polynomial-coefficient",coefficient);}
            expected.challenge_scalar(b"gkr-line-challenge");
        }expected
    }
    struct ConsumerAttempt {error:Option<GkrError>,source_error:bool,observed:[u64;3],binds:usize,wires:usize}
    fn consumer(f:&Fixture,proof:&GkrProof,prepared:&Transcript,caller:&mut Transcript,changed_source:Option<usize>,
        wiring:impl Fn(&[Fr],&[Fr],&[Fr])->[Fr;4])->ConsumerAttempt{
        let mut working=caller.clone();let binds=Cell::new(0);let wires=Cell::new(0);
        let result=gkr::verify_with_wiring(&[INPUT_BITS],1usize<<ROW_BITS,proof,&mut working,
            |t|{binds.set(binds.get()+1);*t=prepared.clone();},
            |_,r,u,v|{wires.set(wires.get()+1);Ok(wiring(r,u,v))});
        let observed=counters(&working);
        match result{
            Err(error)=>ConsumerAttempt{error:Some(error),source_error:false,observed,binds:binds.get(),wires:wires.get()},
            Ok(claim)=>{
                let source_error=f.source_mle(&claim.point,changed_source)!=claim.value;
                if !source_error{*caller=working;}
                ConsumerAttempt{error:None,source_error,observed,binds:binds.get(),wires:wires.get()}
            }
        }
    }
    fn expect_consumer_fault(f:&Fixture,out:&Produced,proof:&GkrProof,prepared:&Transcript,expected:GkrError,challenges:u64,
        expected_wires:usize,wiring:impl Fn(&[Fr],&[Fr],&[Fr])->[Fr;4]){
        let mut caller=f.initial.clone();let before=caller.clone();
        let attempted=consumer(f,proof,prepared,&mut caller,None,wiring);
        assert_eq!(attempted.error,Some(expected));assert!(!attempted.source_error);
        let replayed=expected_prefix(prepared,proof,usize::try_from(challenges-ROW_BITS as u64).unwrap(),false);
        assert_eq!(replayed.challenges(),challenges);
        assert_eq!(attempted.observed,counters(&replayed));
        assert_eq!((attempted.binds,attempted.wires),(1,expected_wires));
        unchanged(&caller,&before);assert_eq!(out.transcript.challenges(),64);
    }

    #[test]
    fn role2_cross_endpoint_kernel_consumers_and_isolated_faults(){
        let began=Instant::now();let mut f=Fixture::new().unwrap();
        eprintln!("R2_CROSS_STAGE fixture_ready elapsed_ms={}",began.elapsed().as_millis());
        f.compare_sources().unwrap();
        eprintln!("R2_CROSS_STAGE sources_compared elapsed_ms={}",began.elapsed().as_millis());
        assert!(began.elapsed()<Duration::from_secs(120));
        let mut reference_caller=f.initial.clone();
        let reference=produce(&f,false,Fault::None,&mut reference_caller,0).unwrap();
        eprintln!("R2_CROSS_STAGE reference_returned elapsed_ms={}",began.elapsed().as_millis());
        let retained=returned_capacity(&reference).unwrap();assert!(retained<256*1024);
        f.ledger.bucket(2,retained+256*1024).unwrap();
        let mut canonical_caller=f.initial.clone();
        let canonical=produce(&f,true,Fault::None,&mut canonical_caller,retained).unwrap();
        eprintln!("R2_CROSS_STAGE canonical_returned elapsed_ms={}",began.elapsed().as_millis());
        let canonical_retained=returned_capacity(&canonical).unwrap();assert!(canonical_retained<256*1024);
        f.ledger.bucket(2,add(add(retained,canonical_retained).unwrap(),256*1024).unwrap()).unwrap();
        assert_eq!(reference.proof,canonical.proof);assert_eq!(reference.packet,canonical.packet);
        assert_eq!(reference.claim,canonical.claim);unchanged(&reference.transcript,&canonical.transcript);
        assert_eq!((reference.loads,canonical.loads,reference.terms,canonical.terms),(4,4,44*TERMS,44*TERMS));
        assert!(began.elapsed()<Duration::from_secs(120));

        // Capture the actual terminal coordinates while consuming the existing proof.
        let terminal=RefCell::new(None);
        let mut consumed=f.initial.clone();
        let accepted=consumer(&f,&canonical.proof,&f.prepared,&mut consumed,None,|r,u,v|{
            *terminal.borrow_mut()=Some((r.to_vec(),u.to_vec(),v.to_vec()));direct_coefficients(&f.circuit,r,u,v)
        });
        assert!(accepted.error.is_none()&&!accepted.source_error);unchanged(&consumed,&canonical.transcript);
        let prefix19=expected_prefix(&f.prepared,&canonical.proof,0,false);
        let prefix20=expected_prefix(&f.prepared,&canonical.proof,1,false);
        let prefix64=expected_prefix(&f.prepared,&canonical.proof,44,true);
        assert_eq!(accepted.observed,counters(&prefix64));unchanged(&prefix64,&canonical.transcript);
        let(r,u,v)=terminal.into_inner().unwrap();let normal=direct_coefficients(&f.circuit,&r,&u,&v);
        assert_eq!(normal,full_split_coefficients(&f.topology,f.engine,&f.fixed,&f.leaf,&f.work,false,&r,&u,&v).unwrap());
        let terminal_value=expression(normal,&canonical);
        for kind in [Semantic::RowOwner,Semantic::Tag,Semantic::Stride,Semantic::Swap,Semantic::Dummy,Semantic::Endpoint]{
            // A valid row equality can remain satisfied under a substitution. Require
            // a nonzero reached terminal differential before asserting rejection.
            let selected=f.circuit.terms.iter().find_map(|original|{
                let changed=changed_term(&f,original,kind)?;
                let old=one_coeff(original,&r,&u,&v);let new=one_coeff(&changed,&r,&u,&v);
                let mut coefficients=normal;for i in 0..4{coefficients[i]+=new[i]-old[i];}
                (expression(coefficients,&canonical)!=terminal_value).then_some((original.clone(),changed))
            }).unwrap_or_else(||panic!("role2 semantic fault not sensitized: {kind:?}"));
            expect_consumer_fault(&f,&canonical,&canonical.proof,&f.prepared,GkrError::TerminalExpression,63,1,|r,u,v|{
                let mut coefficients=direct_coefficients(&f.circuit,r,u,v);
                let old=one_coeff(&selected.0,r,u,v);let new=one_coeff(&selected.1,r,u,v);
                for i in 0..4{coefficients[i]+=new[i]-old[i];}coefficients
            });
        }
        // Omit a whole member, not an arbitrary individual row that might vanish.
        let omitted=full_split_coefficients_omitting(&f.topology,f.engine,&f.fixed,&f.leaf,&f.work,false,&r,&u,&v,
            Some("header_to_leaf_raw_length_nbits_height")).unwrap();
        assert_ne!(expression(omitted,&canonical),terminal_value,"role2 member omission not sensitized");
        expect_consumer_fault(&f,&canonical,&canonical.proof,&f.prepared,GkrError::TerminalExpression,63,1,|r,u,v|{
            let mut coefficients=direct_coefficients(&f.circuit,r,u,v);
            for term in &f.circuit.terms{if term.row>>(BASE+2)==0{
                let contribution=one_coeff(term,r,u,v);for i in 0..4{coefficients[i]-=contribution[i];}
            }}coefficients
        });
        // A whole-member permutation and failure to advance the empty padding
        // member are separate tag faults, with the same existing proof reused.
        for collapse_empty in [false,true]{
            let altered=|r:&[Fr],u:&[Fr],v:&[Fr]|{
                let mut coefficients=direct_coefficients(&f.circuit,r,u,v);
                for term in &f.circuit.terms{
                    let family=term.row>>(BASE+2);let mut changed=term.clone();
                    if collapse_empty{if family<=6{continue;}changed.row-=1usize<<(BASE+2);}
                    else{if family>1{continue;}changed.row^=1usize<<(BASE+2);}
                    let old=one_coeff(term,r,u,v);let new=one_coeff(&changed,r,u,v);
                    for i in 0..4{coefficients[i]+=new[i]-old[i];}
                }coefficients
            };
            assert_ne!(expression(altered(&r,&u,&v),&canonical),terminal_value,
                "role2 whole-member/empty-member fault not sensitized");
            expect_consumer_fault(&f,&canonical,&canonical.proof,&f.prepared,GkrError::TerminalExpression,63,1,altered);
        }
        expect_consumer_fault(&f,&canonical,&canonical.proof,&f.prepared,GkrError::TerminalExpression,63,1,|r,u,v|{
            let mut coefficients=direct_coefficients(&f.circuit,r,u,v);coefficients[0]+=Fr::one();coefficients
        });
        let mut changed_round=canonical.proof.clone();changed_round.layers[0].rounds[0][1]+=Fr::one();
        expect_consumer_fault(&f,&canonical,&changed_round,&f.prepared,GkrError::SumcheckIdentity,19,0,
            |r,u,v|direct_coefficients(&f.circuit,r,u,v));drop(changed_round);

        let mut wrong_prefix=Transcript::new(b"role2-cross-endpoint-wrong-domain-v1");sparse::bind(&f.circuit,0,&mut wrong_prefix);
        let mut sensitized=wrong_prefix.clone();let _r=gkr::output_point(1usize<<ROW_BITS,&mut sensitized);
        gkr::append_usize(&mut sensitized,b"gkr-layer-index",0);
        let first=&canonical.proof.layers[0].rounds[0];let second=&canonical.proof.layers[0].rounds[1];
        assert_eq!(first[0]+gkr::eval_polynomial(first,Fr::one()),Fr::zero());
        gkr::append_polynomial(&mut sensitized,b"gkr-sumcheck-polynomial",first);
        let bad_challenge=sensitized.challenge_scalar(b"gkr-sumcheck-challenge");
        assert_ne!(gkr::eval_polynomial(first,bad_challenge),second[0]+gkr::eval_polynomial(second,Fr::one()),
            "role2 wrong prefix must reach the second identity");
        expect_consumer_fault(&f,&canonical,&canonical.proof,&wrong_prefix,GkrError::SumcheckIdentity,20,0,
            |r,u,v|direct_coefficients(&f.circuit,r,u,v));
        let changed_source=3*WIDTH;
        assert!(!eq_index(&canonical.claim.point,changed_source).is_zero(),"role2 inactive off-support source is not observable");
        assert_ne!(f.source_mle(&canonical.claim.point,Some(changed_source)),canonical.claim.value);
        let mut source_caller=f.initial.clone();let before=source_caller.clone();
        let rejected=consumer(&f,&canonical.proof,&f.prepared,&mut source_caller,Some(changed_source),
            |r,u,v|direct_coefficients(&f.circuit,r,u,v));
        assert!(rejected.error.is_none()&&rejected.source_error);
        assert_eq!(rejected.observed,counters(&prefix64));
        assert_eq!((rejected.binds,rejected.wires),(1,1));unchanged(&source_caller,&before);
        eprintln!("R2_CROSS_STAGE consumer_faults_done elapsed_ms={}",began.elapsed().as_millis());

        for fault in [Fault::Budget,Fault::Overflow,Fault::SourceSlot,Fault::Endpoint,Fault::Member,
            Fault::CountDrift,Fault::Read(1),Fault::Read(4),Fault::Short,Fault::Capacity,Fault::LateVisit]{
            let stage=match fault{
                Fault::Budget=>"budget",Fault::Overflow=>"overflow",Fault::SourceSlot=>"source_slot",
                Fault::Endpoint=>"endpoint",Fault::Member=>"member",Fault::CountDrift=>"count_drift",
                Fault::Read(1)=>"read1",Fault::Read(4)=>"read4",Fault::Short=>"short",
                Fault::Capacity=>"capacity",Fault::LateVisit=>"late_visit",_=>unreachable!(),
            };
            eprintln!("R2_CROSS_FAULT {stage} elapsed_ms={}",began.elapsed().as_millis());
            let mut caller=f.initial.clone();let before=caller.clone();
            let failure=match produce(&f,true,fault,&mut caller,retained){Err(e)=>e,Ok(_)=>panic!("role2 fault survived: {fault:?}")};
            assert_eq!(failure.hits,1,"role2 injection not reached: {fault:?}");assert_eq!(failure.wires,0);
            let expected=match fault{
                Fault::Budget|Fault::Overflow|Fault::SourceSlot|Fault::Endpoint|Fault::Member=>&f.initial,
                Fault::LateVisit=>&prefix20,
                _=>&prefix19,
            };
            assert_eq!(failure.observed,counters(expected),"role2 full reached prefix differs: {fault:?}");
            match fault{
                Fault::Budget=>{assert_eq!(failure.error,"role2 scoped preflight exceeds512MiB");assert_eq!((failure.loads,failure.visits,failure.binds,failure.observed[0]),(0,0,0,0));},
                Fault::Overflow=>{assert_eq!(failure.error,"role2 inventory overflow");assert_eq!((failure.loads,failure.visits,failure.binds,failure.observed[0]),(0,0,0,0));},
                Fault::SourceSlot|Fault::Endpoint|Fault::Member=>{
                    assert_eq!(failure.error,"edge endpoint wire or row outside declared slot");
                    assert_eq!((failure.loads,failure.visits,failure.binds,failure.observed[0]),(0,1,0,0));
                },
                Fault::CountDrift=>{assert_eq!(failure.error,"edge endpoint source count changed between passes");
                    // LEFT0 skips one fanout term, then reads profile owner1 and
                    // child/root owner0. The remaining terms introduce no2/3.
                    assert_eq!((failure.loads,failure.visits,failure.binds,failure.observed[0]),(2,9,1,19));},
                Fault::Read(call)=>{assert_eq!(failure.error,"role2 isolated loader failure");assert_eq!(failure.loads,call);
                    assert_eq!((failure.binds,failure.observed[0]),(1,19));},
                Fault::Short=>{assert_eq!(failure.error,GkrError::InvalidInputWidth.to_string());assert_eq!((failure.loads,failure.binds,failure.observed[0]),(1,1,19));},
                Fault::Capacity=>{assert_eq!(failure.error,"role2 loader capacity differs");assert_eq!((failure.loads,failure.binds,failure.observed[0]),(1,1,19));},
                Fault::LateVisit=>{assert_eq!(failure.error,"role2 isolated second-U visitor failure");
                    assert_eq!((failure.loads,failure.visits,failure.binds,failure.observed[0]),(4,13,1,20));},
                Fault::None=>unreachable!(),
            }unchanged(&caller,&before);
            assert!(began.elapsed()<Duration::from_secs(120));
        }
        assert_eq!(f.ledger.scoped,383041664);assert!(f.ledger.buckets.iter().all(|bytes|*bytes<=BUCKET));
        assert_eq!(f.base.endpoints.lower.len(),224);
        eprintln!("R2_CROSS_STAGE producer_faults_done elapsed_ms={}",began.elapsed().as_millis());
    }
}

#[cfg(test)]
mod full_roster_falsifier {
    use super::*;
    use crate::{daa_history_layout::HeaderAssignmentTemplate,gkr::{self,GkrError,GkrProof,InputClaim},
        nph2_header_source::MainnetH3Input,packed::{PackedFile,PackedFileWriter,PackedReaderFault},
        sparse,sparse_stream_roster::{self as edge,EdgeTerm},transcript::Transcript,
        work_tree_fixed_hash::{self as fixed,Engine,FixedProfile},
        work_tree_leaf_hash::{self as leaf,LeafProfile},work_tree_work::{self as work,WorkProfile}};
    use ark_serialize::CanonicalSerialize;
    use blake2::{Blake2b,Digest,digest::consts::U32};
    use num_bigint::BigUint;
    use std::{cell::{Cell,RefCell},mem::size_of,path::PathBuf,time::{Duration,Instant,SystemTime,UNIX_EPOCH}};

    const MIB:usize=1024*1024;
    const SCOPED:usize=512*MIB;
    const JOB:usize=2*1024*MIB;
    const AUX:usize=24*MIB;
    const AUX_BUCKETS:[usize;4]=[16*MIB,2*MIB,2*MIB,4*MIB];
    const METADATA:usize=17*MIB;
    const PREPARATION:usize=406941696;
    const PROOF_BOUND:usize=347734144;
    const TERMS:usize=111668;
    const BASE:usize=14;
    const ROW_BITS:usize=21;
    const INPUT_BITS:usize=22;
    const PACKED:usize=524288;
    const DOMAIN:&[u8]=b"role2-full-roster-honest-n3-falsifier-v1";
    const CONTINUE:&[u8]=b"role2-full-roster-falsifier-continuation";
    const STAGES:[&str;23]=["preflight","template_begin","template_ready","owner0_begin","owner0_ready",
        "owner1_begin","owner1_ready","owner2_begin","owner2_ready","owner3_begin","owner3_ready",
        "packed_ready","template_dropped","roster_ready","residuals_begin","residuals_ready",
        "producer_begin","producer_ready","consumers_begin","consumers_ready","faults_begin","faults_ready","complete"];
    const FAULTS:[&str;11]=["budget","overflow","source_slot","endpoint","member","count_drift",
        "read1","read4","short","capacity","late_visit"];
    fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or_else(||"role2 full byte overflow".into())}
    fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or_else(||"role2 full byte overflow".into())}
    fn need(value:bool,message:&str)->Result<(),String>{if value{Ok(())}else{Err(message.into())}}
    fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
    fn continuation(t:&Transcript)->Fr{t.clone().challenge_scalar(CONTINUE)}
    fn unchanged(a:&Transcript,b:&Transcript){assert_eq!(counters(a),counters(b));assert_eq!(continuation(a),continuation(b));}
    struct Progress {began:Instant,stage:Cell<usize>,fault:Cell<usize>}
    impl Progress {
        fn new()->Self{Self{began:Instant::now(),stage:Cell::new(0),fault:Cell::new(0)}}
        fn mark(&self,name:&str){let i=self.stage.get();assert_eq!(STAGES.get(i),Some(&name));
            assert!(self.began.elapsed()<Duration::from_secs(120));
            eprintln!("R2_FULL_STAGE {name} elapsed_ms={}",self.began.elapsed().as_millis());self.stage.set(i+1);}
        fn fault(&self,name:&str){let i=self.fault.get();assert_eq!(FAULTS.get(i),Some(&name));
            assert!(self.began.elapsed()<Duration::from_secs(120));
            eprintln!("R2_FULL_FAULT {name} elapsed_ms={}",self.began.elapsed().as_millis());self.fault.set(i+1);}
    }
    fn preflight(extra:usize)->Result<(),String>{
        need(size_of::<Fr>()==32&&size_of::<Term>()==152&&size_of::<usize>()==8,"role2 full typed ABI")?;
        let map=mul(add(5*65536+6690+26,32)?,1024)?;
        let preparation=add(add(add(add(add(map,mul(WIDTH,32)?)?,4*MIB)?,PACKED)?,WIDTH)?,AUX)?;
        need(preparation==PREPARATION&&preparation<=SCOPED,"role2 full preparation model changed")?;
        let proof=add(add(add(add(add(mul(9,mul(WIDTH,32)?)?,128)?,131072)?,mul(131072,152)?)?,PACKED)?,AUX)?;
        need(proof==PROOF_BOUND&&add(proof,extra)?<=SCOPED,"role2 full scoped preflight exceeds512MiB")?;
        need(add(384*MIB,preparation)?<=JOB&&add(64*MIB,proof)?<=JOB,"role2 full parent Job reservation")?;
        // Actual payloads are checked separately. These four source-derived buckets
        // cover small boundary parents/binding JSON, validation index and row scratch,
        // returned proofs/consumers, and packed MLE/IO/typed descriptors respectively.
        need(AUX_BUCKETS.iter().sum::<usize>()==AUX,"role2 full auxiliary model")?;
        need(add(add(384*MIB,18*MIB+9*MIB/4)?,METADATA)?<=SCOPED,"role2 full local construction model")
    }
    fn aux(bucket:usize,bytes:usize)->Result<(),String>{need(AUX_BUCKETS.get(bucket).is_some_and(|cap|bytes<=*cap),"role2 full auxiliary capacity")}
    fn local_heap(leaf_bytes:usize,work_bytes:usize,metadata:usize)->Result<(),String>{
        need(leaf_bytes<=12*MIB,"role2 full leaf capacity exceeds bound")?;
        need(work_bytes<=3*MIB/2,"role2 full work capacity exceeds bound")?;
        // 2 MiB includes work::count's cloned Term vector, JSON, private group
        // Vec capacity and bounded header/profile construction scratch.
        aux(0,add(add(add(leaf_bytes,work_bytes)?,metadata)?,2*MIB)?)
    }
    fn report_bytes(report:&serde_json::Value,key:&str)->Result<usize,String>{
        usize::try_from(report.get(key).and_then(serde_json::Value::as_u64)
            .ok_or("role2 full capacity report field")?).map_err(|_|"role2 full capacity report overflow".into())
    }
    fn family_heap(family:&Family)->Result<usize,String>{
        add(add(family.name.capacity(),mul(add(family.left_wires.capacity(),family.right_wires.capacity())?,8)?)?,
            family.constants.as_ref().map_or(0,Vec::capacity))
    }
    fn descriptor_heap(d:&Descriptor)->Result<usize,String>{
        let mut bytes=0;
        for s in [&d.schema,&d.leaf_schema,&d.padding_schema,&d.node_schema,&d.profile_schema]{bytes=add(bytes,s.capacity())?;}
        Ok(bytes)
    }
    fn check_order(row:&[Fr])->Result<(),String>{
        let order=crate::header_order::local_order()?;
        need(order.circuit.terms.capacity()==2081,"role2 full local order capacity")?;
        let offset=crate::header_order::ORDER_OFFSET;
        let mut previous=None;let mut sum=Fr::zero();
        for term in &order.circuit.terms{
            if previous!=Some(term.row){need(sum.is_zero(),"role2 full order residual")?;sum=Fr::zero();previous=Some(term.row);}
            let g=&term.gate;let a=row[offset+g.left];let b=row[offset+g.right];
            sum+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;
        }
        need(sum.is_zero(),"role2 full order residual")
    }
    fn be28(value:&BigUint)->Result<[u8;28],String>{let bytes=value.to_bytes_be();
        need(bytes.len()<=28,"role2 full U224 overflow")?;let mut out=[0;28];out[28-bytes.len()..].copy_from_slice(&bytes);Ok(out)}
    fn hash(bytes:&[u8])->[u8;32]{Blake2b::<U32>::digest(bytes).into()}
    fn honest_headers()->Result<MainnetH3Input,String>{
        #[derive(Deserialize)] struct Pack {networks:Networks}
        #[derive(Deserialize)] struct Networks {mainnet:Network}
        #[derive(Deserialize)] struct Network {source_headers_hex:Vec<String>}
        let pack:Pack=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"))
            .map_err(|e|e.to_string())?;
        need(pack.networks.mainnet.source_headers_hex.len()>=3,"role2 full fixture headers")?;
        aux(0,pack.networks.mainnet.source_headers_hex.iter().map(String::capacity).sum::<usize>()
            +pack.networks.mainnet.source_headers_hex.capacity()*size_of::<String>())?;
        let mut frame=Vec::with_capacity(4096);frame.extend_from_slice(b"NPH2");frame.extend_from_slice(&3u32.to_be_bytes());
        for text in pack.networks.mainnet.source_headers_hex.iter().take(3){
            need(!text.is_empty()&&text.len()%2==0&&text.len()<=1028,"role2 full fixture header extent")?;
            frame.extend_from_slice(&u32::try_from(text.len()/2).map_err(|_|"role2 full raw length")?.to_be_bytes());
            for pair in text.as_bytes().chunks_exact(2){let s=std::str::from_utf8(pair).map_err(|e|e.to_string())?;
                frame.push(u8::from_str_radix(s,16).map_err(|e|e.to_string())?);}
        }
        need(frame.capacity()<=4096,"role2 full frame capacity")?;
        MainnetH3Input::decode_nph2(&frame).map_err(|e|e.to_string())
    }
    struct Temporary {path:PathBuf,owned:bool,removed:bool}
    impl Temporary {
        fn fresh()->Result<Self,String>{let directory=std::env::temp_dir();
            need(directory.is_absolute()&&directory.is_dir(),"role2 full TEMP directory")?;
            let metadata=std::fs::symlink_metadata(&directory).map_err(|e|e.to_string())?;
            need(!metadata.file_type().is_symlink(),"role2 full TEMP link")?;
            #[cfg(windows)] {use std::os::windows::fs::MetadataExt;
                need(metadata.file_attributes()&0x400==0,"role2 full TEMP reparse")?;}
            let stamp=SystemTime::now().duration_since(UNIX_EPOCH).map_err(|e|e.to_string())?.as_nanos();
            let path=directory.join(format!("r2full-{}-{stamp}.bits",std::process::id()));
            need(path.as_os_str().len()<=240&&!path.exists(),"role2 full temporary path")?;
            Ok(Self{path,owned:false,removed:false})
        }
        fn remove(&mut self)->Result<(),String>{need(self.owned,"role2 full temporary not owned")?;
            std::fs::remove_file(&self.path).map_err(|e|e.to_string())?;
            need(!self.path.exists(),"role2 full temporary remains")?;self.removed=true;Ok(())}
    }
    impl Drop for Temporary {fn drop(&mut self){if self.owned&&!self.removed{let _=std::fs::remove_file(&self.path);}}}
    fn claim(row:&mut[Fr],claimed:&mut[bool],wire:usize,value:Fr)->Result<(),String>{
        need(wire<WIDTH&&(value.is_zero()||value.is_one()),"role2 full setter outside Boolean owner")?;
        need(!claimed[wire]||row[wire]==value,"role2 full conflicting explicit setter")?;
        row[wire]=value;claimed[wire]=true;Ok(())
    }
    fn mapped(row:&mut[Fr],claimed:&mut[bool],values:&BTreeMap<usize,Fr>,ranges:&[(usize,usize)],keys:&[&[usize]])->Result<(),String>{
        need(values.len()<=334396,"role2 full B3 map model exceeded")?;
        for &wire in values.keys(){need(ranges.iter().any(|&(start,len)|wire>=start&&wire-start<len)
            ||keys.iter().any(|bank|bank.contains(&wire)),"role2 full unexpected assignment key")?;}
        for &(start,len) in ranges{for wire in start..start+len{claim(row,claimed,wire,values.get(&wire).copied().unwrap_or_else(Fr::zero))?;}}
        for bank in keys{for &wire in *bank{claim(row,claimed,wire,values.get(&wire).copied().unwrap_or_else(Fr::zero))?;}}Ok(())
    }
    fn set_uint(row:&mut[Fr],claimed:&mut[bool],wires:&[usize],value:&BigUint)->Result<(),String>{
        need(value.bits()<=wires.len()as u64,"role2 full integer exceeds endpoint")?;
        for (bit,&wire) in wires.iter().enumerate(){claim(row,claimed,wire,Fr::from(value.bit(bit as u64)as u64))?;}Ok(())
    }
    fn owner(template:&HeaderAssignmentTemplate,engine:&Engine,leaf_boundary:&leaf::Boundary,fixed_profile:&FixedProfile,
        headers:&MainnetH3Input,slot:usize,intervals:&[(BigUint,BigUint,BigUint);2],profile:[u8;32],
        profile_bytes:&[u8],node_bytes:&[u8],expected_leaves:&[[u8;32];2])->Result<Vec<u8>,String>{
        HeaderAssignmentTemplate::role2_capacity_preflight_for_test(METADATA)?.require_preparation_for_test(METADATA)?;
        need(slot<4,"role2 full owner outside four")?;
        let selected=slot.min(2);let header=headers.headers()[selected].decoded();
        let fields=crate::serializer::Fields::from_header(header)?;
        let mut row=template.assign(&fields)?;
        need(row.len()==WIDTH&&row.capacity()==WIDTH,"role2 full owner allocation")?;
        let (previous_height,previous_timestamp)=if selected==0{(0,0)}else{
            let prev=headers.headers()[selected-1].decoded();(prev.height,prev.timestamp)};
        template.assign_order(&mut row,&fields,previous_height,previous_timestamp,selected==0)?;
        check_order(&row)?;
        if selected==0{
            let wire=crate::header_order::ORDER_OFFSET;
            need(row[wire].is_zero(),"role2 full genesis predecessor height")?;
            row[wire]=Fr::one();
            assert_eq!(check_order(&row).unwrap_err(),"role2 full order residual");
            row[wire]=Fr::zero();
        }
        template.role2_capacity_inventory_for_test(engine)?.require_bounds_for_test()?;
        // Clear only banks owned by B3/B2/endpoints. Header/hash/point/order banks
        // remain exactly the canonical assignment, including the repeated last header.
        let mut claimed=vec![true;WIDTH];need(claimed.capacity()==WIDTH,"role2 full setter bitmap capacity")?;
        for (start,len) in leaf::CORES.iter().map(|&start|(start,65536))
            .chain([(fixed::NODE_CORE,65536),(leaf::AUX,26),(ENDPOINT_BASE,ENDPOINT_WIDTH)]){
            for wire in start..start+len{row[wire]=Fr::zero();claimed[wire]=false;}
        }
        let e=&engine.base.endpoints;
        {
            let assigned=if slot<2{leaf::assign_header_leaf(engine,leaf_boundary,slot,headers.headers()[slot+1].decoded(),
                be28(&intervals[slot].0)?,be28(&intervals[slot].2)?,profile)?}
                else{leaf::assign_inactive_leaf(engine,leaf_boundary,slot,profile)?};
            if slot<2{need(assigned.digest==expected_leaves[slot],"role2 full B3 native digest differs")?;}
            let ranges=[(leaf::CORES[0],65536),(leaf::CORES[1],65536),(leaf::CORES[2],65536),
                (leaf::CORES[3],65536),(leaf::CORES[4],65536),(leaf::AUX,26)];
            mapped(&mut row,&mut claimed,&assigned.values,&ranges,
                &[&e.raw,&e.length,&e.height,&e.lower,&e.upper,&e.leaf,&e.profile])?;
        } // Drop the five-core BTreeMap before constructing either fixed map.
        {
            let bytes=match slot{0=>node_bytes,1=>profile_bytes,_=>&[]};
            let assigned=leaf::assign_fixed_slot_native(engine,fixed_profile,slot,bytes)?;
            need(assigned.values.len()<=65536+8192,"role2 full fixed map model exceeded")?;
            need(assigned.digest==leaf::native_fixed_preimage_hash(fixed_profile,slot,bytes)?,"role2 full B2 native digest differs")?;
            mapped(&mut row,&mut claimed,&assigned.values,&[(fixed::NODE_CORE,65536)],&[&e.node_left,&e.node_right,&e.node])?;
        }
        let zero=BigUint::from(0u8);
        if slot<2{
            let (lower,amount,upper)=&intervals[slot];
            let nbits=headers.headers()[slot+1].decoded().n_bits;
            set_uint(&mut row,&mut claimed,&e.n_bits,&BigUint::from(nbits))?;
            set_uint(&mut row,&mut claimed,&e.lower,lower)?;set_uint(&mut row,&mut claimed,&e.upper,upper)?;
            set_uint(&mut row,&mut claimed,&e.work,amount)?;
            set_uint(&mut row,&mut claimed,&e.work_minus_one,&(amount-BigUint::from(1u8)))?;
            for (exponent,&wire) in e.exponent.iter().enumerate(){claim(&mut row,&mut claimed,wire,Fr::from((exponent==(nbits>>24)as usize)as u64))?;}
        }else{
            for bank in [&e.n_bits,&e.lower,&e.upper,&e.work,&e.work_minus_one,&e.exponent]{set_uint(&mut row,&mut claimed,bank,&zero)?;}
        }
        for wire in ENDPOINT_BASE..ENDPOINT_BASE+ENDPOINT_WIDTH{if !claimed[wire]{claim(&mut row,&mut claimed,wire,Fr::zero())?;}}
        need(claimed.iter().all(|x|*x)&&row.iter().all(|x|x.is_zero()||x.is_one()),"role2 full unclaimed/nonBoolean assignment")?;
        if slot==3{need(row[crate::segment_points::POINT_OFFSET..crate::segment_points::POINT_OFFSET+crate::segment_points::POINT_WIDTH]
            .iter().any(|x|x.is_one()),"role2 full inactive header point bank was erased")?;}
        let mut packed=vec![0u8;WIDTH/8];need(packed.capacity()==WIDTH/8,"role2 full owner packed capacity")?;
        for (index,value) in row.iter().enumerate(){if value.is_one(){packed[index/8]|=1u8<<(index%8);}}
        Ok(packed)
    }
    struct Fixture {engine:&'static Engine,topology:Topology,fixed:FixedProfile,leaf:leaf::Boundary,work:work::Boundary,
        circuit:Circuit,members:Vec<usize>,source:PackedFile,bytes:Vec<u8>,temporary:Temporary,initial:Transcript,prepared:Transcript}
    impl Fixture {
        fn new(progress:&Progress)->Result<Self,String>{
            preflight(0)?;let plan=HeaderAssignmentTemplate::role2_capacity_preflight_for_test(METADATA)?;
            need(plan.preparation_bound_bytes==PREPARATION,"role2 full inventory plan differs")?;
            assert_eq!(HeaderAssignmentTemplate::role2_capacity_preflight_for_test(METADATA+1).unwrap_err(),
                "role2 inventory metadata capacity exceeds bound");
            let mut bad_plan=plan;bad_plan.construct_bound_bytes+=1;
            assert_eq!(bad_plan.require_preparation_for_test(METADATA).unwrap_err(),"role2 inventory static plan changed");
            progress.mark("preflight");progress.mark("template_begin");
            let base=layout::shared_baseline()?;let engine=fixed::engine()?;
            need(std::ptr::eq(base,engine.base),"role2 full detached shared baseline")?;
            let template=HeaderAssignmentTemplate::new()?;
            let inventory=template.role2_capacity_inventory_for_test(engine)?;inventory.require_bounds_for_test()?;
            for i in 0..5{
                let mut changed=inventory;changed.circuit_lengths[i]+=1;
                assert_eq!(changed.require_bounds_for_test().unwrap_err(),"role2 inventory circuit length changed");
                let mut changed=inventory;changed.circuit_capacities[i]=[689920,524288,524288,288158,2081][i]+1;
                assert_eq!(changed.require_bounds_for_test().unwrap_err(),"role2 inventory circuit capacity exceeds bound");
            }
            let mut changed=inventory;changed.template_private_source_bound_bytes+=1;
            assert_eq!(changed.require_bounds_for_test().unwrap_err(),"role2 inventory payload accounting changed");
            let mut changed=inventory;changed.shared_core_capacity=262145;
            assert_eq!(changed.require_bounds_for_test().unwrap_err(),"role2 inventory shared core capacity exceeds bound");
            let mut changed=inventory;changed.shared_baseline_public_capacity_bytes=16*MIB+1;
            assert_eq!(changed.require_bounds_for_test().unwrap_err(),"role2 inventory shared baseline accounting changed");
            let mut changed=inventory;changed.retained_total_bound_bytes+=1;
            assert_eq!(changed.require_bounds_for_test().unwrap_err(),"role2 inventory total accounting changed");
            let mut changed=inventory;changed.template_public_capacity_bytes=usize::MAX;
            assert_eq!(changed.require_bounds_for_test().unwrap_err(),"role2 inventory byte addition overflow");
            progress.mark("template_ready");
            let headers=honest_headers()?;let provisional=LeafProfile::new(3,[0;32])?;
            let mut profile_bytes=Vec::with_capacity(59);profile_bytes.extend_from_slice(fixed::PROFILE_PREFIX);
            profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
            need(profile_bytes.len()==59&&profile_bytes.capacity()==59,"role2 full profile capacity")?;
            let profile=hash(&profile_bytes);let first=work::native_decode(headers.headers()[1].decoded().n_bits)?;
            let second=work::native_decode(headers.headers()[2].decoded().n_bits)?;
            need(!first.is_zero()&&!second.is_zero(),"role2 full work is not positive")?;
            let total=&first+&second;
            let intervals=[(BigUint::from(0u8),first.clone(),first.clone()),(first,second,total.clone())];
            let mut digests=[[0u8;32];2];
            for slot in 0..2{digests[slot]=leaf::native_leaf_preimage_hash(&provisional,slot,headers.headers()[slot+1].raw_bytes(),
                headers.headers()[slot+1].decoded().height,be28(&intervals[slot].0)?,be28(&intervals[slot].2)?,profile)?;}
            let mut node_bytes=Vec::with_capacity(70);node_bytes.extend_from_slice(b"N\x01\x00\x00\x00\x00");
            node_bytes.extend_from_slice(&digests[0]);node_bytes.extend_from_slice(&digests[1]);
            need(node_bytes.capacity()==70,"role2 full node capacity")?;
            let root=leaf::native_fixed_preimage_hash(&FixedProfile::new(3,[0;32])?,0,&node_bytes)?;
            let topology=Topology::new(base,3,root)?;let fixed=FixedProfile::new(3,root)?;
            let leaf=leaf::compile(engine,LeafProfile::new(3,root)?)?;
            let work=work::compile(base,WorkProfile::new(3,root,be28(&total)?)?)?;
            need(full_roster_shape(&topology)?==(16,5,ROW_BITS,INPUT_BITS)&&topology.families.len()==12,
                "role2 full roster geometry")?;
            let mut small=add(size_of::<Self>(),size_of::<MainnetH3Input>())?;
            small=add(small,mul(topology.families.capacity(),size_of::<Family>())?)?;
            for family in &topology.families{small=add(small,family_heap(family)?)?;}
            small=add(small,topology.frozen_manifest.capacity())?;
            small=add(small,mul(leaf.families.capacity(),size_of::<leaf::Family>())?)?;
            for family in &leaf.families{small=add(small,family.name.capacity())?;}
            for family in work.links(){small=add(small,family_heap(family)?)?;}
            // The private group Vec is source-bounded in the 2 MiB reserve.
            need(work.groups().len()<=32,"role2 full work group count")?;
            for group in work.groups(){small=add(small,group.name.capacity())?;}
            for d in [&topology.descriptor,&fixed.tree,&leaf.profile.tree,&work.profile().tree]{small=add(small,descriptor_heap(d)?)?;}
            for s in [&fixed.schema,&fixed.native_work_sha256,&leaf.profile.schema,&leaf.profile.lower_upper_encoding,
                &leaf.profile.raw_tail_producer,&leaf.profile.native_work_sha256,&work.profile().schema,
                &work.profile().integer_encoding,&work.profile().native_work_sha256]{small=add(small,s.capacity())?;}
            small=add(small,add(fixed.prefix.capacity(),add(profile_bytes.capacity(),node_bytes.capacity())?)?)?;
            // Admit source-derived maxima before constructing either report; then
            // check actual private term capacities via existing count APIs.
            local_heap(12*MIB,3*MIB/2,small)?;
            assert_eq!(local_heap(12*MIB+1,0,0).unwrap_err(),"role2 full leaf capacity exceeds bound");
            assert_eq!(local_heap(0,3*MIB/2+1,0).unwrap_err(),"role2 full work capacity exceeds bound");
            assert_eq!(local_heap(12*MIB,3*MIB/2,MIB/2+1).unwrap_err(),"role2 full auxiliary capacity");
            let leaf_report=leaf::count(engine,&leaf)?;
            let leaf_bytes=report_bytes(&leaf_report,"retained_local_boundary_capacity_bytes")?;
            drop(leaf_report);
            let work_report=work::count(&work)?;
            let work_bytes=report_bytes(&work_report,"retained_local_term_capacity_bytes")?;
            drop(work_report);
            local_heap(leaf_bytes,work_bytes,small)?;
            let mut temporary=Temporary::fresh()?;
            let mut writer=PackedFileWriter::create_new(&temporary.path,INPUT_BITS)?;
            temporary.owned=true;
            let mut bytes=Vec::new();bytes.try_reserve_exact(PACKED).map_err(|_|"role2 full packed allocation")?;
            need(bytes.capacity()==PACKED,"role2 full packed destination capacity")?;
            for slot in 0..4{
                progress.mark(["owner0_begin","owner1_begin","owner2_begin","owner3_begin"][slot]);
                plan.require_preparation_for_test(METADATA)?;
                let packed=owner(&template,engine,&leaf,&fixed,&headers,slot,&intervals,profile,&profile_bytes,&node_bytes,&digests)?;
                writer.write_bytes(&packed)?;bytes.extend_from_slice(&packed);drop(packed);
                progress.mark(["owner0_ready","owner1_ready","owner2_ready","owner3_ready"][slot]);
            }
            let source=writer.finish()?;need(bytes.len()==PACKED&&source.input_len()==1usize<<INPUT_BITS,"role2 full packed extent")?;
            let view=source.h2_boolean_view()?;view.require_same_source(&source)?;view.check_expected(&bytes)?;
            progress.mark("packed_ready");drop(template);progress.mark("template_dropped");
            // HeaderAssignmentTemplate is no longer retained during circuit growth.
            // Source-derived old/new/largest-member payload is 39845888B, below
            // the proof reservation and independent of the discarded B3 maps.
            need(mul(65536+131072+65536,152)?==39845888,"role2 full roster construction model")?;
            let circuit=full_roster_circuit(&topology,engine,&fixed,&leaf,&work)?;
            need(circuit.terms.len()==TERMS&&circuit.terms.capacity()<=131072&&circuit.row_count==1usize<<ROW_BITS
                &&circuit.input_len==1usize<<INPUT_BITS,"role2 full reference census/capacity")?;
            sparse::validate(&circuit,0).map_err(|e|e.to_string())?;
            let mut members=Vec::with_capacity(18);
            for family in &topology.families{members.push(family.count(&topology.descriptor)?.row_log-2);}
            members.extend_from_slice(&[11,14,11]);
            for family in work.links(){members.push(family.count(&topology.descriptor)?.row_log-2);}
            need(members.len()==18&&members.capacity()==18&&members.iter().all(|b|*b<=BASE),"role2 full member strides")?;
            let initial=Transcript::new(DOMAIN);let mut prepared=initial.clone();
            bind_full_roster(&topology,&fixed,&leaf.profile,work.profile(),&mut prepared);
            progress.mark("roster_ready");
            Ok(Self{engine,topology,fixed,leaf,work,circuit,members,source,bytes,temporary,initial,prepared})
        }
        fn decode_row(&self,row:usize)->Result<(usize,usize),String>{let family=row>>16;
            let bits=*self.members.get(family).ok_or("role2 full family outside roster")?;
            let allocated=row&65535;let source=allocated>>bits;let low=allocated&((1usize<<bits)-1);
            need(source<4,"role2 full occupied member padding")?;Ok((source,(family<<BASE)|low))}
        fn emit(&self,mut sink:impl FnMut(usize,Term)->Result<(),String>)->Result<(),String>{
            let mut member=0usize;
            for family in &self.topology.families{family.emit_terms(&self.topology.descriptor,|mut t|{t.row+=member<<16;sink(member,t)})?;member+=1;}
            for kind in 0..3{
                for slot in 0..4{let mut error=None;let mut push=|mut term:Term|{if error.is_none(){term.row+=member<<16;
                    if let Err(e)=sink(member,term){error=Some(e);}}};
                    match kind{0=>fixed::emit_slot(self.engine,&self.fixed,slot,&mut push)?,
                        1=>self.leaf.emit_slot(slot,&mut push)?,_=>self.work.emit_slot(slot,&mut push)?,}
                    if let Some(e)=error{return Err(e);}
                }member+=1;
            }
            for family in self.work.links(){family.emit_terms(&self.topology.descriptor,|mut t|{t.row+=member<<16;sink(member,t)})?;member+=1;}
            need(member==18,"role2 full streaming member roster")
        }
        fn visit(&self,left:bool,owner:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
            need(owner<4,"role2 full endpoint owner")?;
            self.emit(|_,term|{if (if left{term.gate.left}else{term.gate.right})/WIDTH==owner{
                let(source_slot,family_row)=self.decode_row(term.row)?;
                sink(EdgeTerm{source_slot,family_row,term})?;}Ok(())})
        }
        fn bit(&self,index:usize)->Fr{assert!(index<4*WIDTH);Fr::from(((self.bytes[index/8]>>(index%8))&1)as u64)}
        fn validate_sources(&self)->Result<(),String>{
            aux(1,add(mul(TERMS,8+1)?,256*1024)?)?;
            let mut index=Vec::with_capacity(TERMS);index.extend(0..TERMS);
            need(index.capacity()==TERMS,"role2 full validation index capacity")?;
            index.sort_unstable_by_key(|&i|{let t=&self.circuit.terms[i];(t.row,t.gate.left,t.gate.right)});
            let mut seen=vec![0u8;TERMS];need(seen.capacity()==TERMS,"role2 full multiset bitmap capacity")?;
            let mut counts=[0usize;18];let mut expected=[0usize;18];
            for t in &self.circuit.terms{expected[t.row>>16]+=1;}
            self.emit(|member,term|{
                let key=(term.row,term.gate.left,term.gate.right);
                let lo=index.partition_point(|&i|{let t=&self.circuit.terms[i];(t.row,t.gate.left,t.gate.right)<key});
                let hi=index.partition_point(|&i|{let t=&self.circuit.terms[i];(t.row,t.gate.left,t.gate.right)<=key});
                let matched=index[lo..hi].iter().copied().find(|&i|seen[i]==0&&self.circuit.terms[i]==term)
                    .ok_or("role2 full multiplicity mismatch")?;seen[matched]=1;counts[member]+=1;Ok(())
            })?;
            need(counts==expected&&counts.iter().sum::<usize>()==TERMS&&counts[9]==0&&seen.iter().all(|n|*n==1),
                "role2 full canonical member census")?;
            for left in [true,false]{seen.fill(0);let mut total=0;let mut cross=false;
                for endpoint in 0..4{let expected=self.circuit.terms.iter().filter(|t|(if left{t.gate.left}else{t.gate.right})/WIDTH==endpoint).count();
                    let mut n=0;self.visit(left,endpoint,&mut |item|{
                        let key=(item.term.row,item.term.gate.left,item.term.gate.right);
                        let lo=index.partition_point(|&i|{let t=&self.circuit.terms[i];(t.row,t.gate.left,t.gate.right)<key});
                        let hi=index.partition_point(|&i|{let t=&self.circuit.terms[i];(t.row,t.gate.left,t.gate.right)<=key});
                        let i=index[lo..hi].iter().copied().find(|&i|seen[i]==0&&self.circuit.terms[i]==item.term)
                            .ok_or("role2 full endpoint multiset mismatch")?;seen[i]=1;n+=1;
                        need(edge::global_edge_row(item.source_slot,item.family_row,2,BASE,5,&self.members)?==item.term.row,
                            "role2 full row/source identity")?;cross|=item.source_slot!=endpoint;Ok(())
                    })?;need(n==expected,"role2 full endpoint census")?;total+=n;
                }need(total==TERMS&&seen.iter().all(|n|*n==1)&&cross,"role2 full endpoint coverage")?;
            }
            let mut previous=None;let mut residual=Fr::zero();let mut rows=0usize;
            for &i in &index{let term=&self.circuit.terms[i];
                if previous!=Some(term.row){if previous.is_some(){need(residual.is_zero(),"role2 full honest row residual")?;rows+=1;}
                    previous=Some(term.row);residual=Fr::zero();}
                let x=self.bit(term.gate.left);let y=self.bit(term.gate.right);
                residual+=term.gate.c0+term.gate.c1*x+term.gate.c2*y+term.gate.c3*x*y;
            }
            need(previous.is_some()&&residual.is_zero()&&rows<TERMS,"role2 full additive residual census")?;
            drop(index);drop(seen);
            for seed in [3u64,97u64]{let point=|bits:usize,offset:u64|(0..bits).map(|i|Fr::from(seed+offset+37*(i as u64+1))).collect::<Vec<_>>();
                let r=point(ROW_BITS,0);let u=point(INPUT_BITS,101);let v=point(INPUT_BITS,211);
                need(direct_coefficients(&self.circuit,&r,&u,&v)==self.analytic(&r,&u,&v)?,"role2 full analytic reference differs")?;
            }Ok(())
        }
        fn analytic(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
            full_roster_coefficients(&self.topology,self.engine,&self.fixed,&self.leaf,&self.work,r,u,v)}
        fn load(&self,owner:usize,fault:Fault)->Result<Vec<Fr>,String>{
            let view=self.source.h2_boolean_view()?;view.require_same_source(&self.source)?;
            let bits=if fault==Fault::Short{
                let error=view.reader_fault_for_test(owner,PackedReaderFault::ShortByOneByte).err()
                    .ok_or("role2 full short fault survived")?;
                need(error.contains("one-byte-short packed four-owner reader fault"),"role2 full short wrong stage")?;
                return Err("role2 full isolated packed short".into());
            }else{view.read_copy(owner)?};
            need(bits.len()==WIDTH&&bits.capacity_bytes()<=131072,"role2 full packed owner width/capacity")?;
            let requested=if fault==Fault::Capacity{WIDTH+1}else{WIDTH};
            let mut values=Vec::new();values.try_reserve_exact(requested).map_err(|_|"role2 full loader allocation")?;
            need(values.capacity()==WIDTH,"role2 full loader capacity differs")?;
            for i in 0..WIDTH{values.push(Fr::from(bits.bit_at(i)as u64));}drop(bits);Ok(values)
        }
        fn close(self)->Result<(),String>{let Self{source,mut temporary,..}=self;drop(source);temporary.remove()}
    }
    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    enum Fault {None,Budget,Overflow,SourceSlot,Endpoint,Member,CountDrift,Read(usize),Short,Capacity,LateVisit}
    #[derive(Debug)] struct Failure {error:String,loads:usize,visits:usize,hits:usize,binds:usize,wires:usize,observed:[u64;3]}
    struct Produced {proof:GkrProof,packet:Vec<u8>,claim:InputClaim,transcript:Transcript}
    fn proof_capacity(proof:&GkrProof)->Result<usize,String>{let mut bytes=add(size_of::<GkrProof>(),mul(proof.layers.capacity(),size_of::<gkr::LayerProof>())?)?;
        for layer in &proof.layers{bytes=add(bytes,mul(layer.rounds.capacity(),size_of::<Vec<Fr>>())?)?;
            bytes=add(bytes,mul(layer.line_coefficients.capacity(),32)?)?;
            for round in &layer.rounds{bytes=add(bytes,mul(round.capacity(),32)?)?;}}Ok(bytes)}
    fn produce(f:&Fixture,fault:Fault,caller:&mut Transcript)->Result<Produced,Failure>{
        let mut working=caller.clone();let loads=Cell::new(0);let visits=Cell::new(0);let hits=Cell::new(0);
        let binds=Cell::new(0);let wires=Cell::new(0);let terms=Cell::new(0);
        let fail=|error:String,working:&Transcript|Failure{error,loads:loads.get(),visits:visits.get(),hits:hits.get(),
            binds:binds.get(),wires:wires.get(),observed:counters(working)};
        let extra=match fault{Fault::Budget=>SCOPED-PROOF_BOUND+1,Fault::Overflow=>usize::MAX,_=>0};
        preflight(extra).map_err(|e|{hits.set(1);fail(e,&working)})?;
        let result=edge::prove_edge_terms_with_cache_limit_for_test(20,2,BASE,5,&f.members,0,
            |left,owner,sink|{
                visits.set(visits.get()+1);let visit=visits.get();let mut first=true;
                if fault==Fault::LateVisit&&visit==13{hits.set(1);return Err("role2 full isolated second-U visitor".into());}
                f.visit(left,owner,&mut |mut item|{
                    if first{first=false;match fault{
                        Fault::SourceSlot if visit==1=>{item.source_slot=4;hits.set(1);},
                        Fault::Endpoint if visit==1=>{item.term.gate.left=4*WIDTH;hits.set(1);},
                        Fault::Member if visit==1=>{item.family_row=32usize<<BASE;hits.set(1);},
                        Fault::CountDrift if visit==9=>{hits.set(1);return Ok(());},_=>{}
                    }}terms.set(terms.get()+1);sink(item)
                })
            },|owner|{loads.set(loads.get()+1);let call=loads.get();
                if fault==Fault::Read(call){hits.set(1);
                    let error=f.source.h2_boolean_view()?.reader_fault_for_test(owner,PackedReaderFault::Io).err()
                        .ok_or("role2 full read fault survived")?;
                    need(error.contains("isolated packed four-owner reader fault"),"role2 full read wrong stage")?;
                    return Err("role2 full isolated packed IO".into());}
                let selected=if call==1&&matches!(fault,Fault::Short|Fault::Capacity){hits.set(1);fault}else{Fault::None};
                f.load(owner,selected)
            },&mut working,|t|{binds.set(binds.get()+1);*t=f.prepared.clone();},
            |r,u,v|{wires.set(wires.get()+1);Ok(direct_coefficients(&f.circuit,r,u,v))});
        let(proof,claim,used_u,used_v)=result.map_err(|e|fail(e,&working))?;
        need(!used_u&&!used_v&&proof.layers.len()==1&&proof.layers[0].rounds.len()==44
            &&proof.layers[0].line_coefficients.len()==23&&working.challenges()==66,"role2 full producer ABI")
            .map_err(|e|fail(e,&working))?;
        aux(2,add(proof_capacity(&proof).map_err(|e|fail(e,&working))?,256*1024).map_err(|e|fail(e,&working))?)
            .map_err(|e|fail(e,&working))?;
        let packet=gkr::encode_proof(&proof).map_err(|e|fail(e,&working))?;
        need((7*INPUT_BITS+3)*Fr::zero().compressed_size()==5024&&packet.len()==5024&&packet.capacity()<=16384,
            "role2 full packet ABI").map_err(|e|fail(e,&working))?;
        let decoded=gkr::decode_dimensions(&[INPUT_BITS],&packet).map_err(|e|fail(e,&working))?;
        need(decoded==proof&&gkr::encode_proof(&decoded).map_err(|e|fail(e,&working))?==packet,"role2 full canonical codec")
            .map_err(|e|fail(e,&working))?;drop(decoded);
        let mut verifier=caller.clone();
        let consumed=gkr::verify_with_wiring(&[INPUT_BITS],1usize<<ROW_BITS,&proof,&mut verifier,
            |t|*t=f.prepared.clone(),|_,r,u,v|f.analytic(r,u,v).map_err(|_|GkrError::PointDimension))
            .map_err(|e|fail(e.to_string(),&working))?;
        need(consumed==claim&&counters(&verifier)==counters(&working)&&continuation(&verifier)==continuation(&working),
            "role2 full analytic verifier differs").map_err(|e|fail(e,&working))?;
        aux(3,2*MIB).map_err(|e|fail(e,&working))?;
        need(f.source.evaluate(&claim.point).map_err(|e|fail(e,&working))?==claim.value,"role2 full packed source MLE differs")
            .map_err(|e|fail(e,&working))?;
        f.source.h2_boolean_view().and_then(|v|v.check_expected(&f.bytes)).map_err(|e|fail(e,&working))?;
        need((loads.get(),visits.get(),terms.get(),binds.get(),wires.get())==(4,176,44*TERMS,1,1),"role2 full producer census")
            .map_err(|e|fail(e,&working))?;
        *caller=working.clone();Ok(Produced{proof,packet,claim,transcript:working})
    }
    fn prefix(prepared:&Transcript,proof:&GkrProof,rounds:usize,line:bool)->Transcript{
        assert!(rounds<=44&&(!line||rounds==44));let mut t=prepared.clone();
        for _ in 0..ROW_BITS{t.challenge_scalar(b"gkr-output-coordinate");}
        t.append_bytes(b"gkr-layer-index",&0u64.to_le_bytes());
        for polynomial in proof.layers[0].rounds.iter().take(rounds){gkr::append_polynomial(&mut t,b"gkr-sumcheck-polynomial",polynomial);
            t.challenge_scalar(b"gkr-sumcheck-challenge");}
        if line{let layer=&proof.layers[0];t.append_scalar(b"gkr-left-value",&layer.left_value);
            t.append_scalar(b"gkr-right-value",&layer.right_value);gkr::append_polynomial(&mut t,b"gkr-line-polynomial",&layer.line_coefficients);
            t.challenge_scalar(b"gkr-line-challenge");}t
    }
    fn terminal_points(f:&Fixture,out:&Produced)->(Vec<Fr>,Vec<Fr>,Vec<Fr>){let mut t=f.prepared.clone();
        let r=gkr::output_point(1usize<<ROW_BITS,&mut t);gkr::append_usize(&mut t,b"gkr-layer-index",0);
        let mut q=Vec::with_capacity(44);for polynomial in &out.proof.layers[0].rounds{
            gkr::append_polynomial(&mut t,b"gkr-sumcheck-polynomial",polynomial);q.push(t.challenge_scalar(b"gkr-sumcheck-challenge"));}
        (r,q[..INPUT_BITS].to_vec(),q[INPUT_BITS..].to_vec())}
    fn one(term:&Term,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{let w=eq_index(r,term.row)*eq_index(u,term.gate.left)*eq_index(v,term.gate.right);
        [w*term.gate.c0,w*term.gate.c1,w*term.gate.c2,w*term.gate.c3]}
    fn expression(coeff:[Fr;4],out:&Produced)->Fr{let l=&out.proof.layers[0];coeff[0]+coeff[1]*l.left_value+coeff[2]*l.right_value+coeff[3]*l.left_value*l.right_value}
    fn reject(f:&Fixture,out:&Produced,proof:&GkrProof,prepared:&Transcript,error:GkrError,rounds:usize,wiring_calls:usize,
        wiring:impl Fn(&[Fr],&[Fr],&[Fr])->[Fr;4]){
        let caller=f.initial.clone();let before=caller.clone();let mut working=caller.clone();let binds=Cell::new(0);let wires=Cell::new(0);
        let result=gkr::verify_with_wiring(&[INPUT_BITS],1usize<<ROW_BITS,proof,&mut working,
            |t|{binds.set(binds.get()+1);*t=prepared.clone();},|_,r,u,v|{wires.set(wires.get()+1);Ok(wiring(r,u,v))});
        assert_eq!(result.unwrap_err(),error);assert_eq!(counters(&working),counters(&prefix(prepared,proof,rounds,false)));
        assert_eq!((binds.get(),wires.get()),(1,wiring_calls));unchanged(&caller,&before);assert_eq!(out.transcript.challenges(),66);
    }
    fn consumer_faults(f:&Fixture,out:&Produced){
        let(r,u,v)=terminal_points(f,out);let normal=direct_coefficients(&f.circuit,&r,&u,&v);
        assert_eq!(normal,f.analytic(&r,&u,&v).unwrap());let terminal=expression(normal,out);
        // Each substitution is sensitized at the real terminal before testing its
        // rejection. Valid equality endpoints need not have different witness values.
        for kind in 0..6{
            let selected=f.circuit.terms.iter().find_map(|original|{
                let(source,local)=f.decode_row(original.row).unwrap();let family=local>>BASE;let low=local&((1<<BASE)-1);
                let mut changed=original.clone();match kind{
                    0=>{if source==original.gate.right/WIDTH{return None;}changed.row=(family<<16)|((original.gate.right/WIDTH)<<f.members[family])|low;},
                    1=>changed.row^=1<<16,
                    2=>{if source==0||f.members[family]==BASE{return None;}changed.row=(family<<16)|(source<<BASE)|low;},
                    3=>{if original.gate.c2.is_zero()||original.gate.left==original.gate.right{return None;}std::mem::swap(&mut changed.gate.left,&mut changed.gate.right);},
                    4=>{if source==0||!original.gate.c2.is_zero()||original.gate.right!=0{return None;}changed.gate.right=source*WIDTH;},
                    _=>changed.gate.left^=1,
                }
                let a=one(original,&r,&u,&v);let b=one(&changed,&r,&u,&v);let mut c=normal;
                for i in 0..4{c[i]+=b[i]-a[i];}(expression(c,out)!=terminal).then_some((original.clone(),changed))
            }).unwrap_or_else(||panic!("role2 full substitution {kind} not sensitized"));
            reject(f,out,&out.proof,&f.prepared,GkrError::TerminalExpression,44,1,|r,u,v|{
                let mut c=direct_coefficients(&f.circuit,r,u,v);let a=one(&selected.0,r,u,v);let b=one(&selected.1,r,u,v);
                for i in 0..4{c[i]+=b[i]-a[i];}c});
        }
        for mode in 0..3{
            let altered=|r:&[Fr],u:&[Fr],v:&[Fr]|{
                let mut c=direct_coefficients(&f.circuit,r,u,v);
                for original in &f.circuit.terms{let tag=original.row>>16;let mut changed=original.clone();
                    match mode{0=>{if tag!=0{continue;}let a=one(original,r,u,v);for i in 0..4{c[i]-=a[i];}continue;},
                        1=>{if tag>1{continue;}changed.row^=1<<16;},
                        _=>{if tag<=9{continue;}changed.row-=1<<16;}}
                    let a=one(original,r,u,v);let b=one(&changed,r,u,v);for i in 0..4{c[i]+=b[i]-a[i];}
                }c};
            assert_ne!(expression(altered(&r,&u,&v),out),terminal,"role2 full omission/order/empty-member prerequisite");
            reject(f,out,&out.proof,&f.prepared,GkrError::TerminalExpression,44,1,altered);
        }
        reject(f,out,&out.proof,&f.prepared,GkrError::TerminalExpression,44,1,|r,u,v|{
            let mut c=direct_coefficients(&f.circuit,r,u,v);c[0]+=Fr::one();c});
        let mut bad=out.proof.clone();bad.layers[0].rounds[0][1]+=Fr::one();
        reject(f,out,&bad,&f.prepared,GkrError::SumcheckIdentity,0,0,|r,u,v|direct_coefficients(&f.circuit,r,u,v));drop(bad);
        let mut wrong=Transcript::new(b"role2-full-roster-wrong-domain-v1");
        bind_full_roster(&f.topology,&f.fixed,&f.leaf.profile,f.work.profile(),&mut wrong);
        let reached=prefix(&wrong,&out.proof,1,false);let mut t=wrong.clone();gkr::output_point(1usize<<ROW_BITS,&mut t);
        gkr::append_usize(&mut t,b"gkr-layer-index",0);let first=&out.proof.layers[0].rounds[0];let second=&out.proof.layers[0].rounds[1];
        assert_eq!(first[0]+gkr::eval_polynomial(first,Fr::one()),Fr::zero());
        gkr::append_polynomial(&mut t,b"gkr-sumcheck-polynomial",first);let q=t.challenge_scalar(b"gkr-sumcheck-challenge");
        unchanged(&t,&reached);assert_ne!(gkr::eval_polynomial(first,q),second[0]+gkr::eval_polynomial(second,Fr::one()),
            "role2 full wrong-prefix second identity prerequisite");
        reject(f,out,&out.proof,&wrong,GkrError::SumcheckIdentity,1,0,|r,u,v|direct_coefficients(&f.circuit,r,u,v));
        // An off-support inactive header bit remains part of the source MLE.
        let index=3*WIDTH+crate::segment_points::POINT_OFFSET;
        let weight=eq_index(&out.claim.point,index);assert!(!weight.is_zero());
        let delta=if f.bit(index).is_zero(){Fr::one()}else{-Fr::one()};
        let caller=f.initial.clone();let before=caller.clone();let mut working=caller.clone();let wires=Cell::new(0);
        let claim=gkr::verify_with_wiring(&[INPUT_BITS],1usize<<ROW_BITS,&out.proof,&mut working,|t|*t=f.prepared.clone(),
            |_,r,u,v|{wires.set(wires.get()+1);Ok(direct_coefficients(&f.circuit,r,u,v))}).unwrap();
        assert_eq!(claim,out.claim);assert_eq!(wires.get(),1);assert_ne!(claim.value,f.source.evaluate(&claim.point).unwrap()+delta*weight);
        unchanged(&working,&prefix(&f.prepared,&out.proof,44,true));unchanged(&caller,&before);
    }
    #[test]
    fn role2_full_roster_honest_packed_kernel_consumers_and_faults(){
        let progress=Progress::new();let f=Fixture::new(&progress).unwrap();
        progress.mark("residuals_begin");f.validate_sources().unwrap();progress.mark("residuals_ready");
        progress.mark("producer_begin");let mut caller=f.initial.clone();let out=produce(&f,Fault::None,&mut caller).unwrap();
        unchanged(&caller,&out.transcript);assert_eq!(out.packet.len(),5024);progress.mark("producer_ready");
        progress.mark("consumers_begin");consumer_faults(&f,&out);progress.mark("consumers_ready");
        aux(2,proof_capacity(&out.proof).unwrap()+out.packet.capacity()+out.claim.point.capacity()*32+256*1024).unwrap();
        progress.mark("faults_begin");
        for (fault,name) in [Fault::Budget,Fault::Overflow,Fault::SourceSlot,Fault::Endpoint,Fault::Member,Fault::CountDrift,
            Fault::Read(1),Fault::Read(4),Fault::Short,Fault::Capacity,Fault::LateVisit].into_iter().zip(FAULTS){
            progress.fault(name);let mut caller=f.initial.clone();let before=caller.clone();
            let error=match produce(&f,fault,&mut caller){Err(e)=>e,Ok(_)=>panic!("role2 full fault survived: {fault:?}")};
            assert_eq!(error.hits,1);assert_eq!(error.wires,0);unchanged(&caller,&before);
            let expected=match fault{Fault::Budget|Fault::Overflow|Fault::SourceSlot|Fault::Endpoint|Fault::Member=>f.initial.clone(),
                Fault::LateVisit=>prefix(&f.prepared,&out.proof,1,false),_=>prefix(&f.prepared,&out.proof,0,false)};
            assert_eq!(error.observed,counters(&expected),"role2 full fault reached prefix: {fault:?}");
            match fault{
                Fault::Budget=>{assert_eq!(error.error,"role2 full scoped preflight exceeds512MiB");assert_eq!((error.loads,error.visits,error.binds),(0,0,0));},
                Fault::Overflow=>{assert_eq!(error.error,"role2 full byte overflow");assert_eq!((error.loads,error.visits,error.binds),(0,0,0));},
                Fault::SourceSlot|Fault::Endpoint|Fault::Member=>{assert_eq!(error.error,"edge endpoint wire or row outside declared slot");
                    assert_eq!((error.loads,error.visits,error.binds),(0,1,0));},
                Fault::CountDrift=>{assert_eq!(error.error,"edge endpoint source count changed between passes");assert_eq!((error.loads,error.visits,error.binds),(2,9,1));},
                Fault::Read(call)=>{assert_eq!(error.error,"role2 full isolated packed IO");assert_eq!((error.loads,error.binds),(call,1));},
                Fault::Short=>{assert_eq!(error.error,"role2 full isolated packed short");assert_eq!((error.loads,error.binds),(1,1));},
                Fault::Capacity=>{assert_eq!(error.error,"role2 full loader capacity differs");assert_eq!((error.loads,error.binds),(1,1));},
                Fault::LateVisit=>{assert_eq!(error.error,"role2 full isolated second-U visitor");assert_eq!((error.loads,error.visits,error.binds),(4,13,1));},
                Fault::None=>unreachable!(),
            }
        }
        assert_eq!(progress.fault.get(),11);progress.mark("faults_ready");f.close().unwrap();progress.mark("complete");
        assert_eq!(progress.stage.get(),23);
    }
}

#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
pub struct Descriptor {
    pub schema:String,pub headers:usize,pub genuine:usize,pub leaves:usize,pub slots:usize,
    pub root_node_slot:usize,pub profile_node_slot:usize,pub root:[u8;32],
    pub leaf_schema:String,pub padding_schema:String,pub node_schema:String,pub profile_schema:String,
}
impl Descriptor {
    pub fn new(headers:usize,root:[u8;32])->Result<Self,String> {
        if !(3..=(1usize<<31)-1).contains(&headers) {return Err("header count outside native build envelope".into());}
        let genuine=headers-1;let leaves=genuine.next_power_of_two();let slots=headers.next_power_of_two();
        Ok(Self {schema:"work-tree-topology-b1-v1".into(),headers,genuine,leaves,slots,
            root_node_slot:leaves-2,profile_node_slot:leaves-1,root,
            leaf_schema:"L|profile32|H_BE32|height_BE32|lower28|upper28|len_BE16|raw<=514".into(),
            padding_schema:"P|profile32|H_BE32|position_BE32".into(),
            node_schema:"N|level_u8|parent_position_BE32|left32|right32".into(),
            profile_schema:"nipopow-v2/work-profile/v1\\0 (27 bytes)|genesis32".into()})
    }
    pub fn validate(&self)->Result<(),String> {
        if *self!=Self::new(self.headers,self.root)? {return Err("descriptor shape/schema/index mismatch".into());}
        Ok(())
    }
    pub fn slot_log(&self)->usize {self.slots.trailing_zeros() as usize}
    pub fn level(&self,level:usize)->Result<(usize,usize),String> {
        if level==0 || level>self.leaves.trailing_zeros() as usize {return Err("node level outside tree".into());}
        let count=self.leaves>>level;Ok((self.leaves-2*count,count))
    }
    pub fn validate_leaf_position(&self,slot:usize,position:usize)->Result<(),String> {
        if slot>=self.leaves || slot!=position {return Err("leaf/padding position mismatch".into());}Ok(())
    }
    pub fn validate_node(&self,level:usize,position:usize,slot:usize,left:usize,right:usize)->Result<(),String> {
        let (base,count)=self.level(level)?;
        let child_base=if level==1 {0}else {self.level(level-1)?.0};
        if position>=count || slot!=base+position || left!=child_base+2*position || right!=left+1 {
            return Err("node level/position/children mismatch".into());
        }Ok(())
    }
    pub fn active_native_compressions_upper(&self)->u64 {2*self.leaves as u64+4*self.genuine as u64}
}

#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
pub enum Mapping {
    Same {lo:usize,hi:usize},
    HeaderSuccessor {lo:usize,hi:usize},
    Child {level:usize,branch:usize},
    FixedRight {lo:usize,hi:usize,target:usize},
}
#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
pub struct Family {
    pub name:String,pub mapping:Mapping,pub left_wires:Vec<usize>,pub right_wires:Vec<usize>,
    /// Some means x-constant=0; None means x-y=0. Constant bits are public.
    pub constants:Option<Vec<u8>>,
}
#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct FamilyCount {
    pub name:String,pub endpoint_bits:usize,pub live_rows:u64,pub padded_rows:u64,pub terms:u64,
    pub global_input_bits:usize,pub row_log:usize,pub maximum_degree:usize,
    pub fits_sparse_dimension24:bool,pub fits_sparse_base_terms_2pow20:bool,
    pub analytic_field_multiplication_upper:u64,pub analytic_scratch_field_upper:usize,
}
#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct TopologyReport {
    pub descriptor:Descriptor,pub descriptor_blake2b256:String,pub topology_blake2b256:String,
    pub families:Vec<FamilyCount>,pub live_rows:u64,pub terms:u64,pub padded_rows_sum:u64,
    pub allocated_new_bits_beyond_endpoint_reservation:usize,pub reserved_endpoint_bits_per_slot:usize,
    pub booleanity_compiled:bool,pub complete_dummy_execution_compiled:bool,
    pub retained_family_capacity_bytes:usize,pub analytic_scratch_field_upper:usize,
    pub active_native_compressions_upper:u64,pub fixed_core_positions:u64,pub packed_global_bytes:u64,
}
#[derive(Clone)]
pub struct Topology {pub descriptor:Descriptor,pub families:Vec<Family>,frozen_manifest:String}

fn equal(name:&str,mapping:Mapping,left:Vec<usize>,right:Vec<usize>)->Family {
    Family {name:name.into(),mapping,left_wires:left,right_wires:right,constants:None}
}
fn zero(name:&str,lo:usize,hi:usize,wires:Vec<usize>)->Family {
    let n=wires.len();Family {name:name.into(),mapping:Mapping::FixedRight {lo,hi,target:0},
        left_wires:wires,right_wires:vec![0;n],constants:Some(vec![0;n])}
}
impl Topology {
    pub fn new(base:&Baseline,headers:usize,root:[u8;32])->Result<Self,String> {
        let d=Descriptor::new(headers,root)?;let e=&base.endpoints;let l=&base.compression;
        let same=|lo,hi|Mapping::Same {lo,hi};let mut families=Vec::new();
        families.push(equal("header_to_leaf_raw_length_nbits_height",Mapping::HeaderSuccessor {lo:1,hi:d.headers},
            base.header_alias_wires.clone(),e.header_aliases()));
        families.push(equal("node_profile_output_core_alias",same(0,d.leaves),e.node.clone(),
            (0..256).map(|bit|917504+l.output[bit/64][bit%64]).collect()));
        for branch in 0..2 {
            let bytes=6+32*branch;
            families.push(equal(&format!("node_message_child_{branch}"),same(0,d.leaves-1),
                if branch==0 {e.node_left.clone()}else {e.node_right.clone()},
                (0..256).map(|bit| {let byte=bytes+bit/8;917504+l.message[byte/8][(byte%8)*8+bit%8]}).collect()));
        }
        families.push(equal("profile_digest_fanout",Mapping::FixedRight {lo:0,hi:d.leaves,target:d.profile_node_slot},
            e.profile.clone(),e.node.clone()));
        for level in 1..=d.leaves.trailing_zeros() as usize {for branch in 0..2 {
            families.push(equal(&format!("level_{level}_child_{branch}"),Mapping::Child {level,branch},
                if branch==0 {e.node_left.clone()}else {e.node_right.clone()},
                if level==1 {e.leaf.clone()}else {e.node.clone()}));
        }}
        families.push(Family {name:"public_root".into(),mapping:Mapping::FixedRight {
            lo:d.root_node_slot,hi:d.root_node_slot+1,target:0},left_wires:e.node.clone(),right_wires:vec![0;256],
            constants:Some((0..256).map(|bit|(root[bit/8]>>(bit%8))&1).collect())});
        families.push(zero("inactive_tree_endpoints",d.leaves,d.slots,(ENDPOINT_BASE..ENDPOINT_BASE+ENDPOINT_WIDTH).collect()));
        families.push(zero("padding_leaf_unused_header_aliases",d.genuine,d.leaves,e.header_aliases()));
        families.push(zero("profile_slot_unused_child_endpoints",d.profile_node_slot,d.profile_node_slot+1,
            e.node_left.iter().chain(&e.node_right).copied().collect()));
        families.push(zero("endpoint_bank_padding",0,d.slots,
            (ENDPOINT_BASE+e.used..ENDPOINT_BASE+ENDPOINT_WIDTH).collect()));
        let frozen_manifest=layout::hash_bytes(&serde_json::to_vec(&(&d,&families)).map_err(|e|e.to_string())?);
        let topology=Self {descriptor:d,families,frozen_manifest};topology.validate()?;Ok(topology)
    }
    pub fn validate(&self)->Result<(),String> {
        self.descriptor.validate()?;
        // Mandatory coverage is derived independently of supplied families and their fingerprint.
        let mut roster=vec![("header_to_leaf_raw_length_nbits_height".to_string(),4186,false),
            ("node_profile_output_core_alias".into(),256,false),("node_message_child_0".into(),256,false),
            ("node_message_child_1".into(),256,false),("profile_digest_fanout".into(),256,false)];
        for level in 1..=self.descriptor.leaves.trailing_zeros() {for branch in 0..2 {
            roster.push((format!("level_{level}_child_{branch}"),256,false));
        }}
        roster.extend([("public_root".into(),256,true),("inactive_tree_endpoints".into(),ENDPOINT_WIDTH,true),
            ("padding_leaf_unused_header_aliases".into(),4186,true),("profile_slot_unused_child_endpoints".into(),512,true),
            ("endpoint_bank_padding".into(),ENDPOINT_WIDTH-layout::Endpoints::new().used,true)]);
        if self.families.len()!=roster.len() || self.families.iter().zip(roster).any(|(f,(name,width,anchor))|
            f.name!=name || f.left_wires.len()!=width || f.right_wires.len()!=width || f.constants.is_some()!=anchor) {
            return Err("mandatory topology family roster/shape coverage".into());
        }
        if self.frozen_manifest!=layout::hash_bytes(&serde_json::to_vec(&(&self.descriptor,&self.families)).map_err(|e|e.to_string())?) {
            return Err("topology descriptor/family differs from frozen constructor".into());
        }
        for f in &self.families {
            if f.left_wires.is_empty() || f.left_wires.len()!=f.right_wires.len()
                || f.left_wires.iter().chain(&f.right_wires).any(|&w|w>=WIDTH)
                || f.constants.as_ref().is_some_and(|v|v.len()!=f.left_wires.len() || v.iter().any(|b|*b>1)) {
                return Err("topology wire shape".into());
            }
            let (lo,hi)=f.range(&self.descriptor)?;
            if lo>hi || hi>self.descriptor.slots {return Err("topology range".into());}
            match f.mapping {
                Mapping::HeaderSuccessor {lo,..} if lo==0 =>return Err("successor underflow".into()),
                Mapping::FixedRight {target,..} if target>=self.descriptor.slots=>return Err("fixed slot outside domain".into()),
                Mapping::Child {branch,..} if branch>1=>return Err("child branch".into()),_=>{}
            }
        }Ok(())
    }
    pub fn report(&self)->Result<TopologyReport,String> {
        self.validate()?;let counts=self.families.iter().map(|f|f.count(&self.descriptor)).collect::<Result<Vec<_>,_>>()?;
        let topology_bytes=serde_json::to_vec(&self.families).map_err(|e|e.to_string())?;
        Ok(TopologyReport {descriptor:self.descriptor.clone(),
            descriptor_blake2b256:layout::hash_bytes(&serde_json::to_vec(&self.descriptor).map_err(|e|e.to_string())?),
            topology_blake2b256:layout::hash_bytes(&topology_bytes),live_rows:counts.iter().map(|f|f.live_rows).sum(),
            terms:counts.iter().map(|f|f.terms).sum(),padded_rows_sum:counts.iter().map(|f|f.padded_rows).sum(),
            allocated_new_bits_beyond_endpoint_reservation:0,reserved_endpoint_bits_per_slot:ENDPOINT_WIDTH,
            booleanity_compiled:false,complete_dummy_execution_compiled:false,
            retained_family_capacity_bytes:self.families.capacity()*std::mem::size_of::<Family>()
                +self.families.iter().map(|f|(f.left_wires.capacity()+f.right_wires.capacity())*std::mem::size_of::<usize>()
                    +f.constants.as_ref().map_or(0,Vec::capacity)).sum::<usize>(),
            analytic_scratch_field_upper:32+3*self.descriptor.slot_log(),families:counts,
            active_native_compressions_upper:self.descriptor.active_native_compressions_upper(),
            fixed_core_positions:11*self.descriptor.slots as u64,
            packed_global_bytes:self.descriptor.slots as u64*(WIDTH as u64/8)})
    }
}

pub fn eq_index(point:&[Fr],index:usize)->Fr {
    point.iter().enumerate().fold(Fr::one(),|a,(bit,x)|a*if (index>>bit)&1==1 {*x}else {Fr::one()-x})
}
fn triple(a:Fr,b:Fr,c:Fr)->Fr {(Fr::one()-a)*(Fr::one()-b)*(Fr::one()-c)+a*b*c}
impl Family {
    fn range(&self,d:&Descriptor)->Result<(usize,usize),String> {
        Ok(match self.mapping {
            Mapping::Same {lo,hi}|Mapping::HeaderSuccessor {lo,hi}|Mapping::FixedRight {lo,hi,..}=>(lo,hi),
            Mapping::Child {level,..}=>{let (first,n)=d.level(level)?;(first,first+n)}
        })
    }
    pub fn count(&self,d:&Descriptor)->Result<FamilyCount,String> {
        let (lo,hi)=self.range(d)?;let n=self.left_wires.len();let low=n.next_power_of_two().trailing_zeros() as usize;
        let padded=d.slots as u64*n.next_power_of_two() as u64;let live=(hi-lo) as u64*n as u64;
        let h=d.slot_log();
        Ok(FamilyCount {name:self.name.clone(),endpoint_bits:n,live_rows:live,padded_rows:padded,terms:live,
            global_input_bits:20+h,row_log:low+h,maximum_degree:1,
            fits_sparse_dimension24:20+h<=24 && low+h<=24,fits_sparse_base_terms_2pow20:live<=1<<20,
            analytic_field_multiplication_upper:n as u64*(low as u64+44)+(160*h+64) as u64,
            analytic_scratch_field_upper:32+3*h})
    }
    /// Independent of B-sized enumeration: fixed wire maps plus O(log S) row arithmetic.
    pub fn coefficients(&self,d:&Descriptor,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        let h=d.slot_log();let low=self.left_wires.len().next_power_of_two().trailing_zeros() as usize;
        if r.len()!=low+h || u.len()!=20+h || v.len()!=20+h {return Err("wiring point dimension".into());}
        let rr=&r[low..];let uu=&u[20..];let vv=&v[20..];
        let factor=match self.mapping {
            Mapping::Same {lo,hi}=>evaluate_shift(rr,uu,vv,0,lo as u64,hi as u64,0,RightIndex::SameRow)?,
            Mapping::HeaderSuccessor {lo,hi}=>evaluate_shift(rr,vv,uu,1,lo as u64,hi as u64,0,RightIndex::SameRow)?,
            Mapping::FixedRight {lo,hi,target}=>{
                let zeros=vec![Fr::zero();h];
                evaluate_shift(rr,uu,&zeros,0,lo as u64,hi as u64,0,RightIndex::GlobalZero)?*eq_index(vv,target)
            },
            Mapping::Child {level,branch}=>{
                let (parent_base,count)=d.level(level)?;let m=count.trailing_zeros() as usize;
                let child_base=if level==1 {0}else {d.level(level-1)?.0};
                let mut z=Fr::one();
                // Parent interval and child interval are dyadically aligned.
                for bit in 0..m {z*=triple(rr[bit],uu[bit],vv[bit+1]);}
                for bit in m..h {
                    let one=(parent_base>>bit)&1==1;
                    z*=if one {rr[bit]}else {Fr::one()-rr[bit]};
                    z*=if one {uu[bit]}else {Fr::one()-uu[bit]};
                }
                z*=if branch==1 {vv[0]}else {Fr::one()-vv[0]};
                for bit in m+1..h {z*=if (child_base>>bit)&1==1 {vv[bit]}else {Fr::one()-vv[bit]};}
                z
            }
        };
        let mut out=[Fr::zero();4];
        for bit in 0..self.left_wires.len() {
            let weight=eq_index(&r[..low],bit)*eq_index(&u[..20],self.left_wires[bit])
                *eq_index(&v[..20],self.right_wires[bit]);
            out[1]+=weight;
            if let Some(constants)=&self.constants {out[0]-=weight*Fr::from(constants[bit] as u64);}
            else {out[2]-=weight;}
        }
        for x in &mut out {*x*=factor;}Ok(out)
    }
    /// Regenerate a family in canonical row/bit order without retaining its terms.
    pub(crate) fn emit_terms(&self,d:&Descriptor,mut sink:impl FnMut(Term)->Result<(),String>)->Result<(),String>{
        let (lo,hi)=self.range(d)?;let stride=self.left_wires.len().next_power_of_two();
        for row_slot in lo..hi{
            let right_slot=match self.mapping{
                Mapping::Same{..}=>row_slot,Mapping::HeaderSuccessor{..}=>row_slot-1,
                Mapping::FixedRight{target,..}=>target,
                Mapping::Child{level,branch}=>{
                    let level_width=d.leaves/(1usize<<level);
                    let ordinal=row_slot-(d.leaves-2*level_width);
                    let previous=if level==1{0}else{d.leaves-4*level_width};previous+2*ordinal+branch
                }
            };
            for bit in 0..self.left_wires.len(){
                sink(Term{row:row_slot*stride+bit,gate:Gate{left:row_slot*WIDTH+self.left_wires[bit],
                    right:right_slot*WIDTH+self.right_wires[bit],
                    c0:self.constants.as_ref().map_or(Fr::zero(),|v|-Fr::from(v[bit] as u64)),
                    c1:Fr::one(),c2:if self.constants.is_some(){Fr::zero()}else{-Fr::one()},c3:Fr::zero()}})?;
            }
        }Ok(())
    }
    /// Emit only terms incident to one input slot, preserving each row's
    /// source slot separately for its GKR output selector.
    pub(crate) fn emit_endpoint_terms(
        &self,d:&Descriptor,left_endpoint:bool,endpoint_slot:usize,
        mut sink:impl FnMut(usize,usize,Term)->Result<(),String>,
    )->Result<(),String>{
        let (lo,hi)=self.range(d)?;let stride=self.left_wires.len().next_power_of_two();
        if endpoint_slot>=d.slots{return Err("endpoint slot outside descriptor".into());}
        let mut emit_row=|row_slot:usize|->Result<(),String>{
            if row_slot<lo||row_slot>=hi{return Ok(());}
            let right_slot=match self.mapping{
                Mapping::Same{..}=>row_slot,
                Mapping::HeaderSuccessor{..}=>row_slot.checked_sub(1).ok_or("successor underflow")?,
                Mapping::FixedRight{target,..}=>target,
                Mapping::Child{level,branch}=>{
                    let level_width=d.leaves/(1usize<<level);let ordinal=row_slot-(d.leaves-2*level_width);
                    let previous=if level==1{0}else{d.leaves-4*level_width};previous+2*ordinal+branch
                }
            };
            for bit in 0..self.left_wires.len(){
                let row=row_slot.checked_mul(stride).and_then(|x|x.checked_add(bit)).ok_or("endpoint row overflow")?;
                let term=Term{row,gate:Gate{left:row_slot.checked_mul(WIDTH).and_then(|x|x.checked_add(self.left_wires[bit])).ok_or("endpoint left wire overflow")?,
                    right:right_slot.checked_mul(WIDTH).and_then(|x|x.checked_add(self.right_wires[bit])).ok_or("endpoint right wire overflow")?,
                    c0:self.constants.as_ref().map_or(Fr::zero(),|v|-Fr::from(v[bit] as u64)),
                    c1:Fr::one(),c2:if self.constants.is_some(){Fr::zero()}else{-Fr::one()},c3:Fr::zero()}};
                sink(row_slot,bit,term)?;
            }
            Ok(())
        };
        if left_endpoint{emit_row(endpoint_slot)?;}else{match self.mapping{
            Mapping::Same{..}=>emit_row(endpoint_slot)?,
            Mapping::HeaderSuccessor{..}=>if let Some(row_slot)=endpoint_slot.checked_add(1){emit_row(row_slot)?;},
            Mapping::FixedRight{target,..}=>if endpoint_slot==target{for row_slot in lo..hi{emit_row(row_slot)?;}},
            Mapping::Child{level,branch}=>{
                let level_width=d.leaves/(1usize<<level);let parent_base=d.leaves-2*level_width;
                let child_base=if level==1{0}else{d.level(level-1)?.0};
                if endpoint_slot>=child_base{let delta=endpoint_slot-child_base;
                    if delta<2*level_width&&delta%2==branch{emit_row(parent_base+delta/2)?;}}
            }
        }}
        Ok(())
    }
    #[cfg(test)]
    fn emit_same_slot_terms(&self,slot:usize,mut sink:impl FnMut(Term)->Result<(),String>)->Result<(),String>{
        let Mapping::Same{lo,hi}=self.mapping else{return Err("local slot emitter requires Same mapping".into());};
        if slot<lo||slot>=hi{return Ok(());}
        let stride=self.left_wires.len().next_power_of_two();
        let row_base=slot.checked_mul(stride).ok_or("local B1 slot row overflow")?;
        let wire_base=slot.checked_mul(WIDTH).ok_or("local B1 slot wire overflow")?;
        for bit in 0..self.left_wires.len(){
            sink(Term{row:row_base.checked_add(bit).ok_or("local B1 row overflow")?,gate:Gate{
                left:wire_base.checked_add(self.left_wires[bit]).ok_or("local B1 left wire overflow")?,
                right:wire_base.checked_add(self.right_wires[bit]).ok_or("local B1 right wire overflow")?,
                c0:self.constants.as_ref().map_or(Fr::zero(),|v|-Fr::from(v[bit] as u64)),
                c1:Fr::one(),c2:if self.constants.is_some(){Fr::zero()}else{-Fr::one()},c3:Fr::zero()}})?;
        }
        Ok(())
    }
    /// Bounded producer/oracle only; this is never called by coefficients().
    pub fn enumerate(&self,d:&Descriptor,cap:usize)->Result<Circuit,String> {
        let counts=self.count(d)?;
        if d.slots>16 || counts.terms>cap as u64 {return Err("tiny topology materialization cap".into());}
        let mut terms=Vec::with_capacity(counts.terms as usize);
        self.emit_terms(d,|term|{terms.push(term);Ok(())})?;
        Ok(Circuit {input_len:d.slots*WIDTH,row_count:counts.padded_rows as usize,terms})
    }
}

#[derive(Clone,Copy)]
#[cfg(test)]
struct TaggedRosterShape {local_row_bits:usize,family_bits:usize,row_bits:usize,input_bits:usize,input_len:usize}

#[cfg(test)]
fn tagged_roster_shape(topology:&Topology)->Result<TaggedRosterShape,String> {
    topology.validate()?;
    if topology.families.is_empty() {return Err("empty topology roster".into());}
    let local_row_bits=topology.families.iter().map(|family|family.count(&topology.descriptor).map(|c|c.row_log))
        .collect::<Result<Vec<_>,_>>()?.into_iter().max().unwrap();
    let family_bits=topology.families.len().next_power_of_two().trailing_zeros() as usize;
    let row_bits=local_row_bits.checked_add(family_bits).ok_or("tagged roster row dimension overflow")?;
    let input_bits=20usize.checked_add(topology.descriptor.slot_log()).ok_or("tagged roster input dimension overflow")?;
    let input_len=1usize.checked_shl(input_bits as u32).ok_or("tagged roster input width overflow")?;
    if row_bits>usize::BITS as usize-1 {return Err("tagged roster row width overflow".into());}
    Ok(TaggedRosterShape {local_row_bits,family_bits,row_bits,input_bits,input_len})
}

#[cfg(test)]
fn tagged_roster_circuit(topology:&Topology)->Result<Circuit,String> {
    topology.validate()?;let shape=tagged_roster_shape(topology)?;
    let row_count=1usize.checked_shl(shape.row_bits as u32).ok_or("tagged roster row count overflow")?;
    let mut terms=Vec::new();
    for (index,family) in topology.families.iter().enumerate() {
        let row_base=index.checked_shl(shape.local_row_bits as u32).ok_or("tagged family row base overflow")?;
        let local=family.enumerate(&topology.descriptor,1<<20)?;
        for mut term in local.terms {
            term.row=term.row.checked_add(row_base).ok_or("tagged family row overflow")?;
            terms.push(term);
        }
    }
    if terms.len()>1<<20 {return Err("tagged roster producer term cap".into());}
    Ok(Circuit {input_len:shape.input_len,row_count,terms})
}

#[cfg(test)]
fn tagged_roster_coefficients(topology:&Topology,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
    tagged_roster_coefficients_with_tag(topology,r,u,v,|index|index)
}

#[cfg(test)]
fn tagged_roster_coefficients_with_tag(
    topology:&Topology,r:&[Fr],u:&[Fr],v:&[Fr],tag_for_family:impl Fn(usize)->usize,
)->Result<[Fr;4],String> {
    let shape=tagged_roster_shape(topology)?;
    if r.len()!=shape.row_bits || u.len()!=shape.input_bits || v.len()!=shape.input_bits {
        return Err("tagged roster point dimension".into());
    }
    let mut out=[Fr::zero();4];let tag_point=&r[shape.local_row_bits..];
    for (index,family) in topology.families.iter().enumerate() {
        let count=family.count(&topology.descriptor)?;
        let coefficients=family.coefficients(&topology.descriptor,&r[..count.row_log],u,v)?;
        let tag=tag_for_family(index);
        if tag>=1usize<<shape.family_bits {return Err("family tag outside roster domain".into());}
        let mut weight=eq_index(tag_point,tag);
        for coordinate in &r[count.row_log..shape.local_row_bits] {weight*=Fr::one()-coordinate;}
        for (sum,coefficient) in out.iter_mut().zip(coefficients) {*sum+=weight*coefficient;}
    }
    Ok(out)
}

#[cfg(test)]
fn bind_tagged_roster(topology:&Topology,transcript:&mut crate::transcript::Transcript) {
    let shape=tagged_roster_shape(topology).expect("validated tagged roster");
    transcript.append_bytes(b"sparse-profile",b"work-tree-tagged-family-roster-v1");
    crate::gkr::append_usize(transcript,b"sparse-input-width",shape.input_len);
    crate::gkr::append_usize(transcript,b"sparse-row-count",1usize<<shape.row_bits);
    crate::gkr::append_usize(transcript,b"roster-family-count",topology.families.len());
    crate::gkr::append_usize(transcript,b"roster-local-row-bits",shape.local_row_bits);
    crate::gkr::append_usize(transcript,b"roster-family-bits",shape.family_bits);
    transcript.append_bytes(b"roster-descriptor",&serde_json::to_vec(&topology.descriptor).unwrap());
    transcript.append_bytes(b"roster-manifest",topology.frozen_manifest.as_bytes());
}

pub(crate) fn full_roster_shape(topology:&Topology)->Result<(usize,usize,usize,usize),String> {
    topology.validate()?;
    let h=topology.descriptor.slot_log();
    let families=topology.families.len()+1+1+1+3;
    let family_bits=families.next_power_of_two().trailing_zeros() as usize;
    let local_row_bits=14usize.checked_add(h).ok_or("full roster local row overflow")?;
    let input_bits=20usize.checked_add(h).ok_or("full roster input overflow")?;
    let row_bits=local_row_bits.checked_add(family_bits).ok_or("full roster row overflow")?;
    if row_bits>usize::BITS as usize-1 {return Err("full roster row width overflow".into());}
    Ok((local_row_bits,family_bits,row_bits,input_bits))
}

pub(crate) fn full_roster_coefficients(
    topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,
    leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work_boundary:&crate::work_tree_work::Boundary,r:&[Fr],u:&[Fr],v:&[Fr],
)->Result<[Fr;4],String> {
    full_roster_coefficients_with_tag(topology,engine,fixed_profile,leaf_boundary,work_boundary,r,u,v,|index|index)
}

pub(crate) fn full_roster_coefficients_with_tag(
    topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,
    leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work_boundary:&crate::work_tree_work::Boundary,r:&[Fr],u:&[Fr],v:&[Fr],
    tag_for_member:impl Fn(usize)->usize,
)->Result<[Fr;4],String> {
    let (local_row_bits,family_bits,row_bits,input_bits)=full_roster_shape(topology)?;
    if r.len()!=row_bits||u.len()!=input_bits||v.len()!=input_bits{return Err("full roster point dimension".into());}
    if fixed_profile.tree!=topology.descriptor||leaf_boundary.profile.tree!=topology.descriptor
        ||work_boundary.profile().tree!=topology.descriptor{return Err("full roster descriptor mismatch".into());}
    let mut out=[Fr::zero();4];let tag_point=&r[local_row_bits..];let mut index=0usize;
    let mut add=|row_log:usize,coefficients:[Fr;4]|->Result<(),String>{
        if row_log>local_row_bits{return Err("full roster member row exceeds reserved local width".into());}
        let tag=tag_for_member(index);if tag>=1usize<<family_bits{return Err("full roster member tag outside domain".into());}
        let tag_weight=eq_index(tag_point,tag);
        let padding_weight=r[row_log..local_row_bits].iter().fold(Fr::one(),|weight,x|weight*(Fr::one()-x));
        for (sum,coefficient) in out.iter_mut().zip(coefficients){*sum+=tag_weight*padding_weight*coefficient;}
        index+=1;Ok(())
    };
    for family in &topology.families {
        let count=family.count(&topology.descriptor)?;
        add(count.row_log,family.coefficients(&topology.descriptor,&r[..count.row_log],u,v)?)?;
    }
    let h=topology.descriptor.slot_log();
    add(11+h,crate::work_tree_fixed_hash::coefficients(engine,fixed_profile,&r[..11+h],u,v)?)?;
    add(14+h,crate::work_tree_leaf_hash::coefficients(leaf_boundary,&r[..14+h],u,v)?)?;
    add(11+h,crate::work_tree_work::local_coefficients(work_boundary,&r[..11+h],u,v)?)?;
    for family in work_boundary.links() {
        let count=family.count(&topology.descriptor)?;
        add(count.row_log,family.coefficients(&topology.descriptor,&r[..count.row_log],u,v)?)?;
    }
    if index!=topology.families.len()+6||index>1usize<<family_bits{return Err("full roster tag capacity/coverage".into());}
    Ok(out)
}

pub(crate) fn full_roster_circuit(
    topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,
    leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work_boundary:&crate::work_tree_work::Boundary,
)->Result<Circuit,String> {
    let (local_row_bits,_,row_bits,input_bits)=full_roster_shape(topology)?;
    let mut circuit=Circuit {input_len:1usize<<input_bits,row_count:1usize<<row_bits,terms:Vec::new()};
    let mut family_index=0usize;
    let mut append=|terms:Vec<Term>|->Result<(),String>{
        let row_base=family_index.checked_shl(local_row_bits as u32).ok_or("full roster row base overflow")?;
        for mut term in terms {term.row=term.row.checked_add(row_base).ok_or("full roster term row overflow")?;circuit.terms.push(term);}
        family_index+=1;Ok(())
    };
    for family in &topology.families {append(family.enumerate(&topology.descriptor,1<<20)?.terms)?;}
    let mut b2=Vec::new();for slot in 0..topology.descriptor.slots {
        crate::work_tree_fixed_hash::emit_slot(engine,fixed_profile,slot,|term|b2.push(term))?;
    }append(b2)?;
    let mut b3=Vec::new();for slot in 0..topology.descriptor.slots {
        leaf_boundary.emit_slot(slot,|term|b3.push(term))?;
    }append(b3)?;
    let mut b4_local=Vec::new();for slot in 0..topology.descriptor.slots {
        work_boundary.emit_slot(slot,|term|b4_local.push(term))?;
    }append(b4_local)?;
    for family in work_boundary.links(){append(family.enumerate(&topology.descriptor,1<<20)?.terms)?;}
    if family_index!=topology.families.len()+6{return Err("full roster circuit member count".into());}
    if circuit.terms.len()>=1<<20{return Err("full roster circuit term cap".into());}
    if circuit.terms.iter().any(|term|term.row>=circuit.row_count||term.gate.left>=circuit.input_len||term.gate.right>=circuit.input_len) {
        return Err("full roster circuit index outside domain".into());
    }
    Ok(circuit)
}

#[cfg(test)]
#[derive(Clone,Copy)]
struct FullSplitShape {local_row_bits:usize,family_bits:usize,row_bits:usize,input_bits:usize,family_count:usize}

#[cfg(test)]
fn validate_full_split_inputs(topology:&Topology,fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,
    leaf_boundary:&crate::work_tree_leaf_hash::Boundary,work:&crate::work_tree_work::Boundary)->Result<(),String>{
    topology.validate()?;fixed_profile.validate()?;leaf_boundary.profile.validate()?;work.profile().validate()?;
    if fixed_profile.tree!=topology.descriptor||leaf_boundary.profile.tree!=topology.descriptor
        ||work.profile().tree!=topology.descriptor{return Err("full split descriptor/profile mismatch".into());}
    Ok(())
}

#[cfg(test)]
fn full_split_shape(topology:&Topology,work:&crate::work_tree_work::Boundary,local:bool)->Result<FullSplitShape,String>{
    topology.validate()?;let d=&topology.descriptor;let mut row_logs=Vec::new();
    for family in &topology.families{if matches!(family.mapping,Mapping::Same{..})==local{
        row_logs.push(family.count(d)?.row_log);
    }}
    let h=d.slot_log();let extras=if local{row_logs.extend([11+h,14+h,11+h]);3}else{
        row_logs.extend(work.links().iter().map(|family|family.count(d).map(|count|count.row_log)).collect::<Result<Vec<_>,_>>()?);
        work.links().len()
    };
    if row_logs.is_empty(){return Err("empty full-roster split".into());}
    let local_row_bits=*row_logs.iter().max().unwrap();
    let family_count=row_logs.len();let family_bits=family_count.next_power_of_two().trailing_zeros() as usize;
    let row_bits=local_row_bits.checked_add(family_bits).ok_or("full split row dimension overflow")?;
    let input_bits=20usize.checked_add(h).ok_or("full split input dimension overflow")?;
    if family_count<extras{return Err("full split member accounting".into());}
    Ok(FullSplitShape{local_row_bits,family_bits,row_bits,input_bits,family_count})
}

#[cfg(test)]
pub(crate) fn full_split_local_tensor_dimensions(topology:&Topology,work:&crate::work_tree_work::Boundary)
    ->Result<(usize,usize,usize,usize),String>{
    let shape=full_split_shape(topology,work,true)?;let slot_bits=topology.descriptor.slot_log();
    Ok((shape.input_bits-slot_bits,slot_bits,shape.local_row_bits-slot_bits,shape.family_bits))
}

#[cfg(test)]
pub(crate) fn full_split_local_tensor_member_row_bits(topology:&Topology,work:&crate::work_tree_work::Boundary)
    ->Result<Vec<usize>,String>{
    let d=&topology.descriptor;let h=d.slot_log();let mut bits=Vec::new();
    for family in &topology.families{if matches!(family.mapping,Mapping::Same{..}){
        bits.push(family.count(d)?.row_log.checked_sub(h).ok_or("B1 local row width underflow")?);
    }}
    bits.extend([11usize,14usize,11usize]);
    let shape=full_split_shape(topology,work,true)?;
    if bits.len()!=shape.family_count||bits.iter().any(|value|*value>shape.local_row_bits-h){
        return Err("local tensor family row shapes mismatch".into());
    }Ok(bits)
}

#[cfg(test)]
pub(crate) fn full_split_cross_tensor_dimensions(topology:&Topology,work:&crate::work_tree_work::Boundary)
    ->Result<(usize,usize,usize,usize),String>{
    let shape=full_split_shape(topology,work,false)?;let slot_bits=topology.descriptor.slot_log();
    Ok((shape.input_bits-slot_bits,slot_bits,shape.local_row_bits-slot_bits,shape.family_bits))
}

#[cfg(test)]
pub(crate) fn full_split_cross_tensor_member_row_bits(topology:&Topology,work:&crate::work_tree_work::Boundary)
    ->Result<Vec<usize>,String>{
    let d=&topology.descriptor;let h=d.slot_log();let mut bits=Vec::new();
    for family in &topology.families{if !matches!(family.mapping,Mapping::Same{..}){
        bits.push(family.count(d)?.row_log.checked_sub(h).ok_or("B1 cross row width underflow")?);
    }}
    for family in work.links(){bits.push(family.count(d)?.row_log.checked_sub(h).ok_or("B4 link row width underflow")?);}
    let shape=full_split_shape(topology,work,false);
    let shape=shape?;let base=shape.local_row_bits-h;
    if bits.len()!=shape.family_count||bits.iter().any(|value|*value>base){return Err("cross tensor family row shapes mismatch".into());}
    Ok(bits)
}

#[cfg(test)]
pub(crate) fn full_split_visit_cross_endpoint_terms(
    topology:&Topology,work:&crate::work_tree_work::Boundary,left_endpoint:bool,endpoint_slot:usize,
    visitor:&mut dyn FnMut(usize,usize,Term)->Result<(),String>,
)->Result<(),String>{
    topology.validate()?;work.profile().validate()?;
    if work.profile().tree!=topology.descriptor{return Err("cross endpoint descriptor mismatch".into());}
    let d=&topology.descriptor;let h=d.slot_log();let shape=full_split_shape(topology,work,false)?;
    let base=shape.local_row_bits.checked_sub(h).ok_or("cross endpoint row width underflow")?;
    if endpoint_slot>=d.slots{return Err("cross endpoint slot outside descriptor".into());}
    let mut member=0usize;
    for family in &topology.families{if !matches!(family.mapping,Mapping::Same{..}){
        let offset=member.checked_shl(base as u32).ok_or("cross family row offset overflow")?;member+=1;
        family.emit_endpoint_terms(d,left_endpoint,endpoint_slot,|source_slot,local_row,mut term|{
            term.row=offset.checked_add(local_row).ok_or("cross family local row overflow")?;
            visitor(source_slot,term.row,term)
        })?;
    }}
    for family in work.links(){
        let offset=member.checked_shl(base as u32).ok_or("cross work-link row offset overflow")?;member+=1;
        family.emit_endpoint_terms(d,left_endpoint,endpoint_slot,|source_slot,local_row,mut term|{
            term.row=offset.checked_add(local_row).ok_or("cross work-link local row overflow")?;
            visitor(source_slot,term.row,term)
        })?;
    }
    if member!=shape.family_count{return Err("cross endpoint member count mismatch".into());}
    Ok(())
}

#[cfg(test)]
pub(crate) fn full_split_circuit(topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,local:bool)->Result<Circuit,String>{
    validate_full_split_inputs(topology,fixed_profile,leaf_boundary,work)?;
    let shape=full_split_shape(topology,work,local)?;let d=&topology.descriptor;let h=d.slot_log();let mut terms=Vec::new();let mut member_index=0usize;
    let mut append=|mut member:Vec<Term>,row_log:usize|->Result<(),String>{
        if row_log>shape.local_row_bits{return Err("full split member exceeds row allocation".into());}
        // Member ordinal is advanced independently of term count, including empty families.
        let offset=member_index.checked_shl(shape.local_row_bits as u32).ok_or("full split row base overflow")?;
        member_index=member_index.checked_add(1).ok_or("full split index overflow")?;
        for term in &mut member{term.row=term.row.checked_add(offset).ok_or("full split row overflow")?;}
        terms.extend(member);Ok(())
    };
    for family in &topology.families{if matches!(family.mapping,Mapping::Same{..})==local{
        let count=family.count(d)?;append(family.enumerate(d,1<<20)?.terms,count.row_log)?;
    }}
    if local{
        let mut b2=Vec::new();for slot in 0..d.slots{crate::work_tree_fixed_hash::emit_slot(engine,fixed_profile,slot,|term|b2.push(term))?;}
        append(b2,11+h)?;
        let mut b3=Vec::new();for slot in 0..d.slots{leaf_boundary.emit_slot(slot,|term|b3.push(term))?;}
        append(b3,14+h)?;
        let mut b4=Vec::new();for slot in 0..d.slots{work.emit_slot(slot,|term|b4.push(term))?;}
        append(b4,11+h)?;
    }else{for family in work.links(){let count=family.count(d)?;append(family.enumerate(d,1<<20)?.terms,count.row_log)?;}}
    if member_index!=shape.family_count{return Err("full split member count mismatch".into());}
    if terms.len()>1<<20{return Err("full split producer term cap".into());}
    Ok(Circuit{input_len:1usize<<shape.input_bits,row_count:1usize<<shape.row_bits,terms})
}

#[cfg(test)]
pub(crate) fn full_split_visit_terms(topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,local:bool,
    visitor:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
    validate_full_split_inputs(topology,fixed_profile,leaf_boundary,work)?;
    let shape=full_split_shape(topology,work,local)?;let d=&topology.descriptor;let h=d.slot_log();let mut index=0usize;
    let mut begin_member=|row_log:usize|->Result<usize,String>{
        if row_log>shape.local_row_bits{return Err("full split member exceeds row allocation".into());}
        let offset=index.checked_shl(shape.local_row_bits as u32).ok_or("full split row base overflow")?;
        index=index.checked_add(1).ok_or("full split member index overflow")?;Ok(offset)
    };
    for family in &topology.families{if matches!(family.mapping,Mapping::Same{..})==local{
        let count=family.count(d)?;let offset=begin_member(count.row_log)?;
        family.emit_terms(d,|mut term|{term.row=term.row.checked_add(offset).ok_or("full split row overflow")?;visitor(term)})?;
    }}
    let mut emit_slots=|emit:&mut dyn FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,row_log:usize|->Result<(),String>{
        let offset=begin_member(row_log)?;let mut failure=None;
        for slot in 0..d.slots{emit(slot,&mut |mut term|{
            term.row=term.row.checked_add(offset).ok_or("full split row overflow")?;
            if failure.is_some(){return Ok(());}
            if let Err(error)=visitor(term){failure=Some(error);}Ok(())
        })?;if let Some(error)=failure{return Err(error);}}
        Ok(())
    };
    if local{
        // These slot emitters have non-fallible sinks; capture and return the
        // first visitor error after the current slot, without scanning later slots.
        emit_slots(&mut |slot,sink|{
            let mut failure=None;crate::work_tree_fixed_hash::emit_slot(engine,fixed_profile,slot,|term|{
                if failure.is_none(){if let Err(error)=sink(term){failure=Some(error);}}
            })?;if let Some(error)=failure{return Err(error);}Ok(())
        },11+h)?;
        emit_slots(&mut |slot,sink|{
            let mut failure=None;leaf_boundary.emit_slot(slot,|term|{if failure.is_none(){if let Err(error)=sink(term){failure=Some(error);}}})?;
            if let Some(error)=failure{return Err(error);}Ok(())
        },14+h)?;
        emit_slots(&mut |slot,sink|{
            let mut failure=None;work.emit_slot(slot,|term|{if failure.is_none(){if let Err(error)=sink(term){failure=Some(error);}}})?;
            if let Some(error)=failure{return Err(error);}Ok(())
        },11+h)?;
    }else{for family in work.links(){let count=family.count(d)?;let offset=begin_member(count.row_log)?;
        family.emit_terms(d,|mut term|{term.row=term.row.checked_add(offset).ok_or("full split row overflow")?;visitor(term)})?;
    }}
    if index!=shape.family_count{return Err("full split member count mismatch".into());}Ok(())
}

#[cfg(test)]
pub(crate) fn full_split_visit_local_slot_terms(topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,slot:usize,
    visitor:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
    validate_full_split_inputs(topology,fixed_profile,leaf_boundary,work)?;
    let shape=full_split_shape(topology,work,true)?;let d=&topology.descriptor;let h=d.slot_log();
    if slot>=d.slots{return Err("local slot outside descriptor".into());}
    let base_row_bits=shape.local_row_bits.checked_sub(h).ok_or("local row width underflow")?;
    let mut member=0usize;
    let mut append=|row_log:usize,emit:&mut dyn FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>|->Result<(),String>{
        if row_log<h||row_log-h>base_row_bits{return Err("local slot family exceeds row allocation".into());}
        let offset=member.checked_shl(base_row_bits as u32).ok_or("local family row base overflow")?;
        member=member.checked_add(1).ok_or("local family index overflow")?;
        let member_stride=1usize.checked_shl((row_log-h) as u32).ok_or("local member stride overflow")?;
        let slot_row_base=slot.checked_mul(member_stride).ok_or("local member slot row overflow")?;
        let mut failure=None;
        emit(&mut |mut term|{
            let local_row=term.row.checked_sub(slot_row_base).ok_or("local member row outside slot")?;
            if local_row>=member_stride{return Err("local member row exceeds local stride".into());}
            let slot_wire=slot.checked_mul(WIDTH).ok_or("local slot wire base overflow")?;
            term.gate.left=if term.gate.c1.is_zero()&&term.gate.c3.is_zero(){0}
                else{term.gate.left.checked_sub(slot_wire).ok_or("local term left wire is outside slot")?};
            term.gate.right=if term.gate.c2.is_zero()&&term.gate.c3.is_zero(){0}
                else{term.gate.right.checked_sub(slot_wire).ok_or("local term right wire is outside slot")?};
            term.row=offset.checked_add(local_row).ok_or("local tagged row overflow")?;
            if let Err(error)=visitor(term){failure=Some(error);}Ok(())
        })?;
        if let Some(error)=failure{return Err(error);}Ok(())
    };
    for family in &topology.families{if matches!(family.mapping,Mapping::Same{..}){
        let row_log=family.count(d)?.row_log;
        append(row_log,&mut |sink|family.emit_same_slot_terms(slot,sink))?;
    }}
    append(11+h,&mut |sink|{
        let mut failure=None;crate::work_tree_fixed_hash::emit_slot(engine,fixed_profile,slot,|term|{
            if failure.is_none(){if let Err(error)=sink(term){failure=Some(error);}}
        })?;if let Some(error)=failure{return Err(error);}Ok(())
    })?;
    append(14+h,&mut |sink|{
        let mut failure=None;leaf_boundary.emit_slot(slot,|term|{if failure.is_none(){if let Err(error)=sink(term){failure=Some(error);}}})?;
        if let Some(error)=failure{return Err(error);}Ok(())
    })?;
    append(11+h,&mut |sink|{
        let mut failure=None;work.emit_slot(slot,|term|{if failure.is_none(){if let Err(error)=sink(term){failure=Some(error);}}})?;
        if let Some(error)=failure{return Err(error);}Ok(())
    })?;
    if member!=shape.family_count{return Err("local slot member count mismatch".into());}Ok(())
}

pub(crate) fn bind_full_roster(
    topology:&Topology,fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,
    leaf_profile:&crate::work_tree_leaf_hash::LeafProfile,work_profile:&crate::work_tree_work::WorkProfile,
    transcript:&mut crate::transcript::Transcript,
) {
    let (local_row_bits,family_bits,row_bits,input_bits)=full_roster_shape(topology).expect("validated full roster");
    let family_count=topology.families.len()+6;
    transcript.append_bytes(b"sparse-profile",b"nipopow-v2-tagged-b1-b2-b3-b4-roster-test-v1");
    crate::gkr::append_usize(transcript,b"roster-input-width",1usize<<input_bits);
    crate::gkr::append_usize(transcript,b"roster-row-count",1usize<<row_bits);
    crate::gkr::append_usize(transcript,b"roster-family-count",family_count);
    crate::gkr::append_usize(transcript,b"roster-local-row-bits",local_row_bits);
    crate::gkr::append_usize(transcript,b"roster-family-bits",family_bits);
    transcript.append_bytes(b"roster-order",b"ordered B1 families; B2 fixed-hash; B3 leaf-hash; B4 local; B4 links[0..3]");
    transcript.append_bytes(b"roster-descriptor",&serde_json::to_vec(&topology.descriptor).expect("descriptor JSON"));
    transcript.append_bytes(b"roster-b1-manifest",topology.frozen_manifest.as_bytes());
    transcript.append_bytes(b"roster-b2-profile",&serde_json::to_vec(fixed_profile).expect("B2 profile JSON"));
    transcript.append_bytes(b"roster-b3-profile",&serde_json::to_vec(leaf_profile).expect("B3 profile JSON"));
    transcript.append_bytes(b"roster-b4-profile",&serde_json::to_vec(work_profile).expect("B4 profile JSON"));
}

#[cfg(test)]
pub(crate) fn full_split_coefficients(topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,local:bool,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
    full_split_coefficients_omitting(topology,engine,fixed_profile,leaf_boundary,work,local,r,u,v,None)
}

#[cfg(test)]
pub(crate) fn full_split_coefficients_omitting(topology:&Topology,engine:&crate::work_tree_fixed_hash::Engine,
    fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,leaf_boundary:&crate::work_tree_leaf_hash::Boundary,
    work:&crate::work_tree_work::Boundary,local:bool,r:&[Fr],u:&[Fr],v:&[Fr],omit:Option<&str>)->Result<[Fr;4],String>{
    validate_full_split_inputs(topology,fixed_profile,leaf_boundary,work)?;
    let shape=full_split_shape(topology,work,local)?;
    if r.len()!=shape.row_bits||u.len()!=shape.input_bits||v.len()!=shape.input_bits{return Err("full split point dimension".into());}
    let mut out=[Fr::zero();4];let mut member=0usize;
    let mut add=|name:&str,row_log:usize,coefficients:[Fr;4]|{
        let tag_weight=eq_index(&r[shape.local_row_bits..],member);
        let padding_weight=r[row_log..shape.local_row_bits].iter().fold(Fr::one(),|w,x|w*(Fr::one()-x));
        if omit!=Some(name){for (sum,coefficient) in out.iter_mut().zip(coefficients){*sum+=tag_weight*padding_weight*coefficient;}}
        member+=1;
    };
    let d=&topology.descriptor;let h=d.slot_log();
    for family in &topology.families{if matches!(family.mapping,Mapping::Same{..})==local{
        let count=family.count(d)?;
        add(&family.name,count.row_log,family.coefficients(d,&r[..count.row_log],u,v)?);
    }}
    if local{
        add("B2_fixed_hash",11+h,crate::work_tree_fixed_hash::coefficients(engine,fixed_profile,&r[..11+h],u,v)?);
        add("B3_leaf_hash",14+h,crate::work_tree_leaf_hash::coefficients(leaf_boundary,&r[..14+h],u,v)?);
        add("B4_local_work",11+h,crate::work_tree_work::local_coefficients(work,&r[..11+h],u,v)?);
    }else{for family in work.links(){let count=family.count(d)?;
        add(&family.name,count.row_log,family.coefficients(d,&r[..count.row_log],u,v)?);
    }}
    if member!=shape.family_count{return Err("full split coefficient member mismatch".into());}
    Ok(out)
}

#[cfg(test)]
pub(crate) fn bind_full_split(topology:&Topology,fixed_profile:&crate::work_tree_fixed_hash::FixedProfile,
    leaf_profile:&crate::work_tree_leaf_hash::LeafProfile,
    work_profile:&crate::work_tree_work::WorkProfile,work:&crate::work_tree_work::Boundary,local:bool,
    transcript:&mut crate::transcript::Transcript){
    assert_eq!(fixed_profile.tree,topology.descriptor,"B2 split profile descriptor");
    assert_eq!(leaf_profile.tree,topology.descriptor,"B3 split profile descriptor");
    assert_eq!(work_profile.tree,topology.descriptor,"B4 split profile descriptor");
    assert_eq!(work_profile,work.profile(),"B4 split profile/boundary mismatch");
    bind_full_roster(topology,fixed_profile,leaf_profile,work_profile,transcript);
    let shape=full_split_shape(topology,work,local).expect("validated full split");
    transcript.append_bytes(b"roster-split-claim",if local{b"local-B1-Same-B2-B3-B4"}else{b"cross-B1-links-B4-continuity"});
    crate::gkr::append_usize(transcript,b"roster-split-family-count",shape.family_count);
    crate::gkr::append_usize(transcript,b"roster-split-local-row-bits",shape.local_row_bits);
    crate::gkr::append_usize(transcript,b"roster-split-family-bits",shape.family_bits);
}

#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct TinyEvidence {
    pub headers:usize,pub families:usize,pub compared_terms:usize,pub compared_residual_rows:usize,
    pub non_boolean_challenge_sets:usize,pub endpoint_mutants_rejected:usize,
    pub max_materialized_terms:usize,pub max_materialized_capacity_bytes:usize,
    pub assignment_coordinates:usize,pub assignment_is_topology_only:bool,
}

fn direct_coefficients(c:&Circuit,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    let mut out=[Fr::zero();4];
    for t in &c.terms {
        let w=eq_index(r,t.row)*eq_index(u,t.gate.left)*eq_index(v,t.gate.right);
        for (slot,c) in out.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*slot+=w*c;}
    }out
}

/// Independent bottom-up level vectors and ordinal iteration. No Family or emitted gate is read.
/// Endpoints have distinct field tags, not valid header/hash bits: only linear topology is tested.
fn native_endpoint_assignment(base:&Baseline,d:&Descriptor)->Result<BTreeMap<usize,Fr>,String> {
    if d.slots>16 {return Err("native tiny assignment cap".into());}
    let e=&base.endpoints;let l=&base.compression;let mut values=BTreeMap::new();
    for slot in 0..d.slots {for wire in ENDPOINT_BASE..ENDPOINT_BASE+ENDPOINT_WIDTH {
        values.insert(slot*WIDTH+wire,Fr::zero());
    }}
    for header in 0..d.headers {for &wire in &base.header_alias_wires {
        values.insert(header*WIDTH+wire,Fr::from((header*WIDTH+wire+1) as u64));
    }}
    let aliases=e.header_aliases();
    for ordinal in 1..d.headers {
        for (&source,&destination) in base.header_alias_wires.iter().zip(&aliases) {
            let value=values[&(ordinal*WIDTH+source)];
            values.insert((ordinal-1)*WIDTH+destination,value);
        }
    }
    let tag=|id:usize|->Vec<Fr>{(0..256).map(|bit|Fr::from((id*1024+bit+1) as u64)).collect()};
    let profile=tag(43);let mut layer=Vec::new();
    for position in 0..d.leaves {
        let digest=tag(position+1);
        for bit in 0..256 {
            values.insert(position*WIDTH+e.leaf[bit],digest[bit]);
            values.insert(position*WIDTH+e.profile[bit],profile[bit]);
        }
        layer.push(digest);
    }
    let mut records=Vec::new();let mut level=1;
    while layer.len()>1 {
        let mut upper=Vec::new();
        for (position,pair) in layer.chunks_exact(2).enumerate() {
            let output=if layer.len()==2 {(0..256).map(|bit|Fr::from(((d.root[bit/8]>>(bit%8))&1) as u64)).collect()}
                else {tag(16+level*7+position)};
            records.push((pair[0].clone(),pair[1].clone(),output.clone()));upper.push(output);
        }
        layer=upper;level+=1;
    }
    if records.len()!=d.leaves-1 {return Err("native node cardinality".into());}
    for (slot,(left,right,output)) in records.iter().enumerate() {
        for bit in 0..256 {
            values.insert(slot*WIDTH+e.node_left[bit],left[bit]);
            values.insert(slot*WIDTH+e.node_right[bit],right[bit]);
            values.insert(slot*WIDTH+e.node[bit],output[bit]);
            values.insert(slot*WIDTH+917504+l.output[bit/64][bit%64],output[bit]);
            for (byte,value) in [(6+bit/8,left[bit]),(38+bit/8,right[bit])] {
                values.insert(slot*WIDTH+917504+l.message[byte/8][(byte%8)*8+bit%8],value);
            }
        }
    }
    // The next node-bank slot contains the profile output; its child endpoints stay zero.
    for bit in 0..256 {
        values.insert(records.len()*WIDTH+e.node[bit],profile[bit]);
        values.insert(records.len()*WIDTH+917504+l.output[bit/64][bit%64],profile[bit]);
    }
    Ok(values)
}

pub fn check_tiny(base:&Baseline,topology:&Topology)->Result<TinyEvidence,String> {
    topology.validate()?;let d=&topology.descriptor;
    if d.slots>16 {return Err("tiny check slot cap".into());}
    let values=native_endpoint_assignment(base,d)?;
    let mut evidence=TinyEvidence {headers:d.headers,families:topology.families.len(),compared_terms:0,
        compared_residual_rows:0,non_boolean_challenge_sets:2,endpoint_mutants_rejected:0,
        max_materialized_terms:0,max_materialized_capacity_bytes:0,assignment_coordinates:values.len(),assignment_is_topology_only:true};
    for family in &topology.families {
        let circuit=family.enumerate(d,1<<20)?;let counts=family.count(d)?;
        if circuit.terms.len()!=counts.terms as usize {return Err("count/emitter mismatch".into());}
        evidence.compared_terms+=circuit.terms.len();evidence.compared_residual_rows+=circuit.terms.len();
        evidence.max_materialized_terms=evidence.max_materialized_terms.max(circuit.terms.len());
        evidence.max_materialized_capacity_bytes=evidence.max_materialized_capacity_bytes.max(circuit.terms.capacity()*std::mem::size_of::<Term>());
        for term in &circuit.terms {
            let left=values.get(&term.gate.left).copied().unwrap_or(Fr::zero());
            let right=values.get(&term.gate.right).copied().unwrap_or(Fr::zero());
            let emitted=term.gate.c0+term.gate.c1*left+term.gate.c2*right+term.gate.c3*left*right;
            if !emitted.is_zero() {return Err(format!("native topology oracle residual {} row {}",family.name,term.row));}
        }
        for seed in [3u64,97] {
            let point=|bits:usize,s:u64|(0..bits).map(|b|Fr::from(s+37*(b as u64+1))).collect::<Vec<_>>();
            let r=point(counts.row_log,seed);let u=point(20+d.slot_log(),seed+17);let v=point(20+d.slot_log(),seed+101);
            if family.coefficients(d,&r,&u,&v)?!=direct_coefficients(&circuit,&r,&u,&v) {
                return Err(format!("analytic/enumerated wiring mismatch {}",family.name));
            }
        }
        if let Some(t)=circuit.terms.first() {
            // Isolate one equality; its omission accepts this changed endpoint.
            let left=values[&t.gate.left]+Fr::one();let right=values.get(&t.gate.right).copied().unwrap_or(Fr::zero());
            if (t.gate.c0+left+t.gate.c2*right).is_zero() {return Err("endpoint mutant survived".into());}
            evidence.endpoint_mutants_rejected+=1;
        }
    }Ok(evidence)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sparse;
    #[test] fn work_tree_wiring_descriptor_s_b_and_index_falsifiers() {
        for (h,s,b) in [(3,4,2),(5,8,4),(6,8,8),(8,8,8),(9,16,8)] {
            let d=Descriptor::new(h,[0;32]).unwrap();assert_eq!((d.slots,d.leaves),(s,b));
            assert!(h-1<d.slots);if h==b+1 {let mut mutant=d.clone();mutant.slots=b;assert!(mutant.validate().is_err());}
            assert!(d.validate_leaf_position(0,1).is_err());assert!(d.validate_leaf_position(b,b).is_err());
            for level in 1..=b.trailing_zeros() as usize {
                let (base,count)=d.level(level).unwrap();let cb=if level==1{0}else{d.level(level-1).unwrap().0};
                for p in 0..count {
                    assert!(d.validate_node(level,p,base+p,cb+2*p,cb+2*p+1).is_ok());
                    assert!(d.validate_node(level,p,base+p,cb+2*p+1,cb+2*p).is_err());
                    assert!(d.validate_node(level+1,p,base+p,cb+2*p,cb+2*p+1).is_err());
                }
            }
            let mut wrong=d.clone();wrong.root_node_slot+=1;assert!(wrong.validate().is_err());
            let mut wrong=d.clone();wrong.headers+=1;assert!(wrong.validate().is_err());
        }
        assert!(Descriptor::new(2,[0;32]).is_err());
    }
    #[test] fn work_tree_wiring_all_small_families_nonboolean_differential() {
        let base=layout::shared_baseline().unwrap();
        for h in [3,5,6,8,9] {
            let t=Topology::new(base,h,[0x5a;32]).unwrap();let evidence=check_tiny(base,&t).unwrap();
            assert!(evidence.compared_terms>0);assert!(evidence.endpoint_mutants_rejected>10);
            let before=t.report().unwrap().topology_blake2b256;
            // Private endpoint assignments never enter either public builder.
            let mut witness=native_endpoint_assignment(base,&t.descriptor).unwrap();if let Some(v)=witness.values_mut().next(){*v+=Fr::from(9u64);}
            assert_eq!(before,Topology::new(&base,h,[0x5a;32]).unwrap().report().unwrap().topology_blake2b256);
        }
    }
    #[test] fn work_tree_wiring_independent_native_oracle_kills_consistent_wrong_maps() {
        let base=layout::shared_baseline().unwrap();
        let mut child=Topology::new(base,6,[0x5a;32]).unwrap();
        let family=child.families.iter_mut().find(|f|f.name=="level_1_child_0").unwrap();
        family.mapping=Mapping::Child {level:1,branch:1};
        child.frozen_manifest=layout::hash_bytes(&serde_json::to_vec(&(&child.descriptor,&child.families)).unwrap());
        assert!(child.validate().is_ok());
        assert!(check_tiny(base,&child).unwrap_err().contains("native topology oracle residual"));
        let mut header=Topology::new(base,5,[0x5a;32]).unwrap();
        let values=native_endpoint_assignment(base,&header.descriptor).unwrap();
        let old=header.families[0].left_wires[0];
        // Same parity defeated the former alternating-bit oracle; distinct field tags must reject it.
        let wrong=*base.header_alias_wires.iter().find(|&&wire|wire!=old && wire%2==old%2).unwrap();
        assert_ne!(values[&(WIDTH+wrong)],values[&(WIDTH+old)]);
        header.families[0].left_wires[0]=wrong;
        header.frozen_manifest=layout::hash_bytes(&serde_json::to_vec(&(&header.descriptor,&header.families)).unwrap());
        assert!(header.validate().is_ok());
        assert!(check_tiny(base,&header).unwrap_err().contains("native topology oracle residual"));
    }
    #[test] fn level_two_child_endpoint_emitter_matches_full_term_multiset() {
        let descriptor=Descriptor::new(7,[0x27;32]).unwrap();
        let family=Family{name:"level_two_right_child".into(),mapping:Mapping::Child {level:2,branch:1},
            left_wires:vec![1,4,9],right_wires:vec![2,5,10],constants:None};
        let mut expected=Vec::new();
        family.emit_terms(&descriptor,|term|{
            let source_slot=term.gate.left/WIDTH;let child_slot=term.gate.right/WIDTH;
            let local_row=term.row%family.left_wires.len().next_power_of_two();
            expected.push((true,source_slot,local_row,term.row,term.gate.left,term.gate.right));
            expected.push((false,child_slot,local_row,term.row,term.gate.left,term.gate.right));
            Ok(())
        }).unwrap();
        let mut actual=Vec::new();
        for left_endpoint in [true,false]{for endpoint_slot in 0..descriptor.slots{
            family.emit_endpoint_terms(&descriptor,left_endpoint,endpoint_slot,|source_slot,local_row,term|{
                assert_eq!(source_slot,term.gate.left/WIDTH,"endpoint emitter must preserve the parent row's source slot");
                actual.push((left_endpoint,endpoint_slot,local_row,term.row,term.gate.left,term.gate.right));Ok(())
            }).unwrap();
        }}
        expected.sort_unstable();actual.sort_unstable();
        assert_eq!(actual,expected,"level>1 child endpoint traversal must emit precisely the resident parent-child term multiset");
    }
    #[test] fn work_tree_wiring_omitted_family_and_wrong_index_reject() {
        let base=layout::shared_baseline().unwrap();
        let mut omitted=Topology::new(base,3,[0;32]).unwrap();omitted.families.pop();assert!(omitted.validate().is_err());
        let mut coherent=Topology::new(base,5,[0;32]).unwrap();
        coherent.families.retain(|f|f.name!="level_1_child_0");
        coherent.frozen_manifest=layout::hash_bytes(&serde_json::to_vec(&(&coherent.descriptor,&coherent.families)).unwrap());
        assert!(coherent.validate().unwrap_err().contains("mandatory topology family roster"));
        let mut shifted=Topology::new(base,5,[0;32]).unwrap();shifted.families[0].right_wires[0]+=1;assert!(shifted.validate().is_err());
        let mut root=Topology::new(base,6,[0;32]).unwrap();root.descriptor.root[0]^=1;assert!(root.validate().is_err());
    }
    #[test] fn work_tree_wiring_large_descriptor_constant_buffers_no_materialization() {
        let d=Descriptor::new(1827840,[0;32]).unwrap();assert_eq!((d.slots,d.leaves),(1<<21,1<<21));
        assert_eq!(d.active_native_compressions_upper(),11505660);
        let f=Family {name:"last_level".into(),mapping:Mapping::Child {level:21,branch:1},
            left_wires:vec![1],right_wires:vec![2],constants:None};
        let p=vec![Fr::from(7u64);41];let r=vec![Fr::from(11u64);21];
        assert!(f.coefficients(&d,&r,&p,&p).is_ok());assert!(f.enumerate(&d,1<<20).is_err());
        let mut invalid=p.clone();invalid.pop();assert!(f.coefficients(&d,&r,&invalid,&p).is_err());
        assert!(!f.count(&d).unwrap().fits_sparse_dimension24);
    }
    #[test] fn descriptor_bound_gkr_verifies_topology_family_analytically() {
        let base=layout::shared_baseline().unwrap();
        let topology=Topology::new(base,3,[0x5a;32]).unwrap();
        let family=topology.families.iter().find(|f|f.name=="header_to_leaf_raw_length_nbits_height").unwrap().clone();
        let circuit=family.enumerate(&topology.descriptor,1<<20).unwrap();
        let mut input=vec![Fr::zero();circuit.input_len];
        for (wire,value) in native_endpoint_assignment(base,&topology.descriptor).unwrap(){input[wire]=value;}
        let mut occupied=vec![false;circuit.row_count];
        let mut layer=vec![crate::gkr::Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()};circuit.row_count];
        for term in &circuit.terms {assert!(!occupied[term.row]);occupied[term.row]=true;layer[term.row]=term.gate.clone();}
        let bind=|transcript:&mut crate::transcript::Transcript|{
            transcript.append_bytes(b"structured-wiring-profile",b"work-tree-topology-descriptor-gkr-v1");
            transcript.append_bytes(b"descriptor-json",&serde_json::to_vec(&topology.descriptor).unwrap());
            transcript.append_bytes(b"family-json",&serde_json::to_vec(&family).unwrap());
        };
        let mut prover=crate::transcript::Transcript::new(b"structured-topology-gkr-v1");
        let (proof,claim)=crate::gkr::prove_with_binding(&input,&[layer],&mut prover,|t|bind(t)).unwrap();
        let dimensions=[20+topology.descriptor.slot_log()];
        let mut verifier=crate::transcript::Transcript::new(b"structured-topology-gkr-v1");
        let checked=crate::gkr::verify_with_wiring(&dimensions,circuit.row_count,&proof,&mut verifier,
            |t|bind(t),|_,r,u,v|family.coefficients(&topology.descriptor,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)).unwrap();
        assert_eq!(checked,claim);
        assert_eq!(checked.value,crate::gkr::mle(&input,&checked.point).unwrap());

        // This profile exercises the analytic callback at the historical
        // slot count without materializing rows or a per-slot term list.
        let historical=Topology::new(base,1_827_840,[0x5a;32]).unwrap();
        let large=historical.families.iter().find(|f|f.name==family.name).unwrap();
        let count=large.count(&historical.descriptor).unwrap();
        let r=vec![Fr::from(13u64);count.row_log];
        let u=vec![Fr::from(17u64);count.global_input_bits];
        let v=vec![Fr::from(19u64);count.global_input_bits];
        let started=std::time::Instant::now();
        let coefficients=large.coefficients(&historical.descriptor,&r,&u,&v).unwrap();
        let elapsed=started.elapsed();
        assert!(coefficients.iter().any(|x|!x.is_zero()));
        assert!(large.enumerate(&historical.descriptor,1<<20).is_err());
        println!("descriptor_gkr_verified_h3_slots={} historical_slots={} family_terms={} analytic_eval_us={}",
            topology.descriptor.slots,historical.descriptor.slots,count.terms,elapsed.as_micros());

        let mut changed=family.clone();changed.right_wires[0]+=1;
        let mut binding_mutant=crate::transcript::Transcript::new(b"structured-topology-gkr-v1");
        let bad_binding=crate::gkr::verify_with_wiring(&dimensions,circuit.row_count,&proof,&mut binding_mutant,
            |t|{
                t.append_bytes(b"structured-wiring-profile",b"work-tree-topology-descriptor-gkr-v1");
                t.append_bytes(b"descriptor-json",&serde_json::to_vec(&topology.descriptor).unwrap());
                t.append_bytes(b"family-json",&serde_json::to_vec(&changed).unwrap());
            },|_,r,u,v|family.coefficients(&topology.descriptor,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(bad_binding.is_err(),"mutated descriptor binding accepted with old GKR proof");
        let mut wiring_mutant=crate::transcript::Transcript::new(b"structured-topology-gkr-v1");
        let bad_wiring=crate::gkr::verify_with_wiring(&dimensions,circuit.row_count,&proof,&mut wiring_mutant,
            |t|bind(t),|_,r,u,v|changed.coefficients(&topology.descriptor,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(bad_wiring.is_err(),"mutated analytic callback accepted with original descriptor");
    }
    #[test] fn every_worktree_analytic_family_accepts_historical_virtual_shape() {
        let headers=1_827_840;let root=[0x5a;32];let base=layout::shared_baseline().unwrap();
        let point=|bits:usize,seed:u64|(0..bits).map(|i|Fr::from(seed+29*(i as u64+1))).collect::<Vec<_>>();
        let descriptor=Descriptor::new(headers,root).unwrap();let h=descriptor.slot_log();
        let topology=Topology::new(base,headers,root).unwrap();let mut b1_count=0usize;let mut empty_families=0usize;
        for family in &topology.families {
            let count=family.count(&descriptor).unwrap();
            let coefficients=family.coefficients(&descriptor,&point(count.row_log,3),&point(count.global_input_bits,17),
                &point(count.global_input_bits,31)).unwrap();
            if count.live_rows==0 {
                assert!(coefficients.iter().all(|coefficient| coefficient.is_zero()),
                    "B1 {} has no live rows but returned nonzero coefficients",family.name);
                empty_families+=1;
            } else {
                assert!(coefficients.iter().any(|coefficient| !coefficient.is_zero()),
                    "B1 {} returned only zero coefficients",family.name);
            }
            assert!(family.enumerate(&descriptor,1<<20).is_err(),"B1 historical enumeration unexpectedly admitted: {}",family.name);
            b1_count+=1;
        }
        assert_eq!(b1_count,52,"historical topology roster changed");
        assert_eq!(empty_families,1,"historical topology empty-family count changed");

        let engine=crate::work_tree_fixed_hash::engine().unwrap();
        let fixed_profile=crate::work_tree_fixed_hash::FixedProfile::new(headers,root).unwrap();
        let b2=crate::work_tree_fixed_hash::coefficients(engine,&fixed_profile,&point(11+h,5),&point(20+h,19),
            &point(20+h,37)).unwrap();
        assert!(b2.iter().any(|coefficient| !coefficient.is_zero()),"B2 returned only zero coefficients");

        let leaf_profile=crate::work_tree_leaf_hash::LeafProfile::new(headers,root).unwrap();
        let leaf_boundary=crate::work_tree_leaf_hash::compile(engine,leaf_profile).unwrap();
        let b3=crate::work_tree_leaf_hash::coefficients(&leaf_boundary,&point(14+h,7),&point(20+h,23),
            &point(20+h,41)).unwrap();
        assert!(b3.iter().any(|coefficient| !coefficient.is_zero()),"B3 returned only zero coefficients");

        let work_profile=crate::work_tree_work::WorkProfile::new(headers,root,[0;28]).unwrap();
        let work_boundary=crate::work_tree_work::compile(base,work_profile).unwrap();
        let b4_local=crate::work_tree_work::local_coefficients(&work_boundary,&point(11+h,11),&point(20+h,29),
            &point(20+h,43)).unwrap();
        assert!(b4_local.iter().any(|coefficient| !coefficient.is_zero()),"B4 local returned only zero coefficients");
        let mut b4_links=0usize;
        for family in work_boundary.links() {
            let count=family.count(&descriptor).unwrap();
            let coefficients=family.coefficients(&descriptor,&point(count.row_log,13),&point(count.global_input_bits,31),
                &point(count.global_input_bits,47)).unwrap();
            assert!(coefficients.iter().any(|coefficient| !coefficient.is_zero()),"B4 {} returned only zero coefficients",family.name);
            b4_links+=1;
        }
        assert_eq!(b4_links,3,"historical B4-link roster changed");
        println!("historical_analytic_roster headers={headers} slots={} b1_families={b1_count} b2=1 b3=1 b4_local=1 b4_links={b4_links}",
            descriptor.slots);
    }
    #[test] fn descriptor_bound_tagged_b1_roster_gkr_matches_sparse_reference() {
        let base=layout::shared_baseline().unwrap();let topology=Topology::new(base,3,[0x5a;32]).unwrap();
        let shape=tagged_roster_shape(&topology).unwrap();let circuit=tagged_roster_circuit(&topology).unwrap();
        assert_eq!(shape.input_len,topology.descriptor.slots*WIDTH);
        assert_eq!(shape.row_bits,shape.local_row_bits+shape.family_bits);
        let assignment=native_endpoint_assignment(base,&topology.descriptor).unwrap();
        let mut input=vec![Fr::zero();circuit.input_len];
        for (index,value) in assignment {input[index]=value;}
        let sparse_shape=sparse::validate(&circuit,0).unwrap();
        let point=|bits:usize,seed:u64|(0..bits).map(|i|Fr::from(seed+37*(i as u64+1))).collect::<Vec<_>>();
        for seed in [3u64,29,71] {
            let r=point(shape.row_bits,seed);let u=point(shape.input_bits,seed+101);let v=point(shape.input_bits,seed+211);
            let expected=sparse::wiring(&circuit,&sparse_shape,&r,&u,&v).unwrap();
            let actual=tagged_roster_coefficients(&topology,&r,&u,&v).unwrap();
            assert_eq!(actual,expected,"tagged B1 analytic/enumerated wiring at seed {seed}");
        }
        let mut prover_transcript=crate::transcript::Transcript::new(b"tagged-b1-roster-gkr-test-v1");
        let (proof,expected)=sparse::prove_with_binding(&circuit,&input,0,&mut prover_transcript,
            |transcript|bind_tagged_roster(&topology,transcript)).unwrap();
        let mut verifier_transcript=crate::transcript::Transcript::new(b"tagged-b1-roster-gkr-test-v1");
        let actual=crate::gkr::verify_with_wiring(&[shape.input_bits],circuit.row_count,&proof,&mut verifier_transcript,
            |transcript|bind_tagged_roster(&topology,transcript),
            |_,r,u,v|tagged_roster_coefficients(&topology,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)).unwrap();
        assert_eq!(actual,expected,"tagged roster GKR prover/verifier claim mismatch");
        assert_eq!(actual.value,crate::gkr::mle(&input,&actual.point).unwrap(),"tagged roster claim is not the input MLE");

        let wrong_tag=|index|match index {0=>1,1=>0,_=>index};
        let mut mutant_transcript=crate::transcript::Transcript::new(b"tagged-b1-roster-gkr-test-v1");
        let mutant=crate::gkr::verify_with_wiring(&[shape.input_bits],circuit.row_count,&proof,&mut mutant_transcript,
            |transcript|bind_tagged_roster(&topology,transcript),
            |_,r,u,v|tagged_roster_coefficients_with_tag(&topology,r,u,v,wrong_tag)
                .map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(mutant.is_err(),"callback with two family tags swapped accepted under the original valid roster binding");
        println!("tagged_b1_roster_gkr headers=3 families={} terms={} input_bits={} row_bits={} proof_layers={} ",
            topology.families.len(),circuit.terms.len(),shape.input_bits,shape.row_bits,proof.layers.len());

        let historical=Topology::new(base,1_827_840,[0x5a;32]).unwrap();
        let historical_shape=tagged_roster_shape(&historical).unwrap();
        let historical_point=|bits:usize,seed:u64|(0..bits).map(|i|Fr::from(seed+37*(i as u64+1))).collect::<Vec<_>>();
        let r=historical_point(historical_shape.row_bits,7);let u=historical_point(historical_shape.input_bits,109);
        let v=historical_point(historical_shape.input_bits,223);let before=std::time::Instant::now();
        let coefficients=tagged_roster_coefficients(&historical,&r,&u,&v).unwrap();
        let elapsed=before.elapsed();let historical_terms=historical.families.iter()
            .map(|family|family.count(&historical.descriptor).unwrap().terms).sum::<u64>();
        assert_eq!(historical.families.len(),52);assert_eq!(historical_shape.input_bits,41);
        assert_eq!(historical_shape.row_bits,40);assert!(coefficients.iter().any(|coefficient|!coefficient.is_zero()));
        println!("historical_tagged_b1_roster headers=1827840 families={} logical_constraints={} input_bits={} row_bits={} callback_us={}",
            historical.families.len(),historical_terms,historical_shape.input_bits,historical_shape.row_bits,elapsed.as_micros());
    }

    #[test] fn full_tagged_worktree_roster_matches_materialized_h3_and_evaluates_historical_shape() {
        let root=[0x5a;32];let base=layout::shared_baseline().unwrap();let engine=crate::work_tree_fixed_hash::engine().unwrap();
        let topology=Topology::new(base,3,root).unwrap();
        let fixed_profile=crate::work_tree_fixed_hash::FixedProfile::new(3,root).unwrap();
        let leaf_boundary=crate::work_tree_leaf_hash::compile(engine,
            crate::work_tree_leaf_hash::LeafProfile::new(3,root).unwrap()).unwrap();
        let work_boundary=crate::work_tree_work::compile(base,
            crate::work_tree_work::WorkProfile::new(3,root,[0;28]).unwrap()).unwrap();
        let (local_row_bits,family_bits,row_bits,input_bits)=full_roster_shape(&topology).unwrap();
        assert_eq!((local_row_bits,family_bits,row_bits,input_bits),(16,5,21,22));
        let circuit=full_roster_circuit(&topology,engine,&fixed_profile,&leaf_boundary,&work_boundary).unwrap();
        let family_index=topology.families.len()+6;
        assert!(circuit.terms.len()<1<<20,"bounded H3 roster exceeds sparse base-term cap");
        let sparse_shape=crate::sparse::validate(&circuit,0).unwrap();
        let point=|bits:usize,seed:u64|(0..bits).map(|i|Fr::from(seed+37*(i as u64+1))).collect::<Vec<_>>();
        for seed in [5u64,43,97] {
            let r=point(row_bits,seed);let u=point(input_bits,seed+101);let v=point(input_bits,seed+211);
            let expected=crate::sparse::wiring(&circuit,&sparse_shape,&r,&u,&v).unwrap();
            let actual=full_roster_coefficients(&topology,engine,&fixed_profile,&leaf_boundary,&work_boundary,&r,&u,&v).unwrap();
            assert_eq!(actual,expected,"full tagged roster analytic/materialized coefficients at seed {seed}");
        }
        println!("full_tagged_roster_h3 families={} terms={} input_bits={} row_bits={} local_row_bits={}",
            family_index,circuit.terms.len(),input_bits,row_bits,local_row_bits);

        let historical=Topology::new(base,1_827_840,root).unwrap();
        let historical_shape=full_roster_shape(&historical).unwrap();
        assert_eq!(historical.families.len()+6,58);assert_eq!(historical_shape,(35,6,41,41));
        let historical_fixed=crate::work_tree_fixed_hash::FixedProfile::new(1_827_840,root).unwrap();
        let historical_leaf=crate::work_tree_leaf_hash::compile(engine,
            crate::work_tree_leaf_hash::LeafProfile::new(1_827_840,root).unwrap()).unwrap();
        let historical_work=crate::work_tree_work::compile(base,
            crate::work_tree_work::WorkProfile::new(1_827_840,root,[0;28]).unwrap()).unwrap();
        let r=point(historical_shape.2,17);let u=point(historical_shape.3,109);let v=point(historical_shape.3,223);
        let started=std::time::Instant::now();
        let coefficients=full_roster_coefficients(&historical,engine,&historical_fixed,&historical_leaf,&historical_work,&r,&u,&v).unwrap();
        let elapsed=started.elapsed();assert!(coefficients.iter().any(|coefficient|!coefficient.is_zero()));
        println!("full_tagged_roster_historical headers=1827840 families=58 input_bits={} row_bits={} callback_us={}",
            historical_shape.3,historical_shape.2,elapsed.as_micros());
    }

    #[test] fn count_h3_local_tensor_active_left_support_for_cache_feasibility() {
        use ark_ff::PrimeField;
        use std::collections::BTreeSet;
        let root=[0x5a;32];let base=layout::shared_baseline().unwrap();
        let engine=crate::work_tree_fixed_hash::engine().unwrap();
        let topology=Topology::new(base,3,root).unwrap();
        let fixed_profile=crate::work_tree_fixed_hash::FixedProfile::new(3,root).unwrap();
        let leaf_boundary=crate::work_tree_leaf_hash::compile(engine,
            crate::work_tree_leaf_hash::LeafProfile::new(3,root).unwrap()).unwrap();
        let work_boundary=crate::work_tree_work::compile(base,
            crate::work_tree_work::WorkProfile::new(3,root,[0;28]).unwrap()).unwrap();
        let member_row_bits=full_split_local_tensor_member_row_bits(&topology,&work_boundary).unwrap();
        let row_width_groups=member_row_bits.iter().copied().collect::<BTreeSet<_>>();
        let mut total_terms=0usize;let mut max_support=0usize;let mut all_support=BTreeSet::new();
        let mut normalized_by_slot=Vec::with_capacity(topology.descriptor.slots);
        let base_row_bits=member_row_bits.iter().copied().max().unwrap();
        let local_row_mask=(1usize<<base_row_bits)-1;let input_width=1usize<<full_split_local_tensor_dimensions(&topology,&work_boundary).unwrap().0;
        for slot in 0..topology.descriptor.slots {
            let mut support=BTreeSet::new();let mut terms=0usize;let mut normalized=BTreeMap::<usize,Vec<(usize,bool,bool,usize,usize,[[u64;4];4])>>::new();
            full_split_visit_local_slot_terms(&topology,engine,&fixed_profile,&leaf_boundary,&work_boundary,slot,&mut |term|{
                terms+=1;
                if !term.gate.c1.is_zero()||!term.gate.c3.is_zero(){support.insert(term.gate.left);}
                let family=term.row>>base_row_bits;let local_row=term.row&local_row_mask;
                let left_anchor=term.gate.left==input_width;let right_anchor=term.gate.right==input_width;
                let coefficients=[term.gate.c0.into_bigint().0,term.gate.c1.into_bigint().0,
                    term.gate.c2.into_bigint().0,term.gate.c3.into_bigint().0];
                normalized.entry(family).or_default().push((local_row,left_anchor,right_anchor,
                    if left_anchor{0}else{term.gate.left},if right_anchor{0}else{term.gate.right},coefficients));
                Ok(())
            }).unwrap();
            for terms in normalized.values_mut(){terms.sort_unstable();}
            normalized_by_slot.push(normalized);
            total_terms+=terms;max_support=max_support.max(support.len());all_support.extend(support);
        }
        let identical_families=normalized_by_slot.first().map(|first|first.iter().filter(|(family,terms)|
            normalized_by_slot.iter().skip(1).all(|slot|slot.get(family)==Some(terms))).count()).unwrap_or(0);
        let padded_slots=1u128<<25;
        let max_sparse_bytes=(max_support as u128)*padded_slots*2*32;
        println!("h3_local_support slots={} terms={} union_active_left={} max_active_left_per_slot={} row_width_groups={row_width_groups:?} identical_normalized_families={identical_families}/{} two_array_bytes_at_2^25_slots={max_sparse_bytes}",
            topology.descriptor.slots,total_terms,all_support.len(),max_support,member_row_bits.len());
        assert!(total_terms>0&&max_support>0);
    }

    #[test] fn full_tagged_worktree_roster_accepts_exact_tag_capacity_at_130_headers() {
        let headers=130;let root=[0x5a;32];let base=layout::shared_baseline().unwrap();
        let engine=crate::work_tree_fixed_hash::engine().unwrap();let topology=Topology::new(base,headers,root).unwrap();
        let fixed_profile=crate::work_tree_fixed_hash::FixedProfile::new(headers,root).unwrap();
        let leaf_boundary=crate::work_tree_leaf_hash::compile(engine,
            crate::work_tree_leaf_hash::LeafProfile::new(headers,root).unwrap()).unwrap();
        let work_boundary=crate::work_tree_work::compile(base,
            crate::work_tree_work::WorkProfile::new(headers,root,[0;28]).unwrap()).unwrap();
        let shape=full_roster_shape(&topology).unwrap();
        assert_eq!(topology.families.len(),26);assert_eq!(shape,(22,5,27,28));
        let point=|bits:usize,seed:u64|(0..bits).map(|i|Fr::from(seed+37*(i as u64+1))).collect::<Vec<_>>();
        let r=point(shape.2,11);let u=point(shape.3,101);let v=point(shape.3,211);
        let coefficients=full_roster_coefficients(&topology,engine,&fixed_profile,&leaf_boundary,&work_boundary,&r,&u,&v).unwrap();
        assert!(coefficients.iter().any(|coefficient|!coefficient.is_zero()));
    }

    #[test] fn historical_b1_gkr_verifier_accepts_synthetic_zero_relation_at_41_bits() {
        let base=layout::shared_baseline().unwrap();
        let topology=Topology::new(base,1_827_840,[0;32]).unwrap();
        let shape=tagged_roster_shape(&topology).unwrap();
        assert_eq!((shape.input_bits,shape.row_bits),(41,40));
        let proof=crate::gkr::GkrProof{layers:vec![crate::gkr::LayerProof{
            rounds:vec![vec![Fr::zero();3];2*shape.input_bits],
            left_value:Fr::zero(),right_value:Fr::zero(),
            line_coefficients:vec![Fr::zero();shape.input_bits+1],
        }]};
        let mut transcript=crate::transcript::Transcript::new(b"historical-b1-zero-gkr-smoke-v1");
        let claim=crate::gkr::verify_with_wiring(&[shape.input_bits],1usize<<shape.row_bits,&proof,&mut transcript,
            |transcript|bind_tagged_roster(&topology,transcript),
            |_,r,u,v|tagged_roster_coefficients(&topology,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(claim.is_ok(),"zero-relation verifier plumbing at historical dimensions rejected: {claim:?}");
        let claim=claim.unwrap();assert!(claim.value.is_zero());
        println!("historical_b1_zero_gkr_verifier input_bits={} row_bits={} rounds={} claim=zero",
            shape.input_bits,shape.row_bits,2*shape.input_bits);
    }
}

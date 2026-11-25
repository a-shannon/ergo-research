use crate::{legacy_composition::{self as lc, Component, LegacyComposition},
    legacy_envelope_map::{self as lm, Map},
    legacy_native_adapter::{native_cap_summary, LegacyNativeAdapter},
    packed_owner_assembly::{self as assembly, NativeOwnerProducer, NativePackedRow, NativePrefix},
    packed_owner_assembly_tests as fixtures, sparse::Term, gkr::Gate, transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{Blake2b512, Digest};
use num_bigint::BigUint;
use std::collections::BTreeMap;

fn error<T>(value: Result<T,String>) -> String {
    match value {Err(e)=>e,Ok(_)=>panic!("negative accepted")}
}
fn prefix() -> &'static NativePrefix {
    // Each selected process replays this before any plan/template/owner rows.
    let input=fixtures::legacy_prefix_for_test();
    let cap=native_cap_summary(input).unwrap();
    assert_eq!(cap.maximum,BigUint::from(185435213004800u64));
    assert_eq!(cap.height,3073);
    assert_eq!(cap.total,BigUint::from(24293759260819456u64));
    assert_eq!((&cap.maximum-BigUint::from(1u8)).bits(),48);
    input
}
fn fixture() -> (&'static NativePrefix,&'static WorkTreeHistoryPlan) {
    let input=prefix(); (input,fixtures::legacy_assembly_plan_for_test())
}
fn point(log:usize,seed:u64)->Vec<Fr> {
    (0..log).map(|i|Fr::from(seed+13*(i as u64+1))).collect()
}
fn boolean(log:usize,index:usize)->Vec<Fr> {
    (0..log).map(|i|Fr::from(((index>>i)&1) as u64)).collect()
}
fn eq(point:&[Fr],index:usize)->Fr {
    point.iter().enumerate().fold(Fr::one(),|a,(b,x)|a*if index>>b&1==1 {*x}else{Fr::one()-x})
}
fn gate_coefficients(g:&Gate)->[Fr;4] {[g.c0,g.c1,g.c2,g.c3]}
fn small_term(row:usize,left:usize,right:usize,coefficients:[Fr;4])->Term {
    Term{row,gate:Gate{left,right,c0:coefficients[0],c1:coefficients[1],c2:coefficients[2],c3:coefficients[3]}}
}
fn direct(term:&Term,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    let w=eq(r,term.row)*eq(u,term.gate.left)*eq(v,term.gate.right);
    gate_coefficients(&term.gate).map(|c|w*c)
}
struct StreamFingerprint { hash:Blake2b512, count:u64 }
impl StreamFingerprint {
    fn new()->Self {
        let mut hash=Blake2b512::new();
        hash.update(b"composition-test-ordered-literal-stream-v1");
        Self{hash,count:0}
    }
    fn push(&mut self,component:Component,term:&Term) {
        for value in [self.count,component.tag() as u64,term.row as u64,
            term.gate.left as u64,term.gate.right as u64] {
            self.hash.update(value.to_le_bytes());
        }
        for coefficient in gate_coefficients(&term.gate) {
            let mut bytes=[0u8;32];
            coefficient.serialize_compressed(&mut bytes[..]).unwrap();
            self.hash.update(bytes);
        }
        self.count+=1;
    }
    fn finish(self)->(u64,Vec<u8>) {(self.count,self.hash.finalize().to_vec())}
}
fn source_embedding(component:Component,owner:usize,source:&Term)->Term {
    let stride_log=if component==Component::LegacyMap {14}else{19};
    assert_eq!(source.row>>stride_log,owner);
    assert!(source.row<1usize<<component.source_log());
    assert!(source.gate.left<1usize<<32 && source.gate.right<1usize<<32);
    let expected=Term{row:component.tag()*lc::PAYLOAD+source.row,gate:source.gate.clone()};
    let embedded=lc::embed(component,source.clone()).unwrap();
    assert_eq!(embedded.row,expected.row);
    assert_eq!((embedded.gate.left,embedded.gate.right),(expected.gate.left,expected.gate.right));
    assert_eq!(gate_coefficients(&embedded.gate),gate_coefficients(&expected.gate));
    expected
}
fn row_point(component:Component,owner:usize,seed:u64)->Vec<Fr> {
    let low=if component==Component::LegacyMap {14}else{19};
    let mut r=point(low,seed);r.extend(boolean(12,owner));
    if component==Component::LegacyMap {r.extend(point(5,seed+97));}
    r.extend(boolean(2,component.tag()));
    assert_eq!(r.len(),33);r
}

// Independent equality tables are bounded to ONE owner-local domain. They
// are coefficient weights, never X, global rows, or an analytic hot path.
fn local_weights(point:&[Fr])->Vec<Fr> {
    let mut out=vec![Fr::one()];
    for x in point {
        let old=out.len();out.reserve(old);
        for i in 0..old {let a=out[i];out[i]=a*(Fr::one()-x);out.push(a*x);}
    }
    out
}
struct OraclePoint {
    seed:u64, u:Vec<Fr>,v:Vec<Fr>,ul:Vec<Fr>,vl:Vec<Fr>,
    r19:Vec<Fr>,r14:Vec<Fr>,u_owner:BTreeMap<usize,Fr>,v_owner:BTreeMap<usize,Fr>,
}
impl OraclePoint {
    fn new(seed:u64)->Self {
        let u=point(32,seed+17);let v=point(32,seed+53);
        let ul=local_weights(&u[..20]);let vl=local_weights(&v[..20]);
        Self{seed,u,v,ul,vl,r19:local_weights(&point(19,seed)),
            r14:local_weights(&point(14,seed)),u_owner:BTreeMap::new(),v_owner:BTreeMap::new()}
    }
    fn add(&mut self,component:Component,owner:usize,source:&Term,output:&mut[Fr;4]) {
        let low=if component==Component::LegacyMap {14}else{19};
        assert_eq!(source.row>>low,owner);
        let local=source.row&((1<<low)-1);
        let mut rw=if low==14 {self.r14[local]}else{self.r19[local]};
        if low==14 {rw*=point(5,self.seed+97).iter().fold(Fr::one(),|a,x|a*(Fr::one()-x));}
        let uo=source.gate.left>>20;let vo=source.gate.right>>20;
        let uw=*self.u_owner.entry(uo).or_insert_with(||eq(&self.u[20..],uo));
        let vw=*self.v_owner.entry(vo).or_insert_with(||eq(&self.v[20..],vo));
        let w=rw*self.ul[source.gate.left&((1<<20)-1)]*uw
            *self.vl[source.gate.right&((1<<20)-1)]*vw;
        for (out,c) in output.iter_mut().zip(gate_coefficients(&source.gate)) {*out+=w*c;}
    }
}

#[test]
fn tagged_rows_reject_cancellation() {
    let h=small_term(17,0,0,[Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()]);
    let m=small_term(17,0,0,[-Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()]);
    assert_eq!(h.gate.c0+m.gate.c0,Fr::zero());
    let tagged_h=lc::embed(Component::Header,h).unwrap();
    let tagged_m=lc::embed(Component::LegacyMap,m).unwrap();
    assert_eq!(tagged_h.row,17);assert_eq!(tagged_m.row,lc::PAYLOAD+17);
    let residuals=BTreeMap::from([(tagged_h.row,tagged_h.gate.c0),(tagged_m.row,tagged_m.gate.c0)]);
    assert_eq!(residuals.len(),2);assert!(residuals.values().all(|r|!r.is_zero()));
    // Collapsing the two tags destroys conjunction even on Boolean rows.
    let collapsed=tagged_h.gate.c0+tagged_m.gate.c0;assert!(collapsed.is_zero());
    for tag in [3usize,4,usize::MAX] {assert_eq!(error(Component::try_from(tag)),"composition component tag rejected");}
    for component in [Component::Header,Component::LegacyMap,Component::Daa] {
        let coeffs=[Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),Fr::from(7u64)];
        let mapped=lc::embed(component,small_term(29,123,456,coeffs)).unwrap();
        assert_eq!(mapped.row,component.tag()*lc::PAYLOAD+29);
        assert_eq!((mapped.gate.left,mapped.gate.right),(123,456));
        assert_eq!(gate_coefficients(&mapped.gate),coeffs);
        assert_eq!(error(lc::embed(component,small_term(1usize<<component.source_log(),0,0,coeffs))),
            "composition source coordinate rejected");
        for side in [0,1] {
            let (left,right)=if side==0 {(1usize<<32,0)}else{(0,1usize<<32)};
            assert_eq!(error(lc::embed(component,small_term(0,left,right,coeffs))),"composition source coordinate rejected");
        }
    }
    // Stored right endpoints matter in all coefficient channels, even when
    // c0/c1 residual evaluation does not read their values.
    let r=point(33,7);let u=point(32,23);let v=point(32,59);
    for channel in [0usize,1] {
        let mut cs=[Fr::zero();4];cs[channel]=Fr::one();
        let a=lc::embed(Component::LegacyMap,small_term(8350,3007*(1<<20)+655654,3007*(1<<20),cs)).unwrap();
        let mut b=a.clone();b.gate.right=0;
        assert_ne!(direct(&a,&r,&u,&v)[channel],direct(&b,&r,&u,&v)[channel]);
    }
    let bit=3007*(1<<20)+655654;
    let boolean_gate=lc::embed(Component::LegacyMap,small_term(3007*(1<<14),bit,bit,
        [Fr::zero(),-Fr::one(),Fr::zero(),Fr::one()])).unwrap();
    let original=direct(&boolean_gate,&r,&u,&v);
    let mut product=boolean_gate.clone();product.gate.c1=Fr::zero();
    let mut linear=boolean_gate.clone();linear.gate.c3=Fr::zero();linear.gate.right=3007*(1<<20);
    let a=direct(&product,&r,&u,&v);let b=direct(&linear,&r,&u,&v);
    let changed=std::array::from_fn::<_,4,_>(|k|a[k]+b[k]);
    assert_ne!(original[1],changed[1]);assert_eq!(original[3],changed[3]);
    let _=prefix();
}

#[test]
fn literal_and_analytic_components() {
    let (input,parent)=fixture();let adapter=LegacyNativeAdapter::compile(parent,input).unwrap();
    let composition=LegacyComposition::compile(&adapter).unwrap();
    assert_eq!((composition.input_log(),composition.row_log()),(32,33));
    let mut points=[OraclePoint::new(7),OraclePoint::new(29)];
    let mut actual=[[[Fr::zero();4];3];2];let mut seen=[0usize;3];
    let mut actual_fingerprint=StreamFingerprint::new();
    // One complete HEADER3007 stream, with both point evaluations in this pass.
    let counts=composition.visit_owner_terms(3007,|term| {
        let component=Component::try_from(term.row>>31)?;
        actual_fingerprint.push(component,&term);let mut source=term;
        source.row-=component.tag()*lc::PAYLOAD;seen[component.tag()]+=1;
        for (index,point) in points.iter_mut().enumerate() {point.add(component,3007,&source,&mut actual[index][component.tag()]);}
        Ok(())
    }).unwrap();
    assert_eq!([counts.header,counts.map,counts.daa],seen);
    assert!(seen.iter().all(|n|*n>0));
    // Each immutable canonical factory is streamed once. This binds EVERY
    // emitted gate, both endpoints, embedded row, component and stream order.
    // The source-owner rejection branch has no peer-supplied constructor:
    // owner correspondence is an inherited canonical-factory premise,
    // checked below for every term rather than fabricated as mutable input.
    let map=Map::from_parent(parent,64).unwrap();
    let mut expected_fingerprint=StreamFingerprint::new();
    let mut expected_counts=[0usize;3];let mut shifted_rows=[false;3];
    let mut shifted_import=false;
    let address_r=point(33,83);let address_u=point(32,101);let address_v=point(32,149);
    let mut compare_source=|component:Component,source:Term|->Result<(),String> {
        let expected=source_embedding(component,3007,&source);
        expected_fingerprint.push(component,&expected);
        expected_counts[component.tag()]+=1;
        let coefficients=gate_coefficients(&source.gate);
        if !shifted_rows[component.tag()] && coefficients.iter().any(|c|!c.is_zero()) {
            let original=direct(&expected,&address_r,&address_u,&address_v);
            assert!(original.iter().any(|c|!c.is_zero()));
            let mut changed_source=source.clone();
            changed_source.row+=1usize<<if component==Component::LegacyMap {14}else{19};
            assert!(changed_source.row<1usize<<component.source_log());
            let changed=lc::embed(component,changed_source).unwrap();
            assert_eq!((changed.gate.left,changed.gate.right),(expected.gate.left,expected.gate.right));
            assert_eq!(gate_coefficients(&changed.gate),coefficients);
            assert_ne!(direct(&changed,&address_r,&address_u,&address_v),original,
                "source row owner shift {component:?}");
            shifted_rows[component.tag()]=true;
        }
        if component==Component::LegacyMap && !shifted_import
            && source.gate.left>>20!=3007
            && (!source.gate.c1.is_zero() || !source.gate.c3.is_zero()) {
            let original=direct(&expected,&address_r,&address_u,&address_v);
            assert!(original.iter().any(|c|!c.is_zero()));
            let mut changed=expected.clone();
            let source_owner=changed.gate.left>>20;
            changed.gate.left=((source_owner+1)<<20)|(changed.gate.left&((1<<20)-1));
            assert!(changed.gate.left<1usize<<32);
            assert_eq!(changed.row,expected.row);assert_eq!(changed.gate.right,expected.gate.right);
            assert_eq!(gate_coefficients(&changed.gate),coefficients);
            assert_ne!(direct(&changed,&address_r,&address_u,&address_v),original,
                "foreign left endpoint owner shift");
            shifted_import=true;
        }
        Ok(())
    };
    adapter.roster().visit_header_terms(3007,|term|compare_source(Component::Header,term)).unwrap();
    for term in map.terms(3007).unwrap() {compare_source(Component::LegacyMap,term).unwrap();}
    adapter.roster().visit_owner_terms(3007,|term|compare_source(Component::Daa,term)).unwrap();
    drop(compare_source);
    assert_eq!(expected_counts,seen);
    assert_eq!(expected_fingerprint.finish(),actual_fingerprint.finish());
    assert_eq!(shifted_rows,[true;3]);assert!(shifted_import);
    for (index,p) in points.iter().enumerate() {
        for component in [Component::Header,Component::LegacyMap,Component::Daa] {
            let r=row_point(component,3007,p.seed);
            let got=composition.coefficients(&r,&p.u,&p.v).unwrap();
            assert_eq!(got,actual[index][component.tag()]);
            assert!(got.iter().any(|c|!c.is_zero()),"nonzero family control {component:?}");
        }
    }
    // One additional DAA owner, not an additional full HEADER stream.
    let mut daa=[[Fr::zero();4];2];let mut count=0;
    let lanes=adapter.roster().visit_owner_terms(2048,|term| {
        count+=1;for (i,p) in points.iter_mut().enumerate(){p.add(Component::Daa,2048,&term,&mut daa[i]);}Ok(())
    }).unwrap();
    assert_eq!(count,lanes.lanes.iter().sum::<usize>());assert!(lanes.lanes[0]>0 && lanes.lanes[1]>0);
    for (i,p) in points.iter().enumerate() {
        let r=row_point(Component::Daa,2048,p.seed);
        assert_eq!(composition.coefficients(&r,&p.u,&p.v).unwrap(),daa[i]);
        assert!(daa[i].iter().any(|c|!c.is_zero()));
    }
    // Boolean A4 controls retain the carry anchor and release short M2 only.
    for (owner,expected) in [(3007usize,Fr::one()),(3072,Fr::zero())] {
        let row=owner*(1<<19)+348441;let left=owner*(1<<20)+991233;let right=owner*(1<<20);
        let mut observed=Fr::zero();
        adapter.roster().visit_header_terms(owner as u64,|t| {
            if t.row==row && t.gate.left==left && t.gate.right==right {observed+=t.gate.c1;}Ok(())
        }).unwrap();
        assert_eq!(observed,expected);
        let r=boolean(31,row);let u=boolean(32,left);let v=boolean(32,right);
        assert_eq!(adapter.roster().header_coefficients(&r,&u,&v).unwrap(),
            [Fr::zero(),expected,Fr::zero(),Fr::zero()]);
    }
    drop(points); // Local equality caches are no longer needed.
    // Full non-Boolean owner points check delegated GLUE. This oracle does
    // not claim selected literal owners span the entire non-Boolean domain.
    for seed in [43u64,71] {
        let r=point(33,seed);let u=point(32,seed+17);let v=point(32,seed+53);
        let h=adapter.roster().header_coefficients(&r[..31],&u,&v).unwrap();
        let m=map.coefficients(&r[..26],&u,&v).unwrap();
        let d=adapter.roster().coefficients(&r[..31],&u,&v).unwrap();
        let weights=[(Fr::one()-r[31])*(Fr::one()-r[32]),r[31]*(Fr::one()-r[32]),
            (Fr::one()-r[31])*r[32]];
        let pad=(26..31).map(|b|Fr::one()-r[b]).product::<Fr>();
        let expected=std::array::from_fn::<_,4,_>(|k|weights[0]*h[k]+weights[1]*pad*m[k]+weights[2]*d[k]);
        assert_eq!(composition.coefficients(&r,&u,&v).unwrap(),expected);
        let source=[h,m.map(|x|pad*x),d];
        for omitted in 0..3 {
            assert!(source[omitted].iter().any(|x|!x.is_zero()));
            let mutant=std::array::from_fn::<_,4,_>(|k|expected[k]-weights[omitted]*source[omitted][k]);
            assert_ne!(mutant,expected,"omitted component{omitted}");
        }
        for (a,b) in [(0usize,1usize),(0,2),(1,2)] {
            let mutant=std::array::from_fn::<_,4,_>(|k|expected[k]+(weights[b]-weights[a])*(source[a][k]-source[b][k]));
            assert_ne!(mutant,expected,"swapped tags{a}/{b}");
        }
        assert!(m.iter().any(|c|!c.is_zero()));
        for omitted in 26..31 {
            let wrong_pad=(26..31).filter(|b|*b!=omitted).map(|b|Fr::one()-r[b]).product::<Fr>();
            let mutant=std::array::from_fn::<_,4,_>(|k|expected[k]+weights[1]*(wrong_pad-pad)*m[k]);
            assert_ne!(mutant,expected,"Map padding bit{omitted}");
        }
        let mut tag3=r.clone();tag3[31]=Fr::one();tag3[32]=Fr::one();
        assert_eq!(composition.coefficients(&tag3,&u,&v).unwrap(),[Fr::zero();4]);
    }
    // The five Boolean Map padding directions and highest payload row are
    // zero by exact equality of the emitted 26-bit source row, not X values.
    let sample=lc::embed(Component::LegacyMap,small_term(3007*(1<<14)+9422,1,2,
        [Fr::one();4])).unwrap();
    for row in (26..31).map(|bit|lc::PAYLOAD+(1usize<<bit)).chain([2*lc::PAYLOAD-1]) {
        assert_eq!(eq(&boolean(33,row),sample.row),Fr::zero());
    }
}

fn selected_residuals(
    composition:&LegacyComposition<'_,'_>,adapter:&LegacyNativeAdapter<'_>,owner:usize,
    row:&NativePackedRow,targets:&[usize],mut foreign:impl FnMut(usize)->Result<bool,String>,
)->Result<Vec<Fr>,String> {
    adapter.check(adapter.parent(),adapter.input())?;row.admit_legacy_for_test(adapter,owner)?;
    let mut sums=vec![Fr::zero();targets.len()];let mut cache=BTreeMap::<usize,Fr>::new();
    let mut value=|index:usize|->Result<Fr,String> {
        if let Some(value)=cache.get(&index){return Ok(*value);}
        let bit=if index>>20==owner {let local=index&((1<<20)-1);
            row.packed_bytes()[local/8]&(1<<(local%8))!=0}else{foreign(index)?};
        let value=Fr::from(bit as u64);cache.insert(index,value);Ok(value)
    };
    composition.visit_owner_terms(owner,|term| {
        if let Some(position)=targets.iter().position(|r|*r==term.row) {
            let g=term.gate;let mut z=g.c0;
            if !g.c1.is_zero(){z+=g.c1*value(g.left)?;}
            if !g.c2.is_zero(){z+=g.c2*value(g.right)?;}
            if !g.c3.is_zero(){z+=g.c3*value(g.left)?*value(g.right)?;}
            sums[position]+=z;
        }Ok(())
    })?;
    Ok(sums)
}

#[test]
fn binding_and_selected_native_faults() {
    let (input,parent)=fixture();let adapter=LegacyNativeAdapter::compile(parent,input).unwrap();
    let composition=LegacyComposition::compile(&adapter).unwrap();
    let other=LegacyNativeAdapter::compile(parent,input).unwrap();
    assert_eq!(error(composition.check(&other)),"composition adapter identity mismatch");drop(other);
    for i in 0..lc::NUMBERS.len() {
        assert_ne!(composition.descriptor_mutant_for_test(Some(i),None,false).unwrap(),composition.binding());
    }
    for i in 0..lc::BYTES.len() {
        assert_ne!(composition.descriptor_mutant_for_test(None,Some(i),false).unwrap(),composition.binding());
    }
    assert_ne!(composition.descriptor_mutant_for_test(None,None,true).unwrap(),composition.binding());
    for dims in [(32,32,32),(34,32,32),(33,31,32),(33,33,32),(33,32,31),(33,32,33)] {
        assert_eq!(error(composition.coefficients(&vec![Fr::zero();dims.0],&vec![Fr::zero();dims.1],
            &vec![Fr::zero();dims.2])),"composition point dimensions rejected");
    }
    for owner in [4096usize,usize::MAX] {
        let mut calls=0;assert_eq!(error(composition.visit_owner_terms(owner,|_|{calls+=1;Ok(())})),
            "composition owner outside domain");assert_eq!(calls,0);
    }
    let mut bound=Transcript::new(b"composition-consumer-control");
    let mut unbound=bound.clone();assert_eq!(bound.challenges(),0);composition.bind(&mut bound);
    assert_eq!(bound.challenges(),0);
    assert_ne!(bound.challenge_scalar(b"after-bind"),unbound.challenge_scalar(b"after-bind"));
    let producer=NativeOwnerProducer::new_for_legacy_history(parent,input,&adapter).unwrap();
    let owner=3007usize;let row=producer.produce(owner).unwrap();
    let receipt=assembly::validate_native_legacy_row_for_history_test(&adapter,input,owner,&row,
        |index|adapter.export_bit(index)).unwrap();
    let mut names=receipt.groups.iter().map(|(name,_)|name.as_str()).collect::<Vec<_>>();names.sort_unstable();
    assert_eq!(names,vec!["DAA/3007","Fixed/3007","Header/3007","Leaf/3007","LegacyMap/3007","Work/3007"]);
    // The full native consumer also checks cores. Tagged selected rows below
    // inspect H/M/D only and do not replace those retained checks.
    let h=owner*(1<<19)+348441;
    let m=lc::PAYLOAD+owner*(1<<14)+8352;
    let d=2*lc::PAYLOAD+owner*(1<<19)+3*(1<<17)+73727;
    let targets=[h,m,d];
    assert_eq!(selected_residuals(&composition,&adapter,owner,&row,&targets,
        |i|adapter.export_bit(i)).unwrap(),vec![Fr::zero();3]);
    for (wire,target,reason) in [(991233usize,h,"Header/3007"),
        (lm::RATIO+155,m,"LegacyMap/3007"),(851967,d,"DAA/3007")] {
        let mut faulty=row.clone();assembly::flip_native_row_bit_for_test(&mut faulty,wire).unwrap();
        let z=selected_residuals(&composition,&adapter,owner,&faulty,&[target],
            |i|adapter.export_bit(i)).unwrap();assert!(!z[0].is_zero(),"tagged family {reason}");
        assert!(error(assembly::validate_native_legacy_row_for_history_test(&adapter,input,owner,&faulty,
            |i|adapter.export_bit(i))).contains(reason));
    }
    let foreign=2046*(1<<20)+lm::D_LOCAL+223;
    let map_import=lc::PAYLOAD+owner*(1<<14)+8350;
    let z=selected_residuals(&composition,&adapter,owner,&row,&[map_import],|i| {
        let bit=adapter.export_bit(i)?;Ok(if i==foreign {!bit}else{bit})
    }).unwrap();assert!(!z[0].is_zero());
    assert!(error(assembly::validate_native_legacy_row_for_history_test(&adapter,input,owner,&row,|i| {
        let bit=adapter.export_bit(i)?;Ok(if i==foreign {!bit}else{bit})
    })).contains("LegacyMap/3007"));
}

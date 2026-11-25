//! Retained N3073 RAW -> local ell2 projection -> GKR -> independently known LOCAL X.
//! No PCS authentication of historical coordinates is supplied by this test module.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::{BigInt,BigUint};
use std::{cell::{Cell,RefCell},ops::Range};
use crate::{certified_legacy_bound::{self as local,Inputs,Layout,Statement,Sub,M,R,LIVE,INITIAL},
    gkr::{self,GkrError,GkrProof,InputClaim}, native_owner_exports::NativeExports,
    packed_owner_assembly::NativePrefix,packed_owner_assembly_tests as fixtures,
    sparse,transcript::Transcript};

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Kind {Difficulty,Timestamp}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Port {kind:Kind,height:usize,owner:usize,base:usize,width:usize,local_start:usize}
const PORTS:[Port;5]=[
    Port{kind:Kind::Difficulty,height:2048,owner:2046,base:987674,width:224,local_start:1},
    Port{kind:Kind::Difficulty,height:3008,owner:3006,base:987674,width:224,local_start:225},
    Port{kind:Kind::Timestamp,height:1024,owner:1023,base:525330,width:64,local_start:449},
    Port{kind:Kind::Timestamp,height:2048,owner:2047,base:525330,width:64,local_start:513},
    Port{kind:Kind::Timestamp,height:3008,owner:3007,base:525330,width:64,local_start:577},
];
fn validate_ports(ports:&[Port])->Result<(),String>{
    if ports!=PORTS{return Err("ordered code-owned projection".into());}
    if std::mem::size_of::<usize>()!=8{return Err("projection requires x64".into());}
    for p in ports{
        let owner=match p.kind{Kind::Difficulty=>p.height.checked_sub(2),Kind::Timestamp=>p.height.checked_sub(1)};
        if owner!=Some(p.owner)||p.base+p.width>1<<20||p.local_start+p.width>641{return Err("projection geometry".into());}
        p.owner.checked_mul(1<<20).and_then(|x|x.checked_add(p.base+p.width)).ok_or("projection coordinate overflow")?;
    }Ok(())
}
fn before_read<T>(ports:&[Port],read:impl FnOnce()->Result<T,String>)->Result<T,String>{
    validate_ports(ports)?;read()
}
pub(crate) fn descriptor_faults(){
    let reads=Cell::new(0usize);
    for axis in 0..8{
        let mut ports=PORTS;
        match axis{0=>ports[0].owner+=1,1=>ports[2].owner-=1,2=>ports[0].height+=1,
            3=>ports[0].base+=1,4=>ports[0].width-=1,5=>ports[0].local_start+=1,6=>ports[0].kind=Kind::Timestamp,_=>ports.swap(0,1)}
        // Reader would return identical scalar D; rejection must precede it.
        assert_eq!(before_read(&ports,||{reads.set(reads.get()+1);Ok(BigUint::from(INITIAL))}).unwrap_err(),"ordered code-owned projection");
        assert_eq!(reads.get(),0);
    }
    assert!(validate_ports(&PORTS).is_ok());
}
fn extract(input:&NativePrefix,ports:&[Port])->Result<Inputs,String>{
    before_read(ports,||{
        if input.header_count()!=3073{return Err("ell2 native prefix count".into());}
        let plan=crate::daa_header_window::for_child_height(3073)?;
        if plan.sample_heights()!=[1024,2048,3072]||plan.action()!=crate::daa_header_window::Action::Retarget(crate::daa_integer::Epoch::Legacy){
            return Err("ell2 native roster".into());
        }
        let mut d=[BigUint::from(0u8),BigUint::from(0u8)];let mut t=[0u64;3];
        for (i,p) in ports.iter().enumerate(){
            let h=input.header(p.height)?;
            match p.kind{
                Kind::Difficulty=>{
                    if h.n_bits!=input.compact_n_bits(p.height)?{return Err("native D view mismatch".into());}
                    d[i]=crate::work_tree_work::native_decode(h.n_bits)?;
                },
                Kind::Timestamp=>{
                    if h.timestamp!=input.timestamp(p.height)?||h.timestamp<0{return Err("native timestamp fixture domain".into());}
                    t[i-2]=h.timestamp as u64;
                }
            }
        }
        let result=Inputs{d,t};result.admit()?;Ok(result)
    })
}
// Independent exact signed-integer scalar authority. No call to local::scalar/producer.
fn reference(input:&Inputs)->Result<BigUint,String>{
    input.admit()?;
    let d1=BigInt::from(input.t[1])-BigInt::from(input.t[0]);
    let future=BigInt::from(input.t[2])+BigInt::from(64u8)-BigInt::from(input.t[1]);
    if d1<=BigInt::from(0u8)||future<=BigInt::from(0u8){return Err("reference positive denominator".into());}
    let y1=BigInt::from(input.d[0].clone())*BigInt::from(122880000u64)/d1;
    let ymax=BigInt::from(input.d[1].clone())*BigInt::from(122880000u64)/future;
    let raw=ymax*2u8-y1+3u8;let bound=std::cmp::max(raw,BigInt::from(0x011765000000u64));
    bound.to_biguint().ok_or_else(||"reference negative bound".into())
}
fn write_bits(x:&mut[Fr],range:Range<usize>,n:&BigUint){
    assert!(n.bits()<=range.len()as u64);for (i,w) in range.enumerate(){x[w]=if n.bit(i as u64){Fr::one()}else{Fr::zero()};}
}
fn mask(w:usize)->BigUint{(BigUint::from(1u8)<<w)-BigUint::from(1u8)}
fn digit(n:&BigUint,col:usize)->BigUint{(n>>(col*16))&BigUint::from(65535u64)}
fn write_carries(x:&mut[Fr],range:Range<usize>,width:usize,values:&[BigUint]){
    assert_eq!(range.len(),width*values.len());for (i,v) in values.iter().enumerate(){
        write_bits(x,range.start+i*width..range.start+(i+1)*width,v);
    }
}
fn ref_sub(x:&mut[Fr],s:&Sub,a:&BigUint,b:&BigUint){
    let w=s.diff.len();let modulus=BigUint::from(1u8)<<w;
    let diff=(&modulus+a-b-BigUint::from(1u8))%&modulus;
    x[s.initial]=Fr::one();write_bits(x,s.diff.clone(),&diff);
    // Prefix inequalities determine every outgoing borrow independently of producer recurrence.
    for i in 0..w{let m=mask(i+1);let borrow=(a.clone()&m.clone())<((b.clone()&m)+BigUint::from(1u8));
        x[s.borrow.start+i]=Fr::from(u64::from(borrow));}
}
struct FixedX {values:Vec<Fr>}
impl FixedX{
    fn independently_from_fixture(input:&Inputs)->Result<Self,String>{
        input.admit()?;let l=Layout::new();let mut x=vec![Fr::zero();M];assert_eq!(x.capacity(),M);
        // This reconstruction never takes a producer vector, circuit, advice or claimed helpers.
        for (i,p) in input.ports().into_iter().enumerate(){let f=Fr::from(u64::from(p));x[1+i]=f;x[641+i]=f;}
        let deltas=[BigUint::from(input.t[1])-BigUint::from(input.t[0]),
            BigUint::from(input.t[2])-BigUint::from(input.t[1]),
            BigUint::from(input.t[2])+BigUint::from(64u8)-BigUint::from(input.t[1])];
        for k in 0..3{
            write_bits(&mut x,l.delta[k].clone(),&deltas[k]);
            let left=if k<2{deltas[k].clone()}else{deltas[1].clone()};
            let right=if k<2{BigUint::from(input.t[k])}else{BigUint::from(64u8)};
            let mut carry=BigUint::from(0u8);let mut values=Vec::with_capacity(3);
            for col in 0..4{carry=(digit(&left,col)+digit(&right,col)+carry)>>16usize;if col<3{values.push(carry.clone());}else{assert!(carry.is_zero());}}
            write_carries(&mut x,l.tc[k].clone(),1,&values);
        }
        for k in 0..2{ref_sub(&mut x,&l.positive[k],&deltas[k],&BigUint::from(0u8));}
        let mut quotients:[BigUint;2]=std::array::from_fn(|_|BigUint::from(0u8));
        for k in 0..2{
            let numerator=&input.d[k]*BigUint::from(122880000u64);
            write_bits(&mut x,l.numerator[k].clone(),&numerator);
            let mut carry=BigUint::from(0u8);let mut values=Vec::with_capacity(15);
            for col in 0..16{carry=(digit(&input.d[k],col)*BigUint::from(122880000u64)+carry)>>16usize;
                if col<15{values.push(carry.clone());}else{assert!(carry.is_zero());}}
            write_carries(&mut x,l.nc[k].clone(),27,&values);
            let den=&deltas[if k==0{0}else{2}];let q=&numerator/den;let r=&numerator%den;
            write_bits(&mut x,l.q[k].clone(),&q);write_bits(&mut x,l.rem[k].clone(),&r);
            let mut carry=BigUint::from(0u8);let mut values=Vec::with_capacity(18);
            for col in 0..19{
                let mut sum=carry+digit(&r,col);
                for qi in 0..16{if col>=qi&&col-qi<4{sum+=digit(&q,qi)*digit(den,col-qi);}}
                carry=sum>>16usize;if col<18{values.push(carry.clone());}else{assert!(carry.is_zero());}
            }
            write_carries(&mut x,l.pc[k].clone(),19,&values);
            ref_sub(&mut x,&l.rem_sub[k],den,&r);quotients[k]=q;
        }
        let a=(&quotients[1]<<1usize)+BigUint::from(3u8);let c=&quotients[0]+BigUint::from(0x011765000000u64);
        write_bits(&mut x,l.a.clone(),&a);write_bits(&mut x,l.c.clone(),&c);
        for k in 0..2{
            let left=if k==0{&quotients[1]<<1usize}else{quotients[0].clone()};
            let right=if k==0{BigUint::from(3u8)}else{BigUint::from(0x011765000000u64)};
            let mut carry=BigUint::from(0u8);let mut values=Vec::with_capacity(15);
            for col in 0..16{carry=(digit(&left,col)+digit(&right,col)+carry)>>16usize;
                if col<15{values.push(carry.clone());}else{assert!(carry.is_zero());}}
            write_carries(&mut x,l.ac[k].clone(),1,&values);
        }
        ref_sub(&mut x,&l.compare,&a,&c);
        let selected=a>c;x[l.selector]=Fr::from(u64::from(selected));
        let b=reference(input)?;write_bits(&mut x,l.b.clone(),&b);
        if selected{
            let mut carry=BigUint::from(0u8);let mut values=Vec::with_capacity(15);
            for col in 0..16{carry=(digit(&b,col)+digit(&quotients[0],col)+carry)>>16usize;
                if col<15{values.push(carry.clone());}else{assert!(carry.is_zero());}}
            write_carries(&mut x,l.selected.clone(),1,&values);
        }
        assert!(x[LIVE..].iter().all(Zero::is_zero));Ok(Self{values:x})
    }
    fn authenticate(&self,claim:&InputClaim)->Result<(),String>{
        if claim.point.len()!=13{return Err("local terminal dimension".into());}
        if claim.value!=gkr::mle(&self.values,&claim.point).map_err(|e|e.to_string())?{
            return Err("local terminal known-X".into());
        }Ok(())
    }
}
fn verify(stmt:&Statement,proof:&GkrProof,t:&mut Transcript)->Result<InputClaim,GkrError>{
    gkr::verify_with_wiring(&[13],R,proof,t,|t|stmt.bind(t),
        |layer,r,u,v|{if layer!=0{return Err(GkrError::ProofLayerCount);}local::coefficients(stmt,r,u,v)})
}
#[cfg(test)]
mod tests{
    use super::*;
    #[test]
    #[ignore="requires pinned N3073 RAW fixture and bounded runner"]
    fn native_j3072_projected_bound(){
        local::bounds();descriptor_faults();
        // Exact descriptor gate precedes prefix reader and NativeExports initialization.
        validate_ports(&PORTS).unwrap();
        let input=fixtures::legacy_prefix_for_test();
        // Replay the existing scalar admission before any history-plan/template construction.
        let cap=crate::legacy_native_adapter::native_cap_summary(input).unwrap();
        assert_eq!(cap.maximum,BigUint::from(185435213004800u64));
        assert_eq!(cap.height,3073);
        assert_eq!(cap.total,BigUint::from(24293759260819456u64));
        assert_eq!((&cap.maximum-BigUint::from(1u8)).bits(),48);
        let values=extract(input,&PORTS).unwrap();
        let plan=fixtures::legacy_assembly_plan_for_test();let exports=NativeExports::new(plan,input).unwrap();
        let mut callbacks=0usize;let projected=values.ports();let mut index=0usize;
        for p in PORTS{for bit in 0..p.width{
            let global=p.owner.checked_mul(1<<20).unwrap()+p.base+bit;
            assert_eq!(exports.bit(global).unwrap(),projected[index]);callbacks+=1;index+=1;
        }}
        assert_eq!((callbacks,index),(640,640));drop(exports);
        let expected=reference(&values).unwrap();
        assert_eq!(local::scalar(&values).unwrap(),expected);
        let fixed=FixedX::independently_from_fixture(&values).unwrap();
        let stmt=Statement::new(&values,&expected).unwrap();let circuit=local::materialize(&stmt);
        let producer=local::producer(&values,&expected).unwrap();
        // Independent reconstruction differential precedes proof; the terminal checker owns FixedX.
        assert_eq!(producer,fixed.values);assert_eq!((producer.capacity(),fixed.values.capacity()),(M,M));
        let mut pt=Transcript::new(b"certified-legacy-ell2-local-fixture-v1");
        let (proof,producer_claim)=sparse::prove_with_binding(&circuit,&producer,0,&mut pt,|t|stmt.bind(t)).unwrap();
        assert_eq!(gkr::encode_proof(&proof).unwrap().len(),3008);
        let bytes=gkr::encode_proof(&proof).unwrap();let decoded=sparse::decode_proof(&circuit,0,&bytes).unwrap();assert_eq!(decoded,proof);
        let mut vt=Transcript::new(b"certified-legacy-ell2-local-fixture-v1");
        let wiring_calls=Cell::new(0usize);let dimensions=RefCell::new(Vec::new());
        let claim=gkr::verify_with_wiring(&[13],R,&decoded,&mut vt,|t|stmt.bind(t),|layer,r,u,v|{
            assert_eq!(layer,0);wiring_calls.set(wiring_calls.get()+1);
            dimensions.borrow_mut().push((r.len(),u.len(),v.len()));local::coefficients(&stmt,r,u,v)
        }).unwrap();
        assert_eq!(wiring_calls.get(),1);assert_eq!(*dimensions.borrow(),vec![(14,13,13)]);
        fixed.authenticate(&claim).unwrap();assert_eq!(claim,producer_claim);
        assert_eq!((pt.challenges(),vt.challenges()),(41,41));
        assert_eq!(pt.challenge_scalar(b"continuation"),vt.challenge_scalar(b"continuation"));
        let mut wrong=claim.clone();wrong.point.pop();assert_eq!(fixed.authenticate(&wrong).unwrap_err(),"local terminal dimension");
        wrong=claim.clone();wrong.value+=Fr::one();assert_eq!(fixed.authenticate(&wrong).unwrap_err(),"local terminal known-X");
        // Hold proof/statement fixed; a changed-X control has provably nonzero equality weight.
        let wire=(0..M).find(|w|!local::eq_at(&claim.point,*w).is_zero()).unwrap();
        let weight=local::eq_at(&claim.point,wire);assert!(!weight.is_zero());
        let mut changed=FixedX{values:fixed.values.clone()};changed.values[wire]+=Fr::one();
        assert_eq!(gkr::mle(&changed.values,&claim.point).unwrap()-claim.value,weight);
        assert_eq!(changed.authenticate(&claim).unwrap_err(),"local terminal known-X");
        let mut fault=proof.clone();fault.layers[0].rounds[0][0]+=Fr::one();
        let mut t=Transcript::new(b"certified-legacy-ell2-local-fixture-v1");
        assert_eq!(verify(&stmt,&fault,&mut t),Err(GkrError::SumcheckIdentity));
        fault=proof.clone();fault.layers[0].line_coefficients[0]+=Fr::one();
        t=Transcript::new(b"certified-legacy-ell2-local-fixture-v1");
        assert_eq!(verify(&stmt,&fault,&mut t),Err(GkrError::LineEndpoints));
        let mut short=bytes.clone();short.pop();assert!(sparse::decode_proof(&circuit,0,&short).is_err());
        let mut trailing=bytes.clone();trailing.push(0);assert!(sparse::decode_proof(&circuit,0,&trailing).is_err());
        let mut bad=proof.clone();bad.layers[0].rounds.pop();t=Transcript::new(b"certified-legacy-ell2-local-fixture-v1");
        assert_eq!(verify(&stmt,&bad,&mut t),Err(GkrError::SumcheckRoundCount));
        bad=proof.clone();bad.layers[0].line_coefficients.pop();t=Transcript::new(b"certified-legacy-ell2-local-fixture-v1");
        assert_eq!(verify(&stmt,&bad,&mut t),Err(GkrError::LineDegree));
        // Keep public statement fixed, isolate local import/output arithmetic faults before consumer.
        let l=Layout::new();let mut alias=producer.clone();alias[l.operand.start]=Fr::one()-alias[l.operand.start];
        let rows=local::residuals(&circuit,&alias);assert!(local::group("aliases").any(|r|!rows[r].is_zero()));
        let mut output=producer.clone();output[l.b.start]=Fr::one()-output[l.b.start];
        let rows=local::residuals(&circuit,&output);assert!(local::group("b-anchors").any(|r|!rows[r].is_zero()));
    }
}

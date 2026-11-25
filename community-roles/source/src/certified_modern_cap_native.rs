//! Retained legacy H3008 D -> elementary q(D) -> independently known LOCAL X.
//! The fixture is not a modern-origin trace and supplies no historical PCS binding.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::{BigInt, BigUint};
use std::{cell::{Cell, RefCell}, ops::Range};
use crate::{certified_modern_cap::{self as local, Statement, M, R, LIVE},
    gkr::{self, GkrError, GkrProof, InputClaim}, native_owner_exports::NativeExports,
    packed_owner_assembly::NativePrefix, packed_owner_assembly_tests as fixtures,
    sparse, transcript::Transcript};

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Kind{Difficulty,Timestamp}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Port{kind:Kind,height:usize,owner:usize,base:usize,width:usize,start:usize,lsb:bool}
const PORT:Port=Port{kind:Kind::Difficulty,height:3008,owner:3006,base:987674,width:224,start:1,lsb:true};
fn validate_port(port:Port)->Result<(),String>{
    if port!=PORT{return Err("code-owned difficulty descriptor".into());}
    if std::mem::size_of::<usize>()!=8||port.height.checked_sub(2)!=Some(port.owner)
        ||port.base+port.width>1usize<<20usize||port.start+port.width!=225{
        return Err("difficulty projection geometry".into());
    }
    port.owner.checked_mul(1usize<<20usize).and_then(|x|x.checked_add(port.base+port.width))
        .ok_or("difficulty projection coordinate overflow")?;Ok(())
}
fn before_read<T>(port:Port,read:impl FnOnce()->Result<T,String>)->Result<T,String>{
    validate_port(port)?;read()
}
pub(crate) fn descriptor_faults(){
    let reads=Cell::new(0usize);
    for axis in 0..7{
        let mut port=PORT;match axis{0=>port.owner+=1,1=>port.height+=1,2=>port.base+=1,
            3=>port.width-=1,4=>port.start+=1,5=>port.lsb=false,_=>port.kind=Kind::Timestamp}
        assert_eq!(before_read(port,||{reads.set(reads.get()+1);Ok(BigUint::from(5u8))}).unwrap_err(),"code-owned difficulty descriptor");
        assert_eq!(reads.get(),0);
    }
    assert!(validate_port(PORT).is_ok());
}
fn extract(prefix:&NativePrefix,port:Port)->Result<BigUint,String>{
    before_read(port,||{
        if prefix.header_count()!=3073{return Err("elementary cap N3073 extent".into());}
        let header=prefix.header(port.height)?;
        if header.n_bits!=prefix.compact_n_bits(port.height)?{return Err("native difficulty view".into());}
        let d=crate::work_tree_work::native_decode(header.n_bits)?;
        if d.is_zero()||d.bits()>224{return Err("native positive D224".into());}Ok(d)
    })
}
struct Reference{p:BigUint,r:BigUint,e:usize,q:BigUint,prev:BigUint,hi:BigUint,low:BigUint,positive:BigUint}
// Positive BigInt division and repeated integer doubling, independent of local scalar/producer.
fn reference(d:&BigUint)->Result<Reference,String>{
    if d.is_zero()||d.bits()>224{return Err("reference positive D224".into());}
    let di=BigInt::from(d.clone());let three=&di*BigInt::from(3u8);
    let pi=&three/BigInt::from(2u8);let ri=&three-&pi*BigInt::from(2u8);
    let mut qi=BigInt::from(1u8);let mut e=0usize;
    while qi<pi{qi*=BigInt::from(2u8);e+=1;if e>64{return Err("reference profile coverage".into());}}
    let prev=if e==0{BigInt::from(0u8)}else{&qi/BigInt::from(2u8)};
    let unsigned=|n:BigInt|n.to_biguint().ok_or_else(||"reference negative rail".to_string());
    Ok(Reference{p:unsigned(pi.clone())?,r:unsigned(ri)?,e,q:unsigned(qi.clone())?,
        prev:unsigned(prev.clone())?,hi:unsigned(&qi-&pi)?,low:unsigned(&pi-&prev-BigInt::from(1u8))?,
        positive:unsigned(di-BigInt::from(1u8))?})
}
fn write_bits(x:&mut[Fr],range:Range<usize>,n:&BigUint){
    assert!(n.bits()<=range.len() as u64);
    for (i,w) in range.enumerate(){x[w]=if n.bit(i as u64){Fr::one()}else{Fr::zero()};}
}
struct FixedX{values:Vec<Fr>}
impl FixedX{
    fn independently_from_fixture(d:&BigUint)->Result<Self,String>{
        let v=reference(d)?;let mut values=vec![Fr::zero();2048];assert_eq!(values.capacity(),2048);
        // Literal reviewed ranges; only fixture D and independent integer arithmetic enter.
        write_bits(&mut values,1..225,d);write_bits(&mut values,225..449,d);
        write_bits(&mut values,449..674,&v.p);write_bits(&mut values,674..675,&v.r);
        values[675+v.e]=Fr::one();write_bits(&mut values,740..805,&v.q);
        write_bits(&mut values,805..869,&v.prev);write_bits(&mut values,869..934,&v.hi);
        write_bits(&mut values,934..1159,&v.low);write_bits(&mut values,1159..1383,&v.positive);
        assert!(values[LIVE..].iter().all(Zero::is_zero));Ok(Self{values})
    }
    fn authenticate(&self,claim:&InputClaim)->Result<(),String>{
        if claim.point.len()!=11{return Err("local cap terminal dimension".into());}
        if claim.value!=gkr::mle(&self.values,&claim.point).map_err(|e|e.to_string())?{
            return Err("local cap terminal known-X".into());
        }Ok(())
    }
}
fn verify(stmt:&Statement,proof:&GkrProof,t:&mut Transcript)->Result<InputClaim,GkrError>{
    gkr::verify_with_wiring(&[11],R,proof,t,|t|stmt.bind(t),
        |layer,r,u,v|{if layer!=0{return Err(GkrError::ProofLayerCount);}local::coefficients(stmt,r,u,v)})
}
#[cfg(test)]
mod tests{
    use super::*;
    const TRANSCRIPT:&[u8]=b"elementary-modern-cap-local-fixture-v1";
    #[test]
    #[ignore="requires pinned N3073 RAW fixture and bounded runner"]
    fn native_h3008_projected_cap(){
        local::bounds();descriptor_faults();validate_port(PORT).unwrap();
        let prefix=fixtures::legacy_prefix_for_test();
        // Existing fixture reader requires scalar admission before history plans/templates.
        let cap=crate::legacy_native_adapter::native_cap_summary(prefix).unwrap();
        assert_eq!(cap.maximum,BigUint::from(185435213004800u64));assert_eq!(cap.height,3073);
        assert_eq!(cap.total,BigUint::from(24293759260819456u64));
        assert_eq!((&cap.maximum-BigUint::from(1u8)).bits(),48);
        let d=extract(prefix,PORT).unwrap();
        let plan=fixtures::legacy_assembly_plan_for_test();let exports=NativeExports::new(plan,prefix).unwrap();
        let mut callbacks=0usize;
        for bit in 0..224{let global=PORT.owner.checked_mul(1usize<<20usize).unwrap()+PORT.base+bit;
            assert_eq!(exports.bit(global).unwrap(),d.bit(bit as u64));callbacks+=1;}
        assert_eq!(callbacks,224);drop(exports);
        let expected=reference(&d).unwrap();assert_eq!(local::scalar(&d).unwrap(),expected.q);
        let fixed=FixedX::independently_from_fixture(&d).unwrap();
        let stmt=Statement::new(&d,&expected.q).unwrap();let circuit=local::materialize(&stmt);
        let producer=local::producer(&d).unwrap();
        assert_eq!(producer,fixed.values);assert_eq!((producer.capacity(),fixed.values.capacity()),(M,M));
        let mut pt=Transcript::new(TRANSCRIPT);
        let (proof,producer_claim)=sparse::prove_with_binding(&circuit,&producer,0,&mut pt,|t|stmt.bind(t)).unwrap();
        let bytes=gkr::encode_proof(&proof).unwrap();assert_eq!(bytes.len(),2560);
        let decoded=sparse::decode_proof(&circuit,0,&bytes).unwrap();assert_eq!(decoded,proof);
        let mut vt=Transcript::new(TRANSCRIPT);let calls=Cell::new(0usize);let dimensions=RefCell::new(Vec::new());
        let claim=gkr::verify_with_wiring(&[11],R,&decoded,&mut vt,|t|stmt.bind(t),|layer,r,u,v|{
            assert_eq!(layer,0);calls.set(calls.get()+1);dimensions.borrow_mut().push((r.len(),u.len(),v.len()));
            local::coefficients(&stmt,r,u,v)
        }).unwrap();
        assert_eq!(calls.get(),1);assert_eq!(*dimensions.borrow(),vec![(12,11,11)]);
        fixed.authenticate(&claim).unwrap();assert_eq!(claim,producer_claim);
        assert_eq!((pt.challenges(),vt.challenges()),(35,35));
        assert_eq!(pt.challenge_scalar(b"continuation"),vt.challenge_scalar(b"continuation"));
        let mut wrong=claim.clone();wrong.point.pop();assert_eq!(fixed.authenticate(&wrong).unwrap_err(),"local cap terminal dimension");
        wrong=claim.clone();wrong.value+=Fr::one();assert_eq!(fixed.authenticate(&wrong).unwrap_err(),"local cap terminal known-X");
        let wire=(0..M).find(|w|!local::eq_at(&claim.point,*w).is_zero()).unwrap();
        let weight=local::eq_at(&claim.point,wire);assert!(!weight.is_zero());
        let mut changed=FixedX{values:fixed.values.clone()};let previous=changed.values[wire];
        assert!(previous.is_zero()||previous==Fr::one());changed.values[wire]=Fr::one()-previous;
        assert_eq!(gkr::mle(&changed.values,&claim.point).unwrap()-claim.value,(Fr::one()-previous-previous)*weight);
        assert_eq!(changed.authenticate(&claim).unwrap_err(),"local cap terminal known-X");
        let mut fault=proof.clone();fault.layers[0].rounds[0][0]+=Fr::one();
        let mut t=Transcript::new(TRANSCRIPT);assert_eq!(verify(&stmt,&fault,&mut t),Err(GkrError::SumcheckIdentity));
        fault=proof.clone();fault.layers[0].line_coefficients[0]+=Fr::one();t=Transcript::new(TRANSCRIPT);
        assert_eq!(verify(&stmt,&fault,&mut t),Err(GkrError::LineEndpoints));
        let mut short=bytes.clone();short.pop();assert!(sparse::decode_proof(&circuit,0,&short).is_err());
        let mut trailing=bytes.clone();trailing.push(0);assert!(sparse::decode_proof(&circuit,0,&trailing).is_err());
        fault=proof.clone();fault.layers[0].rounds.pop();t=Transcript::new(TRANSCRIPT);
        assert_eq!(verify(&stmt,&fault,&mut t),Err(GkrError::SumcheckRoundCount));
        fault=proof.clone();fault.layers[0].line_coefficients.pop();t=Transcript::new(TRANSCRIPT);
        assert_eq!(verify(&stmt,&fault,&mut t),Err(GkrError::LineDegree));
        // Keep public ports/q fixed; own predicate failures precede proof/terminal controls.
        let l=local::Layout::new();let mut alias=producer.clone();alias[l.operand.start]=Fr::one()-alias[l.operand.start];
        let rows=local::residuals(&circuit,&alias);assert!(local::group("aliases").any(|row|!rows[row].is_zero()));
        let mut port=producer.clone();port[l.source.start]=Fr::one()-port[l.source.start];
        let rows=local::residuals(&circuit,&port);assert!(local::group("input-anchors").any(|row|!rows[row].is_zero()));
        let mut output=producer.clone();output[l.q.start]=Fr::one()-output[l.q.start];
        let rows=local::residuals(&circuit,&output);assert!(local::group("q-anchors").any(|row|!rows[row].is_zero()));
        let changed_statement=Statement::new(&d,&(&expected.q+1u8)).unwrap();t=Transcript::new(TRANSCRIPT);
        assert!(verify(&changed_statement,&proof,&mut t).is_err());
    }
}


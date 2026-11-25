//! Boolean secp256k1 point residuals, reusable over prime fields larger than 2^132.
//! This component checks encoded points, not proof of work or knowledge of keys.
use ark_bn254::Fr;
use ark_ff::{PrimeField, Zero};
use num_bigint::{BigInt, BigUint};
use num_traits::One;
use std::ops::Range;
use crate::{gkr::Gate, sparse::{Circuit,Term}};

pub const POINT_WIDTH:usize=8192;
pub const USED_BITS:usize=8061;
pub const RESIDUAL_ROWS:usize=10502;
pub const TERM_COUNT:usize=288158;
type Bits=Box<[usize;256]>;

#[derive(Clone,Debug,PartialEq,Eq)]
pub struct PointRows {
    pub arithmetic:[Range<usize>;3], pub canonical:[Range<usize>;4],
    pub format:Range<usize>, pub parity:usize,
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct PointLayout {
    pub bytes:[[usize;8];33], pub x:Bits, pub y:Bits, pub u:Bits, pub v:Bits,
    pub quotients:[Bits;3], pub carries:[[Box<[usize;67]>;6];3],
    pub comparisons:[Bits;4], pub rows:PointRows,
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Layout {
    pub points:[PointLayout;2], pub boolean_rows:Range<usize>,
    pub padding_rows:Range<usize>, pub zero_row:usize,
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Stats {pub used_bits:usize,pub input_len:usize,pub residual_rows:usize,pub padded_rows:usize,pub terms:usize}
pub struct Compiled {pub circuit:Circuit,pub layout:Layout,pub stats:Stats}

fn alloc<const N:usize>(next:&mut usize)->[usize;N] {
    std::array::from_fn(|_|{let out=*next;*next+=1;out})
}
// Construct on the heap rather than Box::new([..]), which first creates a
// large stack temporary. Layout travels through multiple constructor returns.
fn alloc_box<const N:usize>(next:&mut usize)->Box<[usize;N]> {
    (0..N).map(|_|{let out=*next;*next+=1;out}).collect::<Vec<_>>()
        .into_boxed_slice().try_into().expect("fixed layout allocation")
}
fn layout()->Layout {
    let mut next=1;
    let sources:[[[usize;8];33];2]=std::array::from_fn(|_|std::array::from_fn(|_|alloc(&mut next)));
    let points=std::array::from_fn(|role| {
        let bytes=sources[role];let x=(0..256).map(|k|bytes[32-k/8][k%8]).collect::<Vec<_>>()
            .into_boxed_slice().try_into().expect("fixed x aliases");
        PointLayout {bytes,x,y:alloc_box(&mut next),u:alloc_box(&mut next),v:alloc_box(&mut next),
            quotients:std::array::from_fn(|_|alloc_box(&mut next)),
            carries:std::array::from_fn(|_|std::array::from_fn(|_|alloc_box(&mut next))),
            comparisons:std::array::from_fn(|_|alloc_box(&mut next)),
            rows:PointRows {arithmetic:std::array::from_fn(|_|0..0),canonical:std::array::from_fn(|_|0..0),format:0..0,parity:0}}
    });
    assert_eq!(next,USED_BITS);
    Layout {points,boolean_rows:0..0,padding_rows:0..0,zero_row:0}
}
pub fn modulus()->BigUint {(BigUint::one()<<256usize)-(BigUint::one()<<32usize)-BigUint::from(977u32)}

/// Emit a fixed topology. The caller cannot substitute a private layout.
pub fn emit<F:PrimeField>(mut sink:impl FnMut(usize,usize,usize,[F;4]))->Result<(Layout,Stats),String> {
    if F::MODULUS_BIT_SIZE<=132 {return Err("point residual field modulus must exceed 2^132".into());}
    let mut l=layout();let mut row=0usize;let mut count=0usize;
    let z=F::zero();let o=F::one();
    let mut powers=vec![o;133];for i in 1..powers.len(){powers[i]=powers[i-1]+powers[i-1];}
    let q=modulus();let ql=q.to_u64_digits();let b=powers[64];let k=powers[66];
    let mut term=|row,left,right,c|{count+=1;sink(row,left,right,c);};
    for p in &mut l.points {
        for identity in 0..3 {
            let first=row;
            let (a,bb,rem)=match identity {0=>(&p.x,&p.x,&p.u),1=>(&p.y,&p.y,&p.v),_=>(&p.x,&p.u,&p.v)};
            for coefficient in 0..7 {
                // Squares use unordered pairs, preserving the limb-coefficient row.
                for i in 0..256 {for j in if identity<2 {i}else{0}..256 {
                    if i/64+j/64==coefficient {
                        let mut weight=powers[i%64+j%64];if identity<2 && i!=j {weight+=weight;}
                        term(row,a[i],bb[j],[z,z,z,weight]);
                    }
                }}
                for (j,&qlimb) in ql.iter().enumerate().take(4) {for kk in 0..4 {
                    if j+kk==coefficient {for bit in 0..64 {
                        term(row,p.quotients[identity][64*kk+bit],0,[z,-F::from(qlimb)*powers[bit],z,z]);
                    }}
                }}
                if coefficient<4 {for bit in 0..64 {term(row,rem[64*coefficient+bit],0,[z,-powers[bit],z,z]);}}
                if coefficient>0 {for bit in 0..67 {term(row,p.carries[identity][coefficient-1][bit],0,[z,powers[bit],z,z]);}}
                if coefficient<6 {for bit in 0..67 {term(row,p.carries[identity][coefficient][bit],0,[z,-b*powers[bit],z,z]);}}
                let constant=k*(b-o)+if coefficient==0 {k}else{z}-if coefficient==6 {b*k}else{z};
                // Include 7*f in the existing constant term; no extra term or row.
                term(row,p.bytes[0][1],0,[constant,if identity==2 && coefficient==0 {F::from(7u64)}else{z},z,z]);
                row+=1;
            }
            p.rows.arithmetic[identity]=first..row;
        }
        for (which,bits) in [&p.x,&p.y,&p.u,&p.v].into_iter().enumerate() {
            let first=row;
            for bit in 0..256 {
                let previous=if bit==0 {0}else{p.comparisons[which][bit-1]};
                let c=if q.bit(bit as u64) {[o,-o,z,o]}else{[z,z,o,-o]};
                term(row,bits[bit],previous,c);
                term(row,p.comparisons[which][bit],0,[z,-o,z,z]);row+=1;
            }
            term(row,p.comparisons[which][255],0,[-o,o,z,z]);row+=1;
            p.rows.canonical[which]=first..row;
        }
        let first=row;
        for bit in 2..8 {term(row,p.bytes[0][bit],0,[z,o,z,z]);row+=1;}
        term(row,p.bytes[0][0],p.bytes[0][1],[z,o,z,-o]);row+=1;
        for byte in &p.bytes[1..] {for bit in 0..8 {
            term(row,byte[bit],p.bytes[0][1],[z,powers[bit],z,-powers[bit]]);
        }row+=1;}
        p.rows.format=first..row;p.rows.parity=row;
        term(row,p.y[0],p.bytes[0][0],[z,o,-o,z]);row+=1;
    }
    let first=row;for wire in 0..POINT_WIDTH {term(row,wire,wire,[z,-o,z,o]);row+=1;}l.boolean_rows=first..row;
    let first=row;for wire in USED_BITS..POINT_WIDTH {term(row,wire,0,[z,o,z,z]);row+=1;}l.padding_rows=first..row;
    l.zero_row=row;term(row,0,0,[z,o,z,z]);row+=1;
    assert_eq!(row,RESIDUAL_ROWS);assert_eq!(count,TERM_COUNT);
    Ok((l,Stats {used_bits:USED_BITS,input_len:POINT_WIDTH,residual_rows:row,padded_rows:row.next_power_of_two(),terms:count}))
}
pub fn build()->Result<Compiled,String> {
    let mut terms=Vec::with_capacity(TERM_COUNT);
    let (layout,stats)=emit::<Fr>(|row,left,right,c|terms.push(Term {row,gate:Gate {left,right,c0:c[0],c1:c[1],c2:c[2],c3:c[3]}}))?;
    Ok(Compiled {circuit:Circuit {input_len:POINT_WIDTH,row_count:stats.padded_rows,terms},layout,stats})
}
fn put_bits(out:&mut[bool],wires:&[usize],value:&BigUint)->Result<(),String> {
    if value.bits()>wires.len() as u64 {return Err("point witness integer exceeds bit width".into());}
    for (bit,&wire) in wires.iter().enumerate(){out[wire]=value.bit(bit as u64);}Ok(())
}
fn limbs(value:&BigUint)->[u64;4] {
    let words=value.to_u64_digits();std::array::from_fn(|i|words.get(i).copied().unwrap_or(0))
}
fn assign_identity(out:&mut[bool],p:&PointLayout,identity:usize,a:&BigUint,b:&BigUint,rem:&BigUint,extra:u8)->Result<(),String> {
    let modulus=modulus();let quotient=(a*b+BigUint::from(extra))/&modulus;
    put_bits(out,p.quotients[identity].as_ref(),&quotient)?;
    let (aa,bb,qq,mm,rr)=(limbs(a),limbs(b),limbs(&quotient),limbs(&modulus),limbs(rem));
    let base=BigInt::one()<<64usize;let offset=BigInt::one()<<66usize;let mut carry=BigInt::zero();
    for i in 0..7 {
        let mut value=carry.clone();
        for j in 0..4 {if i>=j && i-j<4 {
            value+=BigInt::from(aa[j])*BigInt::from(bb[i-j])-BigInt::from(mm[j])*BigInt::from(qq[i-j]);
        }}
        if i<4 {value-=BigInt::from(rr[i]);}if i==0 {value+=extra;}
        if (&value%&base)!=BigInt::zero(){return Err("point integer residual has no integral carry".into());}
        carry=value/&base;
        if i<6 {let encoded=(&carry+&offset).to_biguint().ok_or("point carry below range")?;
            put_bits(out,p.carries[identity][i].as_ref(),&encoded)?;}
    }
    if !carry.is_zero(){return Err("point integer carry does not terminate".into());}Ok(())
}
/// Honest assignment only. Acceptance must always check emitted residuals.
pub fn witness(pk:[u8;33],w:[u8;33])->Result<Vec<bool>,String> {
    let l=layout();let q=modulus();let mut out=vec![false;POINT_WIDTH];
    for (p,bytes) in l.points.iter().zip([pk,w]) {
        if !matches!(bytes[0],0|2|3){return Err("point prefix outside 0,2,3".into());}
        let x=BigUint::from_bytes_be(&bytes[1..]);if x>=q{return Err("point x is not canonical".into());}
        let finite=bytes[0]&2!=0;
        let mut y=if finite {
            let rhs=((&x*&x%&q)*&x+BigUint::from(7u8))%&q;
            let root=rhs.modpow(&((&q+BigUint::one())>>2usize),&q);
            if &root*&root%&q!=rhs{return Err("point x has no curve ordinate".into());}root
        } else {if !x.is_zero(){return Err("point infinity has a nonzero x".into());}BigUint::zero()};
        if y.bit(0)!=(bytes[0]&1!=0){y=&q-y;}
        if y>=q{return Err("point ordinate parity impossible".into());}
        let u=&x*&x%&q;let v=&y*&y%&q;
        for (wires,&byte) in p.bytes.iter().zip(&bytes){put_bits(&mut out,wires,&BigUint::from(byte))?;}
        for (wires,value) in [(&p.y,&y),(&p.u,&u),(&p.v,&v)] {put_bits(&mut out,wires.as_ref(),value)?;}
        for (identity,a,b,rem,extra) in [(0,&x,&x,&u,0),(1,&y,&y,&v,0),(2,&x,&u,&v,if finite{7}else{0})] {
            assign_identity(&mut out,p,identity,a,b,rem,extra)?;
        }
        for (index,value) in [&x,&y,&u,&v].into_iter().enumerate(){let mut less=false;
            for bit in 0..256 {let xb=value.bit(bit as u64);less=if q.bit(bit as u64){!xb||less}else{!xb&&less};
                out[p.comparisons[index][bit]]=less;}
        }
    }Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn generator(prefix:u8)->[u8;33] {
        let hex="79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
        let mut out=[0;33];out[0]=prefix;
        for i in 0..32 {out[i+1]=u8::from_str_radix(&hex[2*i..2*i+2],16).unwrap();}out
    }
    fn fields(bits:&[bool])->Vec<Fr>{bits.iter().map(|b|Fr::from(*b as u64)).collect()}
    fn rows(c:&Circuit,w:&[Fr])->Vec<Fr>{let mut out=vec![Fr::zero();c.row_count];
        for t in &c.terms {out[t.row]+=t.gate.evaluate(w);}out}
    fn failures(c:&Circuit,w:&[Fr])->Vec<usize>{rows(c,w).into_iter().enumerate().filter_map(|(i,x)|(!x.is_zero()).then_some(i)).collect()}
    fn integer(w:&[bool],indices:&[usize])->BigUint {
        indices.iter().enumerate().fold(BigUint::zero(),|mut a,(i,&wire)|{if w[wire]{a.set_bit(i as u64,true);}a})
    }
    fn field_integer(n:&BigInt)->Fr {let (sign,bytes)=n.to_bytes_le();let f=Fr::from_le_bytes_mod_order(&bytes);
        if sign==num_bigint::Sign::Minus{-f}else{f}}
    #[test]
    fn exact_shape_native_points_and_both_prime_field_evaluations() {
        let c=build().unwrap();assert_eq!((c.stats.used_bits,c.stats.residual_rows,c.stats.terms),(8061,10502,288158));
        assert_eq!((c.circuit.input_len,c.circuit.row_count),(8192,16384));
        for pair in [([0;33],[0;33]),(generator(2),generator(3)),(generator(3),generator(2)),
            (generator(2),[0;33]),([0;33],generator(3))] {
            for p in [pair.0,pair.1]{assert!(ergo_header_core::GroupElement::from_bytes(p).is_ok());}
            let bits=witness(pair.0,pair.1).unwrap();assert!(failures(&c.circuit,&fields(&bits)).is_empty());
            for (role,bytes) in [pair.0,pair.1].iter().enumerate(){for byte in 0..33 {for bit in 0..8 {
                assert_eq!(bits[c.layout.points[role].bytes[byte][bit]],(bytes[byte]>>bit)&1!=0);
            }}}
        }
        let bits=witness(generator(3),generator(2)).unwrap();let mut values=vec![ark_bn254::Fq::zero();16384];
        let (l,s)=emit::<ark_bn254::Fq>(|row,a,b,c|{
            let x=ark_bn254::Fq::from(bits[a] as u64);let y=ark_bn254::Fq::from(bits[b] as u64);
            values[row]+=c[0]+c[1]*x+c[2]*y+c[3]*x*y;
        }).unwrap();assert_eq!(l,c.layout);assert_eq!(s,c.stats);assert!(values.iter().all(Zero::is_zero));
    }
    #[derive(ark_ff::MontConfig)]
    #[modulus="17"]
    #[generator="3"]
    struct SmallConfig;
    #[test]
    fn insufficient_field_rejected_before_emission() {
        type Small=ark_ff::Fp64<ark_ff::MontBackend<SmallConfig,1>>;
        assert!(emit::<Small>(|_,_,_,_|panic!("must reject before emitting")).unwrap_err().contains("2^132"));
    }
    #[test]
    fn limb_residuals_match_signed_integer_oracle_on_arbitrary_bits() {
        let c=build().unwrap();let mut seed=0x7864913u64;
        for _ in 0..8 {
            let bits:Vec<_>=(0..POINT_WIDTH).map(|_|{seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);seed>>63!=0}).collect();
            let mut bits=bits;bits[0]=false;let got=rows(&c.circuit,&fields(&bits));
            for p in &c.layout.points {
                let numbers=[integer(&bits,p.x.as_ref()),integer(&bits,p.y.as_ref()),integer(&bits,p.u.as_ref()),integer(&bits,p.v.as_ref())];
                for identity in 0..3 {
                    let (a,b,rem)=match identity {0=>(&numbers[0],&numbers[0],&numbers[2]),1=>(&numbers[1],&numbers[1],&numbers[3]),_=>(&numbers[0],&numbers[2],&numbers[3])};
                    let (aa,bb,qq,rr,mm)=(limbs(a),limbs(b),limbs(&integer(&bits,p.quotients[identity].as_ref())),limbs(rem),limbs(&modulus()));
                    let base=BigInt::one()<<64usize;let k=BigInt::one()<<66usize;
                    for i in 0..7 {
                        let before=if i==0{k.clone()}else{BigInt::from(integer(&bits,p.carries[identity][i-1].as_ref()))};
                        let after=if i==6{k.clone()}else{BigInt::from(integer(&bits,p.carries[identity][i].as_ref()))};
                        let mut value=before-&base*after+&k*(&base-BigInt::one());
                        for j in 0..4{if i>=j&&i-j<4{value+=BigInt::from(aa[j])*BigInt::from(bb[i-j])-BigInt::from(mm[j])*BigInt::from(qq[i-j]);}}
                        if i<4{value-=BigInt::from(rr[i]);}if identity==2&&i==0&&bits[p.bytes[0][1]]{value+=7;}
                        assert!(value.magnitude()<&(BigUint::one()<<132usize));
                        assert_eq!(got[p.rows.arithmetic[identity].start+i],field_integer(&value));
                    }
                }
            }
        }
    }
    #[test]
    fn each_carry_and_arithmetic_family_rejects_at_named_rows() {
        let c=build().unwrap();let honest=witness(generator(2),generator(3)).unwrap();
        for p in &c.layout.points {for identity in 0..3 {for carry in 0..6 {
            let mut w=honest.clone();let wire=p.carries[identity][carry][0];w[wire]=!w[wire];
            assert_eq!(failures(&c.circuit,&fields(&w)),vec![p.rows.arithmetic[identity].start+carry,p.rows.arithmetic[identity].start+carry+1]);
        }
        let mut w=honest.clone();let wire=p.carries[identity][0][66];w[wire]=!w[wire];
        assert_eq!(failures(&c.circuit,&fields(&w)),vec![p.rows.arithmetic[identity].start,p.rows.arithmetic[identity].start+1]);
        }}
    }
    #[test]
    fn canonical_ranges_parity_format_boolean_and_padding_are_constrained() {
        let c=build().unwrap();let honest=witness(generator(2),generator(3)).unwrap();
        for p in &c.layout.points {
            for (which,wires) in [&p.x,&p.y,&p.u,&p.v].into_iter().enumerate(){
                let mut bad=honest.clone();put_bits(&mut bad,wires.as_ref(),&modulus()).unwrap();
                // Recompute all range states honestly, leaving the terminal x<q false.
                for &wire in p.comparisons[which].iter(){bad[wire]=false;}
                let got=failures(&c.circuit,&fields(&bad));assert!(got.contains(&(p.rows.canonical[which].end-1)));
                assert!(got.iter().filter(|r|p.rows.canonical[which].contains(r)).eq([&(p.rows.canonical[which].end-1)]));
            }
            let mut w=honest.clone();w[p.y[0]]=!w[p.y[0]];assert!(failures(&c.circuit,&fields(&w)).contains(&p.rows.parity));
            let mut w=honest.clone();w[p.bytes[0][7]]=true;
            assert_eq!(failures(&c.circuit,&fields(&w)),vec![p.rows.format.start+5]);
            let mut w=honest.clone();w[p.comparisons[0][123]]=!w[p.comparisons[0][123]];
            assert!(failures(&c.circuit,&fields(&w)).contains(&(p.rows.canonical[0].start+123)));
        }
        let mut w=fields(&honest);w[POINT_WIDTH-1]=Fr::from(2u64);let failures=failures(&c.circuit,&w);
        assert_eq!(failures,vec![c.layout.boolean_rows.start+POINT_WIDTH-1,c.layout.padding_rows.end-1]);
        let mut infinity=witness([0;33],[0;33]).unwrap();let p=&c.layout.points[0];infinity[p.x[255]]=true;
        assert!(rows(&c.circuit,&fields(&infinity))[p.rows.format.start+7].is_zero()==false);
        let mut bad=[0;33];bad[0]=2;assert!(witness(bad,[0;33]).is_err());assert!(ergo_header_core::GroupElement::from_bytes(bad).is_err());
    }

    #[test]
    fn role3_single_owner_calibration_guards() { calibration::guards(); }

    #[test]
    #[ignore = "bounded component calibration; requires the reviewed capture controller"]
    fn role3_single_owner_boolean_u_calibration_bounded() { calibration::capture(); }

    // This component fixture leaves the production relation and producer APIs intact.
    mod calibration {
        use super::*;
        use crate::{gkr::{self,GkrError,GkrProof,InputClaim},sparse,
            sparse_stream_roster::{self as stream,GroupedVAdmission,GroupedVStats,BooleanUPreweightStats},
            transcript::Transcript};
        use ark_serialize::CanonicalSerialize;
        use serde::{Serialize,Serializer};
        use std::{cell::Cell,io::{self,Write},mem::size_of,path::{Path,PathBuf},time::Instant};

        const DOMAIN:&[u8]=b"role3-single-owner-component-calibration-v1";
        const CONTINUATION:&[u8]=b"role3-component-continuation";
        const PRODUCER:usize=512*1024*1024;
        const JOB:usize=2*1024*1024*1024;
        const REPORT_CAP:usize=32768;
        const MARK_CAP:usize=256;
        const PACKET_CAP:usize=4096; // encode_proof's doubling Vec for 3008 scalar bytes.

        #[derive(Clone,Copy,Debug,Serialize,PartialEq,Eq)]
        #[serde(rename_all="lowercase")]
        enum Case { Finite,Mixed }
        #[derive(Clone,Copy,Debug,Serialize,PartialEq,Eq)]
        #[serde(rename_all="lowercase")]
        enum Arm { Direct,Boolean }
        #[derive(Clone,Copy)]
        struct FieldHex(Fr);
        impl Serialize for FieldHex {
            fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{
                let mut raw=[0u8;32];self.0.serialize_compressed(&mut raw[..]).map_err(serde::ser::Error::custom)?;
                let mut hex=[0u8;64];const DIGITS:&[u8]=b"0123456789ABCDEF";
                for (i,b) in raw.iter().enumerate(){hex[2*i]=DIGITS[(b>>4)as usize];hex[2*i+1]=DIGITS[(b&15)as usize];}
                s.serialize_str(std::str::from_utf8(&hex).map_err(serde::ser::Error::custom)?)
            }
        }
        #[derive(Clone,Copy)]
        struct Pin([u8;64]);
        impl Serialize for Pin {
            fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{s.serialize_str(std::str::from_utf8(&self.0).map_err(serde::ser::Error::custom)?)}
        }
        #[derive(Serialize)]
        struct Pins {source_manifest_sha256:Pin,binary_sha256:Pin,point_source_sha256:Pin}
        impl Pins {
            fn parse(value:&str)->Result<Self,String>{
                let b=value.as_bytes();
                if b.len()!=194||b[64]!=b':'||b[129]!=b':'||b.iter().enumerate().any(|(i,c)|i!=64&&i!=129&&!matches!(*c,b'0'..=b'9'|b'A'..=b'F')){
                    return Err("role3 source pins must be the exact uppercase SHA256 triplet".into());
                }
                Ok(Self{source_manifest_sha256:Pin(b[..64].try_into().unwrap()),binary_sha256:Pin(b[65..129].try_into().unwrap()),point_source_sha256:Pin(b[130..].try_into().unwrap())})
            }
        }
        #[derive(Serialize)]
        struct Scope {input_log:u64,row_log:u64,owners:u64,terms:u64,producer_limit_bytes:u64,job_limit_bytes:u64,
            deadline_seconds:u64,native:bool,common_opening:bool,all_seven_claims:bool,production:bool,helper_bounds_measured:bool}
        #[derive(Clone,Copy,Debug,PartialEq,Eq)]
        struct Counters {challenges:u64,raw_queries:u64,bytes_absorbed:u64}
        impl Serialize for Counters {
            fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{[self.challenges,self.raw_queries,self.bytes_absorbed].serialize(s)}
        }
        fn counters(t:&Transcript)->Counters{Counters{challenges:t.challenges(),raw_queries:t.raw_queries(),bytes_absorbed:t.bytes_absorbed()}}
        fn continuation(t:&Transcript)->Fr{t.clone().challenge_scalar(CONTINUATION)}
        #[derive(Clone,Serialize)]
        struct Preparation {template:u64,witness:u64,residual:u64,prefix:u64}
        #[derive(Clone,Serialize)]
        struct Census {loads:u64,fields:u64,visitor_calls:u64,term_callbacks:u64,binds:u64,producer_wiring_calls:u64,verifier_wiring_calls:u64}
        #[derive(Clone,Serialize)]
        struct Grouped {baseline_callbacks:u64,template_terms:u64,template_capacity_bytes:u64,bank_callbacks:u64,
            handoff_callbacks:u64,local_rounds:u64,handoff_owners:u64,group_owners:[u64;1],group_terms:[u64;1],
            state_peak_capacity_bytes:u64,baseline_elapsed_ns:u64}
        #[derive(Clone,Serialize)]
        struct Boolean {prefix_builds:u64,shared_term_iterations:u64,owner_term_selections:u64,boolean_checked_loads:u64,
            boolean_checked_fields:u64,zero_anchor_sweep_skipped:bool,preweight_entry_size_bytes:u64,
            preweight_peak_capacity_bytes:u64,u_state_peak_capacity_bytes:u64,u_preflight_capacity_bound_bytes:u64,
            u_prefix_preweight_elapsed_ns:u64,u_owner_selection_elapsed_ns:u64,u_x_fold_elapsed_ns:u64,u_phase_peak_capacity_bytes:[u64;6]}
        #[derive(Clone,Copy,Serialize)]
        struct Memory {template_capacity_bytes:u64,layout_box_bytes:u64,external_owned_bytes:u64,retained_previous_arm_bytes:u64,
            export_reserved_bytes:u64,producer_reserved_bytes:u64,preparation_reserved_bytes:u64,managed_preflight_bytes:u64,
            returned_owned_capacity_bytes:u64}
        #[derive(Clone,Serialize)]
        struct ProofShape {scalars:u64,bytes:u64,rounds:u64,line_coefficients:u64}
        #[derive(Clone,Serialize)]
        struct Claim {point_hex:[FieldHex;13],value_hex:FieldHex}
        #[derive(Clone,Serialize)]
        struct TranscriptRecord {producer:Counters,verifier:Counters,continuation_hex:FieldHex}
        #[derive(Clone,Serialize)]
        struct Checks {canonical_codec:bool,independent_verify:bool,source_mle:bool}
        #[derive(Clone,Serialize)]
        struct ArmReport {arm:Arm,proof_ns:u64,codec_ns:u64,verify_ns:u64,mle_ns:u64,census:Census,grouped:Grouped,
            boolean_u:Option<Boolean>,memory:Memory,proof:ProofShape,claim:Claim,transcript:TranscriptRecord,checks:Checks}
        #[derive(Serialize)]
        struct Comparison {proof_equal:bool,claim_equal:bool,counters_equal:bool,continuation_equal:bool}
        #[derive(Serialize)]
        struct CaseReport {case:Case,complete:bool,preparation_ns:Preparation,arms:[Option<ArmReport>;2],comparison:Comparison}
        impl CaseReport {fn empty(case:Case,template:u64)->Self{Self{case,complete:false,preparation_ns:Preparation{template,witness:0,residual:0,prefix:0},
            arms:[None,None],comparison:Comparison{proof_equal:false,claim_equal:false,counters_equal:false,continuation_equal:false}}}}
        #[derive(Serialize)]
        struct Report {schema:&'static str,state:&'static str,scope:Scope,source_pins:Pins,cases:[CaseReport;2],total_elapsed_ns:u64}
        #[derive(Serialize)]
        struct Mark {stage:&'static str,case:Option<Case>,arm:Option<Arm>,elapsed_ns:u64}
        struct Capped {bytes:Vec<u8>,cap:usize}
        impl Capped {
            fn new(cap:usize)->Result<Self,String>{let mut bytes=Vec::new();bytes.try_reserve_exact(cap).map_err(|e|e.to_string())?;
                if bytes.capacity()!=cap{return Err("role3 writer capacity differs from reservation".into());}Ok(Self{bytes,cap})}
        }
        impl Write for Capped {
            fn write(&mut self,b:&[u8])->io::Result<usize>{let n=self.bytes.len().checked_add(b.len()).ok_or_else(||io::Error::other("role3 writer overflow"))?;
                if n>self.cap{return Err(io::Error::other("role3 writer cap exceeded"));}self.bytes.extend_from_slice(b);Ok(b.len())}
            fn flush(&mut self)->io::Result<()>{Ok(())}
        }
        struct Observer {began:Instant,writer:Capped,marks:usize,current_case:Option<Case>,current_arm:Option<Arm>}
        impl Observer {
            fn mark(&mut self,stage:&'static str)->Result<(),String>{
                if self.marks>=22{return Err("role3 marker count exceeded".into());}
                self.writer.bytes.clear();serde_json::to_writer(&mut self.writer,&Mark{stage,case:self.current_case,arm:self.current_arm,elapsed_ns:if self.marks==0{0}else{ns(self.began)?}}).map_err(|e|e.to_string())?;
                let out=io::stdout();let mut out=out.lock();if self.marks==0{writeln!(out).map_err(|e|e.to_string())?;}
                out.write_all(b"R3_COMPONENT_PHASE ").and_then(|_|out.write_all(&self.writer.bytes)).and_then(|_|out.write_all(b"\n")).map_err(|e|e.to_string())?;
                self.marks+=1;Ok(())
            }
        }
        fn ns(start:Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"role3 timer overflow".into())}
        fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or_else(||"role3 inventory overflow".into())}
        fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or_else(||"role3 inventory overflow".into())}
        fn sum(values:&[usize])->Result<usize,String>{values.iter().try_fold(0usize,|a,b|add(a,*b))}
        fn layout_bytes()->Result<usize,String>{
            // Per point: x,y,u,v,3 quotients,4 comparison arrays; 18 carry arrays.
            mul(2,mul(11*256+18*67,size_of::<usize>())?)
        }
        fn preparation_reservation()->Result<usize,String>{
            // Two simultaneously owned layout constructions, residual/MLE tables,
            // Boolean/source conversions, and bounded 256-bit integer witness work.
            sum(&[mul(2,layout_bytes()?)?,mul(4*16384+4*POINT_WIDTH,size_of::<Fr>())?,1024*1024])
        }
        fn export_reservation()->Result<usize,String>{
            // Typed records and serialization stack overlap; Windows environment/path
            // buffers are bounded separately from the fixed writer payloads.
            sum(&[REPORT_CAP,MARK_CAP,mul(4,PACKET_CAP)?,mul(3,size_of::<Report>())?,
                mul(4,size_of::<ArmReport>())?,size_of::<Observer>(),2*size_of::<Capped>(),256*1024,65536])
        }
        fn memory(c:&Compiled,input:&Vec<Fr>,retained:usize)->Result<Memory,String>{
            let template=mul(c.circuit.terms.capacity(),size_of::<Term>())?;
            let boxes=layout_bytes()?;
            let external=sum(&[size_of::<Compiled>(),template,boxes,mul(input.capacity(),size_of::<Fr>())?,
                size_of::<sparse::Shape>(),size_of::<GroupedVAdmission>(),2*size_of::<usize>(),
                6*size_of::<Transcript>(),size_of::<Failure>(),size_of::<Outcome>(),32*size_of::<Cell<u64>>()])?;
            let export=export_reservation()?;let preparation=preparation_reservation()?;
            let managed=sum(&[external,retained,export,PRODUCER,preparation])?;
            if managed>JOB{return Err("role3 managed preflight exceeds Job reservation".into());}
            Ok(Memory{template_capacity_bytes:template as u64,layout_box_bytes:boxes as u64,external_owned_bytes:external as u64,
                retained_previous_arm_bytes:retained as u64,export_reserved_bytes:export as u64,producer_reserved_bytes:PRODUCER as u64,
                preparation_reserved_bytes:preparation as u64,managed_preflight_bytes:managed as u64,returned_owned_capacity_bytes:0})
        }
        fn proof_capacity(p:&GkrProof)->Result<usize,String>{
            // The GkrProof inline header is already inside Outcome.
            let mut n=mul(p.layers.capacity(),size_of::<gkr::LayerProof>())?;
            for l in &p.layers {n=add(n,mul(l.rounds.capacity(),size_of::<Vec<Fr>>())?)?;
                n=add(n,mul(l.line_coefficients.capacity(),size_of::<Fr>())?)?;
                for r in &l.rounds{n=add(n,mul(r.capacity(),size_of::<Fr>())?)?;}}
            Ok(n)
        }
        struct Outcome {proof:GkrProof,claim:InputClaim,packet:Vec<u8>,grouped:GroupedVStats,boolean:Option<BooleanUPreweightStats>,
            transcript:Transcript,report:ArmReport}
        impl Outcome {fn capacity(&self)->Result<usize,String>{sum(&[size_of::<Self>(),proof_capacity(&self.proof)?,
            mul(self.claim.point.capacity(),size_of::<Fr>())?,self.packet.capacity(),
            mul(add(self.grouped.group_owner_counts.capacity(),self.grouped.group_term_counts.capacity())?,size_of::<usize>())?,
            mul(add(self.grouped.group_weight_sums.capacity(),self.grouped.group_d_local_contributions.capacity())?,size_of::<Fr>())?])}}
        fn seed(case:Case,wrong_domain:bool)->Transcript{let mut t=Transcript::new(if wrong_domain{b"role3-wrong-domain-v1"}else{DOMAIN});
            t.append_bytes(b"role3-case",match case{Case::Finite=>b"finite",Case::Mixed=>b"mixed"});t}
        fn prefix(c:&Compiled,case:Case,wrong_domain:bool)->Transcript{let mut t=seed(case,wrong_domain);sparse::bind(&c.circuit,0,&mut t);t}
        fn unchanged(before:&Transcript,after:&Transcript){assert_eq!(counters(before),counters(after));assert_eq!(continuation(before),continuation(after));}
        #[derive(Clone,Copy,Debug,PartialEq,Eq)]
        enum Fault {None,Geometry,CountLow,CountHigh,Endpoint,Read{call:u64,kind:u8}}
        #[derive(Debug)]
        struct Failure {tag:String,loads:u64,binds:u64,terms:u64,visitors:u64,wiring:u64,counters:Counters,hit:bool,stage:&'static str}
        fn read_tag(kind:u8)->&'static str{match kind{0=>"role3 injected loader error",1=>"role3 loader short input",2=>"role3 loader non-Boolean input",3=>"role3 loader overcapacity input",_=>"role3 unknown fault"}}
        fn load(input:&Vec<Fr>,owner:usize,call:u64,fault:Fault,hit:&Cell<bool>)->Result<Vec<Fr>,String>{
            if owner!=0{return Err("role3 loader owner differs from zero".into());}
            let mut values=input.clone();
            if let Fault::Read{call:target,kind}=fault{if call==target{hit.set(true);match kind{
                0=>return Err(read_tag(0).into()),1=>{values.pop();},2=>values[0]=Fr::from(2u64),
                3=>values.reserve_exact(1),_=>return Err("role3 unknown fault".into())
            }}}
            if values.len()!=POINT_WIDTH{return Err(read_tag(1).into());}
            if values.capacity()!=POINT_WIDTH{return Err(read_tag(3).into());}
            if values.iter().any(|x|!x.is_zero()&&*x!=Fr::from(1u64)){return Err(read_tag(2).into());}
            Ok(values)
        }
        fn run_arm(c:&Compiled,input:&Vec<Fr>,prepared:&Transcript,caller:&mut Transcript,arm:Arm,fault:Fault,mut mem:Memory)->Result<Outcome,Failure>{
            let loads=Cell::new(0u64);let binds=Cell::new(0u64);let terms=Cell::new(0u64);let visitors=Cell::new(0u64);
            let wires=Cell::new(0u64);let hit=Cell::new(false);let mut working=caller.clone();
            let shape=sparse::validate(&c.circuit,0).expect("fixed validated component");
            let count=match fault{Fault::CountLow=>TERM_COUNT-1,Fault::CountHigh=>TERM_COUNT+1,_=>TERM_COUNT};
            let admission=GroupedVAdmission::try_new(0,&[0],&[count]).expect("closed owner census");
            let loader=|owner|{let call=loads.get().checked_add(1).ok_or("role3 load counter overflow")?;loads.set(call);load(input,owner,call,fault,&hit)};
            let binder=|t:&mut Transcript|{binds.set(binds.get()+1);*t=prepared.clone();};
            let visitor=|owner,sink:&mut dyn FnMut(Term)->Result<(),String>|{
                if owner!=0{return Err("role3 visitor owner differs from zero".into());}visitors.set(visitors.get()+1);
                for (i,term) in c.circuit.terms.iter().enumerate(){terms.set(terms.get()+1);let mut term=term.clone();
                    if fault==Fault::Endpoint&&i==0{term.gate.left=POINT_WIDTH;hit.set(true);}sink(term)?;}Ok(())};
            let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|{wires.set(wires.get()+1);sparse::wiring(&c.circuit,&shape,r,u,v).map_err(|e|e.to_string())};
            let start=Instant::now();let bits=if fault==Fault::Geometry{25}else{13};
            let produced=match arm{
                Arm::Direct=>stream::prove_with_direct_u_grouped_v_for_test(bits,0,14,0,&[14],Some(0),&admission,loader,&mut working,binder,visitor,wiring).map(|(p,q,g)|(p,q,g,None)),
                Arm::Boolean=>stream::prove_with_boolean_u_grouped_v_for_test(bits,0,14,0,&[14],Some(0),&admission,loader,&mut working,binder,visitor,wiring).map(|(p,q,g,b)|(p,q,g,Some(b)))
            };
            let fail=|tag:String,w:&Transcript|Failure{tag,loads:loads.get(),binds:binds.get(),terms:terms.get(),visitors:visitors.get(),wiring:wires.get(),counters:counters(w),hit:hit.get(),
                stage:if loads.get()<=1{"prebind admission"}else{match arm{Arm::Direct=>"zero-anchor sweep after baseline_done",Arm::Boolean=>"first owner selection after u_anchor_done"}}};
            let (proof,claim,grouped,boolean)=produced.map_err(|e|fail(e,&working))?;
            let proof_ns=ns(start).map_err(|e|fail(e,&working))?;
            let checked=(||->Result<(Vec<u8>,ArmReport),String>{
                if fault!=Fault::None{return Err("role3 fault unexpectedly produced a proof".into());}
                let expected_loads=if arm==Arm::Direct{19}else{18};
                if loads.get()!=expected_loads||binds.get()!=1||wires.get()!=1||visitors.get()!=(if arm==Arm::Direct{16}else{1})
                    ||terms.get()!=(if arm==Arm::Direct{16*TERM_COUNT as u64}else{TERM_COUNT as u64}){return Err("role3 producer census differs".into());}
                if proof.layers.len()!=1||proof.layers[0].rounds.len()!=26||proof.layers[0].rounds.iter().any(|p|p.len()!=3)
                    ||proof.layers[0].line_coefficients.len()!=14||claim.point.len()!=13{return Err("role3 proof shape differs".into());}
                let codec=Instant::now();let packet=gkr::encode_proof(&proof)?;
                let expected=mul(7*13+3,Fr::zero().compressed_size())?;
                if expected!=3008||packet.len()!=expected||packet.capacity()>PACKET_CAP{return Err("role3 scalar codec capacity differs".into());}
                let decoded=gkr::decode_dimensions(&[13],&packet)?;
                if decoded!=proof||gkr::encode_proof(&decoded)?!=packet{return Err("role3 noncanonical codec".into());}
                let codec_ns=ns(codec)?;let verify=Instant::now();
                let (verified,verifier,verifier_wires)=consume(c,prepared,&decoded)?;
                claim_matches(&verified,&claim)?;
                if counters(&working)!=counters(&verifier)||continuation(&working)!=continuation(&verifier)
                    ||working.challenges()!=41||verifier_wires!=1{return Err("role3 independent consumer differs".into());}
                let verify_ns=ns(verify)?;let mle=Instant::now();
                source_matches(input,&claim)?;
                let mle_ns=ns(mle)?;
                if grouped.baseline_term_callbacks!=TERM_COUNT||grouped.template_term_count!=TERM_COUNT||grouped.bank_term_callbacks!=TERM_COUNT
                    ||grouped.handoff_term_callbacks!=0||grouped.local_rounds!=13||grouped.owner_handoff_count!=1
                    ||grouped.group_owner_counts!=[1]||grouped.group_term_counts!=[TERM_COUNT]||grouped.grouped_state_peak_capacity_bytes>PRODUCER
                    ||grouped.baseline_elapsed_ns>proof_ns{return Err("role3 grouped census differs".into());}
                if let Some(b)=&boolean{let spans=b.u_prefix_preweight_elapsed_ns.checked_add(b.u_owner_selection_elapsed_ns).and_then(|n|n.checked_add(b.u_x_fold_elapsed_ns)).ok_or("role3 span overflow")?;
                    if b.prefix_builds!=14||b.shared_term_iterations!=4034212||b.owner_term_selections!=4034212||b.boolean_checked_loads!=18
                        ||b.boolean_checked_fields!=147456||!b.zero_anchor_sweep_skipped||b.u_preflight_capacity_bound_bytes>PRODUCER
                        ||b.u_state_peak_capacity_bytes>b.u_preflight_capacity_bound_bytes||b.u_phase_peak_capacity_bytes.iter().copied().max()!=Some(b.u_state_peak_capacity_bytes)
                        ||spans>proof_ns{return Err("role3 Boolean census differs".into());}}
                let report=ArmReport{arm,proof_ns,codec_ns,verify_ns,mle_ns,census:Census{loads:loads.get(),fields:loads.get()*POINT_WIDTH as u64,
                    visitor_calls:visitors.get(),term_callbacks:terms.get(),binds:binds.get(),producer_wiring_calls:wires.get(),verifier_wiring_calls:verifier_wires},
                    grouped:Grouped{baseline_callbacks:grouped.baseline_term_callbacks as u64,template_terms:grouped.template_term_count as u64,
                        template_capacity_bytes:grouped.template_capacity_bytes as u64,bank_callbacks:grouped.bank_term_callbacks as u64,handoff_callbacks:0,
                        local_rounds:13,handoff_owners:1,group_owners:[1],group_terms:[TERM_COUNT as u64],state_peak_capacity_bytes:grouped.grouped_state_peak_capacity_bytes as u64,baseline_elapsed_ns:grouped.baseline_elapsed_ns},
                    boolean_u:boolean.as_ref().map(|b|Boolean{prefix_builds:b.prefix_builds as u64,shared_term_iterations:b.shared_term_iterations as u64,
                        owner_term_selections:b.owner_term_selections as u64,boolean_checked_loads:b.boolean_checked_loads as u64,boolean_checked_fields:b.boolean_checked_fields as u64,
                        zero_anchor_sweep_skipped:b.zero_anchor_sweep_skipped,preweight_entry_size_bytes:b.preweight_entry_size_bytes as u64,
                        preweight_peak_capacity_bytes:b.preweight_peak_capacity_bytes as u64,u_state_peak_capacity_bytes:b.u_state_peak_capacity_bytes as u64,
                        u_preflight_capacity_bound_bytes:b.u_preflight_capacity_bound_bytes as u64,u_prefix_preweight_elapsed_ns:b.u_prefix_preweight_elapsed_ns,
                        u_owner_selection_elapsed_ns:b.u_owner_selection_elapsed_ns,u_x_fold_elapsed_ns:b.u_x_fold_elapsed_ns,u_phase_peak_capacity_bytes:b.u_phase_peak_capacity_bytes.map(|n|n as u64)}),
                    memory:mem,proof:ProofShape{scalars:94,bytes:expected as u64,rounds:26,line_coefficients:14},
                    claim:Claim{point_hex:std::array::from_fn(|i|FieldHex(claim.point[i])),value_hex:FieldHex(claim.value)},
                    transcript:TranscriptRecord{producer:counters(&working),verifier:counters(&verifier),continuation_hex:FieldHex(continuation(&working))},
                    checks:Checks{canonical_codec:true,independent_verify:true,source_mle:true}};
                Ok((packet,report))
            })().map_err(|e|fail(e,&working))?;
            let mut outcome=Outcome{proof,claim,packet:checked.0,grouped,boolean,transcript:working,report:checked.1};
            let actual=outcome.capacity().map_err(|e|fail(e,&outcome.transcript))?;
            if actual>PRODUCER{return Err(fail("role3 returned capacity exceeds reservation".into(),&outcome.transcript));}
            mem.returned_owned_capacity_bytes=actual as u64;outcome.report.memory=mem;
            *caller=outcome.transcript.clone();Ok(outcome)
        }
        fn verify_state(c:&Compiled,prepared:&Transcript,proof:&GkrProof,caller:&Transcript)
            ->(Result<InputClaim,GkrError>,Transcript,u64,u64){
            let shape=sparse::validate(&c.circuit,0).expect("fixed validated consumer");let mut working=caller.clone();
            let binds=Cell::new(0u64);let wires=Cell::new(0u64);
            let result=gkr::verify_with_wiring(&[13],16384,proof,&mut working,|t|{binds.set(binds.get()+1);*t=prepared.clone();},
                |_,r,u,v|{wires.set(wires.get()+1);sparse::wiring(&c.circuit,&shape,r,u,v)});
            (result,working,binds.get(),wires.get())
        }
        fn consume(c:&Compiled,prepared:&Transcript,proof:&GkrProof)->Result<(InputClaim,Transcript,u64),String>{
            let (result,t,binds,wires)=verify_state(c,prepared,proof,&Transcript::new(DOMAIN));
            let claim=result.map_err(|e|e.to_string())?;
            if binds!=1{return Err("role3 verifier bind count differs".into());}Ok((claim,t,wires))
        }
        fn claim_matches(verified:&InputClaim,expected:&InputClaim)->Result<(),String>{
            if verified!=expected{return Err("role3 verified claim differs".into());}Ok(())
        }
        fn source_matches(input:&[Fr],claim:&InputClaim)->Result<(),String>{
            if gkr::mle(input,&claim.point).map_err(|e|e.to_string())?!=claim.value{return Err("role3 source MLE differs".into());}Ok(())
        }
        fn consumer_failure(c:&Compiled,proof:&GkrProof,prepared:&Transcript,wrong:bool,caller:&mut Transcript)->Result<(GkrError,Counters,u64,u64),String>{
            let before=caller.clone();
            // The wrong-prefix prerequisite reaches the second message, rather
            // than treating any verifier error as evidence of domain binding.
            if wrong{let p=&proof.layers[0].rounds;let mut probe=prepared.clone();
                for _ in 0..14{probe.challenge_scalar(b"gkr-output-coordinate");}gkr::append_usize(&mut probe,b"gkr-layer-index",0);
                if gkr::eval_polynomial(&p[0],Fr::zero())+gkr::eval_polynomial(&p[0],Fr::from(1u64))!=Fr::zero(){return Err("role3 first identity is not zero".into());}
                gkr::append_polynomial(&mut probe,b"gkr-sumcheck-polynomial",&p[0]);let z=probe.challenge_scalar(b"gkr-sumcheck-challenge");
                if gkr::eval_polynomial(&p[0],z)==gkr::eval_polynomial(&p[1],Fr::zero())+gkr::eval_polynomial(&p[1],Fr::from(1u64)){
                    return Err("role3 wrong-prefix prerequisite not observable".into());}}
            let (result,working,binds,wires)=verify_state(c,prepared,proof,caller);
            let error=result.expect_err("isolated consumer fault must fail");
            unchanged(&before,caller);Ok((error,counters(&working),binds,wires))
        }
        fn comparison(a:&Outcome,b:&Outcome)->Result<Comparison,String>{
            let proof_equal=a.packet==b.packet&&a.proof==b.proof;let claim_equal=a.claim==b.claim;
            let counters_equal=counters(&a.transcript)==counters(&b.transcript);let continuation_equal=continuation(&a.transcript)==continuation(&b.transcript);
            if !(proof_equal&&claim_equal&&counters_equal&&continuation_equal){return Err("role3 arms differ".into());}
            Ok(Comparison{proof_equal,claim_equal,counters_equal,continuation_equal})
        }
        pub(super) fn guards(){
            assert_eq!((size_of::<Fr>(),size_of::<Term>()),(32,152));assert_eq!(layout_bytes().unwrap(),64352);
            assert!(Pins::parse(&format!("{}:{}:{}","A".repeat(64),"B".repeat(64),"C".repeat(64))).is_ok());
            assert!(Pins::parse(&"a".repeat(194)).is_err());assert!(add(usize::MAX,1).is_err());
            let c=build().unwrap();let input=fields(&witness(generator(2),generator(3)).unwrap());assert!(failures(&c.circuit,&input).is_empty());
            let prepared=prefix(&c,Case::Finite,false);let mem=memory(&c,&input,0).unwrap();assert!(memory(&c,&input,JOB).is_err());
            for arm in [Arm::Direct,Arm::Boolean]{
                for fault in [Fault::Geometry,Fault::CountLow,Fault::CountHigh,Fault::Endpoint]{
                    let mut t=seed(Case::Finite,false);t.append_bytes(b"outer-preserved",b"fixture");let before=t.clone();
                    let e=run_arm(&c,&input,&prepared,&mut t,arm,fault,mem).err().expect("isolated producer fault");unchanged(&before,&t);
                    let expected=match fault{Fault::Geometry=>match arm{Arm::Direct=>"grouped V dimensions exceed the supported bound before allocation",Arm::Boolean=>"Boolean U input dimensions exceed the supported bound"},
                        Fault::CountLow=>"grouped V owner exceeded its admitted topology count",Fault::CountHigh=>"grouped V owner census differs from its admitted topology",_=>"grouped V rejects sentinel or out-of-range endpoints"};
                    assert_eq!(e.tag,expected);assert_eq!(e.binds,0);assert_eq!(e.counters.challenges,0);assert_eq!(e.wiring,0);assert_eq!(e.stage,"prebind admission");
                    if fault==Fault::Geometry{assert_eq!((e.loads,e.visitors,e.terms),(0,0,0));}else{assert_eq!((e.loads,e.visitors),(1,1));}
                    if matches!(fault,Fault::CountLow|Fault::CountHigh){assert_eq!(e.terms,TERM_COUNT as u64);}
                    if fault==Fault::Endpoint{assert!(e.hit);assert_eq!(e.terms,1);}
                }
                for call in [1u64,2]{for kind in 0u8..4{
                    let mut t=seed(Case::Finite,false);let before=t.clone();let e=run_arm(&c,&input,&prepared,&mut t,arm,Fault::Read{call,kind},mem).err().expect("isolated reader fault");
                    unchanged(&before,&t);assert_eq!(e.tag,read_tag(kind));assert!(e.hit);assert_eq!(e.loads,call);assert_eq!(e.binds,call-1);
                    assert_eq!(e.counters.challenges,14*(call-1));assert_eq!(e.wiring,0);
                    let mut expected_working=if call==1{before.clone()}else{prepared.clone()};
                    if call==2{for _ in 0..14{expected_working.challenge_scalar(b"gkr-output-coordinate");}
                        gkr::append_usize(&mut expected_working,b"gkr-layer-index",0);}
                    assert_eq!(e.counters,counters(&expected_working));
                    assert_eq!(e.stage,if call==1{"prebind admission"}else{match arm{Arm::Direct=>"zero-anchor sweep after baseline_done",Arm::Boolean=>"first owner selection after u_anchor_done"}});
                }}
                let mut t=seed(Case::Finite,false);let outcome=run_arm(&c,&input,&prepared,&mut t,arm,Fault::None,mem).unwrap_or_else(|e|panic!("{}",e.tag));
                let before=t.clone();let mut wrong_claim=outcome.claim.clone();wrong_claim.value+=Fr::from(1u64);
                assert_eq!(claim_matches(&outcome.claim,&wrong_claim).unwrap_err(),"role3 verified claim differs");
                assert_eq!(source_matches(&input,&wrong_claim).unwrap_err(),"role3 source MLE differs");unchanged(&before,&t);
                let mut changed=outcome.proof.clone();changed.layers[0].rounds[0][1]+=Fr::from(1u64);
                for (p,prefix,wrong,expected) in [(&changed,prepared.clone(),false,14u64),(&outcome.proof,prefix(&c,Case::Finite,true),true,15),
                    (&outcome.proof,prefix(&c,Case::Mixed,false),true,15)]{
                    let mut caller=seed(Case::Finite,false);caller.append_bytes(b"outer-preserved",b"consumer");
                    let (error,observed,binds,wires)=consumer_failure(&c,p,&prefix,wrong,&mut caller).expect("consumer prerequisite must be observable");
                    assert_eq!(error,GkrError::SumcheckIdentity);assert_eq!(observed.challenges,expected);assert_eq!((binds,wires),(1,0));
                }
            }
        }
        fn directory()->Result<PathBuf,String>{let p=PathBuf::from(std::env::var_os("NIPOPOW_ROLE3_CALIBRATION_CAPTURE_DIR").ok_or("role3 capture directory is required")?);
            if !p.is_absolute()||p.exists(){return Err("role3 capture destination must be new and absolute".into());}
            let parent=p.parent().ok_or("role3 capture parent absent")?;let meta=std::fs::symlink_metadata(parent).map_err(|e|e.to_string())?;
            if !meta.is_dir()||meta.file_type().is_symlink(){return Err("role3 capture parent is not a plain directory".into());}
            #[cfg(windows)]{use std::os::windows::fs::MetadataExt;if meta.file_attributes()&0x400!=0{return Err("role3 capture parent is a reparse point".into());}}
            std::fs::create_dir(&p).map_err(|e|e.to_string())?;Ok(p)}
        fn export(path:&Path,writer:&mut Capped,report:&Report)->Result<(),String>{writer.bytes.clear();serde_json::to_writer(&mut *writer,report).map_err(|e|e.to_string())?;
            let mut f=std::fs::OpenOptions::new().write(true).create_new(true).open(path.join("report.json")).map_err(|e|e.to_string())?;
            f.write_all(&writer.bytes).and_then(|_|f.sync_all()).map_err(|e|e.to_string())}
        pub(super) fn capture(){
            // Reserve the complete typed/export/preparation model before even the
            // environment, template or writer allocations. Helper bounds are models.
            let initial=sum(&[size_of::<Compiled>(),mul(TERM_COUNT,size_of::<Term>()).unwrap(),layout_bytes().unwrap(),preparation_reservation().unwrap(),
                export_reservation().unwrap(),PRODUCER]).unwrap();assert!(initial<=JOB);
            let mut writer=Capped::new(REPORT_CAP).unwrap();let mut observer=Observer{began:Instant::now(),writer:Capped::new(MARK_CAP).unwrap(),marks:0,current_case:None,current_arm:None};
            let path=directory().unwrap();let pins=Pins::parse(&std::env::var("NIPOPOW_ROLE3_CALIBRATION_PINS").expect("role3 provenance pins required")).unwrap();
            let mut report=Report{schema:"role3-single-owner-calibration-v1",state:"HOLD",scope:Scope{input_log:13,row_log:14,owners:1,terms:TERM_COUNT as u64,
                producer_limit_bytes:PRODUCER as u64,job_limit_bytes:JOB as u64,deadline_seconds:120,native:false,common_opening:false,all_seven_claims:false,production:false,helper_bounds_measured:false},
                source_pins:pins,cases:[CaseReport::empty(Case::Finite,0),CaseReport::empty(Case::Mixed,0)],total_elapsed_ns:0};
            let result=(||->Result<(),String>{observer.mark("preparation_begin")?;let start=Instant::now();let c=build()?;let template_ns=ns(start)?;
                sparse::validate(&c.circuit,0).map_err(|e|e.to_string())?;let _=memory(&c,&Vec::new(),0)?;
                for case in &mut report.cases{case.preparation_ns.template=template_ns;}observer.mark("template_complete")?;
                for (index,case) in [Case::Finite,Case::Mixed].into_iter().enumerate(){observer.current_case=Some(case);observer.mark("case_begin")?;
                    let start=Instant::now();let pair=match case{Case::Finite=>(generator(2),generator(3)),Case::Mixed=>([0;33],generator(3))};
                    let input=fields(&witness(pair.0,pair.1)?);let witness_ns=ns(start)?;observer.mark("witness_complete")?;
                    let _=memory(&c,&input,0)?;let start=Instant::now();if !failures(&c.circuit,&input).is_empty(){return Err("role3 honest residual admission failed".into());}
                    let residual_ns=ns(start)?;observer.mark("residual_complete")?;let start=Instant::now();let prepared=prefix(&c,case,false);let prefix_ns=ns(start)?;
                    if prepared.challenges()!=0{return Err("role3 prepared prefix challenged".into());}observer.mark("prefix_complete")?;
                    report.cases[index].preparation_ns=Preparation{template:template_ns,witness:witness_ns,residual:residual_ns,prefix:prefix_ns};
                    let order=if case==Case::Finite{[Arm::Direct,Arm::Boolean]}else{[Arm::Boolean,Arm::Direct]};
                    let mut previous:Option<Outcome>=None;
                    for (slot,arm) in order.into_iter().enumerate(){observer.current_arm=Some(arm);let retained=previous.as_ref().map(Outcome::capacity).transpose()?.unwrap_or(0);
                        let mem=memory(&c,&input,retained)?;observer.mark("arm_begin")?;let mut caller=seed(case,false);
                        let outcome=run_arm(&c,&input,&prepared,&mut caller,arm,Fault::None,mem).map_err(|e|e.tag)?;
                        observer.mark("arm_complete")?;
                        if let Some(first)=previous.take(){report.cases[index].comparison=comparison(&first,&outcome)?;
                            report.cases[index].arms[0]=Some(first.report);report.cases[index].arms[slot]=Some(outcome.report);
                        }else{report.cases[index].arms[slot]=Some(outcome.report.clone());previous=Some(outcome);}
                    }
                    report.cases[index].complete=true;observer.current_arm=None;observer.mark("case_complete")?;
                }
                observer.current_case=None;report.total_elapsed_ns=ns(observer.began)?;observer.mark("export_ready")?;
                if observer.marks!=21{return Err("role3 marker roster differs".into());}report.state="COMPONENT_CALIBRATION_PASS";Ok(())
            })();
            if let Err(error)=result{report.state="HOLD";report.total_elapsed_ns=ns(observer.began).unwrap_or(u64::MAX);let _=observer.mark("hold");let _=export(&path,&mut writer,&report);panic!("role3 calibration HOLD: {error}");}
            export(&path,&mut writer,&report).expect("role3 bounded report export");
        }
    }
}

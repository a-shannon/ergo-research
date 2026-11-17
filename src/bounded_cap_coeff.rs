//! Bounded c105/c110 physical-coordinate Cap differential, using frozen c104.
//! Provisional row numbers only: no final H21 merger, native authentication,
//! every-origin Score V alias, proof, production allocation or activation claim.
use ark_bn254::Fr;
use ark_ff::{Field, One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use crate::{certified_modern_suffix as source,
    wiring::{evaluate_residue_shift, RightIndex, SourceDelta}};

const C: [u64;2] = [1000770,1002818];
const M: [u64;2] = [999424,1000097];
const A: [u64;2] = [357978,360026];
const E: [u64;2] = [407304,407824];
const HI: [u64;2] = [1827776,1827648];
const CLIPPED: [(u64,u64);2] = [(1827837,1826814),(1827774,1826686)];
const LO: u64 = 845759;
fn x(owner:u64,local:u64)->u64 {(owner<<20)+local}
fn row(owner:u64,local:u64)->u64 {(owner<<19)+local}
fn packed_row(c:usize,q:u64)->u64 {if q<2048 {A[c]+q} else {E[c]+q-2048}}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Tuple {row:u64,left:u64,right:u64,c:[Fr;4]}
#[derive(Clone,Copy,Debug)]
struct Local {q:u64,left:u64,right:u64,import:bool,c:[Fr;4]}

/// Frozen source template, translated to exact physical coordinates.
fn physical(c:usize,owner:u64,import_owner:u64,mut sink:impl FnMut(Tuple)) {
    source::emit_cap(source::I0,|t| {
        assert_eq!(t.row.family,2);
        assert_eq!(t.row.owner,source::I0);
        let wire=|w:source::Wire|match w {
            source::Wire::Cap{origin,local}=> {
                assert_eq!(origin,source::I0); x(owner,C[c]+local as u64)
            },
            source::Wire::Native{owner:old,local}=> {
                assert_eq!(old,source::I0-1090);
                assert!((999424..999648).contains(&local));
                x(import_owner,M[c]+local as u64-999424)
            },
        };
        sink(Tuple{row:row(owner,packed_row(c,t.row.local as u64)),
            left:wire(t.left),right:wire(t.right),c:t.c});
    });
}

/// Independent arithmetic tuple roster: never calls the source emitter.
/// The 65 omitted public-q anchor rows remain absent, rather than compacted.
fn literal(mut sink:impl FnMut(Local)) {
    let one=Fr::one();let zero=Fr::zero();
    let mut emit=|q,left,right,import,channel,value| {
        let mut c=[zero;4];c[channel]=value;
        sink(Local{q,left,right,import,c});
    };
    emit(0,0,0,false,1,one);
    for w in 1..1383 {
        emit(w,w,0,false,1,-one);emit(w,w,w,false,3,one);
    }
    for b in 0..224 {
        emit(1383+b,1+b,0,false,1,one);
        emit(1383+b,b,0,true,1,-one);
    }
    for b in 0..224 {
        emit(1607+b,225+b,0,false,1,one);
        emit(1607+b,1+b,0,false,1,-one);
    }
    emit(1831,0,0,false,0,-one);
    for (q,lo,hi,scale) in [
        (1831,225,449,1i64),(1831,1159,1383,-1),
        (1832,225,449,3),(1832,449,674,-2),
        (1834,740,805,1),(1834,675,740,-1),
        (1835,805,869,1),(1835,676,740,-1),
        (1836,740,805,1),(1836,449,674,-1),(1836,869,934,-1),
        (1837,449,674,1),(1837,805,869,-1),(1837,934,1159,-1),
    ] {
        for w in lo..hi {
            let power=Fr::from(2u64).pow([w-lo]);
            let scalar=if scale<0 {-Fr::from((-scale)as u64)}else{Fr::from(scale as u64)};
            emit(q,w,0,false,1,scalar*power);
        }
    }
    emit(1832,674,0,false,1,-one);
    emit(1833,0,0,false,0,-one);
    for w in 675..740 {emit(1833,w,0,false,1,one);}
    emit(1837,0,0,false,0,-one);
    for w in 1383..2048 {emit(1903+w-1383,w,0,false,1,one);}
}

fn eq(p:&[Fr],n:u64)->Fr {
    let mut acc=Fr::one();
    for (b,p) in p.iter().enumerate() {
        acc*=if n>>b&1==1 {*p}else{Fr::one()-p};
        if acc.is_zero(){break;}
    }
    acc
}
fn point(h:usize,seed:u64)->Vec<Fr> {(0..h).map(|b|Fr::from(seed+37*(b as u64+1))).collect()}
fn bits(h:usize,n:u64)->Vec<Fr> {(0..h).map(|b|Fr::from(n>>b&1)).collect()}

#[derive(Clone,Debug)]
struct Schedule {lo:u64,hi:u64,clipped:bool}
impl Schedule {
    fn bounded(_c:usize)->Self {Self{lo:LO,hi:LO+257,clipped:true}}
    fn full(c:usize)->Self {Self{lo:LO,hi:HI[c],clipped:true}}
    fn owners(&self,c:usize)->Vec<(u64,u64)> {
        let mut out:Vec<_>=(self.lo..self.hi).filter(|o|o%128==63).map(|o|(o,o-1089)).collect();
        if self.clipped {out.push(CLIPPED[c]);}out
    }
}

fn owner_weights(c:usize,s:&Schedule,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;2] {
    let k=|delta|evaluate_residue_shift(&r[19..],&u[20..],&v[20..],delta,
        s.lo,s.hi,7,63,RightIndex::SameRow).unwrap();
    let mut out=[k(SourceDelta::Add(0)),k(SourceDelta::Sub(1089))];
    if s.clipped {
        let (dest,src)=CLIPPED[c];
        out[0]+=eq(&r[19..],dest)*eq(&u[20..],dest)*eq(&v[20..],dest);
        out[1]+=eq(&r[19..],dest)*eq(&u[20..],src)*eq(&v[20..],dest);
    }
    out
}
fn factored(c:usize,s:&Schedule,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    assert_eq!((r.len(),u.len(),v.len()),(40,41,41));
    let weights=owner_weights(c,s,r,u,v);
    let rr:Vec<_>=(0..2568).map(|q|eq(&r[..19],packed_row(c,q))).collect();
    let uu:Vec<_>=(0..2048).map(|w|eq(&u[..20],C[c]+w)).collect();
    let vv:Vec<_>=(0..2048).map(|w|eq(&v[..20],C[c]+w)).collect();
    let mm:Vec<_>=(0..224).map(|w|eq(&u[..20],M[c]+w)).collect();
    let mut out=[Fr::zero();4];
    literal(|t| {
        let l=if t.import {mm[t.left as usize]}else{uu[t.left as usize]};
        let w=rr[t.q as usize]*l*vv[t.right as usize]*weights[usize::from(t.import)];
        for (sum,c) in out.iter_mut().zip(t.c){*sum+=w*c;}
    });out
}

/// Direct full physical-index evaluation with independent integer schedule.
/// Caches evaluate full 40/41-bit eq, never factored local/owner products.
fn direct(c:usize,s:&Schedule,r:&[Fr],u:&[Fr],v:&[Fr],fault:u8)->[Fr;4] {
    let mut rc=BTreeMap::new();let mut uc=BTreeMap::new();let mut vc=BTreeMap::new();
    let mut out=[Fr::zero();4];
    for (owner,src) in s.owners(c) {
        if fault==6 && owner==CLIPPED[c].0 {continue;}
        let source=if fault==7 && owner==CLIPPED[c].0 {owner-1089}else{src};
        physical(c,owner,source,|mut t| {
            let local=t.left&((1<<20)-1);
            let import=(M[c]..M[c]+224).contains(&local);
            match fault {
                1 if import=>t.left=x(source+1,local),
                2 if t.right==x(owner,C[c])=>t.right=x(owner,0),
                3 if import=>t.c[1]=-t.c[1],
                4=>t.row+=1,
                5=>t.row^=1u64<<39,
                8 if import && local==M[c]+223=>t.left=x(source,M[c]),
                9=>t.left^=1u64<<40,
                _=>(),
            }
            let w=*rc.entry(t.row).or_insert_with(||eq(r,t.row))
                **uc.entry(t.left).or_insert_with(||eq(u,t.left))
                **vc.entry(t.right).or_insert_with(||eq(v,t.right));
            for (sum,c) in out.iter_mut().zip(t.c){*sum+=w*c;}
        });
    }out
}

#[test]
fn cap_shape_literal_and_physical_coordinates() {
    let mut source_terms=Vec::new();source::emit_cap(source::I0,|t|source_terms.push(t));
    let mut independent=Vec::new();literal(|t|independent.push(t));
    assert_eq!((source_terms.len(),independent.len()),(6419,6419));
    let locals:BTreeSet<_>=source_terms.iter().map(|t|t.row.local).collect();
    assert_eq!(locals.len(),2503);assert!(locals.iter().all(|q|!(1838..1903).contains(q)));
    assert_eq!(locals.first(),Some(&0));assert_eq!(locals.last(),Some(&2567));
    // Literal order need not match source order; compare all exact tuple fields.
    for c in 0..2 {
        for (owner,src) in [(LO,LO-1089),CLIPPED[c]] {
            let mut actual=Vec::new();physical(c,owner,src,|t|actual.push(t));
            let mut expected:Vec<_>=independent.iter().map(|t|Tuple {
                row:row(owner,packed_row(c,t.q)),
                left:if t.import{x(src,M[c]+t.left)}else{x(owner,C[c]+t.left)},
                right:x(owner,C[c]+t.right),c:t.c,
            }).collect();
            let key=|t:&Tuple|(t.row,t.left,t.right);
            actual.sort_by_key(key);expected.sort_by_key(key);
            assert_eq!(actual,expected);
            assert!(actual.iter().all(|t|t.row<1<<40 && t.left<1<<41 && t.right<1<<41));
            assert_eq!(packed_row(c,2047),A[c]+2047);
            assert_eq!(packed_row(c,2048),E[c]);assert_eq!(packed_row(c,2567),E[c]+519);
        }
    }
}

#[test]
fn cap_full_ordinary_and_clipped_owner_selector() {
    let r=point(40,3);let u=point(41,31);let v=point(41,103);
    for c in 0..2 {
        let s=Schedule::full(c);let owners=s.owners(c);
        assert_eq!(owners.len(),if c==0 {7674}else{7673});
        assert_eq!(owners.iter().filter(|(o,_)|*o==LO).count(),1,"activation already ordinary");
        let mut expected=[Fr::zero();2];
        for (o,src) in owners {
            expected[0]+=eq(&r[19..],o)*eq(&u[20..],o)*eq(&v[20..],o);
            expected[1]+=eq(&r[19..],o)*eq(&u[20..],src)*eq(&v[20..],o);
        }
        assert_eq!(owner_weights(c,&s,&r,&u,&v),expected);
        let (o,src)=CLIPPED[c];
        assert_ne!(src,o-1089);
        assert_eq!(owner_weights(c,&s,&bits(40,row(o,0)),&bits(41,x(src,0)),&bits(41,x(o,0)))[1],Fr::one());
        assert_eq!(owner_weights(c,&s,&bits(40,row(o,0)),&bits(41,x(o-1089,0)),&bits(41,x(o,0)))[1],Fr::zero());
    }
}

#[test]
fn cap_physical_nonboolean_all_channels_and_single_fault_coefficients() {
    for c in 0..2 {
        let s=Schedule::bounded(c);
        assert_eq!(s.owners(c).len(),4);
        for seed in [7,113] {
            let r=point(40,seed);let u=point(41,seed+23);let v=point(41,seed+87);
            let expected=factored(c,&s,&r,&u,&v);
            assert_eq!(direct(c,&s,&r,&u,&v,0),expected);
            assert!(!expected[0].is_zero());assert!(!expected[1].is_zero());
            assert!(expected[2].is_zero());assert!(!expected[3].is_zero());
            if seed==7 {
                for fault in 1..=9 {
                    assert_ne!(direct(c,&s,&r,&u,&v,fault),expected,"context {c}, fault {fault}");
                }
                let mut double=s.clone();double.lo=LO;double.hi=LO+1;double.clipped=false;
                let activation=factored(c,&double,&r,&u,&v);
                let doubled:[Fr;4]=std::array::from_fn(|j|expected[j]+activation[j]);
                assert_ne!(doubled,expected,"double-count activation");
                assert_ne!(factored(1-c,&s,&r,&u,&v),expected,"context range swap");
            }
        }
    }
}

#[test]
fn cap_boolean_import_rows_gap_padding_highbit_and_inactive() {
    for c in 0..2 {
        // First ordinary, ordinary 2^20 owner crossing, last ordinary, clipped.
        for owner in [LO,1048639,HI[c]-1,CLIPPED[c].0] {
            let clipped=owner==CLIPPED[c].0;
            let src=if clipped{CLIPPED[c].1}else{owner-1089};
            let s=Schedule{lo:owner,hi:owner+1,clipped:false};
            let s=if clipped{Schedule{lo:owner,hi:owner,clipped:true}}else{s};
            for b in [0,223] {
                let r=bits(40,row(owner,A[c]+1383+b));
                let u=bits(41,x(src,M[c]+b));let v=bits(41,x(owner,C[c]));
                assert_eq!(factored(c,&s,&r,&u,&v),[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()]);
                assert_eq!(direct(c,&s,&r,&u,&v,0),factored(c,&s,&r,&u,&v));
                for fault in [1,2,3,4,5,9] {
                    assert_ne!(direct(c,&s,&r,&u,&v,fault),factored(c,&s,&r,&u,&v),"fault {fault}");
                }
                if clipped {for fault in [6,7] {assert_eq!(direct(c,&s,&r,&u,&v,fault),[Fr::zero();4]);}}
            }
        }
        let s=Schedule::bounded(c);
        for q in [0,1,1831,1838,1902,1903,2047,2048,2567] {
            let r=bits(40,row(LO,packed_row(c,q)));
            let local=match q {0|1831|1838|1902=>0,1=>1,1903=>1383,2047=>1527,2048=>1528,_=>2047};
            let u=bits(41,x(LO,C[c]+local));let v=bits(41,x(LO,C[c]));
            assert_eq!(direct(c,&s,&r,&u,&v,0),factored(c,&s,&r,&u,&v));
            if [1838,1902].contains(&q){assert_eq!(factored(c,&s,&r,&u,&v),[Fr::zero();4]);}
        }
        let inactive=LO+1;
        let r=bits(40,row(inactive,A[c]));let u=bits(41,x(inactive,C[c]));let v=u.clone();
        assert_eq!(direct(c,&s,&r,&u,&v,0),[Fr::zero();4]);
        assert_eq!(factored(c,&s,&r,&u,&v),[Fr::zero();4]);
        // An inactive Cap emits nothing. Retaining its canonical HEADER anchor
        // is an external merger obligation, not established by this emitter.
        // At active local row zero the two coefficient placeholders differ.
        let r=bits(40,row(LO,A[c]));let u=bits(41,x(LO,C[c]));
        let cap_v=bits(41,x(LO,C[c]));let header_v=bits(41,x(LO,0));
        let anchor=|v:&[Fr]|eq(&r,row(LO,A[c]))*eq(&u,x(LO,C[c]))*eq(v,x(LO,0));
        assert_eq!(anchor(&header_v),Fr::one());assert!(anchor(&cap_v).is_zero());
        assert_eq!(direct(c,&s,&r,&u,&cap_v,0)[1],Fr::one());
        assert!(direct(c,&s,&r,&u,&header_v,0)[1].is_zero());
        assert_ne!(x(LO,0),x(LO,C[c]));
    }
}

#[test]
fn cap_physical_residual_import_bits_rounding_and_padding() {
    use crate::certified_modern_cap as cap;
    use num_bigint::BigUint;
    let d=BigUint::from(5u8);let values=cap::producer(&d).unwrap();
    assert_eq!(cap::scalar(&d).unwrap(),BigUint::from(8u8));
    let max=((BigUint::from(1u8)<<65usize)+1u8)/3u8;
    assert!(cap::admit(&(max+1u8)).is_err());
    for c in 0..2 {for (o,src) in [(LO,LO-1089),CLIPPED[c]] {
        let mut terms=Vec::new();physical(c,o,src,|t|terms.push(t));
        let read=|wire:u64| {
            if (x(o,C[c])..x(o,C[c]+2048)).contains(&wire) {values[(wire-x(o,C[c]))as usize]}
            else if (x(src,M[c])..x(src,M[c]+224)).contains(&wire) {values[1+(wire-x(src,M[c]))as usize]}
            else {panic!("unexpected physical witness read")}
        };
        let residual=|q:u64,changed:Option<(u64,Fr)>| {
            let get=|w| {if let Some((target,value))=changed{if w==target{return value;}} read(w)};
            terms.iter().filter(|t|t.row==row(o,packed_row(c,q))).fold(Fr::zero(),|sum,t| {
                let left=if !t.c[1].is_zero()||!t.c[3].is_zero(){get(t.left)}else{Fr::zero()};
                let right=if !t.c[2].is_zero()||!t.c[3].is_zero(){get(t.right)}else{Fr::zero()};
                sum+t.c[0]+t.c[1]*left+t.c[2]*right+t.c[3]*left*right
            })
        };
        let qs:BTreeSet<_>=terms.iter().map(|t|t.row&((1<<19)-1)).collect();
        assert_eq!(qs.len(),2503);
        for q in 0..2568 {assert!(residual(q,None).is_zero(),"q={q}");}
        for b in 0..224 {
            let wire=x(src,M[c]+b);let bad=Fr::one()-read(wire);
            assert!(!residual(1383+b,Some((wire,bad))).is_zero(),"import bit {b}");
        }
        for (wire,q) in [(x(o,C[c]),0),(x(o,C[c]+740+3),1834),(x(o,C[c]+2047),2567)] {
            assert!(!residual(q,Some((wire,Fr::one()-read(wire)))).is_zero());
        }
        assert!(!residual(1,Some((x(o,C[c]+1),Fr::from(2u64)))).is_zero());
    }}
}

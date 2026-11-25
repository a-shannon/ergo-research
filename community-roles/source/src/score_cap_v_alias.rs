//! Bounded test-only Cap producer -> physical X -> Score sv/v differential.
//! No native D authentication, final H21 merger, PCS or modern adapter admission.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};
use crate::{gkr::Gate, sparse::Term, origin_score as score,
    certified_modern_cap as cap, certified_modern_suffix as suffix,
    wiring::{evaluate_shift, evaluate_residue_shift, RightIndex, SourceDelta}};

const FIRST:usize=845759;
const G:[usize;2]=[1827838,1827775];
const TAIL:[usize;2]=[1827776,1827648];
const SCORE:[usize;2]=[677501,685693];
const CAP:[usize;2]=[1000770,1002818];
const MAX:[usize;2]=[999424,1000097];
const SCORE_ROWS:[usize;2]=[425984,458752];
const ALIAS:[usize;2]=[430192,462960];
fn x(o:usize,l:usize)->usize {(o<<20)+l}
fn row(o:usize,q:usize)->usize {(o<<19)+q}
fn eq(p:&[Fr],n:usize)->Fr {
    p.iter().enumerate().fold(Fr::one(),|a,(b,z)|a*if n>>b&1==1 {*z}else{Fr::one()-z})
}
fn bits(h:usize,n:usize)->Vec<Fr> {(0..h).map(|b|Fr::from(((n>>b)&1)as u64)).collect()}
fn point(h:usize,seed:u64)->Vec<Fr> {(0..h).map(|b|Fr::from(seed+37*(b as u64+1))).collect()}

fn destination(c:usize,s:usize)->Option<usize> {
    if c>=2 || !(FIRST..G[c]).contains(&s) {return None;}
    Some(if s==FIRST {s}else if s>=TAIL[c] {G[c]-1}
        else {((s+64)/128)*128+63})
}
fn aliases(c:usize,s:usize)->Vec<Term> {
    let Some(d)=destination(c,s) else{return Vec::new()};
    (0..65).map(|k|Term{row:row(s,ALIAS[c]+k),gate:Gate{
        left:x(s,SCORE[c]+224+k),right:x(d,CAP[c]+740+k),
        c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}}).collect()
}

/// Physical coefficient owner factor; three O(H) interval kernels, no owner scan.
fn owner_weight(c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    assert!(c<2);assert_eq!((r.len(),u.len(),v.len()),(21,21,21));
    let q=TAIL[c]/128;
    let low=(0..6).fold(Fr::one(),|a,b|a*((Fr::one()-r[b])*(Fr::one()-u[b])+r[b]*u[b]));
    let same=evaluate_shift(&r[7..],&u[7..],&v[7..],0,6608,(q+1)as u64,0,RightIndex::SameRow).unwrap();
    // Shifted input is Cap (v); same-row input is Score (u).
    let next=evaluate_residue_shift(&r[7..],&v[7..],&u[7..],SourceDelta::Add(1),6607,q as u64,0,0,RightIndex::SameRow).unwrap();
    let ordinary=eq(&v[..7],63)*low*((Fr::one()-r[6])*(Fr::one()-u[6])*same+r[6]*u[6]*next);
    let singleton=eq(r,FIRST)*eq(u,FIRST)*eq(v,FIRST);
    let pair=evaluate_shift(r,u,&[Fr::zero();21],0,TAIL[c]as u64,G[c]as u64,0,RightIndex::GlobalZero).unwrap();
    singleton+ordinary+pair*eq(v,G[c]-1)
}
fn local_factor(c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    (0..65).map(|k|eq(r,ALIAS[c]+k)*eq(u,SCORE[c]+224+k)*eq(v,CAP[c]+740+k)).sum()
}
fn coefficients(c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    assert_eq!((r.len(),u.len(),v.len()),(40,41,41));
    let a=owner_weight(c,&r[19..],&u[20..],&v[20..])*local_factor(c,&r[..19],&u[..20],&v[..20]);
    [Fr::zero(),a,-a,Fr::zero()]
}
fn direct(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    let mut out=[Fr::zero();4];
    for t in terms {let g=&t.gate;let w=eq(r,t.row)*eq(u,g.left)*eq(v,g.right);
        for (a,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*a+=w*c;}}
    out
}

/// Independent integer oracle: original singleton then height-space epochs.
fn expected_guard(c:usize,s:usize)->Option<(usize,usize)> {
    let i=s+1;if c>1 || i<845760 || i>G[c] {return None;}
    let q=i-1088;
    let b=if q==844672 {844672}else{844800+128*((q-844673)/128)};
    Some(((b+1088).min(G[c])-1,b-2))
}
fn expected_aliases(c:usize,s:usize)->Vec<Term> {
    let Some((dest,_))=expected_guard(c,s)else{return Vec::new()};
    // Separate literal coordinate oracle; do not call aliases/destination/x/row.
    let (rq,sq,cq)=if c==0 {(430192,677725,1001510)}else{(462960,685917,1003558)};
    (0..65).map(|k|Term{row:s*524288+rq+k,gate:Gate{
        left:s*1048576+sq+k,right:dest*1048576+cq+k,
        c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}}).collect()
}
fn roster_ok(c:usize,s:usize,actual:&[Term])->bool {actual==expected_aliases(c,s)}

/// Dyadic interval decomposition, independent of wiring carry/borrow kernels.
fn pair_interval(r:&[Fr],u:&[Fr],mut lo:usize,hi:usize)->Fr {
    let mut out=Fr::zero();
    while lo<hi {
        let mut k=lo.trailing_zeros().min(21)as usize;
        while (1usize<<k)>hi-lo {k-=1;}
        let mut w=Fr::one();
        for b in 0..r.len() {w*=if b<k {(Fr::one()-r[b])*(Fr::one()-u[b])+r[b]*u[b]}
            else if (lo>>b)&1==1 {r[b]*u[b]}else{(Fr::one()-r[b])*(Fr::one()-u[b])};}
        out+=w;lo+=1usize<<k;
    }out
}
fn block_oracle(c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    let mut out=eq(r,845759)*eq(u,845759)*eq(v,845759);
    let mut a=844673;
    while a+1087<G[c] {
        let b=a+127;let lo=a+1087;let hi=(b+1088).min(G[c]);
        let dest=(b+1088).min(G[c])-1;
        out+=pair_interval(r,u,lo,hi)*eq(v,dest);a+=128;
    }out
}

#[test]
fn full_h21_schedule_and_boundary_census() {
    for c in 0..2 {
        let mut counts=[0usize;3];
        for s in FIRST..G[c] {assert_eq!(destination(c,s),expected_guard(c,s).map(|p|p.0));
            counts[if s==FIRST{0}else if s<TAIL[c]{1}else{2}]+=1;}
        assert_eq!(counts,if c==0 {[1,982016,62]}else{[1,981888,127]});
        for (s,d) in [(845759,845759),(845760,845887),(845887,845887),(845888,846015),
            (1048511,1048511),(1048512,1048639),(TAIL[c],G[c]-1),(G[c]-1,G[c]-1)] {
            assert_eq!(destination(c,s),Some(d));
        }
        assert!(aliases(c,FIRST-1).is_empty());assert!(aliases(c,G[c]).is_empty());
        assert!(aliases(c,(1<<21)-1).is_empty());
    }
    assert!(aliases(2,FIRST).is_empty());
}

#[test]
fn oh_owner_factor_matches_independent_full_epoch_oracle() {
    let r=point(21,3);let u=point(21,41);let v=point(21,109);
    for c in 0..2 {assert_eq!(owner_weight(c,&r,&u,&v),block_oracle(c,&r,&u,&v));}
    // Independent explicit small interval reference validates dyadic summation.
    for (lo,hi) in [(845759,845760),(845760,845888),(1048500,1048700),(1827776,1827838)] {
        let sum:Fr=(lo..hi).map(|s|eq(&r,s)*eq(&u,s)).sum();
        assert_eq!(pair_interval(&r,&u,lo,hi),sum);
    }
}

#[test]
fn physical_coefficients_and_isolated_coordinate_faults() {
    for c in 0..2 {
        for s in [FIRST,FIRST+1,FIRST+128,FIRST+129,1048511,1048512,TAIL[c],G[c]-1] {
            let terms=aliases(c,s);let d=expected_guard(c,s).unwrap().0;
            for k in [0usize,64] {
                let r=bits(40,s*524288+ALIAS[c]+k);
                let u=bits(41,s*1048576+SCORE[c]+224+k);
                let v=bits(41,d*1048576+CAP[c]+740+k);
                let expected=[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()];
                assert_eq!(coefficients(c,&r,&u,&v),expected);
                assert_eq!(direct(&terms,&r,&u,&v),expected);
                for fault in 0..8 {let mut bad=terms.clone();let t=&mut bad[k];
                    match fault {0=>t.gate.right+=128*1048576,1=>t.gate.right+=if c==0{2048}else{0},
                        2=>t.gate.left+=1,3=>t.gate.right+=1,4=>t.gate.c2=Fr::one(),
                        5=>t.row+=1,6=>t.gate.left^=1usize<<40,7=>t.gate.right^=1usize<<40,_=>unreachable!()}
                    if fault==1 && c==1 {bad[k].gate.right-=2048;}
                    assert_ne!(direct(&bad,&r,&u,&v),expected,"c{c} s{s} bit{k} fault{fault}");
                }
            }
        }
        let s=G[c];let r=bits(40,row(s,ALIAS[c]));let u=bits(41,x(s,SCORE[c]+224));
        let v=bits(41,x(G[c]-1,CAP[c]+740));assert_eq!(coefficients(c,&r,&u,&v),[Fr::zero();4]);
        // Bounded non-Boolean full-index tuple versus separately factored roster.
        let r=point(40,7);let u=point(41,43);let v=point(41,113);
        let owners=[FIRST,FIRST+1,1048512,TAIL[c],G[c]-1];
        let terms:Vec<_>=owners.iter().flat_map(|s|aliases(c,*s)).collect();
        let owner:Fr=owners.iter().map(|s|eq(&r[19..],*s)*eq(&u[20..],*s)*eq(&v[20..],expected_guard(c,*s).unwrap().0)).sum();
        let a=owner*local_factor(c,&r[..19],&u[..20],&v[..20]);
        assert_eq!(direct(&terms,&r,&u,&v),[Fr::zero(),a,-a,Fr::zero()]);
    }
}

#[test]
fn exact_ordered_alias_roster_rejects_omission_and_field_mutants() {
    for c in 0..2 {for s in [FIRST,FIRST+1,1048512,TAIL[c],G[c]-1] {
        let terms=aliases(c,s);assert_eq!(terms.len(),65);assert!(roster_ok(c,s,&terms));
        for fault in 0..10 {let mut bad=terms.clone();match fault {
            0=>{bad.remove(0);},1=>{bad.push(bad[64].clone());},
            2=>bad[0].gate.right+=128*1048576,
            3=>{if c==0{bad[0].gate.right+=2048;}else{bad[0].gate.right-=2048;}},
            4=>bad[0].gate.left+=1,5=>bad[64].gate.right-=1,
            6=>bad[0].gate.c2=Fr::one(),7=>bad[0].row+=1,
            8=>bad[0].gate.right^=1usize<<40,9=>bad.swap(0,64),_=>unreachable!()}
            assert!(!roster_ok(c,s,&bad),"c{c} s{s} fault{fault}");
        }
    }}
}

type SharedX=BTreeMap<usize,Fr>;
fn put_shared(values:&mut SharedX,index:usize,value:Fr) {
    assert!(!values.contains_key(&index),"duplicate physical X writer");
    values.insert(index,value);
}
/// Multiple terms of one relation row are normal; a second row writer is not.
/// Validate the complete claim before mutation, including equal-value claims.
fn claim_rows(claims:&mut BTreeMap<usize,&'static str>,writer:&'static str,terms:&[Term])->Result<(),&'static str> {
    let rows:BTreeSet<_>=terms.iter().map(|t|t.row).collect();
    if rows.iter().any(|q|claims.contains_key(q)){return Err("duplicate physical ROW writer");}
    for q in rows {claims.insert(q,writer);}Ok(())
}
fn residuals(terms:&[Term],values:&SharedX)->BTreeMap<usize,Fr> {
    let mut rows=BTreeMap::new();
    for t in terms {let g=&t.gate;
        let a=if !g.c1.is_zero()||!g.c3.is_zero(){*values.get(&g.left).expect("missing physical left")}else{Fr::zero()};
        let b=if !g.c2.is_zero()||!g.c3.is_zero(){*values.get(&g.right).expect("missing physical right")}else{Fr::zero()};
        *rows.entry(t.row).or_insert(Fr::zero())+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;
    }rows.retain(|_,v|!v.is_zero());rows
}
fn cap_rows(c:usize,dest:usize,source_owner:usize)->Vec<Term> {
    let mut terms=Vec::new();suffix::emit_cap(845760,|t| {
        let wire=|w|match w {
            suffix::Wire::Cap{origin,local}=>{assert_eq!(origin,845760);x(dest,CAP[c]+local as usize)},
            suffix::Wire::Native{owner,local}=>{assert_eq!(owner,844670);x(source_owner,MAX[c]+local as usize-999424)},
        };
        let q=t.row.local as usize;
        let local=if q<2048 {[357978,360026][c]+q}else{[407304,407824][c]+q-2048};
        terms.push(Term{row:row(dest,local),gate:Gate{left:wire(t.left),right:wire(t.right),
            c0:t.c[0],c1:t.c[1],c2:t.c[2],c3:t.c[3]}});
    });terms
}
fn insert_cap(values:&mut SharedX,c:usize,dest:usize,source_owner:usize,d:&BigUint)->Vec<Term> {
    let produced=cap::producer(d).unwrap();
    for (k,b) in produced.into_iter().enumerate(){put_shared(values,x(dest,CAP[c]+k),b);}
    for k in 0..224 {put_shared(values,x(source_owner,MAX[c]+k),Fr::from(u64::from(d.bit(k as u64))));}
    let terms=cap_rows(c,dest,source_owner);assert_eq!(terms.len(),6419);
    assert!(residuals(&terms,values).is_empty());terms
}
fn spec(c:usize,s:usize)->score::Spec {
    score::Spec{active:s<G[c],origin_one:false,reducing:false,first:false,terminal:false,
        empty_terminal:false,maturity:if c==0{4995}else{2090},guard_total:None,expected:BigUint::from(0u8)}
}
fn translated_score(c:usize,s:usize,spec:&score::Spec)->Vec<Term> {
    let mut out=Vec::new();score::emit_local(spec,|local| {
        assert!(!local.previous);let mut t=local.term;t.row=row(s,SCORE_ROWS[c]+t.row);
        t.gate.left=x(s,SCORE[c]+t.gate.left);t.gate.right=x(s,SCORE[c]+t.gate.right);out.push(t);
    }).unwrap();out
}

#[test]
fn real_cap_producer_to_score_producer_shared_x_and_bit_negatives() {
    let top=(BigUint::from(1u8)<<65usize)/3u8;
    let cases=[(0,FIRST,BigUint::from(1u8)),(1,FIRST+1,BigUint::from(5u8)),
        (0,1048512,BigUint::from(6u8)),(1,1048512,BigUint::from(5u8)),
        (0,TAIL[0],top.clone()),(1,TAIL[1],top)];
    for (c,s,d) in cases {
        let (dest,source_owner)=expected_guard(c,s).unwrap();let mut values=SharedX::new();
        let cap_terms=insert_cap(&mut values,c,dest,source_owner,&d);
        // Read V exclusively from the exact physical Cap producer bits.
        let mut v=BigUint::from(0u8);
        for k in 0..65 {let b=values[&x(dest,CAP[c]+740+k)];assert!(b.is_zero()||b.is_one());
            if b.is_one(){v+=BigUint::from(1u8)<<k;}}
        assert_eq!(v,cap::scalar(&d).unwrap());
        let expected=if d==BigUint::from(1u8){BigUint::from(1u8)}else if d==BigUint::from(5u8){BigUint::from(8u8)}
            else if d==BigUint::from(6u8){BigUint::from(16u8)}else{BigUint::from(1u8)<<64usize};
        assert_eq!(v,expected);
        let sp=spec(c,s);let produced=score::produce(&sp,Some(&score::ConditionalInputs{w:BigUint::from(0u8),v}),&BigUint::from(0u8)).unwrap();
        for (k,b) in produced.into_iter().enumerate(){put_shared(&mut values,x(s,SCORE[c]+k),b);}
        let mut all=cap_terms;all.extend(translated_score(c,s,&sp));all.extend(aliases(c,s));
        // The immutable physical address map is the sole evaluation source.
        assert!(residuals(&all,&values).is_empty());
        for k in 0..65 {assert_eq!(values[&x(s,SCORE[c]+224+k)],values[&x(dest,CAP[c]+740+k)]);
            assert_eq!(values[&x(s,SCORE[c]+513+k)],values[&x(dest,CAP[c]+740+k)]);
            let mut bad=values.clone();let b=bad.get_mut(&x(s,SCORE[c]+224+k)).unwrap();*b=Fr::one()-*b;
            let failed=residuals(&aliases(c,s),&bad);
            assert_eq!(failed.len(),1);assert!(failed.contains_key(&row(s,ALIAS[c]+k)));
        }
        // Distinct valid Cap producers expose wrong guard and context residuals.
        let decoy_d=if d==BigUint::from(5u8){BigUint::from(6u8)}else{BigUint::from(5u8)};
        insert_cap(&mut values,c,dest+128,source_owner+128,&decoy_d);
        insert_cap(&mut values,1-c,dest,source_owner,&decoy_d);
        for fault in 0..2 {let mut bad=aliases(c,s);
            for t in &mut bad {if fault==0 {t.gate.right+=128*1048576;}
                else if c==0 {t.gate.right+=2048;}else{t.gate.right-=2048;}}
            assert!(!residuals(&bad,&values).is_empty(),"wrong guard/context must fail");
        }
    }
}

#[test]
fn frozen_score_and_cap_row_placement_census() {
    for c in 0..2 {
        let s=FIRST;let local=translated_score(c,s,&spec(c,s));
        assert!(local.iter().all(|t|t.row<row(s,SCORE_ROWS[c]+4208)));
        assert_eq!(SCORE_ROWS[c]+4208,ALIAS[c]);
        assert!(ALIAS[c]+65<=SCORE_ROWS[c]+8192);
        assert!(SCORE_ROWS[c]+8192<[438272,471040][c]);
        let cap_terms=cap_rows(c,s,844670);
        assert!(cap_terms.iter().all(|t|(t.row%524288)<408344));
        let actual=aliases(c,s);let mut claims=BTreeMap::new();
        claim_rows(&mut claims,"Score",&local).unwrap();
        claim_rows(&mut claims,"Cap",&cap_terms).unwrap();
        let baseline=claims.clone();
        claim_rows(&mut claims,"CapV alias",&actual).unwrap();
        assert_eq!(claims.len()-baseline.len(),65);
        let joined=claims.clone();
        assert!(claim_rows(&mut claims,"CapV alias",&actual).is_err());
        assert_eq!(claims,joined,"duplicate equal-value claim is atomic");
        for q in [ALIAS[c],ALIAS[c]+64] {
            let mut occupied=baseline.clone();
            let mut inserted=actual[0].clone();inserted.row=row(s,q);
            claim_rows(&mut occupied,"existing writer mutant",&[inserted]).unwrap();
            let before=occupied.clone();
            assert!(claim_rows(&mut occupied,"CapV alias",&actual).is_err(),"inserted writer must reject alias claim");
            assert_eq!(occupied,before,"failed complete row claim is atomic");
        }
        let mut values=SharedX::new();put_shared(&mut values,x(s,SCORE[c]),Fr::zero());
        let duplicate=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||put_shared(&mut values,x(s,SCORE[c]),Fr::zero())));
        assert!(duplicate.is_err(),"equal-value X writer must reject");
        assert_eq!(values.len(),1);
        let padded=score::produce(&spec(c,G[c]),None,&BigUint::from(0u8)).unwrap();
        assert!(padded.iter().all(Zero::is_zero));assert!(aliases(c,G[c]).is_empty());
    }
}

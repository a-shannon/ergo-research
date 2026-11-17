//! Direct symbolic diagnostics only. Import bits are explicit Boolean premises;
//! none of these sparse fixtures authenticates a native prefix or old X.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use num_bigint::{BigInt, BigUint};
use num_traits::Signed;
use std::collections::BTreeSet;
use crate::{legacy_envelope_map::{self as lm, Map, Inputs, Import, Kind, OwnerRow, Scope,
    LowerBranch, LowerSelector, LowerSource, BASE, BANK, RATIO, PRED, SMAX,
    D_LOCAL, T_LOCAL, I, TE}, sparse::Term};

fn map(n:u64,e:usize)->Map {
    Map::new(n,(64-(n-1).leading_zeros()) as usize,e).unwrap()
}
fn d(owner:u64)->Import {Import {owner,local:D_LOCAL,width:224,kind:Kind::Difficulty}}
fn t(owner:u64)->Import {Import {owner,local:T_LOCAL,width:64,kind:Kind::Timestamp}}
fn anchor(q:u64)->u64 {1024*q+959}
fn timestamp_owners(q:u64,ell:usize)->Vec<u64> {
    if ell==0 {return Vec::new();}
    let mut out:Vec<_>=(0..ell).map(|i|1024*(q-ell as u64+i as u64)+1023).collect();
    out.push(anchor(q));out
}
fn difficulty_owners(q:u64,ell:usize)->Vec<u64> {
    (0..ell).map(|i|if i+1==ell {1024*q+958}
        else {1024*(q-ell as u64+1+i as u64)+1022}).collect()
}
fn fixture(q:u64,e:usize,ds:&[BigInt],times:&[BigInt])->(Map,Inputs,OwnerRow) {
    let s=anchor(q);let m=map(s+2,e);let ell=q.min(8) as usize;
    assert_eq!(ds.len(),ell);
    assert_eq!(times.len(),if ell==0 {0}else{ell+1});
    let mut inputs=Inputs::default();
    inputs.put(&m,d(s),&BigInt::from(1)).unwrap();
    let mut expected=BTreeSet::from([d(s)]);
    for (owner,n) in difficulty_owners(q,ell).into_iter().zip(ds) {
        inputs.put(&m,d(owner),n).unwrap();expected.insert(d(owner));
    }
    for (owner,n) in timestamp_owners(q,ell).into_iter().zip(times) {
        inputs.put(&m,t(owner),n).unwrap();expected.insert(t(owner));
    }
    assert_eq!(m.imports(s).unwrap().into_iter().collect::<BTreeSet<_>>(),expected);
    let row=m.generate(s,&inputs).unwrap();
    (m,inputs,row)
}
fn height_times(q:u64,ell:usize)->Vec<BigInt> {
    timestamp_owners(q,ell).iter().map(|s|BigInt::from(s+1)).collect()
}
fn gaps_times(ell:usize,first:u64,later:u64,final_delta:u64)->Vec<BigInt> {
    let mut out=vec![BigInt::from(1000000)];
    for i in 0..ell-1 {
        let next=out.last().unwrap()+if i==0 {first}else{later};
        out.push(next);
    }
    out.push(out.last().unwrap()+final_delta-64u64);
    out
}
fn sat(m:&Map,inputs:&Inputs,row:&OwnerRow) {
    let faults=m.failures(row,inputs).unwrap();
    assert!(faults.is_empty(),"owner{} unexpected residues {faults:?}",row.owner);
}
fn source_guards(m:&Map,inputs:&Inputs,row:&OwnerRow) {
    for imp in m.imports(row.owner).unwrap().into_iter().filter(|i|i.kind==Kind::Difficulty) {
        if imp.owner==row.owner {continue;}
        let guard=m.generate(imp.owner,inputs).unwrap();
        sat(m,inputs,&guard);
    }
}
fn local_rows(faults:Vec<(usize,Fr)>,owner:u64)->BTreeSet<usize> {
    faults.into_iter().map(|(row,_)|row-owner as usize*(1<<14)).collect()
}
fn exact_fault(m:&Map,inputs:&Inputs,row:&OwnerRow,expected:&[usize]) {
    assert_eq!(local_rows(m.failures(row,inputs).unwrap(),row.owner),
        expected.iter().copied().collect::<BTreeSet<_>>());
}
fn contains_fault(m:&Map,inputs:&Inputs,row:&OwnerRow,expected:usize) {
    assert!(local_rows(m.failures(row,inputs).unwrap(),row.owner).contains(&expected),
        "missing intended local row{expected}");
}
fn nonuniform(ell:usize)->(Map,Inputs,OwnerRow,Vec<BigInt>) {
    let scale=BigInt::from(1u64)<<40;
    let mut ys:Vec<_>=(1..ell).map(|i|&scale*(i*i+1)+i).collect();
    ys.push(&scale*((ell+1)*(ell+1)+1)+11);
    let times=gaps_times(ell,TE as u64,TE as u64,TE as u64);
    let (m,inputs,row)=fixture(ell as u64,47,&ys,&times);
    (m,inputs,row,ys)
}
fn add_poly_bit(terms:&mut Vec<Term>,owner:u64,ratio:usize,bit:usize) {
    terms.push(Term {row:owner as usize*(1<<14)+9422,
        gate:crate::gkr::Gate {left:owner as usize*(1<<20)+RATIO+503*ratio+155+bit,
            right:owner as usize*(1<<20),c0:Fr::zero(),c1:Fr::from(4000000000u64),
            c2:Fr::zero(),c3:Fr::zero()}});
}

#[test]
fn full_tiers_and_isolated_faults() {
    let expected=[19791209299992u64,25288767438865,32985348833295,42661051157722,
        54242573636962,67698501653078,83013127897101];
    for ell in 1..=8 {
        let q=ell as u64;
        let value=BigInt::from(1u64)<<60usize;
        let ds=vec![value.clone();ell];
        let (m,inputs,row)=fixture(q,64,&ds,&height_times(q,ell));
        sat(&m,&inputs,&row);source_guards(&m,&inputs,&row);
        let quotient=&value*120000u64;
        assert_eq!(row.bound(&m).unwrap(),&quotient+if ell==1 {0u64}else{3u64});
        for i in 0..ell {
            assert_eq!(row.get(RATIO+503*i+155,91).unwrap(),quotient);
            assert_eq!(row.get(RATIO+503*i+246,64).unwrap(),BigInt::from(0));
        }
        if ell==1 {
            assert_eq!(row.get(PRED,782).unwrap(),BigInt::from(0));
        } else {
            let mut ds=vec![BigInt::from(1);ell];ds[0]=BigInt::from(1u64)<<64;
            let (m,inputs,row)=fixture(q,64,&ds,&height_times(q,ell));
            sat(&m,&inputs,&row);source_guards(&m,&inputs,&row);
            let c=row.signed_get(PRED+262,92,PRED+354).unwrap();
            assert!(c< -m.cap(),"ell{ell} negative magnitude must exceed diagnostic U");
            assert_eq!(row.bound(&m).unwrap(),BigInt::from(I));
            assert!(!row.bit(SMAX+92).unwrap());
            let mut false_select=row.clone();false_select.flip(SMAX+92).unwrap();
            false_select.put(SMAX,92,&row.get(PRED+262,92).unwrap()).unwrap();
            exact_fault(&m,&inputs,&false_select,&[9915]);
        }
        let (m,inputs,row,ys)=nonuniform(ell);
        sat(&m,&inputs,&row);source_guards(&m,&inputs,&row);
        assert_eq!(row.bound(&m).unwrap(),if ell==1 {ys[0].clone()}
            else {BigInt::from(expected[ell-2])});
        // Every genuine imported endpoint is independently guarded; first
        // endpoint D is distinct, so a start/end substitution cannot hide.
        let first=timestamp_owners(q,ell)[0]-1;
        let mut extra=inputs.clone();extra.put(&m,d(first),&BigInt::from(1)).unwrap();
        let guard=m.generate(first,&extra).unwrap();sat(&m,&extra,&guard);
        let mut wrong=m.terms(row.owner).unwrap();
        let source_owner=difficulty_owners(q,ell)[0];
        for term in &mut wrong {
            if term.row==row.owner as usize*(1<<14)+8350 &&
                term.gate.left/(1<<20)==source_owner as usize {
                let local=term.gate.left%(1<<20);
                term.gate.left=first as usize*(1<<20)+local;
            }
        }
        assert_eq!(local_rows(m.failures_with(&row,&extra,&wrong).unwrap(),row.owner),
            BTreeSet::from([8350]));
    }
    // Exact ell1 tie behavior with a real ratio, not a detached maximum.
    for value in [I-1,I,I+1] {
        let (m,inputs,row)=fixture(1,41,&[BigInt::from(value)],
            &gaps_times(1,TE as u64,TE as u64,TE as u64));
        sat(&m,&inputs,&row);
        assert_eq!(row.bound(&m).unwrap(),BigInt::from(value.max(I)));
        assert_eq!(row.bit(SMAX+92).unwrap(),value>I);
        if value==I {
            let mut false_select=row.clone();false_select.flip(SMAX+92).unwrap();
            exact_fault(&m,&inputs,&false_select,&[9915]);
        }
    }
    for ell in 2..=8 {
        for negative in [false,true] {
            let desired=ell+usize::from(negative);
            let (m,inputs,row)=fixture(ell as u64,64,&vec![BigInt::from(1);ell],
                &gaps_times(ell,TE as u64/desired as u64,TE as u64+1,TE as u64+1));
            sat(&m,&inputs,&row);source_guards(&m,&inputs,&row);
            assert_eq!(row.get(PRED+131,92).unwrap(),BigInt::from(0));
            assert!(!row.bit(PRED+223).unwrap());
            assert_eq!(row.bit(PRED+261).unwrap(),negative);
            assert_eq!(row.get(PRED+262,92).unwrap(),BigInt::from(u8::from(!negative)));
            assert!(!row.bit(PRED+354).unwrap());
            assert_eq!(row.bound(&m).unwrap(),BigInt::from(I));
        }
    }
    let (_,_,_,ys)=nonuniform(8);
    let (m9,inputs9,row9)=fixture(9,47,&ys,&gaps_times(8,TE as u64,TE as u64,TE as u64));
    sat(&m9,&inputs9,&row9);source_guards(&m9,&inputs9,&row9);
    assert_eq!(row9.bound(&m9).unwrap(),BigInt::from(expected[6]));
    let (m,inputs,row,_)=nonuniform(8);
    for (wire,intended) in [(RATIO+91,8351),(RATIO+155,8352),(RATIO+246,8352),
        (RATIO+502,8483),
        (PRED+131,9423),(PRED+224,9423),(PRED+262,9424),(PRED+261,9423),
        (SMAX+92,9915)] {
        let mut bad=row.clone();bad.flip(wire).unwrap();
        contains_fault(&m,&inputs,&bad,intended);
    }
    let time_owners=timestamp_owners(8,8);
    let mut swapped=m.terms(row.owner).unwrap();
    for term in &mut swapped {
        if term.row!=row.owner as usize*(1<<14)+8351 {continue;}
        let owner=(term.gate.left/(1<<20)) as u64;
        let local=term.gate.left%(1<<20);
        if (T_LOCAL..T_LOCAL+64).contains(&local) {
            if owner==time_owners[0] {
                term.gate.left=time_owners[1] as usize*(1<<20)+local;
            } else if owner==time_owners[1] {
                term.gate.left=time_owners[0] as usize*(1<<20)+local;
            }
        }
    }
    assert_eq!(local_rows(m.failures_with(&row,&inputs,&swapped).unwrap(),row.owner),
        BTreeSet::from([8351]));
    for (i,owner) in timestamp_owners(8,8).into_iter().enumerate() {
        let mut bad=inputs.clone();bad.flip(t(owner),63).unwrap();
        contains_fault(&m,&bad,&row,10008+i);
    }
    // Each needed original word gets an isolated wrong-owner consumer fault.
    // Distinct alternate values make the intended numeric predicate decide it.
    for imp in m.imports(row.owner).unwrap() {
        let mut missing=Inputs::default();
        for keep in m.imports(row.owner).unwrap().into_iter().filter(|i|*i!=imp) {
            missing.put(&m,keep,&inputs.get(keep).unwrap()).unwrap();
        }
        assert!(m.generate(row.owner,&missing).err().unwrap().contains("missing typed import"));
        let alternate=Import {owner:0,..imp};
        let mut extra=inputs.clone();
        extra.put(&m,alternate,&(inputs.get(imp).unwrap()+3)).unwrap();
        let mut wrong=m.terms(row.owner).unwrap();
        for term in &mut wrong {
            let owner=(term.gate.left/(1<<20)) as u64;
            let local=term.gate.left%(1<<20);
            if owner==imp.owner && imp.local<=local && local<imp.local+imp.width {
                term.gate.left=local; // owner0, with the actual bit offset retained
            }
        }
        let faults=local_rows(m.failures_with(&row,&extra,&wrong).unwrap(),row.owner);
        let intended=if imp.kind==Kind::Difficulty {
            if imp.owner==row.owner {7899} else {
                let i=difficulty_owners(8,8).iter().position(|s|*s==imp.owner).unwrap();
                8350+134*i
            }
        } else {
            let i=timestamp_owners(8,8).iter().position(|s|*s==imp.owner).unwrap();
            8351+134*i.saturating_sub(1).min(7)
        };
        assert!(faults.contains(&intended),"wrong original owner {imp:?} misses row{intended}");
    }
    // Recomputed single-input range faults target the shared guard only.
    for (n,e,intended) in [(BigInt::from(0),64,8349),
        ((BigInt::from(1u64)<<64)+1,64,8123),
        (BigInt::from(1u64)<<223,64,8123)] {
        let m=map(3,e);let mut inputs=Inputs::default();
        inputs.put(&m,d(0),&n).unwrap();
        let row=m.generate(0,&inputs).unwrap();
        exact_fault(&m,&inputs,&row,&[intended]);
        assert_eq!(inputs.get(d(0)).unwrap(),n);
    }
    // D=0 imported by an anchor, recomputing all downstream helpers. The
    // anchor itself is SAT; its source guard isolates the missing positivity.
    let (m,mut inputs,_,_)=nonuniform(8);
    let source=difficulty_owners(8,8)[0];
    inputs.put(&m,d(source),&BigInt::from(0)).unwrap();
    let anchor_row=m.generate(anchor(8),&inputs).unwrap();sat(&m,&inputs,&anchor_row);
    let guard=m.generate(source,&inputs).unwrap();
    exact_fault(&m,&inputs,&guard,&[8349]);
    // Zero coefficients have an explicit exception: changing true Yi keeps
    // PRED unchanged after ratio recomputation, but stale advice is rejected.
    for (ell,ordinal) in [(4,2),(7,3)] {
        let (m,mut inputs,row,_)=nonuniform(ell);
        let imp=d(difficulty_owners(ell as u64,ell)[ordinal-1]);
        let value=inputs.get(imp).unwrap();
        inputs.put(&m,imp,&(&value+1)).unwrap();
        let next=m.generate(row.owner,&inputs).unwrap();sat(&m,&inputs,&next);
        assert_eq!(&row.bits[PRED-BASE..PRED+782-BASE],
            &next.bits[PRED-BASE..PRED+782-BASE]);
        contains_fault(&m,&inputs,&row,8350+134*(ordinal-1));
        let mut terms=m.terms(next.owner).unwrap();
        // After +1, ordinal2 has bit1 set and ordinal3 has bit2 set.
        add_poly_bit(&mut terms,next.owner,ordinal-1,if ordinal==2 {1}else{2});
        assert_eq!(local_rows(m.failures_with(&next,&inputs,&terms).unwrap(),next.owner),
            BTreeSet::from([9422]));
    }
    // Components explicitly omit the polynomial. Full factory rejects these
    // substitutions, so they cannot masquerade as complete tier SAT.
    let (m,inputs,row,_)=nonuniform(2);
    let terms=lm::prediction_component_terms(&m,row.owner,2).unwrap();
    for n in [BigInt::from(0),BigInt::from(4000000000u64),
        -BigInt::from(4000000000u64),BigInt::from(4000000000u64)*I] {
        let mut component=row.clone();
        component.assign_prediction_component(&n,2).unwrap();
        assert!(m.failures_with(&component,&inputs,&terms).unwrap().is_empty());
        assert!(local_rows(m.failures(&component,&inputs).unwrap(),row.owner).contains(&9422));
        assert_eq!(component.get(PRED+224,37).unwrap(),BigInt::from(0));
        assert!(!component.bit(PRED+261).unwrap());
        let mut bad=component.clone();bad.flip(PRED+261).unwrap();
        assert_eq!(local_rows(m.failures_with(&bad,&inputs,&terms).unwrap(),row.owner),
            BTreeSet::from([9779]));
        if n==BigInt::from(0) {
            for (wire,target) in [(PRED+130,9777),(PRED+223,9778),(PRED+354,9780)] {
                let mut bad=component.clone();bad.flip(wire).unwrap();
                assert_eq!(local_rows(m.failures_with(&bad,&inputs,&terms).unwrap(),row.owner),
                    BTreeSet::from([target]));
            }
        }
    }
    // Terminal, unused ratio/PRED and complete tail zeros.
    let m=map(3,0);let inputs=Inputs::default();
    let terminal=m.generate(2,&inputs).unwrap();sat(&m,&inputs,&terminal);
    for offset in [0,673,777,5757,BANK-1] {
        let mut bad=terminal.clone();bad.flip(BASE+offset).unwrap();
        exact_fault(&m,&inputs,&bad,&[offset]);
    }
    let (m,inputs,row)=fixture(1,41,&[BigInt::from(I)],
        &gaps_times(1,TE as u64,TE as u64,TE as u64));
    for wire in [RATIO+503,PRED,SMAX+278,BASE+BANK-1] {
        let mut bad=row.clone();bad.flip(wire).unwrap();
        exact_fault(&m,&inputs,&bad,&[wire-BASE]);
    }
}
fn point(n:usize,seed:u64)->Vec<Fr> {
    (0..n).map(|i|Fr::from(seed+3*i as u64+2)/Fr::from(seed+11*i as u64+19)).collect()
}
fn boolean(n:usize,x:u64)->Vec<Fr> {
    (0..n).map(|b|Fr::from((x>>b)&1)).collect()
}
fn reference(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    let mut out=[Fr::zero();4];
    for t in terms {
        let rw=lm::eq(r,t.row as u64);
        if rw.is_zero() {continue;}
        let k=rw*lm::eq(u,t.gate.left as u64)*lm::eq(v,t.gate.right as u64);
        for (z,c) in out.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*z+=k*c;}
    }
    out
}

#[test]
fn q9_relocated_analytic_first_falsifier() {
    use crate::h21_row_support::{relocate,Family};
    const OWNER:usize=10175;
    // Symbolic upper-only profile: no RAW/native membership or global-U claim.
    let map=Map::new_modern_global_u(1_827_840,21,55).unwrap();
    let source=crate::bank53_map::map_owner_terms(&map,OWNER as u64,0).unwrap();
    let terms:Vec<_>=source.iter().map(|t|relocate(Family::Map(0),OWNER,t).unwrap()).collect();
    assert!(!terms.is_empty());
    for (old,new) in source.iter().zip(&terms) {
        assert_eq!(old.gate,new.gate);
        assert_eq!(new.row,old.row-409600+477074);
        assert!((OWNER*(1<<19)+477074..OWNER*(1<<19)+487421).contains(&new.row));
    }
    // Deliberately independent full-coordinate literal equality, not the
    // analytic owner kernel, local placement helper or emitted-template path.
    fn eq_literal(p:&[Fr],index:usize)->Fr {
        let mut z=Fr::one();
        for (bit,value) in p.iter().enumerate() {
            z*=if (index>>bit)&1==1 {*value}else{Fr::one()-value};
        }
        z
    }
    fn literal(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
        let mut out=[Fr::zero();4];
        for t in terms {
            let weight=eq_literal(r,t.row)*eq_literal(u,t.gate.left)*eq_literal(v,t.gate.right);
            for (actual,c) in out.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {
                *actual+=weight*c;
            }
        }
        out
    }
    let (r,u,v)=(point(40,101),point(41,211),point(41,307));
    let expected=literal(&terms,&r,&u,&v);
    let actual=map.q9_relocated_coefficients_diagnostic(&r,&u,&v).unwrap();
    assert_eq!(actual,expected,"q9 full nonboolean owner/local projection");
    assert_eq!(expected[2],Fr::zero(),"honest Map has no c2 terms");
    for channel in 0..4 {
        let mut bad=actual;bad[channel]+=Fr::one();
        assert_ne!(bad,expected,"isolated coefficient channel {channel}");
    }
    let foreign=terms.iter().position(|t|t.gate.left==2047*(1<<20)+T_LOCAL+63
        && (!t.gate.c1.is_zero() || !t.gate.c3.is_zero())).expect("active foreign timestamp bit63");
    let term=&terms[foreign];
    let weight=eq_literal(&r,term.row)*eq_literal(&u,term.gate.left)*eq_literal(&v,term.gate.right);
    assert!(!weight.is_zero());
    assert!([term.gate.c1,term.gate.c3].iter().any(|c|!(*c*weight).is_zero()));
    let mut bad=terms.clone();bad[foreign].gate.left=OWNER*(1<<20)+T_LOCAL+63;
    assert_ne!(literal(&bad,&r,&u,&v),expected,"active foreign owner must survive projection");
    let mut other_r=r.clone();other_r[19..].copy_from_slice(&boolean(21,9151));
    assert_eq!(map.q9_relocated_coefficients_diagnostic(&other_r,&u,&v).unwrap(),[Fr::zero();4]);
    assert_eq!(literal(&terms,&other_r,&u,&v),[Fr::zero();4]);
    println!("C130A_Q9_FIRST_PASS owner=10175 foreign_owner=2047 channels=4 other_owner=9151 terms={}",terms.len());
}
fn selected_points(m:&Map,owner:u64,seed:u64)->(Vec<Fr>,Vec<Fr>,Vec<Fr>) {
    let mut r=point(14,seed);r.extend(boolean(m.h(),owner));
    let mut u=point(20,seed+17);u.extend(point(m.h(),seed+31));
    let mut v=point(20,seed+53);v.extend(point(m.h(),seed+71));
    (r,u,v)
}
fn lower_pivot(value:&BigUint,threshold:&BigUint,width:usize)->usize {
    (0..width).rev().find(|k| !threshold.bit(*k as u64) && value.bit(*k as u64))
        .expect("strictly larger value has a zero-to-one highest differing bit")
}
fn kernel_reference(m:&Map,ell:usize,r:&[Fr],u:&[Fr],v:&[Fr],d:u64,low:u64)->Fr {
    let mut out=Fr::zero();
    // Fixed schedule bound, never row/bit terms times owners.
    for q in 0..824u64 {
        if q>=m.m() || q==407 || q.min(8) as usize!=ell || q<d {continue;}
        let s=1024*q+959;let source=1024*(q-d)+low;
        out+=lm::eq(r,s)*lm::eq(u,source)*lm::eq(v,s);
    }
    out
}
#[test]
fn mapped_coefficients_and_owner_boundaries() {
    // Local differential isolates exactly one row owner, while imported input
    // owners and all local coordinates remain asymmetric and non-Boolean.
    for q in 0..=8u64 {
        let m=map(anchor(q)+2,64);
        let terms=m.terms(anchor(q)).unwrap();
        for seed in [7,29] {
            let (r,u,v)=selected_points(&m,anchor(q),seed);
            assert_eq!(m.coefficients(&r,&u,&v).unwrap(),reference(&terms,&r,&u,&v),"q{q}/seed{seed}");
        }
    }
    for (n,owner) in [(3,0),(3,2),(960,959),(3008,3007),(8192,8191)] {
        let m=map(n,64);let terms=m.terms(owner).unwrap();
        let (r,u,v)=selected_points(&m,owner,43);
        assert_eq!(m.coefficients(&r,&u,&v).unwrap(),reference(&terms,&r,&u,&v));
    }
    let m=map(9217,64);let owner=anchor(8);let terms=m.terms(owner).unwrap();
    let (r,u,v)=selected_points(&m,owner,19);
    let expected=m.coefficients(&r,&u,&v).unwrap();
    let mut split=terms.clone();
    let diagonal=split.iter().position(|t|t.row==owner as usize*(1<<14)
        && t.gate.left==t.gate.right && t.gate.c1== -Fr::one()
        && t.gate.c3==Fr::one()).unwrap();
    let mut two_point=split[diagonal].clone();
    split[diagonal].gate.c1=Fr::zero();
    two_point.gate.c3=Fr::zero();two_point.gate.right=owner as usize*(1<<20);
    split.push(two_point);
    let split_coefficients=reference(&split,&r,&u,&v);
    assert_ne!(expected[1],split_coefficients[1]);
    for channel in [0,2,3] {assert_eq!(expected[channel],split_coefficients[channel]);}
    let mut wrong=terms.clone();
    let term=wrong.iter_mut().find(|t|t.row==owner as usize*(1<<14)+8350 && !t.gate.c1.is_zero()).unwrap();
    term.gate.right=0; // Non-reading placeholder mutation is invisible to SAT.
    assert_ne!(expected,reference(&wrong,&r,&u,&v));
    let mut omitted=terms.clone();
    omitted.retain(|t|t.row!=owner as usize*(1<<14)+9422);
    assert_ne!(expected,reference(&omitted,&r,&u,&v));
    // Boolean local-row census includes every family, gap and final tail.
    for q in [0,1,4,7,8] {
        let m=map(anchor(q)+2,64);let owner=anchor(q);
        let terms=m.terms(owner).unwrap();
        let u=point(20+m.h(),11);let v=point(20+m.h(),37);
        for local in [0,672,673,5680,5757,7897,7898,8123,8124,8349,
            8350,8352,8483,9419,9421,9422,9777,9821,9822,9915,10007,
            10008,10016,10017,16383] {
            let r=boolean(14+m.h(),owner*(1<<14)+local);
            assert_eq!(m.coefficients(&r,&u,&v).unwrap(),reference(&terms,&r,&u,&v),
                "Boolean census q{q}/row{local}");
        }
    }
    // Every owner point is non-Boolean in these separate joint-kernel tests.
    for n in [3,511,960,1984,8192,9216,417791,417792,843776,1827840,i32::MAX as u64] {
        let m=map(n,64);
        for seed in [13,47] {
            let r=point(m.h(),seed);let u=point(m.h(),seed+17);let v=point(m.h(),seed+41);
            for ell in 0..=8 {
                for (d,low) in [(0,959),(0,958),(1,1023),(3,1022),(8,1023)] {
                    assert_eq!(m.owner_kernel(Scope::Anchor(ell),&r,&u,&v,d,low).unwrap(),
                        kernel_reference(&m,ell,&r,&u,&v,d,low),"n{n}/ell{ell}/d{d}");
                }
            }
        }
    }
    for n in [3,17,255,512,1024,4096] {
        let m=map(n,64);let r=point(m.h(),7);let u=point(m.h(),29);let v=point(m.h(),61);
        let work=(0..n-1).fold(Fr::zero(),|a,s|a+lm::eq(&r,s)*lm::eq(&u,s)*lm::eq(&v,s));
        let all=(0..m.slots()).fold(Fr::zero(),|a,s|a+lm::eq(&r,s)*lm::eq(&u,s)*lm::eq(&v,s));
        assert_eq!(m.owner_kernel(Scope::Work,&r,&u,&v,0,0).unwrap(),work);
        assert_eq!(m.owner_kernel(Scope::All,&r,&u,&v,0,0).unwrap(),all);
    }
    // Large integer addresses without a large reference interval or X.
    let m=map(i32::MAX as u64,64);let s=m.n()-2;
    let rp=boolean(m.h(),s);let up=point(m.h(),23);let vp=point(m.h(),59);
    assert_eq!(m.owner_kernel(Scope::Work,&rp,&up,&vp,0,0).unwrap(),
        lm::eq(&up,s)*lm::eq(&vp,s));
    let (r,u,v)=selected_points(&m,anchor(823),67);
    let terms=m.terms(anchor(823)).unwrap();
    assert_eq!(m.coefficients(&r,&u,&v).unwrap(),reference(&terms,&r,&u,&v));
}

#[test]
fn modern_global_u_d_upper_guard_and_coefficients() {
    for e in [0,64] {
        let m=Map::new_modern_global_u(3,2,e).unwrap();
        let upper=(2*(1u128<<e)+1)/3;
        let mut inputs=Inputs::default();
        inputs.put(&m,d(0),&BigInt::from(upper)).unwrap();
        let at_upper=m.generate(0,&inputs).unwrap();
        assert!(m.failures(&at_upper,&inputs).unwrap().is_empty(),"e{e}");

        inputs.put(&m,d(0),&BigInt::from(upper+1)).unwrap();
        let above_upper=m.generate(0,&inputs).unwrap();
        assert_eq!(local_rows(m.failures(&above_upper,&inputs).unwrap(),0),
            BTreeSet::from([BANK+225]),"e{e} must leave only the final-borrow residue");

        inputs.put(&m,d(0),&BigInt::from(0)).unwrap();
        let zero=m.generate(0,&inputs).unwrap();
        assert_eq!(local_rows(m.failures(&zero,&inputs).unwrap(),0),
            BTreeSet::from([BANK+451]),"e{e} must retain the D>0 guard");
    }
    assert!(Map::new_modern_global_u(3,2,65).is_err());

    let modern=Map::new_modern_global_u(3,2,4).unwrap();
    let legacy=Map::new(3,2,4).unwrap();
    let mut inputs=Inputs::default();
    inputs.put(&modern,d(0),&BigInt::from(11)).unwrap();
    let row=modern.generate(0,&inputs).unwrap();
    assert_eq!(legacy.check_row(&row).unwrap_err(),"legacy map row binding");
    let legacy_row=legacy.generate(0,&inputs).unwrap();
    assert_eq!(modern.check_row(&legacy_row).unwrap_err(),"legacy map row binding");

    let terms=modern.terms(0).unwrap();
    let (r,u,v)=selected_points(&modern,0,83);
    assert_eq!(modern.coefficients(&r,&u,&v).unwrap(),reference(&terms,&r,&u,&v));
}

#[test]
fn modern_global_u_legacy_b_upper_bound_and_coefficients() {
    let n=1984u64;let h=11usize;let owner=1983u64;
    let make_inputs=|m:&Map| {
        let mut inputs=Inputs::default();
        inputs.put(m,d(1982),&BigInt::from(I)).unwrap();
        inputs.put(m,t(1023),&BigInt::from(1_000_000u64)).unwrap();
        inputs.put(m,t(1983),&BigInt::from(2_000_000u64)).unwrap();
        inputs
    };

    let modern47=Map::new_modern_global_u(n,h,47).unwrap();
    let inputs47=make_inputs(&modern47);
    let row47=modern47.generate(owner,&inputs47).unwrap();
    assert_eq!(row47.bound(&modern47).unwrap(),BigInt::from(147_445_380_701_907u64));
    let failures47=modern47.failures(&row47,&inputs47).unwrap();
    let local47=local_rows(failures47.clone(),owner);
    assert!(!local47.is_empty());
    assert!(local47.iter().all(|r|(10032..=10122).contains(r)),"unexpected non-B-upper failures {local47:?}");

    let modern48=Map::new_modern_global_u(n,h,48).unwrap();
    let inputs48=make_inputs(&modern48);
    let row48=modern48.generate(owner,&inputs48).unwrap();
    assert_eq!(row48.bound(&modern48).unwrap(),BigInt::from(147_445_380_701_907u64));
    assert!(modern48.failures(&row48,&inputs48).unwrap().is_empty());

    // Local ordinary coefficients select owner 1983 with Boolean owner bits
    // while keeping row/input evaluation points non-Boolean.
    let terms=modern48.terms(owner).unwrap();
    let (r,u,v)=selected_points(&modern48,owner,101);
    assert_eq!(modern48.coefficients(&r,&u,&v).unwrap(),reference(&terms,&r,&u,&v));

    // The same sparse owner translated into bank53's physical row/input lanes
    // agrees with its analytic coefficient emitter under the same Boolean owner.
    let physical=crate::bank53_map_score::map_owner_terms(&modern48,owner,0).unwrap();
    let mut rp=point(19,107);rp.extend(boolean(h,owner));
    let mut up=point(20,109);up.extend(point(h,127));
    let mut vp=point(20,131);vp.extend(point(h,149));
    assert_eq!(modern48.bank53_coefficients(0,&rp,&up,&vp).unwrap(),
        reference(&physical,&rp,&up,&vp));

    // Owner 1982 independently selects its own D guard, whose physical input
    // is distinct from owner 1983's tier imports.
    let guard_terms=modern48.terms(1982).unwrap();
    let mut rg=point(14,157);rg.extend(boolean(h,1982));
    let mut ug=point(20,163);ug.extend(point(h,167));
    let mut vg=point(20,173);vg.extend(point(h,179));
    assert_eq!(modern48.coefficients(&rg,&ug,&vg).unwrap(),
        reference(&guard_terms,&rg,&ug,&vg));

    for e in [0usize,64] {
        let m=Map::new_modern_global_u(n,h,e).unwrap();
        let inputs=make_inputs(&m);
        let generated=m.generate(owner,&inputs).unwrap();
        let all=m.terms(owner).unwrap();
        let start=owner as usize*(1<<14);
        let upper:Vec<_>=all.into_iter().filter(|term|
            (start+10032..=start+10122).contains(&term.row)).collect();
        assert_eq!(upper.len(),91,"e{e} fixed B-upper row count");
        let mut at_u=generated.clone();
        at_u.put(SMAX,92,&(BigInt::from(1u8)<<e)).unwrap();
        assert!(m.failures_with(&at_u,&inputs,&upper).unwrap().is_empty(),"e{e} B=U");

        let mut above=generated.clone();
        above.put(SMAX,92,&((BigInt::from(1u8)<<e)+1u8)).unwrap();
        let failed=local_rows(m.failures_with(&above,&inputs,&upper).unwrap(),owner);
        let expected=if e==0 {10032} else {10032+91-e};
        assert_eq!(failed,BTreeSet::from([expected]),"e{e} B=U+1");

        let mut high=generated.clone();
        high.put(SMAX,92,&(BigInt::from(1u8)<<(e+1))).unwrap();
        assert_eq!(local_rows(m.failures_with(&high,&inputs,&upper).unwrap(),owner),
            BTreeSet::from([10032]),"e{e} high-bit failure");
    }
}

#[test]
fn selected_global_u_lower_d_equality_and_pivot_are_exact_owner_bound() {
    let n=1984u64;let h=11usize;let height=1984u64;let owner=height-2;
    let threshold=((BigUint::from(1u8)<<48usize)+BigUint::from(4u8))/BigUint::from(3u8);
    let equality=Map::new_modern_global_u_selected_lower(n,h,48,LowerSelector {
        source:LowerSource::HeaderDifficulty{height},branch:LowerBranch::Equality,
    }).unwrap();
    let mut inputs=Inputs::default();
    inputs.put(&equality,d(owner),&BigInt::from(threshold.clone())).unwrap();
    let row=equality.generate(owner,&inputs).unwrap();
    sat(&equality,&inputs,&row);
    let all=equality.terms(owner).unwrap();
    let lower:Vec<_>=all.iter().filter(|t| (owner as usize*(1<<14)+10123..=owner as usize*(1<<14)+10346).contains(&t.row)).cloned().collect();
    assert_eq!(lower.iter().map(|t|t.row).collect::<BTreeSet<_>>().len(),224);
    assert!(equality.terms(owner-1).unwrap().iter().all(|t| !(10123..=10346).contains(&(t.row-(owner as usize-1)*(1<<14)))));
    for bad in [&threshold-BigUint::from(1u8),&threshold+BigUint::from(1u8)] {
        let mut changed=inputs.clone();changed.put(&equality,d(owner),&BigInt::from(bad.clone())).unwrap();
        let candidate=equality.generate(owner,&changed).unwrap();
        let faults=equality.failures_with(&candidate,&changed,&lower).unwrap();
        assert!(!faults.is_empty(),"D equality must reject {bad}");
        assert!(local_rows(faults,owner).iter().all(|r|(10123..=10346).contains(r)));
    }

    let above=&threshold+BigUint::from(1u8);
    let k=lower_pivot(&above,&threshold,224);
    let pivot=Map::new_modern_global_u_selected_lower(n,h,48,LowerSelector {
        source:LowerSource::HeaderDifficulty{height},branch:LowerBranch::Pivot(k),
    }).unwrap();
    let mut pivot_inputs=Inputs::default();
    pivot_inputs.put(&pivot,d(owner),&BigInt::from(above.clone())).unwrap();
    let pivot_row=pivot.generate(owner,&pivot_inputs).unwrap();
    sat(&pivot,&pivot_inputs,&pivot_row);
    let pivot_terms=pivot.terms(owner).unwrap();
    let lower:Vec<_>=pivot_terms.iter().filter(|t| (owner as usize*(1<<14)+10123..=owner as usize*(1<<14)+10346).contains(&t.row)).cloned().collect();
    assert!(!lower.is_empty());
    let mut bad=pivot_inputs.clone();bad.flip(d(owner),k).unwrap();
    assert!(local_rows(pivot.failures_with(&pivot_row,&bad,&lower).unwrap(),owner).contains(&10123));
    let mut bad=pivot_inputs.clone();bad.flip(d(owner),k+1).unwrap();
    assert!(local_rows(pivot.failures_with(&pivot_row,&bad,&lower).unwrap(),owner).contains(&(10123+k+1-k)));

    let (r,u,v)=selected_points(&pivot,owner,223);
    assert_eq!(pivot.coefficients(&r,&u,&v).unwrap(),reference(&pivot_terms,&r,&u,&v));
    let physical=crate::bank53_map_score::map_owner_terms(&pivot,owner,0).unwrap();
    let mut rp=point(19,227);rp.extend(boolean(h,owner));
    let mut up=point(20,229);up.extend(point(h,233));
    let mut vp=point(20,239);vp.extend(point(h,241));
    assert_eq!(pivot.bank53_coefficients(0,&rp,&up,&vp).unwrap(),reference(&physical,&rp,&up,&vp));
}

#[test]
fn selected_global_u_lower_b_literals_and_parent_binding_are_canonical() {
    let n=1984u64;let h=11usize;let owner=anchor(1);
    let selector=|branch|LowerSelector {source:LowerSource::LegacyBound{q:1},branch};
    let threshold=BigUint::from(1u8)<<47usize;
    let make_inputs=|m:&Map| {
        let mut x=Inputs::default();
        x.put(m,d(1982),&BigInt::from(I)).unwrap();
        x.put(m,t(1023),&BigInt::from(1_000_000u64)).unwrap();
        x.put(m,t(1983),&BigInt::from(2_000_000u64)).unwrap();x
    };
    let upper_only=Map::new_modern_global_u(n,h,48).unwrap();
    let inputs=make_inputs(&upper_only);
    let base=upper_only.generate(owner,&inputs).unwrap();
    let bound=base.bound(&upper_only).unwrap().to_biguint().unwrap();
    assert_eq!(bound,BigUint::from(147_445_380_701_907u64));
    let k=lower_pivot(&bound,&threshold,92);
    let selected=Map::new_modern_global_u_selected_lower(n,h,48,selector(LowerBranch::Pivot(k))).unwrap();
    let selected_inputs=make_inputs(&selected);
    let selected_row=selected.generate(owner,&selected_inputs).unwrap();
    sat(&selected,&selected_inputs,&selected_row);
    let terms=selected.terms(owner).unwrap();
    let lower:Vec<_>=terms.iter().filter(|t| (owner as usize*(1<<14)+10123..=owner as usize*(1<<14)+10214).contains(&t.row)).cloned().collect();
    assert!(!lower.is_empty() && lower.len()<=92);
    let mut bad=selected_row.clone();bad.flip(SMAX+k).unwrap();
    assert!(local_rows(selected.failures_with(&bad,&selected_inputs,&lower).unwrap(),owner).contains(&10123));
    let mut bad=selected_row.clone();bad.flip(SMAX+k+1).unwrap();
    assert!(local_rows(selected.failures_with(&bad,&selected_inputs,&lower).unwrap(),owner).contains(&(10123+k+1-k)));
    assert!(Map::new_modern_global_u_selected_lower(n,h,48,selector(LowerBranch::Equality)).is_err());

    let (r,u,v)=selected_points(&selected,owner,251);
    assert_eq!(selected.coefficients(&r,&u,&v).unwrap(),reference(&terms,&r,&u,&v));
    let physical=crate::bank53_map_score::map_owner_terms(&selected,owner,0).unwrap();
    let mut rp=point(19,257);rp.extend(boolean(h,owner));
    let mut up=point(20,263);up.extend(point(h,269));
    let mut vp=point(20,271);vp.extend(point(h,277));
    assert_eq!(selected.bank53_coefficients(0,&rp,&up,&vp).unwrap(),reference(&physical,&rp,&up,&vp));

    let low_literal=Map::new_modern_global_u_selected_lower(n,h,40,LowerSelector {
        source:LowerSource::InitialI,branch:LowerBranch::Literal,
    }).unwrap();
    let literal_terms=low_literal.terms(owner).unwrap();
    assert!(literal_terms.iter().all(|t| !(10123..=10346).contains(&(t.row-owner as usize*(1<<14)))));
    assert!(Map::new_modern_global_u_selected_lower(n,h,42,LowerSelector {
        source:LowerSource::InitialI,branch:LowerBranch::Literal,
    }).is_err());
    for source in [LowerSource::Reset417792,LowerSource::Reset417793] {
        assert!(Map::new_modern_global_u_selected_lower(n,h,47,LowerSelector {
            source,branch:LowerBranch::Literal,
        }).is_ok());
    }

    for source in [LowerSource::HeaderDifficulty{height:1},LowerSource::HeaderDifficulty{height:n+1},
        LowerSource::LegacyBound{q:0},LowerSource::LegacyBound{q:2},LowerSource::LegacyBound{q:407}] {
        assert!(Map::new_modern_global_u_selected_lower(n,h,48,LowerSelector {
            source,branch:LowerBranch::Pivot(0),
        }).is_err(),"invalid selector {source:?}");
    }
    assert!(Map::new_modern_global_u_selected_lower(2,1,48,LowerSelector {
        source:LowerSource::HeaderDifficulty{height:2},branch:LowerBranch::Equality,
    }).is_err());
    assert!(Map::new_modern_global_u_selected_lower(n,h,48,selector(LowerBranch::Pivot(92))).is_err());

    let parent=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(n,h,[7;32],[0;28]).unwrap();
    let foreign=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(n,h,[8;32],[0;28]).unwrap();
    let bound_parent=Map::from_parent_modern_global_u(&parent,40,LowerSelector {
        source:LowerSource::InitialI,branch:LowerBranch::Literal,
    }).unwrap();
    let foreign_parent=Map::from_parent_modern_global_u(&foreign,40,LowerSelector {
        source:LowerSource::InitialI,branch:LowerBranch::Literal,
    }).unwrap();
    assert_eq!(bound_parent.binding().parent_root,Some([7;32]));
    assert!(foreign_parent.check_row(&bound_parent.generate(owner,&make_inputs(&bound_parent)).unwrap()).is_err());
    assert!(upper_only.check_row(&selected_row).is_err());
}

#[test]
fn selected_global_u_lower_threshold_edges_and_exponent_extremes() {
    for e in [0usize,64] {
        let n=3u64;let h=2usize;let height=3u64;let owner=height-2;
        let threshold=((BigUint::from(1u8)<<e)+BigUint::from(4u8))/BigUint::from(3u8);
        let m=Map::new_modern_global_u_selected_lower(n,h,e,LowerSelector {
            source:LowerSource::HeaderDifficulty{height},branch:LowerBranch::Equality,
        }).unwrap();
        let mut inputs=Inputs::default();inputs.put(&m,d(owner),&BigInt::from(threshold)).unwrap();
        let row=m.generate(owner,&inputs).unwrap();sat(&m,&inputs,&row);
    }

    let n=1984u64;let h=11usize;let owner=anchor(1);
    let threshold=BigUint::from(1u8)<<47usize;
    let above=&threshold+BigUint::from(1u8);
    let k=lower_pivot(&above,&threshold,92);
    let m=Map::new_modern_global_u_selected_lower(n,h,48,LowerSelector {
        source:LowerSource::LegacyBound{q:1},branch:LowerBranch::Pivot(k),
    }).unwrap();
    let mut inputs=Inputs::default();
    inputs.put(&m,d(1982),&BigInt::from(I)).unwrap();
    inputs.put(&m,t(1023),&BigInt::from(1_000_000u64)).unwrap();
    inputs.put(&m,t(1983),&BigInt::from(2_000_000u64)).unwrap();
    let base=m.generate(owner,&inputs).unwrap();
    let terms=m.terms(owner).unwrap();
    let lower:Vec<_>=terms.iter().filter(|t| (owner as usize*(1<<14)+10123..=owner as usize*(1<<14)+10214).contains(&t.row)).cloned().collect();
    // These row substitutions test only the local comparator. They do not
    // authenticate B against the Map producer or a common commitment.
    let mut at_threshold=base.clone();at_threshold.put(SMAX,92,&BigInt::from(threshold)).unwrap();
    assert!(local_rows(m.failures_with(&at_threshold,&inputs,&lower).unwrap(),owner).contains(&10123));
    let mut at_plus_one=base.clone();at_plus_one.put(SMAX,92,&BigInt::from(above)).unwrap();
    assert!(m.failures_with(&at_plus_one,&inputs,&lower).unwrap().is_empty());

    for e in [0usize,64] {
        let threshold=if e==0 {BigUint::from(0u8)} else {BigUint::from(1u8)<<(e-1)};
        let edge=Map::new_modern_global_u_selected_lower(n,h,e,LowerSelector {
            source:LowerSource::LegacyBound{q:1},branch:LowerBranch::Pivot(0),
        }).unwrap();
        let edge_inputs={
            let mut x=Inputs::default();
            x.put(&edge,d(1982),&BigInt::from(I)).unwrap();
            x.put(&edge,t(1023),&BigInt::from(1_000_000u64)).unwrap();
            x.put(&edge,t(1983),&BigInt::from(2_000_000u64)).unwrap();x
        };
        let mut candidate=edge.generate(owner,&edge_inputs).unwrap();
        let edge_terms=edge.terms(owner).unwrap();
        let selected:Vec<_>=edge_terms.iter().filter(|t| (owner as usize*(1<<14)+10123..=owner as usize*(1<<14)+10214).contains(&t.row)).cloned().collect();
        if e==0 {
            candidate.put(SMAX,92,&BigInt::from(1u8)).unwrap();
            assert!(edge.failures_with(&candidate,&edge_inputs,&selected).unwrap().is_empty());
        } else {
            assert!(!edge.failures_with(&candidate,&edge_inputs,&selected).unwrap().is_empty());
        }
        assert_eq!(threshold.bit(0),false);
    }
}

#[test]
fn descriptor_ranges_and_binding() {
    for (n,h,e) in [(2,1,0),(3,1,0),(3,2,65),(i32::MAX as u64+1,31,64),
        (i32::MAX as u64,32,64)] {
        assert!(Map::new(n,h,e).is_err());
    }
    assert!(Map::native_geometry(1<<21,21).is_ok());
    assert_eq!(Map::native_geometry((1<<21)+1,22).unwrap_err(),
        "native parent admission HOLD above 2^21");
    assert!(Map::new(i32::MAX as u64,31,64).is_ok());
    let modulus=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
    assert!(modulus>BigUint::from(1u8)<<225);
    assert!(modulus>BigUint::from(1u8)<<155);
    for e in [0,64] {
        let m=map(3,e);let mut inputs=Inputs::default();
        inputs.put(&m,d(0),&m.cap()).unwrap();
        let row=m.generate(0,&inputs).unwrap();sat(&m,&inputs,&row);
    }
    let m=map(3,0);
    assert!(m.generate(0,&Inputs::default()).err().unwrap().contains("missing typed import"));
    assert!(m.generate(m.slots(),&Inputs::default()).is_err());
    let mut inputs=Inputs::default();
    assert!(inputs.put(&m,d(2),&BigInt::from(1)).is_err()); // terminal work is absent
    assert!(inputs.put(&m,Import{width:223,..d(0)},&BigInt::from(1)).is_err());
    assert!(inputs.put(&m,d(0),&BigInt::from(-1)).is_err());
    assert!(inputs.put(&m,d(0),&(BigInt::from(1u64)<<224)).is_err());
    assert!(inputs.put(&m,t(0),&(BigInt::from(1u64)<<64)).is_err());
    let (m,inputs,row,_)=nonuniform(2);
    let mut bad=row.clone();bad.binding.e=46;
    assert_eq!(m.failures(&bad,&inputs).unwrap_err(),"legacy map row binding");
    let other=map(m.n(),46);
    assert_eq!(other.failures(&row,&inputs).unwrap_err(),"legacy map row binding");
    let mut bad=row.clone();bad.binding.parent_root=Some([9;32]);
    assert_eq!(m.check_row(&bad).unwrap_err(),"legacy map row binding");
    let mut bad=row.clone();bad.bits.pop();
    assert_eq!(m.check_row(&bad).unwrap_err(),"legacy map row binding");
    let mut bad=row.clone();
    assert!(bad.put(PRED,130,&(BigInt::from(1u64)<<130)).is_err());
    assert!(bad.put(PRED,130,&BigInt::from(-1)).is_err());
    assert!(bad.flip(BASE-1).is_err());
    assert!(m.coefficients(&[],&[],&[]).is_err());
    assert!(m.owner_kernel(Scope::Anchor(9),&point(m.h(),1),&point(m.h(),2),
        &point(m.h(),3),0,959).is_err());
    let kr=point(m.h(),7);let ku=point(m.h(),23);let kv=point(m.h(),53);
    assert!(m.owner_kernel(Scope::Anchor(2),&kr,&ku,&kv,0,958).is_ok());
    for low in [1024,1982,u64::MAX] {
        assert_eq!(m.owner_kernel(Scope::Anchor(2),&kr,&ku,&kv,0,low).unwrap_err(),
            "owner kernel low coordinate");
    }
    // Exact activation cuts and low-owner formulas, including terminal anchors.
    for q in [0,1,7,8,406,407,408,823,824] {
        let s=anchor(q);let a=s+1;
        for n in [a-1,a,a+1] {
            let m=map(n,64);
            let expected=if n>=a && q<=823 && q!=407 {Some(q.min(8) as usize)} else {None};
            assert_eq!(m.tier(s).unwrap(),expected);
            assert!(m.tier(s+1).unwrap().is_none()); // low960 is not header-owner low959
            if n==a && expected.is_some() {
                let active=m.active_intervals(s).unwrap();
                assert!(!active.iter().any(|&(lo,_)|lo==BASE));
            }
        }
    }
    for n in [3,511,512,959] {
        let m=map(n,64);
        assert_eq!(m.m(),0);
        let owner=if m.slots()>959 {959}else{m.slots()-1};
        assert!(m.tier(owner).unwrap().is_none());
    }
    let m=map(960,0);let row=m.generate(959,&Inputs::default()).unwrap();
    sat(&m,&Inputs::default(),&row);
    assert_eq!(row.bound(&m).unwrap(),BigInt::from(I));
    assert!(row.bits.iter().all(|b|!*b));
    let m=map(3008,64);
    let ds=vec![BigInt::from(1);2];
    let times=height_times(2,2);
    let mut inputs=Inputs::default();
    for (owner,n) in difficulty_owners(2,2).into_iter().zip(ds) {inputs.put(&m,d(owner),&n).unwrap();}
    for (owner,n) in timestamp_owners(2,2).into_iter().zip(times) {inputs.put(&m,t(owner),&n).unwrap();}
    let row=m.generate(3007,&inputs).unwrap();sat(&m,&inputs,&row);
    assert_eq!(m.tier(3007).unwrap(),Some(2)); // terminal work owner, active header anchor
    assert_eq!(row.get(BASE,673).unwrap(),BigInt::from(0));
    assert_eq!(m.input_index(d(3006),223).unwrap(),3006*(1<<20)+D_LOCAL+223);
    assert_eq!(m.input_index(t(3007),63).unwrap(),3007*(1<<20)+T_LOCAL+63);
    assert!(m.input_index(d(3006),224).is_err());
    assert!(m.input_index(d(3070),0).is_err()); // no future D(j)
}

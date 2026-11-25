//! Bounded projection diagnostics only; no native/old-X/full-history/PCS claim.
use std::collections::{BTreeMap,BTreeSet};
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::BigInt;
use crate::{envelope_fragment::*,gkr,sparse::Circuit};

fn n(s:&str)->BigInt{s.parse().unwrap()}
fn bits(index:usize,width:usize)->Vec<Fr>{(0..width).map(|b|Fr::from(((index>>b)&1)as u64)).collect()}
fn point(width:usize,seed:u64)->Vec<Fr>{(0..width).map(|b|Fr::from(seed+37*(b as u64+1))).collect()}
fn clean(c:&Circuit,x:&Witness,label:&str){let bad=failures(c,x);assert!(bad.is_empty(),"{label}: {} nonzero rows, first {:?}",bad.len(),bad.first());}
fn rejects(c:&Circuit,x:&Witness,wanted:usize,label:&str){let bad=failures(c,x);assert!(bad.iter().any(|(r,_)|*r==wanted),"{label}: expected row{wanted}, found {:?}",bad.iter().map(|(r,_)|*r).take(12).collect::<Vec<_>>());}
fn only(c:&Circuit,x:&Witness,wanted:usize,label:&str){let bad=failures(c,x);assert_eq!(bad.len(),1,"{label}: unexpected failure rows {:?}",bad.iter().map(|(r,_)|*r).collect::<Vec<_>>());assert_eq!(bad[0].0,wanted,"{label}");}

#[test]
fn complete_positive_negative_and_faults(){
    let c=circuit();assert_eq!((c.input_len,c.row_count),(INPUT,ROWS));assert!(c.terms.len()<729089);
    let positive=fixture(false,false,None,false,100);clean(&c,&positive,"complete synthetic positive");
    for(base,width,expected)in [(h(12)+155,91,"143998844928120000"),(h(13)+155,91,"143998844928240000"),
        (h(14),130,"575995379713440008000006144"),(h(14)+131,92,"143998844928360002"),
        (h(14)+224,37,"6144"),(h(15),92,"143998844928360003"),(h(1)+72,65,"144115188075855872")]{assert_eq!(positive.get(word(base,width)),n(expected));}
    // Native arithmetic is not assumed: these RAW-address imports are synthetic.
    let negative=fixture(true,false,None,false,100);clean(&c,&negative,"complete negative-N synthetic positive");
    assert_eq!(negative.signed_get(h(14),130,h(14)+130),n("-575995379711519991999993856"));
    assert_eq!(negative.signed_get(h(14)+131,92,h(14)+223),n("-143998844927879997"));
    assert_eq!(negative.signed_get(h(14)+224,37,h(14)+261),n("-3999993856"));
    assert_eq!(negative.get(word(h(15),92)),BigInt::from(I));
    assert!(negative.get(word(h(14)+262,92))>negative.get(word(h(1)+72,65)),"internal |ceil| is not capped by Ug");
    assert_eq!(negative.get(word(h(1)+72,65)),BigInt::from(1)<<47);
    // The third approved complete SAT recipe is the explicit left-on-tie observation.
    assert!(!positive.bits[h(16)+672]);assert_eq!(positive.get(word(h(16),224)),BigInt::from(1));
    clean(&c,&positive,"complete positive tie observation");

    // All six immutable origins, not a supplied maximum or chosen subset.
    let ug=positive.get(word(h(1)+72,65));let expected=[17867*&ug,BigInt::from(1)+17867*&ug,
        BigInt::from(2)+9548*&ug,BigInt::from(3)+9548*&ug,BigInt::from(2094),BigInt::from(2095)];
    for(k,value)in expected.iter().enumerate(){assert_eq!(positive.get(word(h(42+k),96)),*value,"origin{}",k+1);}
    assert_eq!(positive.get(word(h(67),96)),expected[1]);assert_eq!(positive.get(word(slot(18)+64,96)),expected[1]);
    assert_eq!(positive.get(word(h(25),66)),BigInt::from(4));assert!(positive.bits[h(25)+66]);
    assert_eq!(positive.get(word(h(26)+72,65)),BigInt::from(4));
    assert_eq!(D_OWNERS[8],Some(3006));assert_eq!(TIME_OWNERS,[1023,2047,3007]);assert_eq!(W_OWNERS,[0,1,2,3,4]);
    assert_eq!((D_LOCAL,TIME_LOCAL,W_LOCAL),(987674,525330,987450));

    // Distinct D values and independently cumulative W exercise every join.
    let mut heterogeneous = positive.clone();
    for (index, difficulty) in [3u64, 5, 7, 11, 13].into_iter().enumerate() {
        heterogeneous.set(slot(index + 1), 224, difficulty);
    }
    for (index, cumulative) in [3u64, 8, 15, 26, 39].into_iter().enumerate() {
        heterogeneous.set(slot(index + 13), 224, cumulative);
    }
    for opcode in ORDER {
        heterogeneous.assign_one(opcode, None, false);
    }
    clean(&c, &heterogeneous, "heterogeneous complete synthetic positive");
    assert_eq!(heterogeneous.get(word(slot(0), 224)), BigInt::from(1));
    for opcode in [50, 51] {
        assert_eq!(heterogeneous.get(word(h(opcode), 224)), BigInt::from(13));
    }
    for opcode in [53, 58] {
        assert_eq!(heterogeneous.get(word(h(opcode), 66)), BigInt::from(19));
        assert!(heterogeneous.bits[h(opcode) + 66]);
    }
    for opcode in [54, 59] {
        assert_eq!(heterogeneous.get(word(h(opcode) + 72, 65)), BigInt::from(32));
    }
    let varied_terms = [
        17867 * &ug,
        BigInt::from(3) + 17867 * &ug,
        BigInt::from(8) + 9548 * &ug,
        BigInt::from(15) + 9548 * &ug,
        BigInt::from(26 + 2090 * 32),
        BigInt::from(39 + 2090 * 32),
    ];
    for (index, expected_term) in varied_terms.iter().enumerate() {
        assert_eq!(heterogeneous.get(word(h(42 + index), 96)), *expected_term,
            "heterogeneous origin{}", index + 1);
    }
    assert_eq!(heterogeneous.get(word(h(67), 96)), varied_terms[1]);
    assert_eq!(heterogeneous.get(word(slot(18) + 64, 96)), varied_terms[1]);

    for (field_base, alias_opcode, label) in [
        (slot(18) + 64, 68, "public_AB_bit40"),
        (slot(18) + 160, 71, "public_Ug_bit40"),
    ] {
        let mut bad = heterogeneous.clone();
        bad.bits[field_base + 40] = !bad.bits[field_base + 40];
        only(&c, &bad, row(alias_opcode, 40), label);
    }
    for import_slot in 13..18 {
        let mut bad = heterogeneous.clone();
        bad.bits[slot(import_slot) + 100] = true;
        let pin_row = 42 + (import_slot - 13) * 129 + 5;
        only(&c, &bad, row(0, pin_row), "full_W_bit100 forcing guard");
    }
    for (field_offset, pin_row, label) in [
        (8, 3, "public_n_env_bit0"),
        (24, 15, "public_j_bit0"),
        (40, 27, "public_a_bit0"),
    ] {
        let mut bad = heterogeneous.clone();
        bad.bits[slot(18) + field_offset] = !bad.bits[slot(18) + field_offset];
        only(&c, &bad, row(0, pin_row), label);
    }
    for import_slot in 10..13 {
        let mut bad = heterogeneous.clone();
        bad.bits[slot(import_slot) + 63] = true;
        // Keep ratio advice unchanged; its residual may also reject this import.
        rejects(&c, &bad, row(0, 39 + import_slot - 10), "timestamp_bit63 guard");
    }
    let mut wrong_w5 = heterogeneous.clone();
    wrong_w5.set(slot(16), 224, 27u64);
    for opcode in ORDER {
        wrong_w5.assign_one(opcode, None, false);
    }
    assert_eq!(wrong_w5.get(word(slot(16), 224)), BigInt::from(27));
    let cumulative_failures = failures(&c, &wrong_w5);
    assert_eq!(cumulative_failures.iter().map(|(at, _)| *at).collect::<Vec<_>>(),
        vec![row(40, 0), row(41, 0)], "W5+1 exact two adjacent continuity failures");
    assert_eq!(cumulative_failures[0].1, Fr::one(), "W5-W4-D5 = 27-15-11");
    assert_eq!(cumulative_failures[1].1, -Fr::one(), "W6-W5-D6 = 39-27-13");

    let mut x=positive.clone();x.assign_ratio(12,Some(word(slot(6),224)));
    rejects(&c,&x,row(12,0),"wrong_end_import");
    let mut x=positive.clone();let delta=x.get(word(h(13)+91,64))+1;x.set(h(13)+91,64,delta);
    rejects(&c,&x,row(13,1),"anchor_time_import");
    let mut x=positive.clone();x.assign_pred_values(positive.get(word(h(14),130)),positive.get(word(h(14)+131,92)),n("6145"),positive.get(word(h(14)+262,92)));
    only(&c,&x,row(14,1),"signed_remainder with recomputed OR/CMP advice");
    let mut x=negative.clone();let q=x.signed_get(h(14)+131,92,h(14)+223);let r=x.signed_get(h(14)+224,37,h(14)+261);
    let signed_n=x.signed_get(h(14),130,h(14)+130);x.assign_pred_values(signed_n,q.clone(),r,q+1);x.assign_one(15,None,false);
    only(&c,&x,row(14,2),"negative_ceil_plus_one");
    let x=fixture(false,true,None,false,100);
    only(&c,&x,row(2,451),"D_zero_recomputed: all dependent words recomputed, same import alias");
    let x=fixture(false,false,Some(58),false,100);only(&c,&x,row(36,225),"wrong_grid_minimality recomputed");
    let mut x=positive.clone();x.set(h(25),66,5u64);rejects(&c,&x,row(25,0),"modern_odd_ceil");
    let mut x=positive.clone();let too_large=x.get(word(h(67),96))+1;x.set(h(67),96,too_large);
    rejects(&c,&x,row(67,97),"false_large_maximum attainment");
    let mut x=positive.clone();x.bits[h(16)+672]=true;only(&c,&x,row(16,224),"tie_wrong_right_selector");
    let x=fixture(false,false,None,true,100);only(&c,&x,row(63,1),"omitted_origin2 producer advice, unchanged consumer");
    let mut x=positive.clone();x.set(slot(18),3,5u64);rejects(&c,&x,row(0,0),"public_cut");
    let mut x=positive.clone();x.bits[slot(0)+100]=true;rejects(&c,&x,row(2,101),"high_D_bit full224 import");
    let mut x=positive.clone();x.bits[82944]=true;only(&c,&x,82944,"inactive_padding");
    let x=fixture(false,false,None,false,101);only(&c,&x,row(70,97),"late_guard_cannot_hide_early");
}

#[test]
fn standalone_ranges_signed_zero_and_grids(){
    // Component-only: all unrelated op constraints are absent by explicit selection.
    let cmp=component(&[2],true);let mut x=Witness::empty();let edge:BigInt=BigInt::from(1)<<64;
    x.set(h(1)+72,65,edge.clone());x.set(slot(0),224,edge.clone());x.assign_one(2,None,false);
    clean(&cmp,&x,"D=U=2^64 component, not full envelope");
    x.set(slot(0),224,&edge+1);x.assign_one(2,None,false);only(&cmp,&x,row(2,225),"D=2^64+1 full comparator");
    let pred=component(&[14],false); // Deliberately excludes the legacy polynomial row0.
    for(value,label)in [("-1","canonical zero quotient and ceil"),("0","all canonical signed zeros"),("4000000000","canonical zero remainder")]{
        let mut x=Witness::empty();x.pred_for_n(n(value));clean(&pred,&x,label);
        let q=x.signed_get(h(14)+131,92,h(14)+223);let r=x.signed_get(h(14)+224,37,h(14)+261);let c=x.signed_get(h(14)+262,92,h(14)+354);
        assert_eq!(q,n(value)/n("4000000000"));assert_eq!(r,n(value)-n("4000000000")*&q);assert_eq!(c,&q+BigInt::from(u8::from(r>BigInt::from(0))));
        for(base,width,sign,canonical_row)in [(h(14),130,h(14)+130,355),(h(14)+131,92,h(14)+223,356),(h(14)+224,37,h(14)+261,357),(h(14)+262,92,h(14)+354,358)]{
            if x.get(word(base,width))==BigInt::from(0){let mut bad=x.clone();bad.bits[sign]=true;only(&pred,&bad,row(14,canonical_row),"isolated negative zero sign");}
        }
    }
    // Generic e0 grid includes B0 and B1; scoped production inputs remain positive.
    let grid=component(&[26,27,28],true);
    for bound in [0u64,1,3,4,5]{let mut x=Witness::empty();x.set(h(25),66,bound);
        for o in [26,27,28]{x.assign_one(o,None,false);}clean(&grid,&x,"standalone exact minimal grid");
        if bound<=1{assert!(x.bits[h(26)]);assert_eq!(x.get(word(h(26)+72,65)),BigInt::from(1));assert_eq!(x.get(word(h(26)+137,65)),BigInt::from(0));}
    }
    let mut x=Witness::empty();x.set(h(25),66,1u64);x.assign_one(26,Some(1),false);x.assign_one(27,None,false);x.assign_one(28,None,false);
    only(&grid,&x,row(28,67),"nonminimal e1 forB1");
    // The complete modern M3 path is also checked above; this isolates odd floor.
    let floor=component(&[25],true);let mut x=Witness::empty();x.set(slot(9),224,3u64);x.assign_one(25,None,false);clean(&floor,&x,"M3 floor4 remainder1");
    x.set(h(25),66,5u64);only(&floor,&x,row(25,0),"M3 ceil differs from floor");
}

fn literal_coefficients(c:&Circuit,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
    // Independent materialized reference is allowed only in this bounded test.
    let rw=gkr::eq_weights(r);let uw=gkr::eq_weights(u);let vw=gkr::eq_weights(v);let mut sum=[Fr::zero();4];
    for t in &c.terms{let weight=rw[t.row]*uw[t.gate.left]*vw[t.gate.right];
        for(k,a)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].into_iter().enumerate(){sum[k]+=weight*a;}}
    sum
}
fn local_boundaries(o:usize)->Vec<usize>{match o{
    0=>vec![0,2,3,14,15,26,27,38,39,41,42,686,687],
    1|26|54|59=>vec![0,1,2,66,67,130,131,132],2..=11=>vec![0,1,224,225,226,227,450,451,452],
    12|13=>vec![0,1,2,3,66,67,68,132,133,134],
    14=>vec![0,1,2,3,4,133,134,225,226,262,263,354,355,358,359,360,361,398,399,400],
    15=>vec![0,1,92,93,94,185,186],
    16..=24|31..=34|48..=52=>vec![0,1,224,225,448,449],
    27|28|55|56|60|61=>vec![0,1,66,67,68],29|57|62=>vec![0,1,65,66,67],
    35|36=>vec![0,1,224,225,226],25|30|37..=47|53|58=>vec![0,1],
    63..=67|69=>vec![0,1,96,97,192,193],68=>vec![0,95,96],70=>vec![0,1,96,97,98],71=>vec![0,64,65],72=>vec![0,1023],_=>unreachable!()}}

#[test]
fn literal_analytic_and_legacy_selector_differential(){
    let c=circuit();for seed in [3u64,11]{let r=point(18,seed);let u=point(17,seed+29);let v=point(17,seed+101);
        let expected=literal_coefficients(&c,&r,&u,&v);assert_eq!(coefficients(&r,&u,&v),expected,"asymmetric nonBoolean coefficients");
        assert_ne!(mutant_coefficients(&r,&u,&v,WiringFault::RelocatedRight),expected,"analytic_wrong_global_right");
        assert_ne!(mutant_coefficients(&r,&u,&v,WiringFault::OmittedOrigin2),expected,"analytic_omitted_origin");
    }
    let mut reference:BTreeMap<(usize,usize,usize),[Fr;4]>=BTreeMap::new();let mut by_row:BTreeMap<usize,Vec<usize>>=BTreeMap::new();
    for(index,t)in c.terms.iter().enumerate(){let e=reference.entry((t.row,t.gate.left,t.gate.right)).or_insert([Fr::zero();4]);
        for(k,a)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].into_iter().enumerate(){e[k]+=a;}by_row.entry(t.row).or_default().push(index);}
    let mut census:BTreeSet<(usize,usize,usize)>=BTreeSet::new();
    for(a,b)in active_intervals(){for i in [a,b-1]{census.insert((i,i,i));census.insert((i,i,0));}
        if b<INPUT{census.insert((b,b,0));}if a>0{census.insert((a-1,a-1,0));}}
    for i in [0,1,8191,82943,82944,INPUT-1]{census.insert((i,i,0));}
    for o in 0..OPS{for local in local_boundaries(o){let r=row(o,local);let mut used=[false;4];
        if let Some(indices)=by_row.get(&r){for &index in indices{let t=&c.terms[index];let cs=[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3];
            for k in 0..4{if !cs[k].is_zero()&&!used[k]{used[k]=true;census.insert((r,t.gate.left,t.gate.right));}}}}
        census.insert((r,0,0));}census.insert((row(o,1023),0,0));}
    for r in [205824,ROWS-1]{census.insert((r,0,0));}
    assert!(census.len()<1800,"bounded boundary census, not full tuple expansion");
    for(r,u,v)in census{let expected=reference.get(&(r,u,v)).copied().unwrap_or([Fr::zero();4]);
        assert_eq!(coefficients(&bits(r,18),&bits(u,17),&bits(v,17)),expected,"Boolean row{r}/left{u}/right{v}");}

    let cases=[(959,960,false,0),(960,960,true,1),(3008,3008,true,3),(8128,8128,true,8),(9152,9152,true,9),
        (417728,417728,false,9),(1827840,843712,true,9)];
    for(n_height,a,yes,count)in cases{assert_eq!(active(a,n_height),yes);let q=a>>10;
        if count>0{assert_eq!(endpoints(q),count);}assert_eq!((a-1)&1023,959);assert_eq!((a-2)&1023,958);
        for(low,index)in [(960,a),(959,a-1),(958,a-2)]{assert_eq!(selector(&bits(index as usize,31),n_height,low),Fr::from(u64::from(yes)));}
        assert_eq!(selector(&bits((a-1)as usize,31),n_height,960),Fr::zero(),"height mask on physical owner");
        assert_eq!(selector(&bits((a-2)as usize,31),n_height,959),Fr::zero(),"header/work owner confusion");
    }
    assert_eq!((m(959),m(960),m(3008),m(8128),m(9152),m(417728),m(1827840)),(0,1,3,8,9,408,824));
    assert_ne!(endpoints(7),9,"q7 incorrectly mature");assert_ne!(endpoints(8),8,"q8 incorrectly short");
    assert_eq!(selector(&bits((407<<10)+959,31),417728,959),Fr::zero(),"excluded q407");
    assert_eq!(selector(&bits(959,31),959,959),Fr::zero(),"empty m0");
    assert_ne!(D_OWNERS[8],Some(TIME_OWNERS[2]),"anchor D confused with header owner");
    // Reference loops at most824 introductions, never an allocated history table.
    for n_height in [959u64,960,3008,8128,9152,417728,1827840]{for seed in [7u64,19]{let r=point(31,seed);let u=point(31,seed+23);let v=point(31,seed+97);
        for low in [960usize,959,958]{let expected=(0..m(n_height)).filter(|q|*q!=407).fold(Fr::zero(),|sum,q|sum+eq(&r,((q<<10)+low as u64)as usize));
            assert_eq!(selector(&r,n_height,low),expected,"interval selector n{n_height}/low{low}");}
        for delta in [1u64,7,8]{let expected=(0..m(n_height)).filter(|q|*q!=407&&*q>=delta).fold(Fr::zero(),|sum,q|{
            sum+eq(&r,((q<<10)+959)as usize)*eq(&u,(((q-delta)<<10)+1023)as usize)*eq(&v,0)});
            assert_eq!(endpoint_coeff(&r,&u,&v,n_height,delta),expected,"endpoint delta{delta}, n{n_height}");}
    }}
    // j3072: earlier endpoint d1 is header2047/work2046; anchor is3007/3006.
    assert_eq!(3072u64-1024-1,2047);assert_eq!(3072u64-2048-1,1023);assert_eq!(3008u64-1,3007);assert_eq!(3008u64-2,3006);
    for(q,delta)in [(7u64,7u64),(8,8),(823,8)]{let r=bits(((q<<10)+959)as usize,31);let u=bits((((q-delta)<<10)+1023)as usize,31);let v=bits(0,31);
        assert_eq!(endpoint_coeff(&r,&u,&v,1827840,delta),Fr::one());
        assert_eq!(endpoint_coeff(&r,&bits((((q-delta)<<10)+1022)as usize,31),&v,1827840,delta),Fr::zero(),"work port substituted for header endpoint");
        assert_eq!(endpoint_coeff(&r,&bits((((q-delta)<<10)+1024)as usize,31),&v,1827840,delta),Fr::zero(),"endpoint header shifted+1");}
    assert_eq!(selector(&point(31,23),(1u64<<31)-1,959),selector(&point(31,23),1827840,959),"large height same fixed legacy cutoff, no history expansion");
}

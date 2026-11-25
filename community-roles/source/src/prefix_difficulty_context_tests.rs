use super::*;
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, sync::OnceLock};

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Packet {
    schema: u32,
    height: u64,
    first_height: u64,
    difficulties: Vec<[u8; 28]>,
}
fn fixture() -> &'static Packet {
    static DATA: OnceLock<Packet> = OnceLock::new();
    DATA.get_or_init(|| {
        let p: Packet = serde_json::from_str(include_str!("fixtures/context-h1810842-v1.json")).unwrap();
        assert_eq!((p.schema, p.height, p.first_height, p.difficulties.len()), (1,1810842,1809755,1088));
        p
    })
}
fn parent() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(1827840, 21, [7;32], [0;28]).unwrap())
}
fn role() -> PrefixDifficultyContext<'static> {
    PrefixDifficultyContext::new(parent(), fixture().height, fixture().difficulties.clone()).unwrap()
}
fn point(log: usize, index: usize) -> Vec<Fr> {
    (0..log).map(|b| Fr::from(((index >> b)&1) as u64)).collect()
}
fn dense(log: usize, seed: u64) -> Vec<Fr> {
    (0..log).map(|b| Fr::from(seed+13*b as u64)).collect()
}
fn terms(layout: &PrefixDifficultyContext<'_>, j: usize) -> Vec<Term> {
    let mut out=Vec::new();
    assert_eq!(layout.visit_position_terms(j, |t| {out.push(t);Ok(())}).unwrap(),224);
    assert_eq!(out.len(),224); out
}
fn select(p: &[Fr], index: usize) -> Fr {
    let mut result=Fr::one();
    for (bit,x) in p.iter().enumerate() {
        if (index>>bit)&1==0 {result*=Fr::one()-x;} else {result*=x;}
    } result
}
fn expansion(layout: &PrefixDifficultyContext<'_>, r: &[Fr],u:&[Fr],v:&[Fr]) -> [Fr;4] {
    let mut out=[Fr::zero();4];
    for j in 0..1088 {
        // Stream224 independent emitted equations; no complete term list.
        for t in terms(layout,j) {
            let weight=select(r,t.row)*select(u,t.gate.left)*select(v,t.gate.right);
            for (a,c) in out.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*a+=weight*c;}
        }
    } out
}
fn assignment(j: usize) -> BTreeMap<usize,Fr> {
    let h=1809755+j;
    let number=BigUint::from_bytes_be(&fixture().difficulties[j]);
    (0..224).map(|b| {
        let bit=(&number>>b)&BigUint::from(1u8);
        ((h-2)*(1<<20)+987674+b,Fr::from(u64::from(bit==BigUint::from(1u8))))
    }).collect()
}
fn failures(ts:&[Term],values:&BTreeMap<usize,Fr>) -> Vec<usize> {
    ts.iter().filter_map(|t| {
        let a=values.get(&t.gate.left).copied().unwrap_or_default();
        let b=values.get(&t.gate.right).copied().unwrap_or_default();
        let residual=t.gate.c0+t.gate.c1*a+t.gate.c2*b+t.gate.c3*a*b;
        (!residual.is_zero()).then_some(t.row)
    }).collect()
}

#[test]
fn prefix_context_admission_preserves_u224_positive_window_and_eligibility() {
    let good=fixture().difficulties.clone(); let layout=role();
    assert_eq!((layout.first_height(),layout.input_log(),layout.row_log()),(1809755,41,19));
    for h in [0,845759,u64::MAX,1827839] {
        assert!(PrefixDifficultyContext::new(parent(),h,good.clone()).is_err());
    }
    for count in [0,1024,1087,1089] {
        let mut wrong=good.clone(); wrong.resize(count,[1;28]);
        assert!(PrefixDifficultyContext::new(parent(),1810842,wrong).is_err());
    }
    for j in [0,537,1087] {
        let mut wrong=good.clone(); wrong[j]=[0;28];
        assert!(PrefixDifficultyContext::new(parent(),1810842,wrong).is_err());
    }
    // Local source binding keeps full U224. A later cap consumer may reject
    // this diagnostic value under its independently enforced profile bounds.
    let mut high=good; high[0]=[0;28];high[0][0]=0x80;
    let high=PrefixDifficultyContext::new(parent(),1810842,high).unwrap();
    let t=terms(&high,0).pop().unwrap();assert_eq!(t.gate.c0,-Fr::one());
    let mut called=false;
    assert!(layout.visit_position_terms(1088,|_| {called=true;Ok(())}).is_err());assert!(!called);
}

#[test]
fn prefix_context_first_interior_last_faults_remove_only_matching_sensitivity() {
    for j in [0,537,1087] {
        let layout=role();let good=assignment(j);let full=terms(&layout,j);
        assert!(failures(&full,&good).is_empty());
        let mut bad=good.clone();let wire=(1809755+j-2)*(1<<20)+987674;
        bad.insert(wire,Fr::one()-good[&wire]);
        assert_eq!(failures(&full,&bad),vec![j*256]);
        let omitted:Vec<_>=full.into_iter().filter(|t|t.row!=j*256).collect();
        assert!(failures(&omitted,&bad).is_empty());
        let mut values=fixture().difficulties.clone();values[j][27]^=1;
        let changed=PrefixDifficultyContext::new(parent(),1810842,values).unwrap();
        assert_eq!(failures(&terms(&changed,j),&good),vec![j*256]);
    }
}

#[test]
fn prefix_context_order_endian_and_decoded_leaf_source_are_distinct() {
    let layout=role();
    let mut reordered=fixture().difficulties.clone();reordered.swap(0,1087);
    assert_ne!(reordered[0],fixture().difficulties[0]);
    let changed=PrefixDifficultyContext::new(parent(),1810842,reordered).unwrap();
    assert!(!failures(&terms(&changed,0),&assignment(0)).is_empty());
    let mut reversed=fixture().difficulties.clone();reversed[0].reverse();
    let changed=PrefixDifficultyContext::new(parent(),1810842,reversed).unwrap();
    assert!(!failures(&terms(&changed,0),&assignment(0)).is_empty());
    let expected=(1809755usize-2)*(1<<20)+987674;
    assert_eq!(terms(&layout,0)[0].gate.left,expected);
    assert_ne!(expected,(1809755usize-1)*(1<<20)+987674);
    assert_ne!(expected,(1809755usize-2)*(1<<20)+987450);
}

#[test]
fn prefix_context_selectors_keep_owner_bits_global_zero_and_both_padding_axes() {
    let layout=role();
    for (j,b) in [(0,0),(537,63),(1087,223)] {
        let t=terms(&layout,j)[b].clone();
        let (r,u,v)=(point(19,j*256+b),point(41,t.gate.left),point(41,0));
        assert_eq!(layout.coefficients(&r,&u,&v).unwrap(),[t.gate.c0,Fr::one(),Fr::zero(),Fr::zero()]);
        for bit in 0..21 {
            let mut wrong=u.clone();wrong[20+bit]=Fr::one()-wrong[20+bit];
            assert_eq!(layout.coefficients(&r,&wrong,&v).unwrap(),[Fr::zero();4]);
        }
        let header_owner=point(41,t.gate.left+(1<<20));
        assert_eq!(layout.coefficients(&r,&header_owner,&v).unwrap(),[Fr::zero();4]);
        let cumulative=point(41,t.gate.left-224);
        assert_eq!(layout.coefficients(&r,&cumulative,&v).unwrap(),[Fr::zero();4]);
        let wrong_right=point(41,(t.gate.left>>20)<<20);
        assert_eq!(layout.coefficients(&r,&u,&wrong_right).unwrap(),[Fr::zero();4]);
        for row in [j*256+224,1088*256+b,2047*256+255] {
            assert_eq!(layout.coefficients(&point(19,row),&u,&v).unwrap(),[Fr::zero();4]);
        }
    }
    for (r,u,v) in [(18,41,41),(20,41,41),(19,40,41),(19,42,41),(19,41,40),(19,41,42)] {
        assert!(layout.coefficients(&vec![Fr::zero();r],&vec![Fr::zero();u],&vec![Fr::zero();v]).is_err());
    }
}

#[test]
fn prefix_context_all_channels_match_independent_nonboolean_stream_expansion() {
    let layout=role();
    let (r,u,v)=(dense(19,3),dense(41,17),dense(41,43));
    assert_eq!(layout.coefficients(&r,&u,&v).unwrap(),expansion(&layout,&r,&u,&v));
}

#[test]
fn prefix_context_transcript_binds_every_position_and_query_before_challenges() {
    fn challenge(layout:&PrefixDifficultyContext<'_>)->Fr {
        let mut t=Transcript::new(b"prefix-context-binding-tests");layout.bind(&mut t);
        assert_eq!(t.challenges(),0);t.challenge_scalar(b"bound")
    }
    let baseline=challenge(&role());
    for j in [0,537,1087] {
        let mut data=fixture().difficulties.clone();data[j][27]^=1;
        assert_ne!(baseline,challenge(&PrefixDifficultyContext::new(parent(),1810842,data).unwrap()));
    }
    let mut query=role();query.h+=1;assert_ne!(baseline,challenge(&query));
    let mut map=role();map.map_fingerprint.push('x');assert_ne!(baseline,challenge(&map));
}

#[test]
fn prefix_context_export_uses_only_exercised_descriptor_public_values() {
    let layout=role();
    assert_eq!(layout.values(),fixture().difficulties.as_slice());
    // Verify every emitted residual against independent retained integer bits
    // before making the exercised descriptor available to the receiver runner.
    for j in 0..1088 {assert!(failures(&terms(&layout,j),&assignment(j)).is_empty());}
    let packet=Packet {schema:1,height:layout.h,first_height:layout.first_height(),difficulties:layout.values().to_vec()};
    let encoded=serde_json::to_vec(&packet).unwrap();assert!(encoded.len()<131072);
    let decoded:Packet=serde_json::from_slice(&encoded).unwrap();
    assert_eq!(decoded.difficulties,fixture().difficulties);
    if let Some(path)=std::env::var_os("NIPOPOW_PREFIX_CONTEXT_PACKET") {
        use std::io::Write;
        let mut out=std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
        out.write_all(&encoded).unwrap();out.sync_all().unwrap();
    }
}

use super::*;
use std::collections::BTreeMap;

fn parameters() -> [PublicMapParameters;2] {
    CutDescriptor::eligible08().terminals().map(|terminal| PublicMapParameters {
        terminal, exponent:55, lower:LowerSelector {
            source:LowerSource::HeaderDifficulty {height:841_729}, branch:LowerBranch::Pivot(54),
        },
    })
}
fn parent() -> WorkTreeHistoryPlan {
    WorkTreeHistoryPlan::compile(N as u64,21,[0x31;32],[0x42;28]).unwrap()
}
fn bits(value:usize,n:usize) -> Vec<Fr> {
    (0..n).map(|bit| Fr::from(((value>>bit)&1) as u64)).collect()
}
fn arbitrary(n:usize,seed:u64) -> Vec<Fr> {
    (0..n).map(|bit| Fr::from(seed+13*bit as u64)).collect()
}
// Independent scalar equality implementation; never turns Fr challenges into
// indices. The literal fold caches only local tables and high-owner products.
fn weight(point:&[Fr],mut index:usize) -> Fr {
    let mut out=Fr::one();
    for value in point { out*=if index%2==0 {Fr::one()-value} else {*value}; index/=2; }
    assert_eq!(index,0); out
}
struct LiteralFold {
    r:Vec<Fr>,u:Vec<Fr>,v:Vec<Fr>,
    rh:Vec<Fr>,uh:Vec<Fr>,vh:Vec<Fr>,
    high:BTreeMap<(usize,usize,usize),Fr>,
}
impl LiteralFold {
    fn new(r:&[Fr],u:&[Fr],v:&[Fr]) -> Self {
        Self {r:crate::gkr::eq_weights(&r[..19]),u:crate::gkr::eq_weights(&u[..20]),
            v:crate::gkr::eq_weights(&v[..20]),rh:r[19..].to_vec(),uh:u[20..].to_vec(),
            vh:v[20..].to_vec(),high:BTreeMap::new()}
    }
    fn term(&mut self,t:&Term) -> [Fr;4] {
        let key=(t.row/ROWS,t.gate.left/WIDTH,t.gate.right/WIDTH);
        let high=*self.high.entry(key).or_insert_with(||
            weight(&self.rh,key.0)*weight(&self.uh,key.1)*weight(&self.vh,key.2));
        let z=high*self.r[t.row%ROWS]*self.u[t.gate.left%WIDTH]*self.v[t.gate.right%WIDTH];
        [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].map(|c|z*c)
    }
}

#[test]
fn c586_role1_literals_match_composed_coefficients_at_nonboolean_points() {
    let parent=parent(); let roster=H21StructuralRoster::from_public(&parent,parameters()).unwrap();
    let rl=arbitrary(19,2); let ul=arbitrary(20,7); let vl=arbitrary(20,11);
    let mut r=rl; r.extend(bits(0,21));
    let mut u=ul;u.extend(arbitrary(21,23));let mut v=vl;v.extend(arbitrary(21,31));
    let mut reference=LiteralFold::new(&r,&u,&v);
    for owner in [0,417_790,845_758,845_759,844_798,845_887,845_951,1_810_841,1_810_904,N,SLOTS-1] {
        r[19..].copy_from_slice(&bits(owner,21));reference.rh=r[19..].to_vec();reference.high.clear();
        let mut expected=[Fr::zero();4];let mut owners=BTreeMap::new();
        let counts=roster.visit_owner_terms(owner,|family,term| {
            assert!(term.row/ROWS==owner&&term.gate.left<WIDTH*SLOTS&&term.gate.right<WIDTH*SLOTS);
            if let Some(previous)=owners.insert(term.row,family) {assert_eq!(previous,family,"cross-family ROW collision");}
            add(&mut expected,reference.term(&term));Ok(())
        }).unwrap();
        assert!(counts.header>300_000);assert_eq!(counts.slack,[387,387]);
        assert_eq!(roster.coefficients(&r,&u,&v).unwrap(),expected,"owner {owner}");
    }
}

#[test]
fn c586_global_score_residue_lift_matches_independent_member_sum() {
    let cut=CutDescriptor::eligible08();
    // Independent named vertices separate all four owner kernels. The old
    // residue127 missed845887 and falsely admitted845951 (delta64).
    for (owner,regular) in [(845_887,true),(845_951,false)] {
        assert_eq!(ClassEquationPlan::for_member(cut,owner).is_ok(),regular);
        for context in 0..2 {
            for (left,right,selected) in [(owner,owner,0),(owner-128,owner,1),
                (owner,0,2),(owner-1,0,3)] {
                let actual=modern_weights(context,&bits(owner,21),&bits(left,21),&bits(right,21)).unwrap();
                let mut expected=[Fr::zero();4];
                if regular {expected[selected]=Fr::one();}
                assert_eq!([actual.same,actual.previous,actual.global_self,actual.global_work],expected,
                    "owner {owner} context {context} kernel {selected}");
            }
        }
    }
    for seed in [2,17] {
        let r=arbitrary(21,seed);let u=arbitrary(21,seed+5);let v=arbitrary(21,seed+11);
        for context in 0..2 {
            let clipped=cut.guards()[context]-1;
            let mut expected=ScoreWeights {same:Fr::zero(),previous:Fr::zero(),global_self:Fr::zero(),global_work:Fr::zero()};
            let first=845_887usize;
            let mut members=(first..clipped).step_by(128).map(|owner|(owner,owner-128)).collect::<Vec<_>>();
            let previous=first+((clipped-first)/128)*128;
            members.extend([(clipped,previous),(FIRST_MODERN_OWNER,845_758)]);
            for (owner,previous) in members {
                let er=weight(&r,owner);let self_u=weight(&u,owner);
                expected.same+=er*self_u*weight(&v,owner);
                expected.previous+=er*weight(&u,previous)*weight(&v,owner);
                expected.global_self+=er*self_u*weight(&v,0);
                expected.global_work+=er*weight(&u,owner-1)*weight(&v,0);
            }
            let actual=modern_weights(context,&r,&u,&v).unwrap();
            assert_eq!([actual.same,actual.previous,actual.global_self,actual.global_work],
                [expected.same,expected.previous,expected.global_self,expected.global_work]);
        }
    }
}

#[test]
fn c586_relocated_map_global_kernel_matches_all_small_domain_literals() {
    let map=Map::new(5,3,64).unwrap();
    let r=arbitrary(22,3);let u=arbitrary(23,7);let v=arbitrary(23,13);
    for context in 0..2 {
        let mut reference=LiteralFold::new(&r,&u,&v);let mut expected=[Fr::zero();4];
        for owner in 0..8 {
            for mut term in bank53_map::map_owner_terms(&map,owner,context).unwrap() {
                term.row=owner as usize*ROWS+MAP_ROW[context]
                    +term.row-owner as usize*ROWS-409_600-context*32_768;
                add(&mut expected,reference.term(&term));
            }
        }
        assert_eq!(map.bank53_coefficients_at(context,MAP_ROW[context],&r,&u,&v).unwrap(),expected);
    }
}

#[test]
fn c586_inactive_padding_and_active_booleanity_have_exact_constraints() {
    let map=Map::new_modern_global_u_selected_lower(parameters()[0].terminal as u64,21,55,parameters()[0].lower).unwrap();
    for (owner,context) in [(1_810_841,0),(1_810_904,1),(N,0),(SLOTS-1,1)] {
        assert!(!score_active(owner,context));let mut terms=Vec::new();
        emit_score_owner(owner,context,&map,|term|{terms.push(term);Ok(())}).unwrap();
        assert_eq!(terms.len(),2048);
        for (bit,t) in terms.iter().enumerate() {
            assert_eq!(t.row,owner*ROWS+SCORE_ROW[context]+bit);
            assert_eq!(t.gate,Gate{left:owner*WIDTH+SCORE_X[context]+bit,right:0,
                c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()});
        }
    }
    let mut active=Vec::new();emit_score_owner(1_810_841,1,&map,|t|{active.push(t);Ok(())}).unwrap();
    let wire=1_810_841*WIDTH+SCORE_X[1]+500;
    let row=1_810_841*ROWS+SCORE_ROW[1]+500;
    let value=Fr::from(2u64);
    let residual=active.iter().filter(|t|t.row==row).fold(Fr::zero(),|sum,t| {
        let l=if t.gate.left==wire {value}else{Fr::zero()};
        let r=if t.gate.right==wire {value}else{Fr::zero()};
        sum+t.gate.c0+t.gate.c1*l+t.gate.c2*r+t.gate.c3*l*r
    });
    assert_eq!(residual,Fr::from(2u64));
}

#[test]
fn c586_clipped_upper_alias_has_exact_context_donor_and_unit_residuals() {
    let parent=parent();let roster=H21StructuralRoster::from_public(&parent,parameters()).unwrap();
    let owner=1_810_841;let context=1;let bit=17;let row=owner*ROWS+W_ALIAS_ROW[context]+bit;
    let mut terms=Vec::new();emit_score_owner(owner,context,&roster.maps[context],|t| {
        if t.row==row {terms.push(t);}Ok(())
    }).unwrap();
    assert_eq!(terms.len(),2);
    let sw=owner*WIDTH+SCORE_X[context]+bit;let upper=1_810_840*WIDTH+UPPER_LOCAL+bit;
    assert_eq!([terms[0].gate.left,terms[1].gate.left],[sw,upper]);
    assert!(terms.iter().all(|t|t.gate.right==0));
    let residual=|changed| terms.iter().fold(Fr::zero(),|sum,t|
        sum+t.gate.c0+t.gate.c1*Fr::from((t.gate.left==changed) as u64));
    assert_eq!(residual(sw),Fr::one());assert_eq!(residual(upper),-Fr::one());
    let r=bits(row,40);let u=bits(upper,41);let v=bits(0,41);
    assert_eq!(roster.coefficients(&r,&u,&v).unwrap(),[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()]);
    let wrong=bits(1_810_839*WIDTH+UPPER_LOCAL+bit,41);
    assert_eq!(roster.coefficients(&r,&wrong,&v).unwrap(),[Fr::zero();4]);
    let wrong_context=bits(owner*ROWS+W_ALIAS_ROW[0]+bit,40);
    assert_eq!(roster.coefficients(&wrong_context,&u,&v).unwrap(),[Fr::zero();4]);
}

#[test]
fn c586_public_descriptor_and_dimensions_reject_foreign_profiles() {
    let parent=parent();let roster=H21StructuralRoster::from_public(&parent,parameters()).unwrap();
    let mut wrong=parameters();wrong[1].terminal=1_827_775;
    assert!(H21StructuralRoster::from_public(&parent,wrong).is_err());
    let mut changed=parameters();changed[0].lower=LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},branch:LowerBranch::Equality};
    let changed=H21StructuralRoster::public_descriptor(&parent,changed).unwrap();
    assert_ne!(roster.descriptor_bytes(),changed.as_slice());
    assert!(roster.coefficients(&arbitrary(39,2),&arbitrary(41,3),&arbitrary(41,7)).is_err());
    assert!(roster.visit_owner_terms(SLOTS,|_,_|Ok(())).is_err());
    let r=arbitrary(40,2);let u=arbitrary(41,3);let v=arbitrary(41,7);
    assert!(roster.maps[0].bank53_coefficients(usize::MAX,&r,&u,&v).is_err());
    assert!(roster.maps[0].bank53_coefficients_at(0,usize::MAX,&r,&u,&v).is_err());
    drop(roster);drop(parent);
    let short=WorkTreeHistoryPlan::compile(3073,12,[0x31;32],[0x42;28]).unwrap();
    assert!(H21StructuralRoster::from_public(&short,parameters()).is_err());
}

use super::*;
use std::collections::{BTreeMap,BTreeSet};
use crate::{gkr::Gate,work_tree_history_plan::WorkTreeHistoryPlan};

fn bits(n:usize,h:usize)->Vec<Fr>{(0..h).map(|b|Fr::from(((n>>b)&1)as u64)).collect()}
fn point(h:usize,seed:u64)->Vec<Fr>{(0..h).map(|b|Fr::from(seed+37*(b as u64+1))).collect()}
fn anchor(o:usize,k:usize)->Term {
    Term{row:o*524288+356632+k,gate:Gate{left:o*1048576+999424+k,right:o*1048576,
        c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}
}
fn anchors(o:usize)->Vec<Term>{(0..5442).map(|k|anchor(o,k)).collect()}

#[test]
fn c194_real_first_modern_cap_header_exact_4096_anchor_retirement_and_single_faults() {
    let owner=845_759;
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[17;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let plan=Scheduled::eligible08();
    let roles=active(&plan,owner).unwrap();
    assert_eq!(roles,[false,false,true,true]);
    let mut raw=Vec::new();roster.visit_header_terms(owner as u64,|term|{raw.push(term);Ok(())}).unwrap();
    let (kept,retired)=filter(owner,roles,raw.clone()).unwrap();
    assert_eq!(retired,[0,0,2048,2048]);
    assert_eq!(raw.len()-kept.len(),4096);
    let cap_anchor=raw.iter().position(|term|term.row==owner*ROWS+357_978).unwrap();
    let mut missing=raw.clone();missing.remove(cap_anchor);
    assert_eq!(filter(owner,roles,missing).unwrap_err(),"missing scheduled HEADER anchor");
    let mut duplicate=raw.clone();duplicate.push(raw[cap_anchor].clone());
    assert_eq!(filter(owner,roles,duplicate).unwrap_err(),"duplicate scheduled HEADER anchor");
    let mut wrong=raw.clone();wrong[cap_anchor].gate.left+=1;
    assert_eq!(filter(owner,roles,wrong).unwrap_err(),"scheduled HEADER anchor identity");
    for (context,row_base) in [357_978,360_026].into_iter().enumerate() {
        let expected=(0..2048).map(|bit|anchor(owner,1346+context*2048+bit)).collect::<Vec<_>>();
        let actual=raw.iter().filter(|term|(owner*ROWS+row_base..owner*ROWS+row_base+2048)
            .contains(&term.row)).cloned().collect::<Vec<_>>();
        assert_eq!(actual,expected);
        assert!(kept.iter().all(|term|!(owner*ROWS+row_base..owner*ROWS+row_base+2048).contains(&term.row)));
    }
}

/// One real owner, not a synthetic anchor census or an all-owner admission.
#[test]
fn real_owner844670_exact_old_anchor_identity_and_multiplicity() {
    std::thread::Builder::new().stack_size(32*1024*1024).spawn(|| {
        const O:usize=844670;
        let parent=WorkTreeHistoryPlan::compile(1827840,21,[0;32],[0;28]).unwrap();
        let mut raw=Vec::new();
        let counts=parent.visit_slot_terms(O as u64,|t|{raw.push(t);Ok(())}).unwrap();
        assert_eq!(counts.emitted,raw.len());
        let scheduled=Scheduled::eligible08();
        let roles=active(&scheduled,O).unwrap();
        assert_eq!(roles,[true,true,false,false]);
        let mut max=Vec::new();
        let max_counts=scheduled.visit_owner(O,|writer,t| {
            assert!(matches!(writer,Writer::Max{context:0|1,end:844672}));
            max.push(t);Ok(())
        }).unwrap();
        assert_eq!(max_counts.cap,[0,0]);
        let header_rows:BTreeSet<_>=raw.iter().map(|t|t.row).collect();
        let max_rows:BTreeSet<_>=max.iter().map(|t|t.row).collect();
        let overlap:BTreeSet<_>=header_rows.intersection(&max_rows).copied().collect();
        let expected:BTreeSet<_>=(356632..357978).map(|q|O*ROWS+q).collect();
        assert_eq!(overlap,expected,"all real HEADER/MAX intersecting rows");
        // Exhaustively compare all occurrences, including any second non-anchor
        // term on an intersecting row. Equality includes every gate field.
        let actual:Vec<_>=raw.iter().filter(|t|overlap.contains(&t.row)).cloned().collect();
        let exact:Vec<_>=(0..1346).map(|k|anchor(O,k)).collect();
        assert_eq!(actual,exact,"exact old-anchor terms and multiplicity");
        let mut replacement_count=BTreeMap::new();
        for t in max.iter().filter(|t|overlap.contains(&t.row)) {
            let k=t.row-O*ROWS-356632;
            let w=O*WIDTH+999424+k;
            assert_eq!(t.gate,Gate{left:w,right:w,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()});
            *replacement_count.entry(t.row).or_insert(0usize)+=1;
        }
        assert_eq!(replacement_count.len(),1346);
        assert!(replacement_count.values().all(|n|*n==1));
        // Existing fail-closed filter also certifies the entire four-band old
        // anchor census and rejects extra consumers of these helper wires.
        let (kept,retired)=filter(O,roles,raw.clone()).unwrap();
        assert_eq!(retired,[673,673,0,0]);
        assert_eq!(kept,raw.iter().filter(|t|!expected.contains(&t.row)).cloned().collect::<Vec<_>>());
        assert!(kept.iter().all(|t|!max_rows.contains(&t.row)));
        let max_anchor_occurrences:Vec<_>=raw.iter().filter(|t| {
            let g=&t.gate;
            (999424..1000770).contains(&(g.left%WIDTH)) ||
                (999424..1000770).contains(&(g.right%WIDTH))
        }).cloned().collect();
        assert_eq!(max_anchor_occurrences,exact,"no extra old MAX anchors/consumers outside set");
        let first=raw.iter().position(|t|t.row==O*ROWS+356632).unwrap();
        let mut altered=raw.clone();altered[first].gate.c1=-Fr::one();
        assert_eq!(filter(O,roles,altered).unwrap_err(),"scheduled HEADER anchor identity");
        let mut duplicate=raw.clone();duplicate.push(raw[first].clone());
        assert_eq!(filter(O,roles,duplicate).unwrap_err(),"duplicate scheduled HEADER anchor");
        let mut extra=raw.clone();let mut t=raw[first].clone();t.row=O*ROWS+475135;extra.push(t);
        assert_eq!(filter(O,roles,extra).unwrap_err(),"additional scheduled helper HEADER consumer");
        println!("C180_OWNER844670_ANCHOR_PASS header_terms={} unique_header_rows={} max_terms={:?} max_unique_rows={} overlap_rows=1346 local_rows=[356632,357978) global_rows=[{},{}] exact_old_anchor_terms=1346 retained_terms={} retired={:?} old_anchor_hash={} kept_hash={} no_extra_old_max_consumers=true altered_c1_rejected=true duplicate_rejected=true extra_consumer_rejected=true",
            raw.len(),header_rows.len(),max_counts.max,max_rows.len(),O*ROWS+356632,O*ROWS+357977,
            kept.len(),retired,crate::work_tree_layout::hash_terms(&actual),crate::work_tree_layout::hash_terms(&kept));
    }).unwrap().join().unwrap();
}

#[test]
fn exact_anchor_census_rejects_isolated_fields_omission_duplicate_and_extra_consumer() {
    let o=1048702;let roles=[true,true,false,false];
    let (kept,counts)=filter(o,roles,anchors(o)).unwrap();
    assert_eq!(counts,[673,673,0,0]);assert_eq!(kept.len(),4096);
    for field in 0..7 {
        let mut bad=anchors(o);let t=&mut bad[0];
        match field{0=>t.row-=1,1=>t.gate.left+=1,2=>t.gate.right=0,
            3=>t.gate.c0=Fr::one(),4=>t.gate.c1=Fr::zero(),
            5=>t.gate.c2=Fr::one(),_=>t.gate.c3=Fr::one()}
        assert!(filter(o,roles,bad).is_err(),"isolated anchor field {field}");
    }
    let mut missing=anchors(o);missing.remove(0);assert!(filter(o,roles,missing).is_err());
    let mut duplicate=anchors(o);duplicate.push(anchor(o,0));assert!(filter(o,roles,duplicate).is_err());
    // An inactive anchor may not disappear merely because no writer claims it.
    let mut missing=anchors(o);missing.remove(1346);assert!(filter(o,roles,missing).is_err());
    for right in [false,true] {
        let mut bad=anchors(o);let mut t=anchor(o,0);t.row=o*524288+356631;
        if right{t.gate.left=o*1048576;t.gate.right=o*1048576+999424;}
        bad.push(t);assert!(filter(o,roles,bad).is_err());
    }
    assert!(filter(1<<21,roles,Vec::new()).is_err());
    let (retained,counts)=filter(3072,[false;4],anchors(3072)).unwrap();
    assert_eq!(counts,[0;4]);assert_eq!(retained,anchors(3072));
    let target=retained.iter().find(|t|t.row==3072*524288+356632).unwrap();
    assert_eq!(target.gate.c1,Fr::one());
}

fn literal_owner_weights(eligible:bool,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    let mut out=[Fr::zero();4];
    for c in 0..2 {
        let end=if c==0{1827840}else if eligible{1810842}else{1827775};
        let guard=if eligible{if c==0{1810905}else{1810842}}else if c==0{1827838}else{1827775};
        let mut epochs=vec![(844672usize,844672usize)];
        epochs.extend((844673..=end).step_by(128).map(|a|(a,(a+127).min(end))));
        let mut caps=BTreeSet::new();
        for &(a,b) in &epochs {
            let o=b-2;out[c]+=eq(r,o)*eq(u,o)*eq(v,o);
            if a+1088<=guard{caps.insert((b+1088).min(guard)-1);}
        }
        assert_eq!(epochs.len(),if eligible && c==1{7550}else{7682});
        assert_eq!(caps.len(),if eligible{if c==0{7542}else{7541}}else if c==0{7674}else{7673});
        for o in caps{out[2+c]+=eq(r,o)*eq(u,o)*eq(v,o);}
    }out
}

#[test]
fn global_retirement_matches_independent_full_calendar_and_literal_local_anchor_sums() {
    let plan=Scheduled::new();
    let r=point(40,3);let u=point(41,41);let v=point(41,109);
    let weights=literal_owner_weights(false,&r[19..],&u[20..],&v[20..]);
    assert_eq!(plan.anchor_owner_weights(&r[19..],&u[20..],&v[20..]).unwrap(),weights);
    let ranges=[(356632,999424,673),(357305,1000097,673),
        (357978,1000770,2048),(360026,1002818,2048)];
    let expected:Fr=ranges.iter().enumerate().map(|(j,&(a,b,n))|{
        weights[j]*(0..n).map(|k|eq(&r[..19],a+k)*eq(&u[..20],b+k)*eq(&v[..20],0)).sum::<Fr>()
    }).sum();
    assert_eq!(retired_coefficient(&plan,&r,&u,&v).unwrap(),expected);
    assert!(retired_coefficient(&plan,&r[..39],&u,&v).is_err());
    for (o,a,b) in [(1048702usize,356632,999424),(845759,357978,1000770)] {
        let r=bits(o*524288+a,40);let u=bits(o*1048576+b,41);let v=bits(o*1048576,41);
        assert_eq!(retired_coefficient(&plan,&r,&u,&v).unwrap(),Fr::one());
        assert!(retired_coefficient(&plan,&r,&u,&bits(0,41)).unwrap().is_zero(),"global-zero placeholder mutant");
        assert!(retired_coefficient(&plan,&r,&u,&bits(o*1048576+b,41)).unwrap().is_zero(),"helper-zero placeholder mutant");
    }
}

#[test]
fn c182_eligible_retirement_off_cube_matches_literal_calendar_and_local_anchors() {
    let plan=Scheduled::eligible08();
    let r=point(40,13);let u=point(41,61);let v=point(41,139);
    let weights=literal_owner_weights(true,&r[19..],&u[20..],&v[20..]);
    assert_eq!(plan.anchor_owner_weights(&r[19..],&u[20..],&v[20..]).unwrap(),weights);
    let expected:Fr=RANGES.iter().enumerate().map(|(j,&(a,b,n))| {
        weights[j]*(0..n).map(|k|eq(&r[..19],a+k)*eq(&u[..20],b+k)*eq(&v[..20],0)).sum::<Fr>()
    }).sum();
    assert_eq!(retired_coefficient(&plan,&r,&u,&v).unwrap(),expected);
    assert_ne!(retired_coefficient(&Scheduled::new(),&r,&u,&v).unwrap(),expected,
        "Diagnostic08 schedule substitution must change retirement");
}

#[test]
fn c182_eligible_clipped_tails_and_adjacent_owners_match_literal_retirement() {
    let plan=Scheduled::eligible08();
    let cases=[(844670usize,[true,true,false,false]),
        (1810814,[true,true,false,false]),(1810815,[false;4]),
        (1810840,[false,true,false,false]),(1810841,[false,false,false,true]),
        (1810842,[false;4]),(1810879,[false,false,true,false]),
        (1810903,[false;4]),(1810904,[false,false,true,false]),(1810905,[false;4]),
        (1827773,[false;4]),(1827774,[false;4]),(1827837,[false;4]),
        (1827838,[true,false,false,false]),(1827839,[false;4])];
    for (o,roles) in cases {
        assert_eq!(active(&plan,o).unwrap(),roles,"actual schedule owner {o}");
        let (kept,retired)=filter(o,roles,anchors(o)).unwrap();
        assert_eq!(retired,std::array::from_fn(|j|if roles[j]{RANGES[j].2}else{0}));
        assert_eq!(kept.len()+retired.iter().sum::<usize>(),5442);
        let (removed,expected_kept):(Vec<_>,Vec<_>)=anchors(o).into_iter().partition(|t| {
            RANGES.iter().enumerate().any(|(j,&(a,_,n))|roles[j] && (a..a+n).contains(&(t.row%ROWS)))
        });
        assert_eq!(kept,expected_kept,"literal retained anchors owner {o}");
        for (j,&(a,b,n)) in RANGES.iter().enumerate() {
            for k in [0,n-1] {
                let r=bits(o*ROWS+a+k,40);let u=bits(o*WIDTH+b+k,41);let v=bits(o*WIDTH,41);
                let literal:Fr=removed.iter().filter(|t|t.row==o*ROWS+a+k
                    && t.gate.left==o*WIDTH+b+k && t.gate.right==o*WIDTH).map(|t|t.gate.c1).sum();
                assert_eq!(literal,if roles[j]{Fr::one()}else{Fr::zero()});
                assert_eq!(retired_coefficient(&plan,&r,&u,&v).unwrap(),literal,
                    "owner {o} role {j} anchor {k}");
                let mut wrong_owner=v.clone();wrong_owner[20..].copy_from_slice(&bits(o+1,21));
                assert!(retired_coefficient(&plan,&r,&u,&wrong_owner).unwrap().is_zero(),
                    "adjacent right-owner selector {o}");
            }
        }
    }
    // This is the original isolated mismatch: the old diagnostic tail retires
    // MAX1 here, whereas the Eligible08 HEADER anchor must remain present.
    let o=1827773;let r=bits(o*ROWS+357305,40);
    let u=bits(o*WIDTH+1000097,41);let v=bits(o*WIDTH,41);
    assert!(retired_coefficient(&plan,&r,&u,&v).unwrap().is_zero());
    assert_eq!(retired_coefficient(&Scheduled::new(),&r,&u,&v).unwrap(),Fr::one());
}

fn basis(p:&[Fr])->Vec<Fr>{
    let mut out=Vec::with_capacity(1<<p.len());out.push(Fr::one());
    for z in p {let n=out.len();for i in 0..n{let old=out[i];out[i]=old*(Fr::one()-z);out.push(old*z);}}out
}
struct LocalPoint {r:Vec<Fr>,u:Vec<Fr>,v:Vec<Fr>}
impl LocalPoint {
    fn new(r:&[Fr],u:&[Fr],v:&[Fr])->Self{Self{r:basis(r),u:basis(u),v:basis(v)}}
    fn sum<'a>(&self,terms:impl IntoIterator<Item=&'a Term>,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
        let mut owner_r=BTreeMap::new();let mut owner_u=BTreeMap::new();let mut owner_v=BTreeMap::new();
        let mut out=[Fr::zero();4];
        for t in terms {
            let g=&t.gate;
            let w=self.r[t.row%524288]*self.u[g.left%1048576]*self.v[g.right%1048576]
                **owner_r.entry(t.row/524288).or_insert_with(||eq(&r[19..],t.row/524288))
                **owner_u.entry(g.left/1048576).or_insert_with(||eq(&u[20..],g.left/1048576))
                **owner_v.entry(g.right/1048576).or_insert_with(||eq(&v[20..],g.right/1048576));
            for (a,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*a+=w*c;}
        }out
    }
}

#[test]
fn real_roster_header_preserves_short_and_mature_a4_and_matches_merged_coefficients() {
    let parent=WorkTreeHistoryPlan::compile(1827840,21,[7;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();let scheduled=Scheduled::new();
    let merge=Merge::new(&roster,&scheduled).unwrap();
    let lr=point(19,7);let lu=point(20,43);let lv=point(20,113);
    let local=LocalPoint::new(&lr,&lu,&lv);
    for (o,wanted,mature,short) in [
        (3072usize,[0,0,0,0],0,8192),
        (844672,[0,0,0,0],8192,0),
        (1048702,[673,673,0,0],0,0),
        (845759,[0,0,2048,2048],0,0),
    ] {
        let header=merge.header_terms(o).unwrap();assert_eq!(header.retired,wanted);
        assert_eq!(header.roster.omitted_short_a4,short);assert_eq!(header.roster.omitted_mature_a4,mature);
        assert_eq!(header.roster.omitted_worktree,78194);
        let a4=header.terms.iter().filter(|t|(348440..356632).contains(&(t.row%524288))).count();
        assert_eq!(a4,if mature+short>0{0}else{8192});
        let mut added=Vec::new();scheduled.visit_owner(o,|w,t|{added.push((w,t));Ok(())}).unwrap();
        let header_rows:BTreeSet<_>=header.terms.iter().map(|t|t.row).collect();
        assert!(added.iter().all(|(_,t)|!header_rows.contains(&t.row)),"HEADER/scheduled duplicate ROW");
        // X reads are retained verbatim. ROW ownership does not reserve read ports.
        let mut r=lr.clone();r.extend(bits(o,21));let mut u=lu.clone();u.extend(bits(o,21));
        let mut v=lv.clone();v.extend(bits(o,21));
        let actual=local.sum(header.terms.iter().chain(added.iter().map(|(_,t)|t)),&r,&u,&v);
        let mut expected=roster.header_coefficients(&r,&u,&v).unwrap();
        let literal_ranges=[(356632,999424,673),(357305,1000097,673),
            (357978,1000770,2048),(360026,1002818,2048)];
        let removed:Fr=literal_ranges.iter().enumerate().filter(|(j,_)|wanted[*j]>0)
            .map(|(_, &(a,b,n))|(0..n).map(|k|eq(&lr,a+k)*eq(&lu,b+k)*eq(&lv,0)).sum::<Fr>()).sum();
        expected[1]-=removed;
        for (a,b) in expected.iter_mut().zip(scheduled.coefficients(&r,&u,&v).unwrap()){*a+=b;}
        assert_eq!(actual,expected,"owner{o} independent literal retirement differential");
        assert_eq!(merge.coefficients(&r,&u,&v).unwrap(),expected,"owner{o} global formula");
        if o==3072 {
            let wrong=parent.coefficients(&r,&u,&v).unwrap();
            assert_ne!(wrong,roster.header_coefficients(&r,&u,&v).unwrap(),"parent-only HEADER resurrects short A4");
        }
        println!("owner{o}: retained={}, shortA4={short}, matureA4={mature}, retired={wanted:?}",header.terms.len());
    }
    assert!(merge.header_terms(1<<21).is_err());
    assert!(merge.coefficients(&point(39,1),&point(41,2),&point(41,3)).is_err());
}

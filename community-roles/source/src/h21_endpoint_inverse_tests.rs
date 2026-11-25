//! Public endpoint-calendar controls and bounded literal differentials.
//! The scoped global-zero checks do not traverse the complete global output.
use super::*;
use ark_serialize::CanonicalSerialize;
use std::collections::{BTreeMap,BTreeSet};

fn parameters() -> [PublicMapParameters;2] {
    CutDescriptor::eligible08().terminals().map(|terminal| PublicMapParameters {
        terminal,exponent:55,lower:LowerSelector {
            source:LowerSource::HeaderDifficulty {height:841_729},branch:LowerBranch::Pivot(54),
        },
    })
}
fn maps() -> [Map;2] {
    parameters().map(|p|Map::new_modern_global_u_selected_lower(
        p.terminal as u64,21,p.exponent,p.lower).unwrap())
}
fn candidates(family:Family,left:bool,source:usize) -> DestinationSet {
    candidate_destinations(&Scheduled::eligible08(),&maps(),family,left,source).unwrap()
}

#[test]
fn c595_endpoint_fixed_calendars_retain_clipped_max_and_cap_edges() {
    for left in [true,false] {
        let header=candidates(Family::Header,left,1_810_840);
        assert_eq!(header.len(),1);assert!(header.contains(1_810_840));
    }
    let clipped=candidates(Family::Max(1),true,1_810_840);
    assert!(clipped.contains(1_810_814));
    assert!(!clipped.contains(1_810_712),"terminal MAX predecessor is not source-128");
    assert!(!candidates(Family::Max(1),false,1_810_840).contains(1_810_814));
    for context in 0..2 {
        assert!(candidates(Family::Cap(context),true,844_670).contains(845_759));
        assert!(!candidates(Family::Cap(context),false,844_670).contains(845_759));
    }
    assert!(candidates(Family::Cap(0),true,1_809_790).contains(1_810_879));
    assert!(candidates(Family::Cap(1),true,1_809_790).contains(1_810_841));
    assert!(candidates(Family::Cap(0),true,1_809_918).contains(1_810_904));
    assert_eq!(845_759%128,63);
    assert!(!candidates(Family::Cap(0),true,844_670).contains(845_823),
        "the old residue127 endpoint is not the ordinary Cap destination");
}

#[test]
fn c595_endpoint_map_import_calendar_matches_actual_anchors() -> Result<(),String> {
    let scheduled=Scheduled::eligible08();let maps=maps();
    for context in 0..2 {
        for destination in [1_983usize,9_151,417_727] {
            for import in maps[context].imports(destination as u64)? {
                let inverse=candidate_destinations(&scheduled,&maps,Family::Map(context),true,import.owner as usize)?;
                assert!(inverse.contains(destination),"context {context}, source {}, destination {destination}",import.owner);
            }
            let right=candidate_destinations(&scheduled,&maps,Family::Map(context),false,destination)?;
            assert_eq!(right.len(),1);assert!(right.contains(destination));
        }
        for (source,destination) in [(1_982,1_983),(1_022,3_007),(1_023,1_983),(9_150,9_151)] {
            assert!(candidate_destinations(&scheduled,&maps,Family::Map(context),true,source)?.contains(destination));
        }
        assert_eq!(maps[context].tier(417_727)?,None,"q407 is the canonical hole");
        assert!(!candidate_destinations(&scheduled,&maps,Family::Map(context),true,417_726)?.contains(417_727));
        assert!(!matches!(candidate_destinations(&scheduled,&maps,Family::Map(context),false,0)?,DestinationSet::All));
    }
    Ok(())
}

#[test]
fn c595_endpoint_global_zero_and_nonzero_candidate_bounds_are_separate() -> Result<(),String> {
    let scheduled=Scheduled::eligible08();let maps=maps();
    for family in families() {
        let right=candidate_destinations(&scheduled,&maps,family,false,0)?;
        assert_eq!(matches!(right,DestinationSet::All),matches!(family,Family::Score(_)|Family::Slack(_)),
            "physical global-zero family {family:?}");
        assert!(!matches!(candidate_destinations(&scheduled,&maps,family,true,0)?,DestinationSet::All));
    }
    for source in [1usize,1_022,1_023,1_982,9_150,417_790,844_670,845_758,845_759,
        845_887,845_951,1_809_790,1_809_918,1_810_814,1_810_840,1_810_841,1_810_904,N,SLOTS-1] {
        for left in [true,false] {
            let mut count=0usize;
            for family in families() {
                let inverse=candidate_destinations(&scheduled,&maps,family,left,source)?;
                assert!(!matches!(inverse,DestinationSet::All),"nonzero source {source}, family {family:?}");
                count=count.checked_add(inverse.len()).ok_or("test candidate count overflow")?;
            }
            assert!(count<=45,"source {source}, left={left}, family candidates={count}");
        }
    }
    for context in 0..2 {
        assert_eq!(candidate_destinations(&scheduled,&maps,Family::Slack(context),false,1)?.len(),0);
    }
    Ok(())
}

#[test]
fn c595_endpoint_candidate_geometry_and_context_refusals() {
    let scheduled=Scheduled::eligible08();let maps=maps();
    for source in [SLOTS,usize::MAX] {
        for left in [true,false] {
            assert!(candidate_destinations(&scheduled,&maps,Family::Header,left,source).is_err());
        }
    }
    for family in [Family::Max(2),Family::Cap(2),Family::Map(2),Family::Score(2),Family::Slack(2)] {
        assert!(candidate_destinations(&scheduled,&maps,family,true,0).is_err());
    }
    assert!(candidate_destinations(&Scheduled::new(),&maps,Family::Header,true,1).is_err());
    let mut wrong=maps.clone();let p=parameters()[0];
    wrong[0]=Map::new_modern_global_u_selected_lower(1_827_775,21,p.exponent,p.lower).unwrap();
    assert!(candidate_destinations(&scheduled,&wrong,Family::Header,true,1).is_err());
}

#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord)]
struct TermKey {family:usize,row:usize,left:usize,right:usize,coefficients:[[u8;32];4]}
fn family_slot(family:Family) -> usize {families().iter().position(|f|*f==family).unwrap()}
fn key(family:Family,term:&Term) -> TermKey {
    let encode=|value:Fr| {
        let mut bytes=[0u8;32];value.serialize_compressed(&mut bytes[..]).unwrap();bytes
    };
    TermKey {family:family_slot(family),row:term.row,left:term.gate.left,right:term.gate.right,
        coefficients:[term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3].map(encode)}
}
fn add_key(multiset:&mut BTreeMap<TermKey,usize>,family:Family,term:&Term) {
    *multiset.entry(key(family,term)).or_insert(0)+=1;
}
fn selected(family:Family,term:&Term,owner:usize) -> bool {
    let first=match family {Family::Header=>0,Family::Max(c)=>[356_632,357_305][c],
        Family::Cap(c)=>[357_978,360_026][c],Family::Map(c)=>MAP_ROW[c],
        Family::Score(c)=>SCORE_ROW[c],Family::Slack(c)=>SLACK_ROW[c]};
    term.gate.left/WIDTH!=owner || term.gate.right/WIDTH!=owner || term.gate.right==0
        || (first..first+3).contains(&(term.row%ROWS))
}
fn bits(index:usize,n:usize) -> Vec<Fr> {(0..n).map(|b|Fr::from(((index>>b)&1)as u64)).collect()}
fn arbitrary(n:usize,seed:u64) -> Vec<Fr> {(0..n).map(|b|Fr::from(seed+13*b as u64)).collect()}

#[test]
fn h21_role1_global_right_zero_literal_score_slack() -> Result<(),String> {
    let maps=maps();
    let u=arbitrary(41,7);
    let cut=CutDescriptor::eligible08();
    let mut owners=vec![0,ANCHOR_OWNERS[0],ANCHOR_OWNERS[1],FIRST_MODERN_OWNER,
        FIRST_MODERN_OWNER+128,SLOTS-1];
    for guard in cut.guards(){owners.extend([guard-2,guard-1,guard]);}
    for owner in owners {
        // Two adjacent row owners at a non-Boolean high coordinate. All other
        // owners have zero weight. Their literal score ports include foreign lefts.
        let mut r=arbitrary(19,3);r.extend(bits(owner&!1,21));r[19]=Fr::from(5u64);
        let mut literal=[Fr::zero();4];
        for destination in [owner&!1,owner|1] {
            for (c,map) in maps.iter().enumerate(){
                let mut collect=|t:Term|{
                    if t.gate.right/WIDTH==0 {
                        assert_eq!(t.gate.right,0,"unexpected local right in physical owner zero");
                        let w=scalar_equality(&r,t.row)*scalar_equality(&u,t.gate.left);
                        for (k,g) in literal.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]){*k+=w*g;}
                    }
                };
                emit_score_owner(destination,c,map,|term|{collect(term);Ok(())})?;
                if destination==cut.guards()[c]-1 {
                    visit_terminal_bits(destination,c,&[0x5a;29],|t|{assert!(t.gate.right>=WIDTH);collect(t);Ok(())})?;
                }
                for mut t in bank53_slack::slack_zero_terms(destination,c)? {
                    let local=t.row-(destination*ROWS+409_600+c*32_768+bank53_slack::SLACK_ROW_OFFSET);
                    t.row=destination*ROWS+SLACK_ROW[c]+local;
                    collect(t);
                }
            }
        }
        assert_eq!([literal[2],literal[3]],[Fr::zero();2]);
        let left_value=Fr::from(owner as u64+17);
        assert_eq!(score_slack_right_zero_d(&maps,&r,&u,left_value)?,literal[0]+literal[1]*left_value);
    }
    for (context,map) in maps.iter().enumerate() {
        let owner=ANCHOR_OWNERS[0];let bit=map.binding().e;
        let r=bits(owner*ROWS+V_ALIAS_ROW[context]+bit,40);
        let u=bits(owner*WIDTH+SCORE_X[context]+224+bit,41);
        assert_eq!(score_slack_right_zero_d(&maps,&r,&u,Fr::zero())?,-Fr::one());
        assert_eq!(score_slack_right_zero_d(&maps,&r,&u,Fr::one())?,Fr::zero());
    }
    Ok(())
}

#[test]
#[ignore="actual H21 public roster; separate bounded native Job"]
fn h21_role1_global_right_zero_preserves_physical_complement() -> Result<(),String> {
    let parent=WorkTreeHistoryPlan::compile(N as u64,21,[0x31;32],[0x42;28])?;
    let roster=H21StructuralRoster::from_public(&parent,parameters())?;
    let mut expected:[Vec<Term>;11]=std::array::from_fn(|_|Vec::new());
    // Right owner zero has exactly one destination (zero) for each of the
    // seven retained families. Collect its literal source independently.
    roster.visit_owner_terms(0,|family,term|{
        if !matches!(family,Family::Score(_)|Family::Slack(_)) && term.gate.right/WIDTH==0 {
            expected[family_slot(family)].push(term);
        }
        Ok(())
    })?;
    // Each family retains its literal emission order and multiplicity.
    let mut seen=[0usize;11];
    let physical=roster.visit_role1_physical_endpoint(false,0,|f,t|{
        assert!(!matches!(f,Family::Score(_)|Family::Slack(_)));
        assert!(t.gate.right<WIDTH);
        let i=family_slot(f);
        assert_eq!(expected[i].get(seen[i]),Some(&t));
        seen[i]+=1;
        Ok(())
    })?;
    assert!(physical.terms>0 && expected.iter().flatten().any(|t|t.gate.right==0));
    assert_eq!(seen,expected.each_ref().map(Vec::len));
    assert_eq!(physical.family_terms,seen);
    Ok(())
}
fn scalar_equality(point:&[Fr],mut index:usize) -> Fr {
    let mut result=Fr::one();
    for coordinate in point {
        result*=if index&1==0 {Fr::one()-coordinate}else{*coordinate};index>>=1;
    }
    assert_eq!(index,0);result
}
// Independent scalar recurrence for the literal oracle's local tables. No
// producer callback, Boolean conversion or wiring helper computes these.
fn equality_table(point:&[Fr]) -> Vec<Fr> {
    let mut values=vec![Fr::one()];
    for coordinate in point {
        let width=values.len();values.resize(2*width,Fr::zero());
        for index in 0..width {
            let old=values[index];values[index]=old*(Fr::one()-coordinate);
            values[index+width]=old*coordinate;
        }
    }
    for index in [0,1,values.len()/2,values.len()-1] {
        assert_eq!(values[index],scalar_equality(point,index));
    }
    values
}
struct IndependentFold {
    local:[Vec<Fr>;3],rh:Vec<Fr>,uh:Vec<Fr>,vh:Vec<Fr>,
    high:BTreeMap<(usize,usize,usize),Fr>,
}
impl IndependentFold {
    fn new(r:&[Fr],u:&[Fr],v:&[Fr]) -> Self {
        Self {local:[equality_table(&r[..19]),equality_table(&u[..20]),equality_table(&v[..20])],
            rh:r[19..].to_vec(),uh:u[20..].to_vec(),vh:v[20..].to_vec(),high:BTreeMap::new()}
    }
    fn owner(&mut self,owner:usize) {self.rh=bits(owner,21);self.high.clear();}
    fn term(&mut self,term:&Term) -> [Fr;4] {
        let owners=(term.row/ROWS,term.gate.left/WIDTH,term.gate.right/WIDTH);
        let high=*self.high.entry(owners).or_insert_with(||scalar_equality(&self.rh,owners.0)
            *scalar_equality(&self.uh,owners.1)*scalar_equality(&self.vh,owners.2));
        let scale=high*self.local[0][term.row%ROWS]*self.local[1][term.gate.left%WIDTH]
            *self.local[2][term.gate.right%WIDTH];
        [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3].map(|c|scale*c)
    }
}
fn accumulate(sum:&mut [Fr;4],term:[Fr;4]) {for (a,b) in sum.iter_mut().zip(term) {*a+=b;}}

#[test]
#[ignore="one actual H21 public roster; separate 2 GiB/120 s diagnostic trial required"]
fn c595_endpoint_actual_multisets_and_nonboolean_contractions_match() -> Result<(),String> {
    let parent=WorkTreeHistoryPlan::compile(N as u64,21,[0x31;32],[0x42;28])?;
    let roster=H21StructuralRoster::from_public(&parent,parameters())?;
    // Every inverse query below intersects the same canonical calendar with
    // one explicit row owner. Global-zero coverage is SCOPED, never a claim
    // that all 2^21 destinations or the full global output were traversed.
    let destinations=[1_983usize,9_151,417_727,417_790,845_758,845_759,845_887,845_951,
        1_810_814,1_810_840,1_810_841,1_810_904,N,SLOTS-1];
    for owner in destinations {
        let mut expected:[BTreeMap<usize,BTreeMap<TermKey,usize>>;2]=std::array::from_fn(|_|BTreeMap::new());
        let mut sources:[BTreeSet<usize>;2]=std::array::from_fn(|_|BTreeSet::new());
        roster.visit_owner_terms(owner,|family,term| {
            assert_eq!(term.row/ROWS,owner);
            for (side,source) in [term.gate.left/WIDTH,term.gate.right/WIDTH].into_iter().enumerate() {
                sources[side].insert(source);
                if selected(family,&term,owner) {add_key(expected[side].entry(source).or_default(),family,&term);}
            }
            Ok(())
        })?;
        for side in 0..2 {for &source in &sources[side] {
            let mut actual=BTreeMap::new();let mut callbacks=0usize;
            let census=roster.visit_endpoint_selected(side==0,source,Some(&[owner]),|family,term| {
                callbacks+=1;assert_eq!(term.row/ROWS,owner);
                assert_eq!(if side==0 {term.gate.left/WIDTH}else{term.gate.right/WIDTH},source);
                if selected(family,&term,owner) {add_key(&mut actual,family,&term);}Ok(())
            })?;
            assert_eq!(census.terms,callbacks);assert_eq!(census.family_terms.iter().sum::<usize>(),callbacks);
            assert!(census.destinations_visited()<=11);
            assert_eq!(actual,expected[side].get(&source).cloned().unwrap_or_default(),
                "row owner {owner}, source {source}, left={}",side==0);
        }}
    }
    let calls=std::cell::Cell::new(0usize);
    let error=roster.visit_endpoint(true,845_759,|_,_| {calls.set(calls.get()+1);Err("isolated endpoint sink error".into())}).unwrap_err();
    assert_eq!(error,"isolated endpoint sink error");assert_eq!(calls.get(),1);
    for owners in [vec![845_759,845_759],vec![845_760,845_759],vec![SLOTS]] {
        let calls=std::cell::Cell::new(0usize);
        assert!(roster.visit_endpoint_selected(true,845_759,Some(&owners),|_,_| {calls.set(calls.get()+1);Ok(())}).is_err());
        assert_eq!(calls.get(),0);
    }
    let calls=std::cell::Cell::new(0usize);
    assert!(roster.visit_endpoint(true,SLOTS,|_,_| {calls.set(calls.get()+1);Ok(())}).is_err());
    assert_eq!(calls.get(),0);
    let mut r=arbitrary(19,2);r.extend(bits(0,21));
    let u=arbitrary(41,7);let v=arbitrary(41,11);let mut fold=IndependentFold::new(&r,&u,&v);
    for owner in [9_151usize,845_759,845_887,1_810_841,N] {
        r[19..].copy_from_slice(&bits(owner,21));fold.owner(owner);
        let mut expected=[Fr::zero();4];let mut sources:[BTreeSet<usize>;2]=std::array::from_fn(|_|BTreeSet::new());
        roster.visit_owner_terms(owner,|_,term| {
            sources[0].insert(term.gate.left/WIDTH);sources[1].insert(term.gate.right/WIDTH);
            accumulate(&mut expected,fold.term(&term));Ok(())
        })?;
        assert_eq!(roster.coefficients(&r,&u,&v)?,expected,"global coefficient row owner {owner}");
        for side in 0..2 {
            let mut inverse=[Fr::zero();4];
            for &source in &sources[side] {
                roster.visit_endpoint_selected(side==0,source,Some(&[owner]),|_,term| {
                    accumulate(&mut inverse,fold.term(&term));Ok(())
                })?;
            }
            assert_eq!(inverse,expected,"full endpoint partition owner {owner}, left={}",side==0);
        }
    }
    println!("C595_ENDPOINT_SCOPE row_owner_slices=14 contraction_owners=5 global_zero=scoped_only full_global_traversal=false");
    Ok(())
}

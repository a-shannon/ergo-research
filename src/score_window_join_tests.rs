use super::*;
use crate::bank53_map_score;
use std::collections::BTreeSet;

fn fixture(rising:bool)->Inputs {
    Inputs{upper:[10u64.into(),11u64.into()],max:[[5u64.into(),6u64.into()],[5u64.into(),6u64.into()]],
        previous:if rising{[100u64.into(),100u64.into()]}else{[1000000u64.into(),1000000u64.into()]}}
}
fn number(s:&SparseX,o:usize,q:usize,n:usize)->u64 {
    (0..n).fold(0,|a,k|{let b=s.cells.get(&(o*1048576+q+k)).unwrap().value;
        assert!(b.is_zero()||b.is_one());if b.is_one(){assert!(k<64);a|(1u64<<k)}else{a}})
}
fn fail(staged:Staged,prefix:&str){
    let mut dest=Destination::default();let before=dest.clone();let e=publish(&mut dest,staged).unwrap_err();
    assert!(e.starts_with(prefix),"expected{prefix}: {e}");assert_eq!(dest,before);
}

#[test]
fn global_specs_real_cap_streams_and_literal_physical_coordinates(){
    let terms=canonical().unwrap();assert_eq!(terms.len(),59856);
    for c in 0..2 {for j in 0..2 {let o=845759+j;let sp=spec(c,o).unwrap();
        assert!(!sp.first&&!sp.terminal&&sp.active&&sp.reducing&&!sp.origin_one);
        assert_eq!(sp.maturity,if c==0{4995}else{2090});
        let mode=if c==0{Mode::Sampled}else{Mode::Exact};
        let plan=ScorePlan::new(1,COUNT[c],vec![Profile{mode,prefix:COUNT[c],expected:0u8.into(),guard:GuardPolicy::Disabled}]).unwrap();
        assert!(bank53_map_score::score_owner_terms(&plan,o,c).unwrap_err().contains("active modern Score"));
        // Independent full-plan physical tuple oracle, including previous left
        // owner and current right owner. No window first/terminal substitution.
        let mut literal=Vec::new();plan.emit_owner(0,o,|mut t| {
            let q=t.row-o*8192;let lo=t.gate.left/2048;let ro=t.gate.right/2048;
            t.row=o*524288+[487421,502652][c]+q;
            t.gate.left=lo*1048576+[677501,685693][c]+t.gate.left%2048;
            t.gate.right=ro*1048576+[677501,685693][c]+t.gate.right%2048;literal.push(t);
        }).unwrap();
        let actual=terms.iter().filter(|p|p.family==Family::Score(c,j)).map(|p|p.term.clone()).collect::<Vec<_>>();
        assert_eq!(actual,literal);assert_eq!(actual.len(),8032);
        assert_eq!(actual.iter().map(|t|t.row).collect::<BTreeSet<_>>().len(),3082);
        assert!(actual.iter().any(|t|t.gate.left/1048576==o-1));
        let w=terms.iter().filter(|p|p.family==Family::W(c,j)).collect::<Vec<_>>();assert_eq!(w.len(),448);
        for k in 0..224 {
            assert_eq!(w[2*k].term.row,o*524288+[491694,506925][c]+k);
            assert_eq!(w[2*k].term.gate.left,o*1048576+[677501,685693][c]+k);
            assert_eq!(w[2*k+1].term.gate.right,(o-1)*1048576+987450+k);
            assert_eq!((w[2*k].term.gate.c1,w[2*k+1].term.gate.c2),(Fr::one(),-Fr::one()));
        }
        let v=terms.iter().filter(|p|p.family==Family::V(c,j)).collect::<Vec<_>>();assert_eq!(v.len(),65);
        for k in 0..65 {let t=&v[k].term;
            assert_eq!(t.row,o*524288+[491629,506860][c]+k);
            assert_eq!(t.gate.left,o*1048576+[677725,685917][c]+k);
            assert_eq!(t.gate.right,[845759,845887][j]*1048576+[1001510,1003558][c]+k);
        }
        let caps=terms.iter().filter(|p|p.family==Family::Cap(c,j)).collect::<Vec<_>>();assert_eq!(caps.len(),6419);
        let foreign=caps.iter().filter(|p|p.term.gate.left/1048576!=[845759,845887][j]).collect::<Vec<_>>();
        assert_eq!(foreign.len(),224);
        for (k,t) in foreign.into_iter().enumerate(){assert_eq!(t.term.gate.left,[844670,844798][j]*1048576+[999424,1000097][c]+k);}
        assert_eq!(caps.iter().map(|p|p.term.row).collect::<BTreeSet<_>>().len(),2503);
        let expected_names=cap::GROUPS.iter().filter(|(n,_,_)|*n!="q-anchors").map(|(n,_,_)|*n).collect::<BTreeSet<_>>();
        assert_eq!(caps.iter().map(|p|p.group).collect::<BTreeSet<_>>(),expected_names);
    }}
    assert_eq!(census(&terms).values().sum::<usize>(),59856);
    assert_eq!(shape().len(),18179);
    println!("C124A_SOURCE owners=2 contexts=2 terms=59856 score_span=4208 score_terms=8032 cap_terms=6419 x_cells=18179 conditional=true");
}

#[test]
fn same_x_two_step_scalar_oracle_and_atomic_publish_both_branches(){
    for rising in [true,false] {let input=fixture(rising);let staged=stage(&input).unwrap();
        validate(&staged).unwrap();
        for c in 0..2 {let mut previous=if rising{100u64}else{1000000};let maturity=if c==0{4995}else{2090};
            for j in 0..2 {let d=[5u64,6][j];let floor=3*d/2;let v=floor.next_power_of_two();let w=[10u64,11][j];
                let a=w+maturity*v;let expected=previous.max(a);let selected=a>previous;
                assert_eq!(v,[8,16][j]);
                assert_eq!(number(&staged.x,[845759,845887][j],[1001510,1003558][c],65),v);
                assert_eq!(number(&staged.x,845759+j,[677501,685693][c]+289,224),w);
                assert_eq!(number(&staged.x,845759+j,[677501,685693][c]+1093,225),previous);
                assert_eq!(number(&staged.x,845759+j,[677501,685693][c]+1318,225),expected);
                assert_eq!(number(&staged.x,845759+j,[677501,685693][c]+1768,1),u64::from(selected));
                if j==1{assert_eq!(selected,rising);}previous=expected;
            }
        }
        let expected=staged.x.clone();let mut destination=Destination::default();publish(&mut destination,staged.clone()).unwrap();
        assert_eq!(destination.window.as_ref().unwrap().x,expected);
        let before=destination.clone();assert!(publish(&mut destination,staged).is_err());assert_eq!(destination,before);
        println!("C124A_JOIN rising_second={rising} contexts=2 owners=2 residuals=zero published_once=true");
    }
}

#[test]
fn real_tuple_coordinate_and_omission_mutants_fail_census_before_residual(){
    let honest=stage(&fixture(true)).unwrap();
    for family in [Family::W(0,0),Family::V(0,0),Family::Score(0,0),Family::Cap(0,0)] {
        let index=honest.terms.iter().position(|p|p.family==family).unwrap();
        let mut bad=honest.clone();bad.terms.remove(index);fail(bad,"census");
        let mut bad=honest.clone();bad.terms.retain(|p|p.family!=family);fail(bad,"census");
        let mut bad=honest.clone();bad.terms.push(bad.terms[index].clone());fail(bad,"census");
    }
    let w=honest.terms.iter().position(|p|p.family==Family::W(0,0)&&!p.term.gate.c2.is_zero()).unwrap();
    let v=honest.terms.iter().position(|p|p.family==Family::V(0,1)).unwrap();
    let p=honest.terms.iter().position(|p|p.family==Family::Score(0,1)&&p.group=="predecessor"&&p.term.gate.left/1048576==845759).unwrap();
    for (i,delta) in [(w,224isize),(w,448),(w,-288),(w,1048576),(w,-1048576),
        (v,2048),(v,128*1048576),(v,1),(p,1048576),(p,-1048576)] {
        let mut bad=honest.clone();if i==w||i==v{bad.terms[i].term.gate.right=bad.terms[i].term.gate.right.checked_add_signed(delta).unwrap();}
        else{bad.terms[i].term.gate.left=bad.terms[i].term.gate.left.checked_add_signed(delta).unwrap();}fail(bad,"census");
    }
    for k in 0..honest.reads.len() {let mut bad=honest.clone();bad.reads[k].context^=1;fail(bad,"census");}
    for delta in [-1isize,1] {let mut bad=honest.clone();bad.reads[0].owner=bad.reads[0].owner.checked_add_signed(delta).unwrap();fail(bad,"census");}
    let cap=honest.terms.iter().position(|p|p.family==Family::Cap(0,0)&&p.term.gate.left/1048576==844670).unwrap();
    for delta in [673,128*1048576] {let mut bad=honest.clone();bad.terms[cap].term.gate.left+=delta;fail(bad,"census");}
    let mut bad=honest.clone();bad.reads.remove(0);fail(bad,"census");
    let mut bad=honest.clone();bad.terms[0].term.row+=1;fail(bad,"census");
}

#[test]
fn actual_x_mutants_fail_closed_and_duplicate_equal_writes_are_atomic(){
    let honest=stage(&fixture(true)).unwrap();
    // Real X mutations exercise Cap input/V, conditional previous, produced
    // predecessor/current and sw/v aliases on the shared witness.
    for (o,q) in [(844670,999424),(845759,1001510+3),(845887,1001510+4),
        (845758,677501+1318),(845759,677501+1318),(845760,677501+1318),
        (845759,677501),(845760,677501+224),(845758,987450)] {
        let mut bad=honest.clone();let cell=bad.x.cells.get_mut(&x(o,q)).unwrap();cell.value=Fr::one()-cell.value;fail(bad,"residual");
    }
    let mut bad=honest.clone();bad.x.cells.remove(&x(845758,987450));fail(bad,"census");
    let mut bad=honest.clone();bad.x.cells.get_mut(&0).unwrap().value=Fr::one();fail(bad,"census");
    let mut bad=honest.clone();bad.x.cells.get_mut(&x(845759,677501)).unwrap().value=Fr::from(2u64);fail(bad,"census");
    let mut bad=honest.clone();bad.x.cells.get_mut(&x(845759,677501)).unwrap().writer=Writer::Score(1,0);fail(bad,"census");
    let mut sx=honest.x.clone();let before=sx.clone();let values=(0..224).map(|k|sx.cells[&x(845758,987450+k)].value).collect::<Vec<_>>();
    assert!(sx.write(845758,987450,224,Writer::Upper(0),&values).unwrap_err().contains("duplicate"));assert_eq!(sx,before);
    for values in [vec![Fr::zero();223],vec![Fr::from(2u64);224]] {let mut sx=SparseX::default();let before=sx.clone();
        assert!(sx.write(845758,987450,224,Writer::Upper(0),&values).is_err());assert_eq!(sx,before);}
    for mutation in 0..5 {let mut input=fixture(true);match mutation {
        0=>input.upper[1]=9u64.into(),1=>input.upper[1]=BigUint::from(1u8)<<224,
        2=>input.max[0][0]=0u8.into(),3=>input.previous[0]=BigUint::from(1u8)<<225,
        4=>input.max[0][0]=BigUint::from(1u8)<<224,_=>unreachable!()}
        let mut dest=Destination::default();let before=dest.clone();assert!(join(&mut dest,&input).is_err());assert_eq!(dest,before);
    }
}

use super::*;
use std::collections::BTreeSet;

fn setup()->Plan{
    let map=|n|Map::new_modern_global_u_selected_lower(n,21,55,LowerSelector{
        source:LowerSource::HeaderDifficulty{height:841729},branch:LowerBranch::Pivot(54)}).unwrap();
    Plan::new(&[map(CUT[0]),map(CUT[1])],[
        SourceIdentity{frame:[127;32],cut:CUT[0],parent_root:None},
        SourceIdentity{frame:[127;32],cut:CUT[1],parent_root:None}]).unwrap()
}
fn input(p:&Plan,t1:BigUint,t2:BigUint)->Inputs{
    Inputs{endpoints:std::array::from_fn(|c|std::array::from_fn(|j|Endpoint{
        source:p.sources[c].clone(),height:HEIGHT[j],owner:UPPER_OWNER[j],local:987450,
        value:if j==0{t1.clone()}else{t2.clone()}})),modern_w:&t2+1u8,
        modern_v:[BigUint::from(16u8),BigUint::from(32u8)]}
}
fn flip(s:&mut Staged,address:usize){let b=&mut s.x.cells.get_mut(&address).unwrap().value;*b=Fr::one()-*b;}
fn assert_atomic_reject(p:&Plan,s:Staged){let mut d=Destination::default();let before=d.clone();
    assert!(publish(p,&mut d,s).is_err());assert_eq!(d,before);}

fn session_stage()->(Plan,Staged){
    let (session,caller)=crate::c146_phase1_session::Session::fixture().unwrap();
    session.stage_for_local_ledger_join(&caller).unwrap()
}

#[test]
fn exact_boundary_both_branches_ties_widths_and_consumer(){
    let p=setup();
    let max=(BigUint::from(1u8)<<224usize)-2u8;
    let pairs=[(BigUint::from(10u8),BigUint::from(427978u64)),
        (BigUint::from(10u8),&p.u[0]*30000u64),
        (BigUint::from(10u8),BigUint::from(10u8)+&p.u[0]*10000u64),
        (BigUint::from(10u8),BigUint::from(10u8)+&p.u[0]*(43410u64-23155)),
        (BigUint::from(10u8),BigUint::from(10u8)+&p.u[1]*(17867u64-9548)),
        (&max-427968u64,max)];
    let mut seen=[[false;3];2];
    for (t1,t2) in pairs {let i=input(&p,t1.clone(),t2.clone());let s=stage(&p,&i).unwrap();validate(&p,&s).unwrap();
        for c in 0..2 {
            // Independent scalar oracle: no comparator d/s or producer outputs.
            let first=&t1+&p.u[c]*[43410u64,17867][c];
            let middle=&t2+&p.u[c]*[23155u64,9548][c];
            let expected=std::cmp::max(first.clone(),middle.clone());
            seen[c][if first>middle{0}else if first<middle{1}else{2}]=true;
            assert_eq!(s.x.word_read(BOUNDARY,BASE[c]+1318,225,Writer::Summary(c)).unwrap(),expected);
            let mut d=Destination::default();publish(&p,&mut d,s.clone()).unwrap();assert_eq!(d.boundary(c).unwrap(),expected);
            let frozen=d.clone();assert!(join(&p,&mut d,&i).is_err());assert_eq!(d,frozen);
        }
    }
    assert!(seen.iter().flatten().all(|b|*b));
    println!("C127A_BOUNDARY_PASS branches=2 ties=2 contexts=2 fixtures=6");
}

#[test]
fn typed_source_map_and_range_fail_closed(){
    let p=setup();let good=input(&p,BigUint::from(5u8),BigUint::from(427973u64));
    // Equal values cannot hide a wrong typed owner/height/context/cut/source.
    for axis in 0..7 {let mut bad=good.clone();let e=&mut bad.endpoints[0][0];match axis{
        0=>e.owner+=1,1=>e.height+=1,2=>e.local=987226,3=>e.local=987674,
        4=>e.source=p.sources[1].clone(),5=>e.source.frame[0]^=1,_=>e.value=BigUint::from(1u8)<<224usize};
        let mut d=Destination::default();let before=d.clone();assert!(join(&p,&mut d,&bad).is_err());assert_eq!(d,before);
    }
    let canonical=|n,e|Map::new_modern_global_u_selected_lower(n,21,e,LowerSelector{
        source:LowerSource::HeaderDifficulty{height:841729},branch:LowerBranch::Pivot(54)}).unwrap();
    for maps in [[canonical(CUT[0],55),canonical(CUT[0],55)],
        [Map::new_modern_global_u(CUT[0],21,55).unwrap(),canonical(CUT[1],55)],
        [canonical(CUT[0],54),canonical(CUT[1],55)]] {
        assert!(Plan::new(&maps,p.sources.clone()).is_err());
    }
    let mut sources=p.sources.clone();sources[1].parent_root=Some([1;32]);
    assert!(Plan::new(&[canonical(CUT[0],55),canonical(CUT[1],55)],sources).is_err());
    let mut bad=good.clone();bad.endpoints[0][1].value=BigUint::from(4u8);bad.endpoints[1][1].value=BigUint::from(4u8);
    assert!(stage(&p,&bad).is_err());
    let equal=input(&p,BigUint::from(5u8),BigUint::from(5u8));assert!(stage(&p,&equal).is_err());
    let short=input(&p,BigUint::from(5u8),BigUint::from(427972u64));assert!(stage(&p,&short).is_err());
    let mut flat=good;flat.modern_w=flat.endpoints[0][1].value.clone();assert!(stage(&p,&flat).is_err());
}

#[test]
fn real_x_and_term_mutants_are_rejected_atomically(){
    let p=setup();let near=(BigUint::from(1u8)<<224usize)-2u8;
    let s=stage(&p,&input(&p,&near-427968u64,near)).unwrap();validate(&p,&s).unwrap();
    // Actual sparse-X perturbations independently exercise R/d/s and predecessor.
    for c in 0..2 {for local in [BASE[c]+1318,BASE[c]+1542,BASE[c]+1543,BASE[c]+1768] {
        let mut bad=s.clone();flip(&mut bad,x(BOUNDARY,local));assert!(validate(&p,&bad).unwrap_err().starts_with("residual"));assert_atomic_reject(&p,bad);
    }
        let mut bad=s.clone();flip(&mut bad,x(MODERN,BASE[c]+1093));assert!(validate(&p,&bad).unwrap_err().starts_with("residual"));assert_atomic_reject(&p,bad);
    }
    // Context V values are distinct conditional premises. Swap their real sv
    // cells while preserving the other producer cells; aliases must detect it.
    let mut bad=s.clone();for k in 0..65 {
        let a=x(MODERN,BASE[0]+224+k);let b=x(MODERN,BASE[1]+224+k);
        let av=bad.x.cells[&a].value;let bv=bad.x.cells[&b].value;
        bad.x.cells.get_mut(&a).unwrap().value=bv;bad.x.cells.get_mut(&b).unwrap().value=av;
    }
    assert!(validate(&p,&bad).unwrap_err().starts_with("residual"));assert_atomic_reject(&p,bad);
    // Perturb a real source cell with spare work-gap margin: the source ranges
    // and monotonicity still pass, leaving the actual comparator equations.
    let mut ports=input(&p,BigUint::from(10u8),BigUint::from(1000000u64));
    ports.modern_w+=2u8;
    let ports=stage(&p,&ports).unwrap();validate(&p,&ports).unwrap();
    for owner in [417789,845757] {
        let mut bad=ports.clone();flip(&mut bad,x(owner,987450));
        assert_eq!(validate(&p,&bad).unwrap_err(),format!("residual ROW {}",row(845758,490222)));
        for c in 0..2 {for q in [ROW_BASE[c]+2801,ROW_BASE[c]+2802] {
            if owner==845757&&q==ROW_BASE[c]+2802{continue;}
            let residual=bad.terms.iter().filter(|p|p.term.row==row(BOUNDARY,q)).fold(Fr::zero(),|sum,p|{
                let g=&p.term.gate;let a=bad.x.cells[&g.left].value;let b=bad.x.cells[&g.right].value;
                sum+g.c0+g.c1*a+g.c2*b+g.c3*a*b});
            assert!(!residual.is_zero());
        }}assert_atomic_reject(&p,bad);
    }
    for c in 0..2 {for kind in 0..7 {let mut bad=s.clone();let k=bad.terms.iter().position(|p|p.relation==Relation::Summary(c)&&p.term.row==row(BOUNDARY,ROW_BASE[c]+2801)).unwrap();
        let w=bad.terms.iter().position(|p|p.relation==Relation::Summary(c)
            &&p.term.row==row(BOUNDARY,ROW_BASE[c]+2801)
            &&p.term.gate.left==x(845757,987450)&&!p.term.gate.c1.is_zero()).unwrap();
        assert_eq!(bad.terms[w].term.gate.c1,Fr::one());
        match kind{
            0=>bad.terms[k].term.gate.c0+=scalar(&p.u[c]), // one wrong maturity unit
            1=>bad.terms[w].term.gate.left=x(845758,987450), // wrong owner, active W operand
            2=>bad.terms[w].term.gate.left=x(845757,987226), // wrong local, active W operand
            3=>bad.terms[k].term.row=row(BOUNDARY,ROW_BASE[1-c]+2801),
            4=>{bad.terms.remove(k);},5=>bad.terms.retain(|p|p.relation!=Relation::Summary(c)),
            _=>bad.terms.push(bad.terms[k].clone()),
        }
        assert_eq!(validate(&p,&bad).unwrap_err(),"census ordered complete terms");assert_atomic_reject(&p,bad);
    }}
    let mut bad=s.clone();bad.x.cells.remove(&x(BOUNDARY,BASE[0]+1318));assert_eq!(validate(&p,&bad).unwrap_err(),"census X writer shape");assert_atomic_reject(&p,bad);
    let mut bad=s.clone();bad.x.cells.get_mut(&x(BOUNDARY,BASE[0]+1318)).unwrap().value=Fr::from(2u8);assert_atomic_reject(&p,bad);
    let mut sx=s.x.clone();let before=sx.clone();let bits=vec![Fr::zero();225];
    assert!(sx.write(BOUNDARY,BASE[0]+1318,Writer::Summary(0),&bits).is_err());assert_eq!(sx,before);
    let current=s.x.cells[&x(BOUNDARY,BASE[0]+1318)].value;
    assert!(sx.write(BOUNDARY,BASE[0]+1318,Writer::Summary(0),&[current]).is_err());assert_eq!(sx,before);
}

#[test]
fn literal_rows_ports_and_global_modern_predecessor(){
    let p=setup();let terms=canonical(&p).unwrap();
    for c in 0..2 {
        let summary=terms.iter().filter(|p|p.relation==Relation::Summary(c)).collect::<Vec<_>>();
        assert_eq!(summary.len(),1802);
        let rows=summary.iter().map(|p|p.term.row).collect::<std::collections::BTreeSet<_>>();
        let start=[488739,503970][c];let eq=[490222,505453][c];
        let expected=(start..start+451).chain(eq..eq+2).map(|q|row(BOUNDARY,q)).collect();assert_eq!(rows,expected);
        assert!(rows.iter().all(|r|(*r%(1<<19))>=[487421,502652][c]&&(*r%(1<<19))<[491629,506860][c]));
        let modern=terms.iter().filter(|p|p.relation==Relation::Modern(c)).collect::<Vec<_>>();
        let predecessor=modern.iter().filter(|p|p.term.gate.left/(1<<20)==BOUNDARY).collect::<Vec<_>>();
        assert_eq!(predecessor.len(),225);
        for (k,piece) in predecessor.iter().enumerate(){assert_eq!(piece.term.gate.left,x(BOUNDARY,[678819,687011][c]+k));assert_eq!(piece.term.gate.c1,-Fr::one());}
        let s=modern_spec(c).unwrap();assert!(!s.first&&!s.terminal&&s.reducing);assert_eq!(s.maturity,[4995,2090][c]);
        // Actual canonical emitter with first=true removes every predecessor read.
        let mut wrong=s;wrong.first=true;let mut reads=0;score::emit_local(&wrong,|p|{if p.previous{reads+=1;}}).unwrap();assert_eq!(reads,0);
        let mut bad=stage(&p,&input(&p,BigUint::from(1u8),BigUint::from(427969u64))).unwrap();
        bad.terms.retain(|p|!(p.relation==Relation::Modern(c)&&p.term.gate.left/(1<<20)==BOUNDARY));
        assert_eq!(validate(&p,&bad).unwrap_err(),"census ordered complete terms");
    }
}

#[test]
fn score_cap_value_projection_exports_exact_validated_x_support(){
    let (plan,staged)=session_stage();
    let structural=project_local_score_cap(&plan,&staged).unwrap();
    let values=project_local_score_cap_values(&plan,&staged).unwrap();
    assert_eq!(values.owner(),MODERN);
    assert_eq!(values.rows(),structural.rows.as_slice());
    assert_eq!(values.x_claims(),structural.x.as_slice());
    assert_eq!(values.sources(),&plan.sources);
    assert_eq!(values.bindings(),&plan.bindings);

    let mut referenced=BTreeSet::new();
    for claim in &structural.rows {
        referenced.insert(claim.term.gate.left);
        referenced.insert(claim.term.gate.right);
    }
    for claim in &structural.x {
        referenced.extend(claim.start..claim.end);
    }
    let exported=values.cells().iter().map(|cell|cell.address()).collect::<BTreeSet<_>>();
    assert_eq!(exported,referenced);
    assert!(values.cells().iter().all(|cell|{
        cell.address()<(1usize<<41)
            && (cell.value().is_zero()||cell.value().is_one())
    }));
    for claim in values.x_claims(){
        assert!((claim.start..claim.end).all(|address|values.cells().iter().any(|cell|
            cell.address()==address)));
    }
}

#[test]
fn score_cap_value_projection_rejects_value_omission_and_provenance_mutants(){
    let (plan,staged)=session_stage();
    let structural=project_local_score_cap(&plan,&staged).unwrap();

    // Changing a real Score bit leaves the structural ROW/range declaration
    // intact, but the source stage no longer satisfies its emitted equations.
    let mut changed_score=staged.clone();
    let score_claim=structural.x.iter().find(|claim|
        claim.relation==ScoreCapRelation::ModernScore(0)).unwrap();
    let score_address=structural.rows.iter().filter(|claim|
        claim.relation==ScoreCapRelation::ModernScore(0)).find_map(|claim|{
        let gate=&claim.term.gate;
        if (score_claim.start..score_claim.end).contains(&gate.left)
            &&(!gate.c1.is_zero()||!gate.c3.is_zero()) {Some(gate.left)}
        else if (score_claim.start..score_claim.end).contains(&gate.right)
            &&(!gate.c2.is_zero()||!gate.c3.is_zero()) {Some(gate.right)}
        else {None}
    }).unwrap();
    let score_cell=changed_score.x.cells.get_mut(&score_address).unwrap();
    score_cell.value=Fr::one()-score_cell.value;
    assert_eq!(structural.x,project_local_score_cap(&plan,&staged).unwrap().x);
    assert!(project_local_score_cap_values(&plan,&changed_score).is_err());

    // Omit one X coordinate actually referenced by an exported row.
    let mut missing_x=staged.clone();
    let needed=structural.rows.iter().find_map(|claim|{
        [claim.term.gate.left,claim.term.gate.right].into_iter()
            .find(|address|*address!=0)
    }).unwrap();
    assert!(missing_x.x.cells.remove(&needed).is_some());
    assert!(project_local_score_cap_values(&plan,&missing_x).is_err());

    // Preserve a Cap bit but change its staged writer identity.
    let mut wrong_writer=staged;
    let cap_claim=structural.x.iter().find(|claim|
        matches!(claim.relation,ScoreCapRelation::Cap(_))).unwrap();
    let cap_cell=wrong_writer.x.cells.get_mut(&cap_claim.start).unwrap();
    cap_cell.writer=Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Cap{
        context:1,origin:MODERN+1,
    });
    assert!(project_local_score_cap_values(&plan,&wrong_writer).is_err());
}

use super::*;
use ark_ff::PrimeField;
use std::collections::BTreeSet;

fn literal(f:Family)->(usize,usize,usize) {
    match f {
        Family::Map(0)=>(409600,477074,10347),Family::Map(1)=>(442368,492305,10347),
        Family::Score(0)=>(425984,487421,4208),Family::Score(1)=>(458752,502652,4208),
        Family::V(0)=>(430192,491629,65),Family::V(1)=>(462960,506860,65),
        Family::W(0)=>(438272,491694,224),Family::W(1)=>(471040,506925,224),
        Family::Slack(0)=>(438496,491918,387),Family::Slack(1)=>(471264,507149,387),
        _=>panic!("test context"),
    }
}
fn gate_words(g:&Gate)->[u64;18] {
    let mut out=[0;18];out[0]=g.left as u64;out[1]=g.right as u64;
    for (j,f) in [g.c0,g.c1,g.c2,g.c3].into_iter().enumerate() {
        out[2+j*4..6+j*4].copy_from_slice(&f.into_bigint().0);
    }out
}
fn representatives()->Vec<usize> {
    vec![0,1,959,1983,3007,4031,5055,6079,7103,8127,9151,417727,843711,844735,
        417790,417791,417792,841727,844670,844798,845758,845759,845760,845887,
        1048511,1048512,1048574,1826686,1826814,1827582,1827647,1827710,1827773,
        1827774,1827775,1827837,1827838,1827839,2097151]
}

#[test]
fn conditional_score_and_w_adapters_match_legacy_sources_guard_stays_closed() {
    let s=Sources::new().unwrap();
    for c in 0..2 {
        assert_eq!(s.maps[c].binding().e,55);assert!(s.maps[c].binding().parent_root.is_none());
        for o in [0,1,1983,9151,417727,845758,COUNT[c],2097151] {
            let mut direct=s.score_terms(c,o).unwrap();direct.extend(s.w_terms(c,o).unwrap());
            direct.extend(bank53_map_score::slack_zero_terms(o,c).unwrap());
            let mut legacy=bank53_map_score::score_owner_terms(&s.score[c],o,c).unwrap();
            assert_eq!(direct.len(),legacy.len());
            let mut normalized=0usize;
            for (index,(canonical,old)) in direct.iter().zip(legacy.iter_mut()).enumerate() {
                let work_row=o*ROWS+438272+c*32768..o*ROWS+438272+c*32768+224;
                let canonical_work=o>0&&work_row.contains(&canonical.row)
                    &&canonical.gate.left/WIDTH==o-1
                    &&(987450..987674).contains(&(canonical.gate.left%WIDTH))
                    &&canonical.gate.right==0&&canonical.gate.c1==-Fr::one()
                    &&canonical.gate.c2.is_zero();
                if canonical_work {
                    assert_eq!(old.row,canonical.row,"W alias ROW at index {index}");
                    assert_eq!(old.gate.left,0,"legacy W left at index {index}");
                    assert_eq!(old.gate.right,canonical.gate.left,"W work X at index {index}");
                    assert_eq!(old.gate.c0,canonical.gate.c0,"W c0 at index {index}");
                    assert_eq!(old.gate.c1,Fr::zero(),"legacy W c1 at index {index}");
                    assert_eq!(old.gate.c2,canonical.gate.c1,"legacy W c2 at index {index}");
                    assert_eq!(old.gate.c3,canonical.gate.c3,"W c3 at index {index}");
                    *old=canonical.clone();normalized+=1;
                } else {
                    assert_eq!(canonical,&*old,"non-W-alias exact tuple at index {index}");
                }
            }
            let expected_work_aliases:usize=if o>0&&s.score[c].spec(0,o).unwrap().active {224}else{0};
            assert_eq!(normalized,expected_work_aliases,"isolated legacy W normalization count");
            assert_eq!(direct,legacy,"all terms exact after only W orientation normalization");
        }
        for o in [845759,845760,COUNT[c]-1] {
            assert!(bank53_map_score::score_owner_terms(&s.score[c],o,c).unwrap_err().contains("active modern Score"));
            let score=s.score_terms(c,o).unwrap();assert!(!score.is_empty());
            assert!(score.iter().any(|t|t.gate.left/WIDTH==o-1),"real predecessor source must remain foreign");
        }
    }
}

#[test]
fn coactive_representative_streams_relocate_only_rows_and_have_distinct_writers() {
    let s=Sources::new().unwrap();let owners=representatives();let mut tiers=BTreeSet::new();
    let mut source_terms=0usize;let mut max_owner_terms=0usize;let mut scheduled=BTreeSet::new();
    for o in &owners {
        let before=s.source_owner(*o).unwrap();let after=s.stage_owner(*o).unwrap();
        assert_eq!(before.terms.len(),after.terms.len());source_terms+=before.terms.len();
        max_owner_terms=max_owner_terms.max(before.terms.len());
        for (a,b) in before.terms.iter().zip(&after.terms) {
            assert_eq!(a.writer,b.writer);assert_eq!(gate_words(&a.term.gate),gate_words(&b.term.gate));
            match a.writer {
                Writer::Relocated(f)=>{
                    let (old,new,span)=literal(f);let q=a.term.row-o*524288-old;
                    assert!(q<span);assert_eq!(b.term.row,o*524288+new+q);
                    check_relocation(f,*o,&a.term,&b.term).unwrap();
                }
                Writer::Scheduled(w)=>{assert_eq!(a.term,b.term);scheduled.insert(w);},
                _=>panic!("unexpected source family"),
            }
        }
        for c in 0..2 {tiers.insert(s.maps[c].tier(*o as u64).unwrap());}
        let mut registry=Registry::new(*o).unwrap();registry.commit(&after).unwrap();
        assert_eq!(registry.x.len(),16384+after.writes.iter().filter(|r|matches!(r.writer,Writer::Scheduled(_)))
            .map(|r|r.wires.len()).sum::<usize>());
    }
    assert_eq!(tiers,(0..=8).map(Some).chain([None]).collect());
    for c in 0..2 {
        assert!(scheduled.iter().any(|w|matches!(w,ScheduledWriter::Max {context,..} if *context==c)));
        assert!(scheduled.iter().any(|w|matches!(w,ScheduledWriter::Cap {context,..} if *context==c)));
        assert!(s.score[c].spec(0,COUNT[c]-1).unwrap().terminal);
        assert!(!s.score[c].spec(0,COUNT[c]).unwrap().active);
    }
    assert!(max_owner_terms<500000);
    println!("C118A_SIGNATURES owners={} source_terms={source_terms} max_owner_terms={max_owner_terms} representative_only=true",owners.len());
}

#[test]
fn emitted_envelopes_preserve_map_holes_and_score_nonreducing_extent() {
    let mut s=Sources::new().unwrap();
    for c in 0..2 {
        // Separate conditional envelope fixture, NOT the selected native binding.
        s.maps[c]=Map::new_modern_global_u_selected_lower(if c==0 {1827840}else{1827775},21,55,
            LowerSelector {source:LowerSource::HeaderDifficulty {height:9153},branch:LowerBranch::Equality}).unwrap();
        let map=bank53_map::map_owner_terms(&s.maps[c],9151,c).unwrap();
        let old=literal(Family::Map(c)).0;let support:BTreeSet<_>=map.iter().map(|t|t.row-9151*524288-old).collect();
        assert_eq!(support.len(),8190);assert_eq!(support.last(),Some(&10346));
        assert!((5757..7898).all(|q|!support.contains(&q)));assert!(!support.contains(&8124));
        for t in &map {let moved=relocate(Family::Map(c),9151,t).unwrap();
            assert_eq!(moved.row-9151*524288, literal(Family::Map(c)).1+(t.row-9151*524288-old));}
        // A separately declared nonreducing conditional Score scope actually
        // emits the final max-mask row; the full-reducing fixture does not.
        s.score[c]=ScorePlan::new(1,COUNT[c],vec![Profile {mode:if c==0 {Mode::Sampled}else{Mode::Exact},
            prefix:845759,expected:BigUint::zero(),guard:GuardPolicy::Disabled}]).unwrap();
        let terms=s.score_terms(c,845759).unwrap();
        let support:BTreeSet<_>=terms.iter().map(|t|t.row-845759*524288-literal(Family::Score(c)).0).collect();
        assert_eq!(support.last(),Some(&4207));
        assert!(relocate(Family::Score(c),845759,&Term {row:845759*524288+literal(Family::Score(c)).0+4208,
            gate:terms[0].gate.clone()}).is_err());
        assert!(bank53_map_score::score_owner_terms(&s.score[c],845759,c).is_err());
    }
}

#[test]
fn atomic_rows_and_x_reservations_reject_equal_cross_writers_and_boundary_faults() {
    let s=Sources::new().unwrap();let o=845759;let honest=s.stage_owner(o).unwrap();
    let mut registry=Registry::new(o).unwrap();registry.commit(&honest).unwrap();
    let before=registry.clone();
    // Same residual writer, multiple genuine monomials: allowed.
    let term=honest.terms.iter().find(|t|matches!(t.writer,Writer::Relocated(Family::V(0)))).unwrap().clone();
    registry.commit(&Batch {owner:o,terms:vec![term.clone(),term.clone()],writes:vec![]}).unwrap();
    assert_eq!(registry,before);
    let mut equal=term.clone();equal.writer=Writer::Daa;
    assert!(registry.commit(&Batch {owner:o,terms:vec![equal],writes:vec![]}).is_err());assert_eq!(registry,before);
    assert!(registry.commit(&Batch {owner:o,terms:vec![],writes:vec![honest.writes[0].clone()]}).is_err());
    assert_eq!(registry,before);
    for f in [Family::Map(0),Family::Score(0),Family::V(0),Family::W(0),Family::Slack(0),
        Family::Map(1),Family::Score(1),Family::V(1),Family::W(1),Family::Slack(1)] {
        let (_,new,len)=literal(f);let mut bad=honest.clone();
        let i=bad.terms.iter().position(|t|t.writer==Writer::Relocated(f)).unwrap();
        for address in [new-1,new+len] {
            bad.terms[i].term.row=o*524288+address;let mut empty=Registry::new(o).unwrap();
            assert!(empty.commit(&bad).is_err(),"family {f:?} boundary {address}");assert!(empty.rows.is_empty());assert!(empty.x.is_empty());
        }
    }
    // An X alias has no writer lease. Reserving its read as a second writer
    // would collide with the genuine Score reservation even at equal values.
    let mut x_bad=honest.clone();x_bad.writes.push(Reservation {writer:Writer::Relocated(Family::W(0)),wires:677501..677502});
    let mut empty=Registry::new(o).unwrap();assert!(empty.commit(&x_bad).is_err());assert!(empty.rows.is_empty());assert!(empty.x.is_empty());
    let mut wrong=Registry::new(o+1).unwrap();assert!(wrong.commit(&honest).is_err());assert!(wrong.rows.is_empty());
}

#[test]
fn relocation_checker_exercises_real_gate_and_owner_mutations() {
    let s=Sources::new().unwrap();let o=1048512;let b=s.source_owner(o).unwrap();
    let original=b.terms.iter().find(|t|t.writer==Writer::Relocated(Family::Score(0))&&t.term.gate.left/WIDTH==o-1).unwrap();
    let good=relocate(Family::Score(0),o,&original.term).unwrap();
    for axis in 0..7 {
        let mut changed=good.clone();match axis {
            0=>changed.gate.left^=1usize<<40,1=>changed.gate.right+=1,
            2=>changed.gate.c0+=Fr::one(),3=>changed.gate.c1+=Fr::one(),
            4=>changed.gate.c2+=Fr::one(),5=>changed.gate.c3+=Fr::one(),_=>changed.row+=1,
        }
        assert!(check_relocation(Family::Score(0),o,&original.term,&changed).is_err());
    }
    assert!(relocate(Family::Score(2),o,&original.term).is_err());
    assert!(relocate(Family::Score(0),o+1,&original.term).is_err());
    assert!(s.stage_owner(2097152).is_err());
}

#[test]
fn old_overlap_is_rejected_against_actual_coactive_daa_before_commit() {
    use crate::{daa_history_roster::{DaaHistoryRoster,OwnerClass,BANKS},work_tree_history_plan::WorkTreeHistoryPlan};
    let s=Sources::new().unwrap();let parent=WorkTreeHistoryPlan::compile(1827840,21,[0;32],[0;28]).unwrap();
    let daa=DaaHistoryRoster::compile(&parent).unwrap();let o=844670;
    assert_eq!(daa.owner_class(o as u64).unwrap(),OwnerClass::Carry);
    let mut terms=Vec::new();daa.visit_owner_terms(o as u64,|term|{terms.push(Tagged {writer:Writer::Daa,term});Ok(())}).unwrap();
    let writes=BANKS.into_iter().map(|(a,b)|Reservation {writer:Writer::Daa,wires:a..b}).collect();
    let mut registry=Registry::new(o).unwrap();registry.commit(&Batch {owner:o,terms,writes}).unwrap();
    let before=registry.clone();let old=s.source_owner(o).unwrap();
    // The old stream violates the sealed relocated ranges and numerically
    // overlaps real DAA. Exhibit the source collision independently of bounds.
    assert!(old.terms.iter().any(|t|t.writer==Writer::Relocated(Family::Map(0))&&registry.rows.contains_key(&t.term.row)));
    assert!(registry.commit(&old).is_err());assert_eq!(registry,before);
    registry.commit(&s.stage_owner(o).unwrap()).unwrap();
    assert!(registry.rows.keys().any(|q|*q==o*524288+477074));
    let mut bad=s.stage_owner(o).unwrap();bad.writes[0].wires.start=671743;
    let mut existing=before.clone();assert!(existing.commit(&bad).is_err());assert_eq!(existing,before);
    // This diagnostic does not contain c117A's HEADER or other proof roles.
}

#[test]
fn old_score_analytic_base_cannot_verify_a_row_only_relocation() {
    let s=Sources::new().unwrap();let o=845759;
    let source=s.score_terms(0,o).unwrap();let t=&source[0];let moved=relocate(Family::Score(0),o,t).unwrap();
    let point=|n:usize,h:usize|(0..h).map(|b|Fr::from(((n>>b)&1)as u64)).collect::<Vec<_>>();
    let old=s.score[0].bank53_coefficients(0,&point(moved.row,40),&point(moved.gate.left,41),&point(moved.gate.right,41)).unwrap();
    assert_eq!(old,[Fr::zero();4]);
    let mut actual=[Fr::zero();4];
    for term in &source {let candidate=relocate(Family::Score(0),o,term).unwrap();
        if (candidate.row,candidate.gate.left,candidate.gate.right)==(moved.row,moved.gate.left,moved.gate.right) {
            for (sum,c) in actual.iter_mut().zip([candidate.gate.c0,candidate.gate.c1,candidate.gate.c2,candidate.gate.c3]) {*sum+=c;}
        }}
    assert_ne!(actual,old,"new ROWs require a separate coefficient-placement adaptation");
}

// Literal height-domain oracle: derive the cap destination from the epoch
// containing i-1088 and clip b+1088 to the context guard. It does not call the
// owner-domain destination helper or reuse its tail/rounding constants.
fn admits_literal_v(c:usize,owner:usize,terms:&[Term])->bool {
    let guard=[1827838usize,1827775][c];
    if owner<845759 || owner>=guard {return terms.is_empty();}
    let origin=owner+1;let q=origin-1088;
    let epoch_start=if q==844672 {844672}else{844800+128*((q-844673)/128)};
    let destination=(epoch_start+1088).min(guard)-1;
    if terms.len()!=65 {return false;}
    terms.iter().enumerate().all(|(k,t)| {
        t.row==owner*524288+[430192,462960][c]+k &&
        t.gate.left==owner*1048576+[677725,685917][c]+k &&
        t.gate.right==destination*1048576+[1001510,1003558][c]+k &&
        [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]==[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()]
    })
}

#[test]
fn v_coordinates_match_independent_height_oracle_and_reject_clipping_owner_padding_faults() {
    let s=Sources::new().unwrap();
    for c in 0..2 {
        let guard=[1827838usize,1827775][c];
        let clipped_start=[1827776usize,1827648][c];
        for owner in [845759,845760,845887,845888,1048511,1048512,clipped_start,guard-1] {
            let honest=s.v_terms(c,owner);
            assert!(admits_literal_v(c,owner,&honest),"context {c}, owner {owner}");
            for axis in 0..13 {
                let mut changed=honest.clone();match axis {
                    0=>changed[0].gate.right^=1usize<<40,
                    1=>changed[0].gate.left^=1usize<<40,
                    2=>changed[0].gate.right+=2048,
                    3=>changed[0].gate.right+=1048576,
                    4=>changed[0].row^=1usize<<39,
                    5=>changed[64].gate.right-=1,
                    6=>{changed.pop();},
                    7=>changed.push(honest[0].clone()),
                    8=>changed[0].gate.c0+=Fr::one(),
                    9=>changed[0].gate.c1+=Fr::one(),
                    10=>changed[0].gate.c2+=Fr::one(),
                    11=>changed[0].gate.c3+=Fr::one(),
                    _=>changed[0].row+=32768,
                }
                assert!(!admits_literal_v(c,owner,&changed),"axis {axis}, context {c}, owner {owner}");
            }
            if owner>=clipped_start {
                assert_eq!(honest[0].gate.right/1048576,guard-1);
                let mut unclipped=honest.clone();
                for t in &mut unclipped {t.gate.right+=128*1048576;}
                assert!(!admits_literal_v(c,owner,&unclipped));
            }
        }
        for owner in [845758,guard,2097151] {
            assert!(s.v_terms(c,owner).is_empty());
            assert!(admits_literal_v(c,owner,&[]));
            assert!(!admits_literal_v(c,owner,&s.v_terms(c,guard-1)));
        }
    }
}

#[test]
fn sparse_score_roster_keeps_only_cell_ends_and_clipped_guards() {
    let s=Sources::new().unwrap();
    let e0=sparse_score_endpoints(0).unwrap();let e1=sparse_score_endpoints(1).unwrap();
    let literal=|c:usize|{
        let (terminal,guard)=if c==0 {(1_827_840usize,1_827_838usize)}else{(1_827_775,1_827_775)};
        let mut origins=vec![845_760usize];let mut epoch_end=844_800usize;
        while epoch_end<=terminal {let q=epoch_end+1088;if q<=guard{origins.push(q);}epoch_end+=128;}
        if origins.last().copied()!=Some(guard){origins.push(guard);}
        origins.into_iter().map(|q|q-1).collect::<Vec<_>>()
    };
    assert_eq!((e0.len(),e1.len()),(7674,7673));
    assert_eq!(e0,literal(0));assert_eq!(e1,literal(1));
    assert_eq!((&e0[..3],&e1[..3]),(&[845759,845887,846015][..],&[845759,845887,846015][..]));
    assert_eq!((*e0.last().unwrap(),*e1.last().unwrap()),(1827837,1827774));
    assert_eq!(e0[e0.len()-2],1827775);assert_eq!(e1[e1.len()-2],1827647);
    assert!(e0.windows(2).take(e0.len()-2).all(|w|w[1]-w[0]==128));
    assert!(e1.windows(2).take(e1.len()-2).all(|w|w[1]-w[0]==128));
    assert!(sparse_score_endpoints(2).is_err());
    // Isolated schedule mutants: endpoint offset, missing first/guard,
    // regular-tail substitution, and cross-context guard swap.
    for mut bad in [e0.clone(),e1.clone()] {
        let context=if bad.len()==e0.len(){0}else{1};
        bad[0]+=1;assert_ne!(bad,literal(context));
        bad=if context==0{e0.clone()}else{e1.clone()};bad.remove(0);assert_ne!(bad,literal(context));
        bad=if context==0{e0.clone()}else{e1.clone()};bad.pop();assert_ne!(bad,literal(context));
        bad=if context==0{e0.clone()}else{e1.clone()};let n=bad.len();bad[n-1]=bad[n-2];assert_ne!(bad,literal(context));
    }
    assert_ne!(e0[e0.len()-1],e1[e1.len()-1]);

    for owner in [845759,845760,845887,1827775,1827776,1827837,1827647,1827648,1827774] {
        let b=s.stage_sparse_score_owner(owner).unwrap();
        let mut registry=Registry::new(owner).unwrap();registry.commit(&b).unwrap();
        for c in 0..2 {
            let retained=sparse_score_endpoints(c).unwrap().binary_search(&owner).is_ok();
            assert_eq!(is_sparse_score_endpoint(c,owner),retained,"O(1) membership owner {owner} context {c}");
            for family in [Family::Score(c),Family::V(c),Family::W(c)] {
                assert_eq!(b.terms.iter().any(|t|t.writer==Writer::Relocated(family)),retained,
                    "owner {owner} context {c} family {family:?}");
            }
            assert_eq!(b.writes.iter().any(|w|w.writer==Writer::Relocated(Family::Score(c))),retained,
                "Score X owner {owner} context {c}");
            assert_eq!(registry.x.contains_key(&[677501,685693][c]),retained,
                "Score X reservation presence owner {owner} context {c}");
            if retained {
                let previous=sparse_previous_endpoint(c,owner).unwrap();
                let score=b.terms.iter().filter(|t|t.writer==Writer::Relocated(Family::Score(c))).collect::<Vec<_>>();
                let rrange=[677501,685693][c]+1318..[677501,685693][c]+1543;
                assert!(score.iter().any(|t|t.term.gate.left/WIDTH==previous&&rrange.contains(&(t.term.gate.left%WIDTH))),
                    "Score R predecessor must name retained owner {previous}");
                if previous!=owner-1 {assert!(!score.iter().any(|t|t.term.gate.left/WIDTH==owner-1
                    &&rrange.contains(&(t.term.gate.left%WIDTH))),"physical predecessor must be absent");}
                let w=b.terms.iter().filter(|t|t.writer==Writer::Relocated(Family::W(c))).collect::<Vec<_>>();
                assert_eq!(w.len(),448);
                let work=w.iter().filter(|t|t.term.gate.c1==-Fr::one()).collect::<Vec<_>>();
                assert_eq!(work.len(),224);
                assert!(work.iter().all(|t|t.term.gate.left/WIDTH==owner-1
                    &&(987450..987674).contains(&(t.term.gate.left%WIDTH))
                    &&t.term.gate.right==0&&t.term.gate.c2.is_zero()),
                    "physical W alias preserves current Score gate orientation");
                let v=b.terms.iter().filter(|t|t.writer==Writer::Relocated(Family::V(c))).collect::<Vec<_>>();
                assert_eq!(v.len(),65);assert!(v.iter().all(|t|t.term.gate.right/WIDTH==owner));
            }
        }
    }
}

use super::*;

fn overlay(owner:usize,score:[bool;2],max:[bool;2],cap:[bool;2])->Overlay {
    Overlay::new(owner,vec![0;BYTES],vec![false;WIDTH],score,max,cap).unwrap()
}
fn install(overlay:&mut Overlay,component:Component,start:usize,n:usize)->Result<(),String> {
    let active=match component {
        Component::Slack(_)=>false,
        Component::Map(context)=>overlay.owner
            <crate::bank53_map::CutDescriptor::eligible08().terminals()[context]-1,
        _=>overlay.owner<N,
    };
    for k in 0..n {
        let nonzero=active && (matches!(k,0|17) || k==n-1);
        overlay.claim(component,overlay.owner*WIDTH+start+k,Fr::from(nonzero as u64))?;
    }
    Ok(())
}
fn fill(overlay:&mut Overlay,cap_limit:usize)->Result<(),String> {
    for c in 0..2 {
        install(overlay,Component::Map(c),MAP_BASE[c],5_757)?;
        install(overlay,Component::Slack(c),MAP_BASE[c]+7_805,387)?;
        if overlay.score[c] {install(overlay,Component::Score(c),SCORE_X[c],2_048)?;}
        if overlay.max[c] {install(overlay,Component::Max(c),MAX_BASE[c],673)?;}
        if overlay.cap[c] {install(overlay,Component::Cap(c),CAP_BASE[c],cap_limit)?;}
    }
    Ok(())
}

#[test]
fn c587_common_overlay_preserves_crossed_map_score_max_cap_values() {
    // Algebraic merger fixture, not a claim that this combined activity is a
    // real calendar owner. The native entry derives its own fixed activity.
    let mut source=overlay(845_887,[true;2],[true;2],[true;2]);
    fill(&mut source,2_048).unwrap();let (bytes,census)=source.finish().unwrap();
    assert_eq!(bytes.len(),131_072);assert_eq!(census.map,[5_757;2]);
    assert_eq!(census.score,[2_048;2]);assert_eq!(census.max,[673;2]);
    assert_eq!(census.cap,[2_048;2]);assert_eq!(census.slack,[387;2]);
    for c in 0..2 {
        for start in [MAP_BASE[c],SCORE_X[c],MAX_BASE[c],CAP_BASE[c]] {
            assert!(bit(&bytes,start));assert!(bit(&bytes,start+17));
        }
        assert!((MAP_BASE[c]+7_805..MAP_BASE[c]+8_192).all(|local|!bit(&bytes,local)));
    }
}

#[test]
fn c587_original_fr_and_zero_duplicate_refusals_are_atomic() {
    let mut source=overlay(844_798,[false;2],[true;2],[false;2]);
    let wire=source.owner*WIDTH+MAP_BASE[0];
    assert_eq!(source.claim(Component::Map(0),wire,Fr::from(2u64)).unwrap_err(),
        "C587 non-Boolean original component Fr");
    assert_eq!(source.census,H21ValueCensus::default());assert!(!bit(&source.written,MAP_BASE[0]));
    source.claim(Component::Map(0),wire,Fr::zero()).unwrap();
    let census=source.census.clone();let bytes=source.bytes.clone();
    assert!(source.claim(Component::Map(0),wire,Fr::zero()).is_err());
    assert_eq!(source.census,census);assert_eq!(source.bytes,bytes);
    assert!(source.claim(Component::Score(0),source.owner*WIDTH+SCORE_X[0],Fr::zero()).is_err());
    assert!(source.claim(Component::Max(1),(source.owner+1)*WIDTH+MAX_BASE[1],Fr::one()).is_err());
    assert!(source.claim(Component::Map(2),wire+1,Fr::zero()).is_err());
    assert!(source.claim(Component::Map(0),source.owner*WIDTH+987_450,Fr::one()).is_err());

    let owner=845_887;let mut cache=ForeignValues::new();
    let score_author=ScoreReplayAuthor {context:0,origin:owner+1,previous_owner:owner-128,
        max_owner:owner-1_089,cap_owner:owner};
    let max_author=MaxReplayAuthor::Scheduled(crate::h21_scheduled_max_cap::Writer::Max {context:1,end:owner+2});
    let mut score_loads=0;let mut max_loads=0;
    for k in 0..225 {
        let wire=owner*WIDTH+SCORE_X[0]+k;
        let (author,value)=cache.score.cell(owner,wire,|requested| {
            assert_eq!(requested,owner);score_loads+=1;
            Ok((0..225).map(|bit|(owner*WIDTH+SCORE_X[0]+bit,score_author,
                if bit==224 {Fr::from(2u64)}else{Fr::one()})).collect())
        }).unwrap().unwrap();
        assert_eq!(author,score_author);
        if k==224 {assert_eq!(value,Fr::from(2u64));assert!(boolean(value).is_err());}
        else {assert_eq!(boolean(value).unwrap(),true);}
    }
    for k in 0..673 {
        let wire=owner*WIDTH+MAX_BASE[1]+k;
        let (author,value)=cache.max.cell(owner,wire,|requested| {
            assert_eq!(requested,owner);max_loads+=1;
            Ok((0..673).map(|bit|(owner*WIDTH+MAX_BASE[1]+bit,max_author,Fr::zero())).collect())
        }).unwrap().unwrap();
        assert_eq!(author,max_author);assert_eq!(value,Fr::zero());
    }
    assert_eq!((score_loads,max_loads),(1,1),"one load per family/owner, not per bit");
    let original=cache.score.cell(owner,owner*WIDTH+SCORE_X[0]+224,
        |_|panic!("original Score bank must remain cached after Fr refusal")).unwrap().unwrap();
    assert_eq!(original,(score_author,Fr::from(2u64)));assert!(boolean(original.1).is_err());
    assert!(cache.score.cell(owner,owner*WIDTH+SCORE_X[0]+225,
        |_|panic!("missing wire must not reload its cached owner")).unwrap().is_none());
}

#[test]
fn c587_base_nonzero_tree_daa_and_incomplete_cap_cannot_be_replaced() {
    let mut source=overlay(1_810_841,[false,true],[false;2],[false,true]);
    let wire=source.owner*WIDTH+CAP_BASE[1];
    set(&mut source.base,CAP_BASE[1],true);
    assert!(source.claim(Component::Cap(1),wire,Fr::one()).is_err());
    set(&mut source.base,CAP_BASE[1],false);source.tree_daa[CAP_BASE[1]]=true;
    assert!(source.claim(Component::Cap(1),wire,Fr::zero()).is_err());
    source.tree_daa[CAP_BASE[1]]=false;
    fill(&mut source,65).unwrap();
    assert_eq!(source.finish().unwrap_err(),"C587 incomplete full-domain component census");
}

#[test]
fn c587_inactive_score_and_padding_are_explicitly_zero() {
    let mut source=overlay(1_810_841,[false,true],[false;2],[false,true]);
    // No inactive Score source is allowed to erase this erroneous base bit.
    set(&mut source.base,SCORE_X[0]+1,true);set(&mut source.bytes,SCORE_X[0]+1,true);
    fill(&mut source,2_048).unwrap();
    assert_eq!(source.finish().unwrap_err(),"C587 nonzero inactive family");
    let mut past_cut=overlay(1_810_904,[true,false],[false;2],[true,false]);
    assert!(past_cut.claim(Component::Map(1),1_810_904*WIDTH+MAP_BASE[1],Fr::one()).is_err());
    let mut padding=overlay(N,[false;2],[false;2],[false;2]);
    let wire=N*WIDTH+MAP_BASE[0];
    assert!(padding.claim(Component::Map(0),wire,Fr::one()).is_err());
    fill(&mut padding,2_048).unwrap();let (bytes,census)=padding.finish().unwrap();
    assert!(bytes.iter().all(|byte|*byte==0));assert_eq!(census.map,[5_757;2]);
    assert_eq!(census.score,[0;2]);assert_eq!(census.max,[0;2]);assert_eq!(census.cap,[0;2]);
    assert_eq!(score_activity(1_810_841).unwrap(),[false,true]);
    assert_eq!(score_activity(1_810_904).unwrap(),[true,false]);
    assert_eq!(score_activity(N).unwrap(),[false;2]);
}

#[test]
fn c589_borrowed_stage_identity_preserves_checks_and_lazy_classification() {
    use crate::daa_history_roster::{DaaHistoryRoster,OwnerClass};
    let plan=WorkTreeHistoryPlan::compile(N as u64,21,[0x31;32],[0x42;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&plan).unwrap();
    let maps=H21EligibleMapStage::source_maps().unwrap();
    let descriptor=crate::bank53_map::CutDescriptor::eligible08();
    let profile=[0x51;32];
    let mask=plan.physical_assignment_replacement_mask(0).unwrap();
    for owner in [0,417_790,845_758,845_759,844_798,1_810_841,N] {
        let stage=H21EligibleMapStage::new_bound(&plan,profile,owner,
            roster.owner_class(owner as u64).unwrap(),descriptor,&maps,&mask).unwrap();
        stage.validate_identity_with_roster(&plan,profile,descriptor,&maps,&roster).unwrap();
        let wrong_profile=[0x52;32];
        let original=stage.validate_identity(&plan,wrong_profile,descriptor,&maps).unwrap_err();
        assert_eq!(stage.validate_identity_with_roster(&plan,wrong_profile,descriptor,&maps,&roster)
            .unwrap_err(),original);
        assert_eq!(stage.validate_identity_with_classifier(&plan,wrong_profile,descriptor,&maps,
            ||panic!("metadata refusal must precede classification/construction")).unwrap_err(),original);
    }
    let owner=0;
    let mut stage=H21EligibleMapStage::new_bound(&plan,profile,owner,OwnerClass::Genesis,
        descriptor,&maps,&mask).unwrap();
    let small=WorkTreeHistoryPlan::compile(3,2,[0x31;32],[0x42;28]).unwrap();
    let foreign=DaaHistoryRoster::compile(&small).unwrap();
    assert_eq!(stage.validate_identity_with_roster(&plan,profile,descriptor,&maps,&foreign).unwrap_err(),
        "c170 borrowed stage roster has another parent");
    stage.class=OwnerClass::Carry;
    assert!(stage.validate_identity_with_roster(&plan,profile,descriptor,&maps,&roster).is_err());
    stage.class=OwnerClass::Genesis;
    let mut wrong_maps=maps.clone();wrong_maps.swap(0,1);
    let calls=std::cell::Cell::new(0usize);
    assert!(stage.validate_identity_with_classifier(&plan,profile,descriptor,&wrong_maps,|| {
        calls.set(calls.get()+1);roster.owner_class(owner as u64)
    }).is_err());
    assert_eq!(calls.get(),1,"Map mismatch remains after the one class check");
}

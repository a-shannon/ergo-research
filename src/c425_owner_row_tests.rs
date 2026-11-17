use super::*;
use crate::{daa_history_layout, daa_integer::Epoch, h21_scheduled_max_cap::Writer,
    work_tree_history_plan::WorkTreeHistoryPlan};
use ark_ff::One;
use std::collections::BTreeMap;

const C425_OWNERS: [(usize,OwnerClass,[bool;4]);4]=[
    (843_776,OwnerClass::Mature(Epoch::Legacy),[false;4]),
    (845_759,OwnerClass::Carry,[false,false,true,true]),
    (1_048_576,OwnerClass::Mature(Epoch::Eip),[false;4]),
    (1_827_840,OwnerClass::Padding,[false;4]),
];
const RANGES:[(usize,usize,usize);4]=[
    (356_632,999_424,673),(357_305,1_000_097,673),
    (357_978,1_000_770,2_048),(360_026,1_002_818,2_048),
];
const FIRST_ROW:usize=356_632;
const FIRST_WIRE:usize=999_424;
const END_WIRE:usize=1_004_866;

#[derive(Clone,Debug)]
struct Tagged {ordinal:usize,term:Term}

fn canonical()->(Vec<Term>,Vec<&'static str>) {
    // Build the cold authority before enabling source-span capture. The first
    // call also initializes the lazy C397 baseline outside the capture window.
    let literal=daa_history_layout::full_header_boundary(None).unwrap();
    let circuit=&literal.base.base.base.boundary;
    assert_eq!(circuit.terms.len(),474_755);
    assert_eq!(circuit.input_len,1<<20);
    assert_eq!(circuit.row_count,1<<19);
    assert_eq!(crate::work_tree_layout::hash_terms(&circuit.terms),
        "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76");
    let terms=circuit.terms.clone();
    crate::c425_span_census::begin_source_spans();
    let joined=daa_history_layout::full_header_boundary(None).unwrap();
    let observed=&joined.base.base.base.boundary.terms;
    let spans=crate::c425_span_census::finish_source_spans();
    assert_eq!(spans.len(),observed.len(),"C425 captured span length changed");
    assert_eq!(observed.len(),terms.len(),"C425 instrumented term count changed");
    if let Some(ordinal)=terms.iter().zip(observed).position(|(a,b)|a!=b) {
        panic!("C425 canonical first tuple divergence ordinal={ordinal} literal={:?} captured={:?}",
            crate::c425_span_census::tuple(&terms[ordinal]),
            crate::c425_span_census::tuple(&observed[ordinal]));
    }
    (terms,spans)
}

fn globalize(owner:usize,term:&Term)->Result<Term,String> {
    let row_base=owner.checked_mul(ROWS).ok_or("C425 source row owner overflow")?;
    let input_base=owner.checked_mul(WIDTH).ok_or("C425 source wire owner overflow")?;
    Ok(Term{row:row_base.checked_add(term.row).ok_or("C425 global row overflow")?,
        gate:crate::gkr::Gate{left:input_base.checked_add(term.gate.left).ok_or("C425 global left overflow")?,
            right:input_base.checked_add(term.gate.right).ok_or("C425 global right overflow")?,
            c0:term.gate.c0,c1:term.gate.c1,c2:term.gate.c2,c3:term.gate.c3}})
}

fn validate_tagged(owner:usize,canonical:&[Term],spans:&[&str],tagged:&[Tagged],stage:&str)
    ->Result<(),String> {
    if canonical.len()!=spans.len(){return Err(format!("C425 {stage} source span/canonical length"));}
    let wire_base=owner.checked_mul(WIDTH).ok_or("C425 endpoint owner base overflow")?;
    let wire_end=wire_base.checked_add(WIDTH).ok_or("C425 endpoint owner end overflow")?;
    let mut previous=None;
    for (output_index,item) in tagged.iter().enumerate() {
        if item.ordinal>=canonical.len(){return Err(format!("C425 {stage} ordinal {} outside canonical stream",item.ordinal));}
        if previous.is_some_and(|ordinal|ordinal>=item.ordinal){
            return Err(format!("C425 {stage} source ordinal is not strictly increasing at output={output_index} previous={previous:?} current={} span={}",item.ordinal,spans[item.ordinal]));
        }
        let expected=globalize(owner,&canonical[item.ordinal])?;
        if !(wire_base..wire_end).contains(&item.term.gate.left)
            || !(wire_base..wire_end).contains(&item.term.gate.right) {
            return Err(format!("C425 {stage} endpoint outside owner-local WIDTH ordinal={} span={} left={} right={} owner_range={wire_base}..{wire_end}",
                item.ordinal,spans[item.ordinal],item.term.gate.left,item.term.gate.right));
        }
        if item.term!=expected {
            return Err(format!("C425 {stage} first tuple divergence output={output_index} ordinal={} span={} expected={:?} observed={:?}",
                item.ordinal,spans[item.ordinal],crate::c425_span_census::tuple(&expected),
                crate::c425_span_census::tuple(&item.term)));
        }
        previous=Some(item.ordinal);
    }
    Ok(())
}

fn collect_tagged<F>(mut visit:F)->Result<Vec<Tagged>,String>
where F:FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String> {
    let mut tagged=Vec::new();
    visit(&mut |term|{
        let ordinal=crate::c425_span_census::current_source_ordinal()
            .ok_or("C425 producer callback missing source ordinal")?;
        tagged.push(Tagged{ordinal,term});Ok(())
    })?;
    Ok(tagged)
}

fn dropped_by_span(before:&[Tagged],after:&[Tagged],spans:&[&str],stage:&str)
    ->Result<BTreeMap<String,usize>,String> {
    let mut dropped=BTreeMap::new();let mut j=0usize;
    for item in before {
        if after.get(j).is_some_and(|kept|kept.ordinal==item.ordinal) {
            if after[j].term!=item.term{return Err(format!("C425 {stage} changed tuple at ordinal {}",item.ordinal));}
            j+=1;
        } else {
            *dropped.entry(spans.get(item.ordinal).ok_or("C425 missing source span")?.to_string()).or_default()+=1;
        }
    }
    if j!=after.len(){return Err(format!("C425 {stage} output is not an ordered source-occurrence subset at ordinal {}",after[j].ordinal));}
    Ok(dropped)
}

fn source_active_mask(schedule:&Scheduled,owner:usize)->Result<[bool;4],String> {
    let mut roles=[false;4];
    schedule.visit_owner(owner,|writer,_|{
        let i=match writer {
            Writer::Max{context,..} if context<2=>context,
            Writer::Cap{context,..} if context<2=>2+context,
            _=>return Err("C425 scheduled owner role outside four source contexts".into()),
        };roles[i]=true;Ok(())
    })?;Ok(roles)
}

fn scheduled_filter(owner:usize,active:[bool;4],source:&[Tagged])
    ->Result<(Vec<Tagged>,[usize;4]),String> {
    if owner>=1<<21{return Err("C425 scheduled owner outside H21".into());}
    let row_base=owner.checked_mul(ROWS).ok_or("C425 scheduled row overflow")?;
    let wire_base=owner.checked_mul(WIDTH).ok_or("C425 scheduled wire overflow")?;
    let mut seen=vec![false;END_WIRE-FIRST_WIRE];let mut retired=[0;4];
    let mut out=Vec::with_capacity(source.len());
    for item in source {
        let q=item.term.row.checked_sub(row_base).filter(|q|*q<ROWS).ok_or("C425 schedule source row owner")?;
        if (FIRST_ROW..FIRST_ROW+seen.len()).contains(&q) {
            let k=q-FIRST_ROW;
            if seen[k]{return Err("C425 duplicate scheduled HEADER anchor".into());}
            if item.term.gate.left!=wire_base+FIRST_WIRE+k || item.term.gate.right!=wire_base
                || [item.term.gate.c0,item.term.gate.c1,item.term.gate.c2,item.term.gate.c3]
                    !=[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()] {
                return Err(format!("C425 scheduled HEADER anchor identity ordinal={}",item.ordinal));
            }
            seen[k]=true;
            let role=RANGES.iter().position(|&(row,_,count)|(row..row+count).contains(&q))
                .ok_or("C425 scheduled anchor range partition")?;
            if active[role]{retired[role]+=1;continue;}
        } else if (FIRST_WIRE..END_WIRE).contains(&(item.term.gate.left%WIDTH))
            || (FIRST_WIRE..END_WIRE).contains(&(item.term.gate.right%WIDTH)) {
            return Err(format!("C425 extra scheduled helper HEADER consumer ordinal={}",item.ordinal));
        }
        out.push(item.clone());
    }
    if seen.iter().any(|present|!*present){return Err("C425 missing scheduled HEADER anchor".into());}
    for role in 0..4 {
        if retired[role]!=(if active[role]{RANGES[role].2}else{0}) {
            return Err(format!("C425 explicit scheduled retirement count role={role}"));
        }
    }
    Ok((out,retired))
}

fn compare_terms(expected:&[Term],observed:&[Term],source_ordinals:Option<&[usize]>,spans:Option<&[&str]>,label:&str) {
    let shared=expected.len().min(observed.len());
    if let Some(i)=(0..shared).find(|&i|expected[i]!=observed[i]) {
        let ordinal=source_ordinals.and_then(|ordinals|ordinals.get(i).copied()).unwrap_or(i);
        panic!("C425 {label} first tuple divergence ordinal={ordinal} span={} expected={:?} observed={:?}",
            spans.and_then(|s|s.get(ordinal).copied()).unwrap_or("owner-output"),
            crate::c425_span_census::tuple(&expected[i]),crate::c425_span_census::tuple(&observed[i]));
    }
    assert_eq!(expected.len(),observed.len(),"C425 {label} stream count divergence at ordinal {shared}");
}

fn collect_owner(owner:usize,parent:&WorkTreeHistoryPlan,roster:&DaaHistoryRoster<'_>,
    row_plan:&RowPlan<'_,'_>,canonical:&[Term],spans:&[&str],native_row_batch:bool) {
    let base=collect_tagged(|sink|parent.header_boundary().visit_slot_terms(owner as u64,sink).map(|_|()))
        .unwrap_or_else(|e|panic!("C425 base/mature-A4 traversal owner={owner}: {e}"));
    validate_tagged(owner,canonical,spans,&base,"base/mature-A4").unwrap();

    let (work_tree,work_counts)= {
        let mut output=Vec::new();
        let counts=parent.visit_slot_terms(owner as u64,|term|{
            let ordinal=crate::c425_span_census::current_source_ordinal()
                .ok_or("C425 WorkTree callback missing source ordinal")?;
            output.push(Tagged{ordinal,term});Ok(())
        }).unwrap_or_else(|e|panic!("C425 work-tree traversal owner={owner}: {e}"));
        (output,counts)
    };
    validate_tagged(owner,canonical,spans,&work_tree,"work-tree").unwrap();
    let worktree_drops=dropped_by_span(&base,&work_tree,spans,"work-tree").unwrap();
    assert_eq!(worktree_drops.values().sum::<usize>(),work_counts.omitted_worktree,
        "C425 work-tree source counter vs ordinal retirement owner={owner}");

    let (rostered,roster_counts)={
        let mut output=Vec::new();
        let counts=roster.visit_header_terms(owner as u64,|term|{
            let ordinal=crate::c425_span_census::current_source_ordinal()
                .ok_or("C425 DaaRoster callback missing source ordinal")?;
            output.push(Tagged{ordinal,term});Ok(())
        }).unwrap_or_else(|e|panic!("C425 DaaRoster traversal owner={owner}: {e}"));
        (output,counts)
    };
    validate_tagged(owner,canonical,spans,&rostered,"DaaRoster").unwrap();
    let short_drops=dropped_by_span(&work_tree,&rostered,spans,"short-A4").unwrap();
    assert_eq!(short_drops.values().sum::<usize>(),roster_counts.omitted_short_a4,
        "C425 short-A4 source counter vs ordinal retirement owner={owner}");
    let mature_drops=dropped_by_span(&canonical.iter().enumerate().map(|(ordinal,term)|
        Tagged{ordinal,term:globalize(owner,term).unwrap()}).collect::<Vec<_>>(),
        &base,spans,"mature-A4").unwrap();
    assert_eq!(mature_drops.values().sum::<usize>(),roster_counts.omitted_mature_a4,
        "C425 mature-A4 source counter vs ordinal retirement owner={owner}");
    assert_eq!(base.len()+roster_counts.omitted_mature_a4,canonical.len(),
        "C425 base traversal omitted count owner={owner}");

    let schedule=Scheduled::eligible08();
    let active=source_active_mask(&schedule,owner).unwrap();
    let (scheduled,retired)=scheduled_filter(owner,active,&rostered)
        .unwrap_or_else(|e|panic!("C425 tagged scheduled predicate owner={owner}: {e}"));
    let scheduled_drops=dropped_by_span(&rostered,&scheduled,spans,"scheduled").unwrap();
    assert_eq!(scheduled_drops.values().sum::<usize>(),retired.iter().sum::<usize>(),
        "C425 scheduled active-range counter vs ordinal retirement owner={owner}");
    let native=row_plan.header.header_terms(owner).unwrap();
    let candidate_terms=scheduled.iter().map(|item|item.term.clone()).collect::<Vec<_>>();
    let scheduled_ordinals=scheduled.iter().map(|item|item.ordinal).collect::<Vec<_>>();
    compare_terms(&candidate_terms,&native.terms,Some(&scheduled_ordinals),Some(spans),"tagged schedule vs native Merge");
    assert_eq!(retired,native.retired,"C425 tagged/native scheduled retirement counts owner={owner}");

    let class=roster.owner_class(owner as u64).unwrap();
    let mut placed=Vec::with_capacity(scheduled.len());
    for item in &scheduled {
        let q=item.term.row-owner*ROWS;
        let mapped=if q<393_216{q}else if q<406_406{507_536+q-393_216}
            else{panic!("C425 HEADER source row beyond placement owner={owner} q={q}")};
        let actual=row_plan.layout.place(class,Relation::Header,owner,item.term.clone()).unwrap();
        let mut expected=item.term.clone();expected.row=owner*ROWS+mapped;
        if actual!=expected{panic!("C425 ROW first divergence owner={owner} ordinal={} span={} expected={:?} actual={:?}",
            item.ordinal,spans[item.ordinal],crate::c425_span_census::tuple(&expected),
            crate::c425_span_census::tuple(&actual));}
        placed.push(actual);
    }

    if native_row_batch {
        let batch=row_plan.stage_owner(owner).unwrap();
        let native_placed=row_plan.check_raw_header_placement(owner,&candidate_terms,&batch).unwrap();
        compare_terms(&placed,&native_placed,None,None,"candidate/native RowPlan placement");
    }

    let digest_records=scheduled.iter().zip(&placed)
        .map(|(item,placed)|(item.ordinal,item.term.clone(),placed.clone())).collect::<Vec<_>>();
    let (source_digest,placed_digest)=crate::c425_span_census::owner_sha256(owner,&digest_records)
        .unwrap_or_else(|error|panic!("C425 owner digest unavailable owner={owner}: {error}"));

    let by_span=|items:&[Tagged]|{
        let mut counts=BTreeMap::<&str,usize>::new();
        for item in items{*counts.entry(spans[item.ordinal]).or_default()+=1;}counts
    };
    let mature_drops=mature_drops.into_iter().collect::<Vec<_>>();
    let worktree_drops=worktree_drops.into_iter().collect::<Vec<_>>();
    let short_drops=short_drops.into_iter().collect::<Vec<_>>();
    let scheduled_drops=scheduled_drops.into_iter().collect::<Vec<_>>();
    println!("C425 indexed owner={owner} class={class:?} active={active:?} mature_a4_drops={mature_drops:?} worktree_drops={worktree_drops:?} short_a4_drops={short_drops:?} scheduled_drops={scheduled_drops:?} retained_by_span={:?} source_terms={} placed_terms={} source_sha256={source_digest} placed_sha256={placed_digest} ordinal_identity=direct",by_span(&scheduled),scheduled.len(),placed.len());
}

fn assert_synthetic_duplicate_ordinal_mutant_rejected(owner:usize) {
    // The real owner may have no duplicate complete Term. This isolated
    // fixture proves that tags still distinguish identical occurrences.
    let local=Term{row:0,gate:crate::gkr::Gate{left:0,right:0,
        c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
    let canonical=[local.clone(),local.clone()];
    let spans=["synthetic.first","synthetic.second"];
    let global=globalize(owner,&local).unwrap();
    let tagged=[Tagged{ordinal:0,term:global.clone()},Tagged{ordinal:1,term:global}];
    validate_tagged(owner,&canonical,&spans,&tagged,"synthetic-duplicate-positive").unwrap();
    let mut mutant=tagged.clone();
    mutant[0].ordinal=1;
    mutant[1].ordinal=0;
    assert!(tagged.iter().zip(&mutant).all(|(a,b)|a.term==b.term),
        "C425 synthetic mutant must change only source ordinals");
    let error=validate_tagged(owner,&canonical,&spans,&mutant,"synthetic-duplicate-mutant")
        .expect_err("C425 identical-tuple ordinal swap was accepted");
    assert!(error.contains("not strictly increasing"),
        "C425 synthetic ordinal mutant failed for the wrong reason: {error}");
}

fn run_census(owners:&[(usize,OwnerClass,[bool;4])],native_first_only:Option<usize>) {
    let (canonical,spans)=canonical();
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[17;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let schedule=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&schedule).unwrap();
    for &(owner,expected_class,expected_active) in owners {
        assert_eq!(roster.owner_class(owner as u64).unwrap(),expected_class,"C425 owner class {owner}");
        assert_eq!(source_active_mask(&schedule,owner).unwrap(),expected_active,"C425 source role mask {owner}");
        collect_owner(owner,&parent,&roster,&row_plan,&canonical,&spans,native_first_only==Some(owner));
    }
}

#[test]
fn c425_owner845759_duplicate_tag_falsifier_and_rowplan_join() {
    let (canonical,spans)=canonical();
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[17;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let schedule=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&schedule).unwrap();
    let owner=C425_OWNERS[1].0;
    collect_owner(owner,&parent,&roster,&row_plan,&canonical,&spans,true);
    assert_synthetic_duplicate_ordinal_mutant_rejected(owner);
    println!("C425 first-owner completion sentinel: owner={owner} synthetic_duplicate_ordinal_mutant=rejected rowplan_join=passed-if-test-green");
}

#[test]
fn c425_four_owner_indexed_provenance_span_census_and_row_placement() {
    run_census(&C425_OWNERS,None);
}

#[path="c427_serializer_cold_ledger_tests.rs"]
mod c427_serializer_cold_ledger_tests;

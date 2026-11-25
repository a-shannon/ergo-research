use super::*;
use ark_ff::{One,Zero};
use crate::{daa_integer::Epoch,gkr::Gate,short_daa_layout::Profile,work_tree_history_plan::WorkTreeHistoryPlan};

fn term(owner:usize,q:usize)->Term {
    Term{row:owner*524288+q,gate:Gate{left:owner*1048576+7,right:owner*1048576,
        c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}
}
fn literal(class:OwnerClass,relation:Relation,q:usize)->usize {
    match relation {
        Relation::Header if q>=393216=>q+114320,
        Relation::DaaLane(0)if class==OwnerClass::M1=>166664+q,
        Relation::DaaLane(1)if class==OwnerClass::M1=>179218+q-131072,
        Relation::DaaLane(lane)if lane<2=>if q<=95479{q+166664}else if q<=108314{q+166665}else{q+284901},
        _=>q,
    }
}

fn gate_term(row:usize,left:usize,right:usize,c0:Fr,c1:Fr,c2:Fr,c3:Fr)->Term {
    Term{row,gate:Gate{left,right,c0,c1,c2,c3}}
}

fn diagnostic_batch(terms:Vec<Term>)->Batch {
    let mut expected=[0;RELATIONS];let mut relations=[None;RELATIONS];
    let entries=terms.into_iter().map(|term|{
        expected[0]+=1;relations[0]=Some(Relation::Header);
        Entry{relation:Relation::Header,term}
    }).collect();
    Batch{owner:0,class:OwnerClass::Initial,layout:Layout::fixed().digest(),
        source:HeaderSourceBinding::diagnostic_for_test(0),terms:entries,expected,relations}
}

fn collect_active(batch:&Batch)->Vec<ActiveOperand> {
    let mut active=Vec::new();
    let count=batch.visit_active_operands(|operand|{active.push(operand);Ok(())}).unwrap();
    assert_eq!(count,active.len());active
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum CensusError {
    BatchOwner,
    BatchClass,
    SourceTraversal,
    SourceMultiplicity,
    SourceTermMultiplicity{source:usize,staged:usize},
    CountOverflow,
    Missing{expected:ActiveOperand},
    Mismatch{expected:ActiveOperand,observed:ActiveOperand},
    Extra{observed:ActiveOperand},
}

struct ActiveOperandComparator<I> {observed:I,compared:usize}
impl<I:Iterator<Item=ActiveOperand>> ActiveOperandComparator<I> {
    fn new(observed:I)->Self{Self{observed,compared:0}}
    fn expect(&mut self,expected:ActiveOperand)->Result<(),CensusError> {
        let observed=self.observed.next().ok_or(CensusError::Missing{expected})?;
        if observed!=expected{return Err(CensusError::Mismatch{expected,observed});}
        self.compared=self.compared.checked_add(1).ok_or(CensusError::CountOverflow)?;Ok(())
    }
    fn finish(mut self)->Result<usize,CensusError> {
        if let Some(observed)=self.observed.next(){return Err(CensusError::Extra{observed});}
        Ok(self.compared)
    }
}

/// Independently rewalk source terms and the test-local placement literal,
/// comparing each active operand immediately with the staged iterator.
/// Only added comparator state is O(1); the source rewalk retains the
/// existing bounded owner-local HEADER vectors.
fn compare_source_to_stream(
    plan:&RowPlan<'_,'_>,batch:&Batch,owner:usize,
    observed:impl Iterator<Item=ActiveOperand>,
)->Result<usize,CensusError> {
    if batch.owner!=owner{return Err(CensusError::BatchOwner);}
    let class=plan.roster.owner_class(owner as u64).map_err(|_|CensusError::BatchClass)?;
    if batch.class!=class{return Err(CensusError::BatchClass);}
    let base=owner.checked_mul(ROWS).ok_or(CensusError::CountOverflow)?;
    let mut comparator=ActiveOperandComparator::new(observed);let mut occurrence=0usize;
    let mut comparison_error=None;
    let source_result=plan.visit_sources(owner,|relation,source|{
        let local=source.row.checked_sub(base).filter(|q|*q<ROWS).ok_or("independent source ROW owner")?;
        let row=base.checked_add(literal(class,relation,local)).ok_or("independent placed ROW overflow")?;
        let c1_active=!source.gate.c1.is_zero();let c2_active=!source.gate.c2.is_zero();
        let c3_active=!source.gate.c3.is_zero();
        if c1_active||c3_active {
            if let Err(error)=comparator.expect(ActiveOperand{occurrence,relation,row,side:OperandSide::Left,
                wire:source.gate.left,c1_active,c2_active:false,c3_active}) {
                comparison_error=Some(error);return Err("active operand census comparison".into());
            }
        }
        if c2_active||c3_active {
            if let Err(error)=comparator.expect(ActiveOperand{occurrence,relation,row,side:OperandSide::Right,
                wire:source.gate.right,c1_active:false,c2_active,c3_active}) {
                comparison_error=Some(error);return Err("active operand census comparison".into());
            }
        }
        occurrence=occurrence.checked_add(1).ok_or("source occurrence overflow")?;Ok(())
    });
    if let Some(error)=comparison_error{return Err(error);}
    let source_counts=source_result.map_err(|_|CensusError::SourceTraversal)?;
    if source_counts!=batch.expected{return Err(CensusError::SourceMultiplicity);}
    if occurrence!=batch.terms.len(){return Err(CensusError::SourceTermMultiplicity{source:occurrence,staged:batch.terms.len()});}
    comparator.finish()
}

fn compare_expected_to_stream(
    expected:impl Iterator<Item=ActiveOperand>,observed:impl Iterator<Item=ActiveOperand>,
)->Result<usize,CensusError> {
    let mut comparator=ActiveOperandComparator::new(observed);
    for operand in expected{comparator.expect(operand)?;}
    comparator.finish()
}

fn omit_first_and_duplicate_at(batch:&Batch,duplicate_index:usize)->impl Iterator<Item=ActiveOperand>+'_ {
    let mut source=batch.active_operands();let mut index=0usize;let mut pending=None;
    std::iter::from_fn(move||{
        if let Some(duplicate)=pending.take(){return Some(duplicate);}
        loop {
            let operand=source.next()?;let current=index;index+=1;
            if current==0{continue;}
            if current==duplicate_index{pending=Some(operand);return Some(operand);}
            return Some(operand);
        }
    })
}

fn c439_map_input(wire:usize,owner:usize,context:usize)->usize {
    let owner_base=owner*WIDTH;
    let Some(local)=wire.checked_sub(owner_base) else{return wire};
    let map_base=crate::legacy_envelope_map::BASE;
    if (map_base..map_base+crate::bank53_map::MAP_LIVE).contains(&local) {
        owner_base+crate::bank53_map::CONTEXT_INPUT_BASE+context*8_192+local-map_base
    } else {wire}
}

fn c439_independent_translation(source:&[Term],owner:usize,context:usize)->Vec<Term> {
    let old_row_base=owner*crate::bank53_map::MAP_ROW_STRIDE;
    source.iter().filter_map(|term| {
        let q=term.row-old_row_base;
        if (crate::bank53_map::MAP_TAIL_START..crate::bank53_map::MAP_TAIL_END).contains(&q) {
            return None;
        }
        let mut translated=term.clone();
        translated.row=owner*ROWS+crate::bank53_map::CONTEXT_ROW_BASE+context*32_768+q;
        translated.gate.left=c439_map_input(translated.gate.left,owner,context);
        translated.gate.right=c439_map_input(translated.gate.right,owner,context);
        Some(translated)
    }).collect()
}

fn c439_independent_relocation(term:&Term,context:usize)->Term {
    let mut relocated=term.clone();
    let context_base=crate::bank53_map::CONTEXT_ROW_BASE+context*32_768;
    relocated.row=[477_074,492_305][context]+term.row-context_base;
    relocated
}

fn c439_reject_pair_unchanged(
    plan:&RowPlan<'_,'_>,owner:usize,batch:&PairedMapBatch,
)->String {
    let mut registry=plan.registry_with_map_pair(owner).unwrap();
    let before=registry.clone();
    let error=registry.commit_map_pair(batch).unwrap_err();
    assert_eq!(registry,before,"paired Map rejection must be atomic");
    error
}

fn c439_literal_paired_layout_descriptor()->Vec<u8> {
    use blake2::{Blake2b,Digest,digest::consts::U32};
    let mut v1=b"c121a-row19-v1\0".to_vec();
    for word in [19u64,20,21,40,41,393216,406406,507536,520726,477074,507536,
        12554,131072,131264,166664,179218,95480,108315,132096,166665,393216,262144,475136,466944] {
        v1.extend_from_slice(&word.to_le_bytes());
    }
    let v1_digest=Blake2b::<U32>::digest(&v1);

    let mut cut=b"nipopow-cut-descriptor-08-v1\0".to_vec();
    cut.push(1); // Eligible08
    for word in [1_827_840u64,1_810_842,1_810_905,1_024,64] {
        cut.extend_from_slice(&word.to_be_bytes());
    }
    cut.extend([0,1]); // Sampled, Exact

    let mut descriptor=b"c439-row19-paired-map-v2\0".to_vec();
    descriptor.extend_from_slice(&v1_digest);
    descriptor.extend_from_slice(&(cut.len() as u64).to_le_bytes());
    descriptor.extend_from_slice(&cut);
    descriptor.extend_from_slice(&11u64.to_le_bytes());
    for slot in 0..11u64 {descriptor.extend_from_slice(&slot.to_le_bytes());}
    for word in [0u64,409_600,419_947,477_074,487_421,
        1,442_368,452_715,492_305,502_652] {
        descriptor.extend_from_slice(&word.to_le_bytes());
    }
    descriptor
}

fn c439_reject_layout_entry(
    registry:&RowRegistry,source:&HeaderSourceBinding,relation:Relation,q:usize,
) -> String {
    let slot=relation.slot(0).unwrap();
    let mut counts=[0usize;RELATIONS];counts[slot]=1;
    let mut relations=[None;RELATIONS];relations[slot]=Some(relation);
    let candidate=term(0,q);
    let error=registry.check_entries(0,OwnerClass::Genesis,Layout::paired_map().digest(),
        source,&counts,&relations,std::iter::once((relation,&candidate))).unwrap_err();
    assert!(error.contains("placement/reservation"),
        "candidate must reach the shared placement/permission checks: {error}");
    error
}

#[test]
fn c439_owner0_paired_map_native_row_admission_no_frame() {
    use crate::bank53_map::{self,CutDescriptor};
    use crate::h21_row_support::{relocate,Family};
    use crate::legacy_envelope_map::{LowerBranch,LowerSelector,LowerSource,Map};
    use crate::packed_owner_assembly::{Eligible08MapPairLease,HeaderSourceBinding};
    use blake2::{Blake2b,Digest,digest::consts::U32};
    use std::collections::BTreeSet;

    const OWNER:usize=0;
    const N:u64=1_827_840;
    const RETAINED:usize=7_579;
    const SOURCE_TERMS:usize=9_720;
    let parent=WorkTreeHistoryPlan::compile(N,21,[0x43;32],[0x44;28])
        .expect("exact no-frame H21 source plan");
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    assert_eq!(roster.owner_class(OWNER as u64).unwrap(),OwnerClass::Genesis);
    let cut=CutDescriptor::eligible08();
    let terminals=cut.terminals();
    assert_eq!(terminals,[1_827_840,1_810_842]);
    let selected_lower=LowerSelector{
        source:LowerSource::HeaderDifficulty{height:841_729},
        branch:LowerBranch::Pivot(54),
    };
    let maps=[
        Map::new_modern_global_u_selected_lower(terminals[0] as u64,21,55,selected_lower).unwrap(),
        Map::new_modern_global_u_selected_lower(terminals[1] as u64,21,55,selected_lower).unwrap(),
    ];
    let source_binding=HeaderSourceBinding::for_plan(&parent,OWNER).unwrap();
    let lease=Eligible08MapPairLease::synthetic_valid_for_test(
        source_binding.clone(),OWNER,OwnerClass::Genesis,maps.clone(),
    ).unwrap();
    let scheduled=Scheduled::eligible08();
    let plan=RowPlan::new(&roster,&scheduled).unwrap();

    let literal_v2=c439_literal_paired_layout_descriptor();
    assert_eq!(Layout::paired_map().descriptor(),literal_v2,
        "C439 v2 descriptor must match the independent literal recipe");
    let literal_v2_digest=Blake2b::<U32>::digest(&literal_v2);

    // The paired constructor materializes the large ordinary producer batch once.
    let paired=plan.stage_owner_with_map_pair(OWNER,&lease).unwrap();
    assert_eq!(paired.owner(),OWNER);
    assert_eq!(paired.class(),OwnerClass::Genesis);
    assert_eq!(paired.source_binding(),&source_binding);
    assert_eq!(paired.source_binding(),&HeaderSourceBinding::for_plan(&parent,OWNER).unwrap());
    assert_eq!(paired.layout_digest(),<[u8;32]>::from(literal_v2_digest));
    assert_eq!(Layout::paired_map().digest(),<[u8;32]>::from(literal_v2_digest));
    assert_ne!(paired.layout_digest(),Layout::fixed().digest());

    // Rewalk the exact nine ordinary producer streams without making a second
    // full Batch, then compare every tuple in order against the paired base.
    let mut base=paired.base_terms();
    let mut base_counts=[0usize;9];
    let source_counts=plan.visit_sources(OWNER,|relation,source|{
        let slot=relation.slot(OWNER)?;
        assert!(slot<9,"ordinary v1 stream gained a Map relation");
        base_counts[slot]+=1;
        let expected=Layout::fixed().place(OwnerClass::Genesis,relation,OWNER,source)?;
        let (observed_relation,observed)=base.next().ok_or("C439 missing ordinary base tuple")?;
        if observed_relation!=relation || observed!=&expected {
            return Err("C439 ordinary v1 base tuple/order changed".into());
        }
        Ok(())
    }).unwrap();
    assert!(base.next().is_none(),"C439 ordinary base has extra tuples");
    assert_eq!(&source_counts[..9],&base_counts);
    assert_eq!(&paired.counts()[..9],&base_counts);
    assert_eq!(&source_counts[9..],&[0,0]);
    assert!(paired.base_terms().all(|(relation,_)|!matches!(relation,Relation::Map(_))));
    assert_eq!(&paired.counts()[9..],&[RETAINED,RETAINED]);

    // Independently derive the source, translated and relocated full tuples.
    // C438 owns zero-tail and physical-X negative coverage; this test checks the
    // exact 55/55 geometry that its historical 55/48 fixture did not establish.
    let mut source_counts_by_context=[0usize;2];
    let mut translated_distinct=[0usize;2];
    let mut relocated=[Vec::<Term>::new(),Vec::<Term>::new()];
    let base_rows=paired.base_terms().map(|(_,term)|term.row).collect::<BTreeSet<_>>();
    let daa_lane3=paired.base_terms().filter(|(relation,_)|*relation==Relation::DaaLane(3))
        .map(|(_,term)|term.row).collect::<BTreeSet<_>>();
    assert_eq!(daa_lane3.len(),81_920,"actual owner-0 full zero DAA lane");
    for context in 0..2 {
        let source=maps[context].terms(OWNER as u64).expect("C439 symbolic exact Map source");
        source_counts_by_context[context]=source.len();
        assert_eq!(source.len(),SOURCE_TERMS);
        assert!(source.iter().all(|term|{
            let q=term.row-OWNER*bank53_map::MAP_ROW_STRIDE;
            q<10_347
        }),"C439 exact source Map row span");
        let raw_tail=source.iter().filter(|term|{
            let q=term.row-OWNER*bank53_map::MAP_ROW_STRIDE;
            (bank53_map::MAP_TAIL_START..bank53_map::MAP_TAIL_END).contains(&q)
        }).count();
        assert_eq!(raw_tail,bank53_map::MAP_TAIL_COUNT);
        let first_tail=source.iter().position(|term|{
            let q=term.row-OWNER*bank53_map::MAP_ROW_STRIDE;
            (bank53_map::MAP_TAIL_START..bank53_map::MAP_TAIL_END).contains(&q)
        }).expect("C439 raw exact-zero tail term");
        let mut missing_tail=source.clone();
        missing_tail.remove(first_tail);
        assert!(bank53_map::translate_map_terms_for_descriptor(
            &maps[context],OWNER as u64,context,&missing_tail,cut,
        ).is_err(),"C439 missing raw zero-tail term context={context}");
        let mut duplicate_tail=source.clone();
        duplicate_tail.push(source[first_tail].clone());
        assert!(bank53_map::translate_map_terms_for_descriptor(
            &maps[context],OWNER as u64,context,&duplicate_tail,cut,
        ).is_err(),"C439 duplicated raw zero-tail term context={context}");
        let mut noncanonical_tail=source.clone();
        noncanonical_tail[first_tail].gate.c1=Fr::zero();
        assert!(bank53_map::translate_map_terms_for_descriptor(
            &maps[context],OWNER as u64,context,&noncanonical_tail,cut,
        ).is_err(),"C439 noncanonical raw zero-tail term context={context}");
        let translated=bank53_map::translate_map_terms_for_descriptor(
            &maps[context],OWNER as u64,context,&source,cut,
        ).expect("production exact Eligible08 Map translation");
        let independent=c439_independent_translation(&source,OWNER,context);
        assert_eq!(translated,independent,"C439 independent translation context={context}");
        assert_eq!(translated.len(),RETAINED,"C439 55/55 retained source term count");
        assert_eq!(source.len()-translated.len(),bank53_map::MAP_TAIL_COUNT);
        let translated_rows=translated.iter().map(|term|term.row).collect::<BTreeSet<_>>();
        translated_distinct[context]=translated_rows.len();
        let row_start=OWNER*ROWS+bank53_map::CONTEXT_ROW_BASE+context*32_768;
        let row_end=row_start+10_347;
        assert!(translated.iter().all(|term|(row_start..row_end).contains(&term.row)));
        assert_eq!(translated_rows.intersection(&daa_lane3).count(),translated_rows.len(),
            "unrelocated Map rows must match the actual owner-0 DAA ROWs");

        let production=translated.iter().map(|term|
            relocate(Family::Map(context),OWNER,term).expect("C439 Map relocation"))
            .collect::<Vec<_>>();
        let expected=translated.iter().map(|term|c439_independent_relocation(term,context))
            .collect::<Vec<_>>();
        assert_eq!(production,expected,"C439 independent relocation context={context}");
        let destination=[477_074,492_305][context];
        assert!(production.iter().all(|term|
            (destination..destination+10_347).contains(&term.row)));
        let native=paired.map_terms(context).expect("native paired context");
        assert_eq!(native,production.as_slice(),"C439 native exact Map tuples context={context}");
        assert!(native.iter().all(|term|!base_rows.contains(&term.row)),
            "relocated Map context must not collide with a native base ROW");
        relocated[context]=production;
    }
    let map0_rows=relocated[0].iter().map(|term|term.row).collect::<BTreeSet<_>>();
    let map1_rows=relocated[1].iter().map(|term|term.row).collect::<BTreeSet<_>>();
    assert!(map0_rows.is_disjoint(&map1_rows),"C439 Map destination ROW sets overlap");
    assert_eq!(source_counts_by_context,[SOURCE_TERMS;2]);

    // Exercise v2 destination permissions directly at the shared registry
    // placement seam. These synthetic single-entry candidates intentionally
    // bypass paired-source tuple checks so each writer reaches placement.
    let placement_registry=plan.registry_with_map_pair(OWNER).unwrap();
    for (relation,q) in [
        (Relation::Map(0),492_305), // Map0 term in Map1 destination
        (Relation::Map(0),490_000), // Map0 term in the reserved hole
        (Relation::Map(1),477_074), // Map1 term in Map0 destination
        (Relation::Map(1),490_000), // Map1 term in the reserved hole
    ] {
        c439_reject_layout_entry(&placement_registry,&source_binding,relation,q);
    }
    let scheduled_writers=[
        Relation::Scheduled(Writer::Max{context:0,end:OWNER+2}),
        Relation::Scheduled(Writer::Cap{context:0,origin:OWNER+1}),
    ];
    for relation in [Relation::Header,Relation::DaaLane(3)]
        .into_iter().chain(scheduled_writers) {
        for q in [477_074,492_305] {
            c439_reject_layout_entry(&placement_registry,&source_binding,relation,q);
        }
    }

    let mut registry=plan.registry_with_map_pair(OWNER).unwrap();
    let before=registry.clone();
    registry.commit_map_pair(&paired).expect("one atomic native paired Map commit");
    assert!(registry.distinct_rows()>0);
    for (relation,term) in paired.terms() {
        assert_eq!(registry.row_tag_for_test(term.row-OWNER*ROWS),
            relation.slot(OWNER).unwrap() as u8+1,
            "native ROW relation tag follows the exact producer");
    }
    for context in 0..2 {
        let expected_tag=10+context as u8;
        for term in paired.map_terms(context).unwrap() {
            assert_eq!(registry.row_tag_for_test(term.row),expected_tag);
        }
    }
    let committed=registry.clone();
    assert!(registry.commit_map_pair(&paired).unwrap_err().contains("duplicate complete"));
    assert_eq!(registry,committed,"duplicate paired commit must preserve committed state");
    assert_ne!(registry,before);

    // Binding and layout faults are isolated and must not partially commit.
    for field in 0..6 {
        let mut bad=paired.clone();
        *bad.source_binding_mut_for_test()=source_binding.mutated_field_for_test(field);
        assert!(c439_reject_pair_unchanged(&plan,OWNER,&bad).contains("source tuples/binding"),
            "C439 source binding field {field}");
    }
    let mut wrong_class=paired.clone();
    *wrong_class.class_mut_for_test()=OwnerClass::Initial;
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&wrong_class).contains("source tuples/binding"));
    let mut wrong_v2=paired.clone();
    wrong_v2.layout_mut_for_test()[0]^=1;
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&wrong_v2).contains("v2 layout"));
    assert!(plan.stage_owner_with_map_pair(1,&lease).is_err());

    // Lease-bound parent/cut/layout/owner and class faults fail closed before
    // any candidate can reach native registry admission.
    for field in 0..6 {
        let binding=source_binding.mutated_field_for_test(field);
        assert!(Eligible08MapPairLease::synthetic_valid_for_test(
            binding,OWNER,OwnerClass::Genesis,maps.clone(),
        ).and_then(|bad|plan.stage_owner_with_map_pair(OWNER,&bad)).is_err(),
            "C439 lease binding field {field}");
    }
    assert!(Eligible08MapPairLease::synthetic_valid_for_test(
        source_binding.clone(),OWNER,OwnerClass::Initial,maps.clone(),
    ).and_then(|bad|plan.stage_owner_with_map_pair(OWNER,&bad)).is_err(),
        "C439 wrong source class");
    let owner1_binding=HeaderSourceBinding::for_plan(&parent,1).unwrap();
    let owner1_class=roster.owner_class(1).unwrap();
    assert!(Eligible08MapPairLease::synthetic_valid_for_test(
        owner1_binding,1,owner1_class,maps.clone(),
    ).and_then(|bad|plan.stage_owner_with_map_pair(OWNER,&bad)).is_err(),
        "C439 wrong source owner");

    let mut swapped_contexts=paired.clone();
    let map0=swapped_contexts.map_terms(0).unwrap().to_vec();
    let map1=swapped_contexts.map_terms(1).unwrap().to_vec();
    *swapped_contexts.map_terms_mut_for_test(0)=map1;
    *swapped_contexts.map_terms_mut_for_test(1)=map0;
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&swapped_contexts).contains("source tuples"));
    let mut missing_context=paired.clone();
    missing_context.map_terms_mut_for_test(1).clear();
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&missing_context).contains("source tuples"));
    let mut swapped_relation=paired.clone();
    *swapped_relation.map_relation_mut_for_test(0)=Relation::Map(1);
    *swapped_relation.map_relation_mut_for_test(1)=Relation::Map(0);
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&swapped_relation).contains("source tuples"));

    let first_live=0usize;
    let mut omitted=paired.clone();omitted.map_terms_mut_for_test(0).remove(first_live);
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&omitted).contains("source tuples"));
    let mut duplicated=paired.clone();
    let first=duplicated.map_terms(0).unwrap()[first_live].clone();
    duplicated.map_terms_mut_for_test(0).push(first);
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&duplicated).contains("source tuples"));
    let mut reordered=paired.clone();
    let last=reordered.map_terms(0).unwrap().len()-1;
    assert_ne!(reordered.map_terms(0).unwrap()[0],reordered.map_terms(0).unwrap()[last]);
    reordered.map_terms_mut_for_test(0).swap(0,last);
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&reordered).contains("source tuples"));
    let mut changed_gate=paired.clone();
    changed_gate.map_terms_mut_for_test(0)[0].gate.left^=1;
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&changed_gate).contains("source tuples"));
    let mut changed_coefficient=paired.clone();
    changed_coefficient.map_terms_mut_for_test(0)[0].gate.c1+=Fr::one();
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&changed_coefficient).contains("source tuples"));
    let mut compensated=paired.clone();
    let removed=compensated.map_terms_mut_for_test(0).remove(0);
    let replacement=compensated.map_terms(0).unwrap()[0].clone();
    assert_ne!(removed,replacement);
    compensated.map_terms_mut_for_test(0).push(replacement);
    assert_eq!(compensated.map_terms(0).unwrap().len(),RETAINED);
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&compensated).contains("source tuples"));
    let mut wrong_relocation=paired.clone();
    wrong_relocation.map_terms_mut_for_test(0)[0].row+=1;
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&wrong_relocation).contains("source tuples"));

    // Preserve the checked source tuple equality while forcing each actual
    // collision through the shared native ROW collision engine.
    let mut map_context_collision=paired.clone();
    let collision_row=map_context_collision.map_terms(0).unwrap()[0].row;
    map_context_collision.map_terms_mut_for_test(1)[0].row=collision_row;
    map_context_collision.expected_maps[1][0].row=collision_row;
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&map_context_collision)
        .contains("cross-relation ROW collision"));
    let mut daa_collision=paired.clone();
    let daa_row=daa_collision.base_terms().find(|(relation,_)|
        matches!(relation,Relation::DaaLane(_))).unwrap().1.row;
    daa_collision.map_terms_mut_for_test(0)[0].row=daa_row;
    daa_collision.expected_maps[0][0].row=daa_row;
    assert!(c439_reject_pair_unchanged(&plan,OWNER,&daa_collision)
        .contains("cross-relation ROW collision"));

    println!("C439_OWNER0_MAP_GEOMETRY source_terms={},{} retained_terms={},{} translated_distinct_rows={},{} relocated_distinct_rows={},{} pre_relocation_daa_intersections={},{} post_relocation_daa_intersections=0 map0_map1_collisions=0",
        source_counts_by_context[0],source_counts_by_context[1],RETAINED,RETAINED,
        translated_distinct[0],translated_distinct[1],map0_rows.len(),map1_rows.len(),
        translated_distinct[0],translated_distinct[1]);
    println!("C439_OWNER0_MAP_ROW_ADMITTED owner=0 contexts=2 e55_pair=true v1_preserved=true native_rowplan=true frame=false proof=false client=false");
}

#[test]
fn descriptor_and_literal_boundaries_pin_fixed_layout_without_binding_a_proof() {
    let layout=Layout::fixed();
    let words=[19u64,20,21,40,41,393216,406406,507536,520726,477074,507536,
        12554,131072,131264,166664,179218,95480,108315,132096,166665,393216,262144,475136,466944];
    let mut descriptor=b"c121a-row19-v1\0".to_vec();for word in words{descriptor.extend(word.to_le_bytes());}
    assert_eq!(layout.descriptor(),descriptor);assert_eq!(layout.digest(),<[u8;32]>::from(Blake2b::<U32>::digest(&descriptor)));
    let mut changed=descriptor;changed[14]^=1;
    assert_ne!(layout.digest(),<[u8;32]>::from(Blake2b::<U32>::digest(changed)));
    let owner=1048576;
    for(class,relation,points)in [
        (OwnerClass::Carry,Relation::Header,vec![0,393215,393216,406405]),
        (OwnerClass::M1,Relation::DaaLane(0),vec![0,12553]),
        (OwnerClass::M1,Relation::DaaLane(1),vec![131072,131263]),
        (OwnerClass::Short(Profile::M2),Relation::DaaLane(0),vec![0,95479,95480,108314,108315,131071]),
        (OwnerClass::Mature(Epoch::Eip),Relation::DaaLane(1),vec![131072,132095]),
        (OwnerClass::Carry,Relation::DaaLane(2),vec![262144]),
        (OwnerClass::Initial,Relation::DaaLane(2),vec![262144]),
        (OwnerClass::Carry,Relation::DaaLane(3),vec![393216,475135]),
        (OwnerClass::M1,Relation::DaaLane(3),vec![393216,466943]),
    ] {
        for q in points {
            let before=term(owner,q);let actual=layout.place(class,relation,owner,before.clone()).unwrap();
            assert_eq!(actual.row,owner*524288+literal(class,relation,q));assert_eq!(actual.gate,before.gate);
            assert!(layout.placed(class,relation,actual.row-owner*524288));
            assert!(!(477074..507536).contains(&(actual.row-owner*524288)));
        }
    }
    for(class,relation,q)in [
        (OwnerClass::Carry,Relation::Header,406406),(OwnerClass::M1,Relation::DaaLane(0),12554),
        (OwnerClass::M1,Relation::DaaLane(1),131264),(OwnerClass::Short(Profile::M2),Relation::DaaLane(1),132096),
        (OwnerClass::Carry,Relation::DaaLane(0),0),(OwnerClass::Carry,Relation::DaaLane(1),131072),
        (OwnerClass::M1,Relation::DaaLane(3),466944),(OwnerClass::Carry,Relation::DaaLane(3),475136),
        (OwnerClass::Short(Profile::M2),Relation::DaaLane(3),393216),
        (OwnerClass::Mature(Epoch::Eip),Relation::DaaLane(2),262144),
        (OwnerClass::Genesis,Relation::DaaLane(2),262144),
    ]{assert!(layout.place(class,relation,owner,term(owner,q)).is_err());}
    assert!(layout.place(OwnerClass::Carry,Relation::Header,owner+1,term(owner,0)).is_err());
    assert!(layout.place(OwnerClass::Carry,Relation::Header,2097152,term(2097152,0)).is_err());
    assert!(Layout::inverse_f3(262144).is_none());assert!(Layout::inverse_f3(477074).is_none());
}

fn reject_unchanged(plan:&RowPlan<'_,'_>,owner:usize,batch:&Batch)->String {
    let mut registry=plan.registry(owner).unwrap();let before=registry.clone();
    let error=registry.commit(batch).unwrap_err();assert_eq!(registry,before);error
}

#[test]
fn true_sources_stage_atomic_rows_and_reject_old_overlap_omission_duplicate_and_class_mutants() {
    let parent=WorkTreeHistoryPlan::compile(1827840,21,[0;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();let scheduled=Scheduled::eligible08();
    let plan=RowPlan::new(&roster,&scheduled).unwrap();let mut max_terms=0;let mut maximum_rows=0;
    // Each class plus scheduled activation/tails and padding. Source bounds,
    // rather than a full H21 sweep, delimit the fixed placement branches.
    for owner in [0usize,1,1024,2048,3072,8192,9216,417791,417792,844670,844672,844800,845759,
        1827773,1827774,1827837,1827838,1827840] {
        let batch=plan.stage_owner(owner).unwrap();let mut next=batch.terms();let mut observed=[0;RELATIONS];
        // Independent literal placement oracle consumes the actual old streams
        // and checks every emitted gate and tuple multiplicity in order.
        let expected=plan.visit_sources(owner,|relation,before| {
            let(actual_relation,actual)=next.next().ok_or("missing placed tuple")?;
            assert_eq!(actual_relation,relation);assert_eq!(actual.gate,before.gate);
            assert_eq!(actual.row,owner*524288+literal(batch.class,relation,before.row-owner*524288));
            observed[relation.slot(owner)?]+=1;Ok(())
        }).unwrap();assert!(next.next().is_none());assert_eq!(observed,expected);
        assert_eq!(&observed[9..],&[0,0],"ordinary v1 stage cannot emit Map relations");drop(next);
        let mut registry=plan.registry(owner).unwrap();registry.commit(&batch).unwrap();
        assert!(registry.distinct_rows()<=524288);assert!(registry.distinct_rows()<batch.terms.len(),"same-relation monomials remain legal");
        assert!((477074..507536).all(|q|registry.rows[q]==0));
        let saved=registry.clone();assert!(registry.commit(&batch).unwrap_err().contains("duplicate complete"));assert_eq!(registry,saved);
        let declarations=batch.declared_x_domains();
        for domain in &declarations {assert!(domain.start<domain.end);assert_eq!(domain.start/1048576,owner);}
        let daa:Vec<_>=declarations.iter().filter(|d|d.producer==Producer::Daa)
            .map(|v|(v.start-owner*1048576,v.end-owner*1048576)).collect();
        if matches!(batch.class,OwnerClass::M1|OwnerClass::Short(_)|OwnerClass::Mature(_)) {
            assert_eq!(daa,BANKS.to_vec());
        }else{assert!(daa.is_empty(),"inactive-zero gates are not X producer leases");}
        max_terms=max_terms.max(batch.terms.len());maximum_rows=maximum_rows.max(registry.distinct_rows());
        println!("C121A_OWNER owner={owner} class={:?} terms={} rows={} declared_partial_x_domains={}",batch.class,batch.terms.len(),registry.distinct_rows(),declarations.len());
        if owner==844670 {
            // Reinstating the old tail produces a genuine HEADER/DAA collision,
            // detected before source counts or candidate-range validation.
            let mut old=batch.clone();for e in &mut old.terms {if e.relation==Relation::Header {
                let q=e.term.row-owner*524288;if(507536..520726).contains(&q){e.term.row-=114320;}
            }}
            assert!(reject_unchanged(&plan,owner,&old).contains("cross-relation ROW collision"));drop(old);
            let mut omitted=batch.clone();omitted.terms.pop();assert!(reject_unchanged(&plan,owner,&omitted).contains("omission/duplicate"));drop(omitted);
            let mut duplicate=batch.clone();duplicate.terms.push(duplicate.terms[0].clone());
            assert!(reject_unchanged(&plan,owner,&duplicate).contains("omission/duplicate"));drop(duplicate);
            let mut equal=batch.clone();let mut collision=equal.terms[0].clone();collision.relation=Relation::DaaLane(3);
            equal.terms.push(collision);assert!(reject_unchanged(&plan,owner,&equal).contains("cross-relation ROW collision"));drop(equal);
            let mut wrong=batch.clone();wrong.class=OwnerClass::M1;
            assert!(reject_unchanged(&plan,owner,&wrong).contains("owner/class/layout"));drop(wrong);
            let mut wrong_layout=batch.clone();wrong_layout.layout[0]^=1;
            assert!(reject_unchanged(&plan,owner,&wrong_layout).contains("owner/class/layout"));drop(wrong_layout);
            let mut foreign=batch.clone();foreign.terms[0].term.row^=1usize<<39;
            assert!(reject_unchanged(&plan,owner,&foreign).contains("physical owner"));drop(foreign);
        }
    }
    assert!(plan.stage_owner(2097152).is_err());
    println!("C121A_SUMMARY owners=18 max_terms={max_terms} maximum_rows={maximum_rows} layout={:02x?} row_only=true no_coefficients=true",Layout::fixed().digest());
}

#[test]
fn daa_active_bank_reads_keep_exact_source_rows_and_reject_isolated_row_faults() {
    let owner=844_672usize;
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[0;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let scheduled=Scheduled::eligible08();
    let plan=RowPlan::new(&roster,&scheduled).unwrap();
    let batch=plan.stage_owner(owner).unwrap();
    let base=owner*WIDTH;
    let active_bank_reads=batch.active_operands().filter(|operand|{
        operand.wire.checked_sub(base).is_some_and(|local|
            BANKS.iter().any(|&(start,end)|(start..end).contains(&local)))
    }).count();
    assert!(active_bank_reads>0,"mature EIP DAA bank has active readers");
    let daa_index=batch.terms.iter().position(|entry|matches!(entry.relation,Relation::DaaLane(_)))
        .expect("mature EIP source has a DAA ROW");
    let mut omitted=batch.clone();omitted.terms.remove(daa_index);
    assert!(reject_unchanged(&plan,owner,&omitted).contains("omission/duplicate"));
    let mut relocated=batch.clone();relocated.terms[daa_index].term.row=owner*ROWS+477_074;
    assert!(reject_unchanged(&plan,owner,&relocated).contains("placement/reservation"));
}

#[test]
fn active_operand_source_comparator_accepts_owner845759_and_rejects_isolated_mutants() {
    let owner=845759usize;
    let parent=WorkTreeHistoryPlan::compile(1827840,21,[0;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();let scheduled=Scheduled::eligible08();
    let plan=RowPlan::new(&roster,&scheduled).unwrap();let batch=plan.stage_owner(owner).unwrap();
    let accepted_count=compare_source_to_stream(&plan,&batch,owner,batch.active_operands()).unwrap();
    assert_eq!(accepted_count,batch.visit_active_operands(|_|Ok(())).unwrap());
    assert!(accepted_count>0);

    // Drop one active occurrence and duplicate a later, distinct occurrence.
    // The stream length remains constant, so only ordered source comparison detects it.
    let omitted=batch.active_operands().next().unwrap();
    let duplicate_index=batch.active_operands().position(|operand|operand.occurrence!=omitted.occurrence)
        .expect("owner845759 has active operands in multiple term occurrences");
    let duplicate=batch.active_operands().nth(duplicate_index).unwrap();
    assert_ne!(omitted.occurrence,duplicate.occurrence);
    assert_eq!(omit_first_and_duplicate_at(&batch,duplicate_index).count(),accepted_count);
    assert!(matches!(compare_source_to_stream(&plan,&batch,owner,
        omit_first_and_duplicate_at(&batch,duplicate_index)),Err(CensusError::Mismatch{..})));

    // The retained HEADER stream excludes the scheduled source term. Reinsert
    // its active operand after the staged census and require a named extra error.
    let retired_counts=plan.header.header_terms(owner).unwrap().retired;
    let role=retired_counts.iter().position(|count|*count>0).expect("owner845759 has an active scheduled HEADER retirement");
    const RANGES:[(usize,usize);4]=[(356632,357305),(357305,357978),(357978,360026),(360026,362074)];
    let(start,end)=RANGES[role];let mut retired_source=None;
    roster.visit_header_terms(owner as u64,|source|{
        let q=source.row.checked_sub(owner*ROWS).ok_or("retired source ROW owner")?;
        if retired_source.is_none()&&(start..end).contains(&q){retired_source=Some(source);}
        Ok(())
    }).unwrap();
    let retired=retired_source.expect("active scheduled HEADER anchor exists in source traversal");
    assert_eq!((retired.gate.c0,retired.gate.c1,retired.gate.c2,retired.gate.c3),
        (Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()));
    let local=retired.row-owner*ROWS;let resurrected=ActiveOperand{occurrence:batch.terms.len(),
        relation:Relation::Header,row:owner*ROWS+literal(batch.class,Relation::Header,local),
        side:OperandSide::Left,wire:retired.gate.left,c1_active:true,c2_active:false,c3_active:false};
    assert!(matches!(compare_source_to_stream(&plan,&batch,owner,
        batch.active_operands().chain(std::iter::once(resurrected))),Err(CensusError::Extra{..})));
}

#[test]
fn active_operand_side_swap_of_distinct_wires_is_detected_when_hypothetical_bits_coincide() {
    let batch=diagnostic_batch(vec![gate_term(7,11,19,Fr::zero(),Fr::zero(),Fr::zero(),Fr::one())]);
    let expected=[
        ActiveOperand{occurrence:0,relation:Relation::Header,row:7,side:OperandSide::Left,
            wire:11,c1_active:false,c2_active:false,c3_active:true},
        ActiveOperand{occurrence:0,relation:Relation::Header,row:7,side:OperandSide::Right,
            wire:19,c1_active:false,c2_active:false,c3_active:true},
    ];
    assert_ne!(expected[0].wire,expected[1].wire);
    let hypothetical_by_wire=[(expected[0].wire,false),(expected[1].wire,false)];
    assert_eq!(hypothetical_by_wire[0].1,hypothetical_by_wire[1].1);
    assert_eq!(compare_expected_to_stream(expected.iter().copied(),batch.active_operands()),Ok(2));
    let side_swapped=batch.active_operands().map(|mut operand|{
        operand.side=match operand.side{OperandSide::Left=>OperandSide::Right,OperandSide::Right=>OperandSide::Left};
        operand
    });
    assert!(matches!(compare_expected_to_stream(expected.iter().copied(),side_swapped),
        Err(CensusError::Mismatch{..})));
}

#[test]
fn active_operand_c1_c2_c3_activation_and_inactive_constant_branch_are_separate() {
    let batch=diagnostic_batch(vec![
        gate_term(10,11,21,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()),
        gate_term(11,12,22,Fr::zero(),Fr::zero(),Fr::one(),Fr::zero()),
        gate_term(12,13,23,Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()),
        gate_term(13,14,24,Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()),
    ]);
    let active=collect_active(&batch);
    assert_eq!(active,vec![
        ActiveOperand{occurrence:0,relation:Relation::Header,row:10,side:OperandSide::Left,
            wire:11,c1_active:true,c2_active:false,c3_active:false},
        ActiveOperand{occurrence:1,relation:Relation::Header,row:11,side:OperandSide::Right,
            wire:22,c1_active:false,c2_active:true,c3_active:false},
        ActiveOperand{occurrence:2,relation:Relation::Header,row:12,side:OperandSide::Left,
            wire:13,c1_active:false,c2_active:false,c3_active:true},
        ActiveOperand{occurrence:2,relation:Relation::Header,row:12,side:OperandSide::Right,
            wire:23,c1_active:false,c2_active:false,c3_active:true},
    ]);
}

#[test]
fn header_not_q14908_wrong_author_rejects_equal_bit_before_read() {
    let owner=845_759usize;
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[0;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    assert!(RowPlan::new(&roster,&Scheduled::new()).err().unwrap()
        .contains("exact Eligible08 cut"));
    let scheduled=Scheduled::eligible08();
    let plan=RowPlan::new(&roster,&scheduled).unwrap();let batch=plan.stage_owner(owner).unwrap();
    let target=batch.active_operands().find(|operand|
        operand.relation==Relation::Header && operand.row==owner*ROWS+14_908
            && operand.wire==owner*WIDTH+526_330).expect("retained HEADER NOT q14908/X526330");
    assert_eq!(target.side,OperandSide::Left);
    assert!(target.c1_active && !target.c2_active && !target.c3_active);
    let mask=parent.physical_assignment_replacement_mask(owner as u64).unwrap();
    assert!(!mask[526_330],"native parent still owns the HEADER NOT wire");
    let binding=batch.source_binding_for_test();
    let wrong=NativeHeaderSourceLease::wrong_author_for_test(binding.clone(),target.wire,false);
    let error=batch.resolve_one(target.occurrence,target.side,&wrong).unwrap_err();
    assert!(error.contains("author mismatch before read admission"),"{error}");
    assert_eq!(wrong.read_count_for_test(),0);
    // This is the isolated removal mutant: the same coordinate and bit pass
    // when only the author predicate is skipped.
    assert_eq!(wrong.removed_author_check_mutant_for_test(&binding,target.wire).unwrap(),Some(false));
    assert_eq!(wrong.read_count_for_test(),1);
    let wrong_owner_binding=HeaderSourceBinding::for_plan(&parent,owner-1).unwrap();
    let wrong_owner=NativeHeaderSourceLease::wrong_author_for_test(wrong_owner_binding,
        (owner-1)*WIDTH+526_330,false);
    assert!(batch.resolve_one(target.occurrence,target.side,&wrong_owner).unwrap_err()
        .contains("root/total/profile/cut/layout/owner"));
    assert_eq!(wrong_owner.read_count_for_test(),0);

    // A shaped one-cell diagnostic keeps all other local and foreign reads
    // typed open; it is not a complete owner witness or source publication.
    let shaped=NativeHeaderSourceLease::wrong_author_for_test(binding.clone(),target.wire,false)
        .native_author_shape_for_test();
    let local=batch.active_operands().find(|operand|operand.wire/WIDTH==owner
        && operand.wire!=target.wire).expect("other active local operand");
    assert!(matches!(batch.resolve_one(local.occurrence,local.side,&shaped).unwrap(),
        SourceRead::Unresolved{reason:UnresolvedRead::UnqualifiedLocal,..}));
    let foreign=batch.active_operands().find(|operand|operand.wire/WIDTH!=owner)
        .expect("foreign active operand");
    assert!(matches!(batch.resolve_one(foreign.occurrence,foreign.side,&shaped).unwrap(),
        SourceRead::Unresolved{reason:UnresolvedRead::ForeignOwner,..}));
}

#[test]
fn wrong_header_author_emits_no_foreign_result_before_rejection() {
    let batch=diagnostic_batch(vec![
        gate_term(10,WIDTH+7,0,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()),
        gate_term(11,7,0,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()),
    ]);
    assert_eq!(batch.active_operands().next().unwrap().wire/WIDTH,1);
    let lease=NativeHeaderSourceLease::wrong_author_for_test(
        batch.source_binding_for_test(),7,false);
    let mut emitted=0usize;
    let error=batch.visit_source_reads(&lease,|_|{emitted+=1;Ok(())}).unwrap_err();
    assert!(error.contains("author mismatch before read admission"),"{error}");
    assert_eq!(emitted,0);
    assert_eq!(lease.read_count_for_test(),0);
}

#[test]
fn c451_general_paired_map_stages_bounded_owner_classes_and_rejects_mutants_no_frame() {
    use crate::bank53_map::{self,CutDescriptor};
    use crate::legacy_envelope_map::{LowerBranch,LowerSelector,LowerSource,Map};
    use crate::packed_owner_assembly::{Eligible08MapPairLease,HeaderSourceBinding};

    const N:usize=1_827_840;
    const S:usize=2_097_152;
    let parent=WorkTreeHistoryPlan::compile(N as u64,21,[0x45;32],[0x46;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let cut=CutDescriptor::eligible08();
    assert_eq!(cut.terminals(),[N,1_810_842]);
    let selected_lower=LowerSelector{
        source:LowerSource::HeaderDifficulty{height:841_729},
        branch:LowerBranch::Pivot(54),
    };
    let maps=[
        Map::new_modern_global_u_selected_lower(N as u64,21,55,selected_lower).unwrap(),
        Map::new_modern_global_u_selected_lower(1_810_842,21,55,selected_lower).unwrap(),
    ];
    let scheduled=Scheduled::eligible08();
    let plan=RowPlan::new(&roster,&scheduled).unwrap();
    let layout=Layout::paired_map_general();
    assert!(layout.descriptor().starts_with(b"c451-row19-paired-map-general-v4\0"));
    assert_ne!(layout.digest(),Layout::fixed().digest());
    assert_ne!(layout.digest(),Layout::paired_map().digest());
    assert_ne!(layout.digest(),AnchorLayout::digest(),"general v4 remains distinct from first-anchor v3");

    // Source class is taken from the actual H21 roster. The small dynamic
    // search only finds a representative Mature class; this is not an owner scan.
    let mature=(2..100_000usize).find(|owner|
        matches!(roster.owner_class(*owner as u64).unwrap(),OwnerClass::Mature(_)))
        .expect("bounded H21 Mature representative");
    assert_eq!(roster.owner_class(0).unwrap(),OwnerClass::Genesis);
    assert_eq!(roster.owner_class(1).unwrap(),OwnerClass::Initial);
    assert_eq!(roster.owner_class(1_024).unwrap(),OwnerClass::Singleton);
    assert_eq!(roster.owner_class(2_048).unwrap(),OwnerClass::M1);
    assert_eq!(roster.owner_class(3_072).unwrap(),OwnerClass::Short(Profile::M2));
    assert_eq!(roster.owner_class(417_791).unwrap(),OwnerClass::FixedV2);
    assert!(matches!(roster.owner_class(mature as u64).unwrap(),OwnerClass::Mature(_)));
    let mut owners=vec![
        0,1,2,1_024,2_048,3_072,417_790,417_791,417_792,841_727,845_758,845_760,
        mature,N-1,N,S-1,
    ];
    for terminal in cut.terminals().map(|x|x as usize) {
        owners.extend([terminal-2,terminal-1,terminal]);
    }
    // Include Map schedule representatives in the same staging gate. Tier
    // dispatch itself is checked below, including the q=407 hole.
    owners.extend([959,9_151,417_727,418_751,843_711,844_735]);
    owners.sort_unstable();owners.dedup();

    let mut saw_non_genesis_map_count=false;
    let mut has_foreign_map_x=false;
    let mut carry_batch=None;
    for owner in owners {
        assert!(owner<S);
        let class=roster.owner_class(owner as u64).unwrap();
        let binding=HeaderSourceBinding::for_plan(&parent,owner).unwrap();
        let lease=Eligible08MapPairLease::synthetic_valid_for_test(
            binding.clone(),owner,class,maps.clone(),
        ).unwrap();
        let batch=plan.stage_owner_with_map_pair_general(owner,&lease)
            .unwrap_or_else(|error|panic!("C451 general stage owner={owner} class={class:?}: {error}"));
        assert_eq!(batch.owner(),owner);
        assert_eq!(batch.class(),class);
        assert_eq!(batch.source_binding(),&binding);
        assert_eq!(batch.layout_digest(),layout.digest());
        for context in 0..2 {
            let source_terms=bank53_map::map_owner_terms_for_descriptor(
                &maps[context],owner as u64,context,cut,
            ).unwrap();
            let expected=source_terms.iter().map(|term|
                c439_independent_relocation(term,context)).collect::<Vec<_>>();
            assert_eq!(batch.map_terms(context).unwrap(),expected.as_slice(),
                "ordered source-derived and independently relocated Map terms owner={owner} context={context}");
            assert_eq!(batch.counts()[9+context],source_terms.len(),
                "branch-specific count comes from this owner's source terms");
            saw_non_genesis_map_count|=source_terms.len()!=7_579;
            if owner==9_151 {
                has_foreign_map_x|=batch.map_terms(context).unwrap().iter().any(|term|
                    term.gate.left/WIDTH!=owner || term.gate.right/WIDTH!=owner);
            }
        }
        if owner==845_760 {carry_batch=Some(batch);}
    }
    assert!(saw_non_genesis_map_count,
        "at least one tested branch must differ from Genesis's 7,579 retained-term count");
    assert!(has_foreign_map_x,"tier-branch Map source may carry foreign-owner X operands");

    // Exercise the registry atomicity and the critical binding/term/ROW
    // boundaries on the selected Carry shape. Synthetic Map sources establish
    // only structure and geometry, never physical authentication.
    let owner=845_760usize;
    let batch=carry_batch.expect("C450 Carry representative retained");
    assert_eq!(roster.owner_class(owner as u64).unwrap(),OwnerClass::Carry);
    let mut registry=plan.registry_with_map_pair_general(owner).unwrap();
    let before=registry.clone();
    registry.commit_map_pair(&batch).expect("one general paired Map commit");
    let committed=registry.clone();
    assert!(registry.commit_map_pair(&batch).is_err());
    assert_eq!(registry,committed,"duplicate commit preserves registry state");
    assert_ne!(registry,before);

    let mut wrong_owner_registry=plan.registry_with_map_pair_general(owner+1).unwrap();
    let wrong_owner_before=wrong_owner_registry.clone();
    assert!(wrong_owner_registry.commit_map_pair(&batch).is_err());
    assert_eq!(wrong_owner_registry,wrong_owner_before,"wrong-owner rejection is atomic");

    let reject_unchanged=|bad:&crate::header_daa_row_placement::PairedMapBatch,expected:&str| {
        let mut candidate=plan.registry_with_map_pair_general(owner).unwrap();
        let snapshot=candidate.clone();
        let error=candidate.commit_map_pair(bad).unwrap_err();
        assert!(error.contains(expected),"unexpected rejection: {error}");
        assert_eq!(candidate,snapshot,"rejected v4 batch must not mutate registry");
    };
    let binding=batch.source_binding().clone();
    for field in 0..6 {
        let mut bad=batch.clone();
        *bad.source_binding_mut_for_test()=binding.mutated_field_for_test(field);
        reject_unchanged(&bad,"source tuples/binding");
    }
    let mut wrong_class=batch.clone();
    *wrong_class.class_mut_for_test()=OwnerClass::Initial;
    reject_unchanged(&wrong_class,"source tuples/binding");
    let mut old_layout=batch.clone();old_layout.layout_mut_for_test()[0]^=1;
    reject_unchanged(&old_layout,"source tuples/binding");

    let mut missing=batch.clone();missing.map_terms_mut_for_test(0).remove(0);
    reject_unchanged(&missing,"source tuples");
    let mut duplicate=batch.clone();
    let first=duplicate.map_terms(0).unwrap()[0].clone();
    duplicate.map_terms_mut_for_test(0).push(first);
    reject_unchanged(&duplicate,"source tuples");
    let mut swapped=batch.clone();
    let left=swapped.map_terms(0).unwrap().to_vec();
    let right=swapped.map_terms(1).unwrap().to_vec();
    *swapped.map_terms_mut_for_test(0)=right;
    *swapped.map_terms_mut_for_test(1)=left;
    reject_unchanged(&swapped,"source tuples");

    let mut cross_relation=batch.clone();
    let native_row=cross_relation.terms().next().expect("ordinary staged tuple").1.row;
    cross_relation.map_terms_mut_for_test(0)[0].row=native_row;
    cross_relation.expected_maps[0][0].row=native_row;
    reject_unchanged(&cross_relation,"cross-relation ROW collision");

    // Address locality applies to ROW destinations. The typed Map operands
    // themselves may legitimately import X values from other owners.
    let mut foreign_row=batch.clone();
    foreign_row.map_terms_mut_for_test(0)[0].row+=ROWS;
    foreign_row.expected_maps[0][0].row+=ROWS;
    reject_unchanged(&foreign_row,"ROW batch physical owner");

    // Padding still receives both canonical Map equation lists. This test
    // does not establish or mint any HEADER-zero physical-author claim.
    for owner in [N,S-1] {
        assert_eq!(roster.owner_class(owner as u64).unwrap(),OwnerClass::Padding);
        let binding=HeaderSourceBinding::for_plan(&parent,owner).unwrap();
        let lease=Eligible08MapPairLease::synthetic_valid_for_test(
            binding,owner,OwnerClass::Padding,maps.clone(),
        ).unwrap();
        let padded=plan.stage_owner_with_map_pair_general(owner,&lease)
            .unwrap_or_else(|error|panic!("C451 padding structural Map stage owner={owner}: {error}"));
        assert!(!padded.map_terms(0).unwrap().is_empty());
        assert!(!padded.map_terms(1).unwrap().is_empty());
        assert_eq!(padded.class(),OwnerClass::Padding);
    }
}

#[test]
fn c504_initial_paired_map_header_source_stop_no_frame() -> Result<(), String> {
    use crate::bank53_map::{self, CutDescriptor};
    use crate::bank53_required_writer::{required_bank53_writer, RequiredWriter};
    use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map};
    use crate::packed_owner_assembly::{Eligible08MapPairLease, HeaderSourceBinding};

    const OWNER: usize = 1;
    const BASE: usize = 671_744;
    const CONTEXT_BITS: usize = 8_192;
    const LIVE: usize = 5_757;
    let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0x52; 32], [0x53; 28])?;
    let roster = DaaHistoryRoster::compile(&parent)?;
    let class = roster.owner_class(OWNER as u64)?;
    assert_eq!(class, OwnerClass::Initial);
    let scheduled = Scheduled::eligible08();
    let counts = scheduled.visit_owner(OWNER, |_, _| Ok(()))?;
    assert_eq!(counts.max, [0; 2]);
    assert_eq!(counts.cap, [0; 2]);
    let mut census = [0usize; 2];
    for context in 0..2 {
        for offset in 0..CONTEXT_BITS {
            match required_bank53_writer(OWNER, context, offset).map_err(|e| e.to_string())? {
                RequiredWriter::Map { context: found } if found == context && offset < LIVE => census[0] += 1,
                RequiredWriter::HeaderZero if offset >= LIVE => census[1] += 1,
                other => return Err(format!("C504 policy context={context} offset={offset} writer={other:?}")),
            }
        }
    }
    assert_eq!(census, [11_514, 4_870]);
    let lower = LowerSelector { source: LowerSource::HeaderDifficulty { height: 841_729 },
        branch: LowerBranch::Pivot(54) };
    let maps = [Map::new_modern_global_u_selected_lower(1_827_840, 21, 55, lower)?,
        Map::new_modern_global_u_selected_lower(1_810_842, 21, 55, lower)?];
    let binding = HeaderSourceBinding::for_plan(&parent, OWNER)?;
    let lease = Eligible08MapPairLease::synthetic_valid_for_test(binding.clone(), OWNER, class, maps.clone())?;
    assert_eq!(lease.checked_cells(&binding, OWNER, class)?.len(), census[0]);
    let plan = RowPlan::new(&roster, &scheduled)?;
    let batch = plan.stage_owner_with_map_pair_general(OWNER, &lease)?;
    assert_eq!(batch.owner(), OWNER);
    assert_eq!(batch.class(), class);
    assert_eq!(batch.source_binding(), &binding);
    assert_eq!(batch.layout_digest(), Layout::paired_map_general().digest());
    for context in 0..2 {
        let source = bank53_map::map_owner_terms_for_descriptor(
            &maps[context], OWNER as u64, context, CutDescriptor::eligible08())?;
        let placed = source.iter().map(|term| c439_independent_relocation(term, context)).collect::<Vec<_>>();
        assert_eq!(batch.map_terms(context)?, placed.as_slice());
        assert_eq!(batch.counts()[9 + context], source.len());
    }
    let mut anchor = 0usize;
    let mut map_sides = [[false; 2]; 2];
    let mut first_overlap = None;
    for operand in batch.active_operands() {
        match operand.relation {
            Relation::Header => {
                if operand.row == OWNER * ROWS + 356_632
                    && operand.wire == OWNER * WIDTH + 999_424 && operand.side == OperandSide::Left {
                    anchor += 1;
                }
                if operand.wire / WIDTH == OWNER {
                    let local = operand.wire % WIDTH;
                    if (BASE..BASE + 2 * CONTEXT_BITS).contains(&local)
                        && (local - BASE) % CONTEXT_BITS < LIVE && first_overlap.is_none() {
                        first_overlap = Some(operand);
                    }
                }
            }
            Relation::Map(context) if context < 2 => {
                let wire = OWNER * WIDTH + BASE + context * CONTEXT_BITS;
                let row = OWNER * ROWS + [477_074, 492_305][context];
                if operand.wire == wire && operand.row == row {
                    match operand.side { OperandSide::Left => map_sides[context][0] = true,
                        OperandSide::Right => map_sides[context][1] = true }
                }
            }
            _ => {}
        }
    }
    assert_eq!(anchor, 1, "C504 retained HEADER anchor control");
    assert_eq!(map_sides, [[true; 2]; 2], "C504 Map Boolean LEFT/RIGHT controls");
    if let Some(operand) = first_overlap {
        return Err(format!("C504 retained HEADER reads Map LIVE occurrence={} row={} side={:?} wire={}",
            operand.occurrence, operand.row, operand.side, operand.wire));
    }
    Ok(())
}

#[test]
fn c502_early_carry_paired_map_header_source_stop_no_frame() -> Result<(), String> {
    use crate::bank53_map::{self, CutDescriptor};
    use crate::bank53_required_writer::{required_bank53_writer, RequiredWriter};
    use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map};
    use crate::packed_owner_assembly::{Eligible08MapPairLease, HeaderSourceBinding};

    const N: usize = 1_827_840;
    const MAP_BASE: usize = 671_744;
    const CONTEXT_BITS: usize = 8_192;
    const MAP_LIVE: usize = 5_757;
    const EXPECTED_MAP_TERMS: usize = 7_579;
    const HEADER_ANCHOR_ROW: usize = 356_632;
    const HEADER_ANCHOR_WIRE: usize = 999_424;

    // The fixture has the real H21 owner calendar and Eligible08 cuts, but no
    // NativePrefix. Its Map bits/import values are synthetic geometry only.
    let parent = WorkTreeHistoryPlan::compile(N as u64, 21, [0x52; 32], [0x53; 28])?;
    let roster = DaaHistoryRoster::compile(&parent)?;
    let scheduled = Scheduled::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled)?;
    let cut = CutDescriptor::eligible08();
    let lower = LowerSelector {
        source: LowerSource::HeaderDifficulty { height: 841_729 },
        branch: LowerBranch::Pivot(54),
    };
    let maps = [
        Map::new_modern_global_u_selected_lower(N as u64, 21, 55, lower)?,
        Map::new_modern_global_u_selected_lower(1_810_842, 21, 55, lower)?,
    ];
    let mut checked_owners = 0usize;

    for owner in [844_673usize, 844_674] {
        let class = roster.owner_class(owner as u64)?;
        assert_eq!(class, OwnerClass::Carry, "C502 owner {owner} must be Carry");
        let scheduled_counts = scheduled.visit_owner(owner, |_, _| Ok(()))?;
        assert_eq!(scheduled_counts.max, [0; 2], "C502 owner {owner} has MAX writer");
        assert_eq!(scheduled_counts.cap, [0; 2], "C502 owner {owner} has Cap writer");

        let mut map_policy = 0usize;
        let mut header_zero_policy = 0usize;
        for context in 0..2 {
            for offset in 0..CONTEXT_BITS {
                match required_bank53_writer(owner, context, offset)
                    .map_err(|error| error.to_string())?
                {
                    RequiredWriter::Map { context: found } if found == context => {
                        map_policy += 1;
                    }
                    RequiredWriter::HeaderZero => {
                        header_zero_policy += 1;
                    }
                    other => {
                        return Err(format!(
                            "C502 owner {owner} unexpected Bank53 writer context={context} offset={offset} writer={other:?}"
                        ));
                    }
                }
            }
        }
        assert_eq!((map_policy, header_zero_policy), (11_514, 4_870));

        let binding = HeaderSourceBinding::for_plan(&parent, owner)?;
        let lease = Eligible08MapPairLease::synthetic_valid_for_test(
            binding.clone(), owner, class, maps.clone(),
        )?;
        assert_eq!(lease.checked_cells(&binding, owner, class)?.len(), map_policy);
        let batch = row_plan.stage_owner_with_map_pair_general(owner, &lease)?;
        assert_eq!(batch.owner(), owner);
        assert_eq!(batch.class(), OwnerClass::Carry);
        assert_eq!(batch.source_binding(), &binding);
        assert_eq!(batch.layout_digest(), Layout::paired_map_general().digest());

        let base_occurrences = batch.base_terms().len();
        let mut map_occurrences = [0usize; 2];
        for context in 0..2 {
            let source = bank53_map::map_owner_terms_for_descriptor(
                &maps[context], owner as u64, context, cut,
            )?;
            assert_eq!(
                source.len(), EXPECTED_MAP_TERMS,
                "C502 owner {owner} context {context} synthetic guard/lower term count"
            );
            let placed = source.iter().map(|term|
                c439_independent_relocation(term, context)
            ).collect::<Vec<_>>();
            assert_eq!(
                batch.map_terms(context)?, placed.as_slice(),
                "C502 owner {owner} context {context} ordered Map source/ROW placement"
            );
            assert_eq!(batch.counts()[9 + context], source.len());
            map_occurrences[context] = source.len();
        }

        let mut header_reads = 0usize;
        let mut header_anchor_reads = 0usize;
        let mut map_reads = [0usize; 2];
        let mut first_map: [Option<ActiveOperand>; 2] = [None, None];
        let mut first_map_right: [Option<ActiveOperand>; 2] = [None, None];
        for operand in batch.active_operands() {
            let active_side = match operand.side {
                OperandSide::Left => operand.c1_active || operand.c3_active,
                OperandSide::Right => operand.c2_active || operand.c3_active,
            };
            assert!(active_side, "C502 inactive operand entered source scan");
            match operand.relation {
                Relation::Header => {
                    header_reads += 1;
                    if operand.row == owner * ROWS + HEADER_ANCHOR_ROW
                        && operand.wire == owner * WIDTH + HEADER_ANCHOR_WIRE
                        && operand.side == OperandSide::Left
                    {
                        header_anchor_reads += 1;
                    }
                    if operand.wire / WIDTH != owner {
                        continue;
                    }
                    let local = operand.wire % WIDTH;
                    if (MAP_BASE..MAP_BASE + 2 * CONTEXT_BITS).contains(&local) {
                        let context = (local - MAP_BASE) / CONTEXT_BITS;
                        let offset = (local - MAP_BASE) % CONTEXT_BITS;
                        if offset < MAP_LIVE {
                            return Err(format!(
                                "C502 retained HEADER reads transferred Map LIVE owner={owner} context={context} occurrence={} row={} side={:?} wire={}",
                                operand.occurrence, operand.row, operand.side, operand.wire
                            ));
                        }
                    }
                }
                Relation::Map(context) if context < 2 => {
                    map_reads[context] += 1;
                    if first_map[context].is_none() {
                        first_map[context] = Some(operand);
                    } else if first_map_right[context].is_none()
                        && first_map[context].is_some_and(|first|
                            first.occurrence == operand.occurrence)
                    {
                        first_map_right[context] = Some(operand);
                    }
                }
                _ => {}
            }
        }

        assert!(header_reads > 0, "C502 empty HEADER active-operand scan");
        assert_eq!(
            header_anchor_reads, 1,
            "C502 owner {owner} retained unscheduled HEADER anchor control"
        );
        for context in 0..2 {
            assert!(map_reads[context] > 0, "C502 empty Map context {context} scan");
            let first = first_map[context].ok_or("C502 first Map operand absent")?;
            let right = first_map_right[context].ok_or("C502 first Map RIGHT operand absent")?;
            let expected_occurrence = base_occurrences
                + if context == 0 { 0 } else { map_occurrences[0] };
            let expected_wire = owner * WIDTH + MAP_BASE + context * CONTEXT_BITS;
            let expected_row = owner * ROWS + [477_074, 492_305][context];
            assert_eq!(first.occurrence, expected_occurrence);
            assert_eq!(first.relation, Relation::Map(context));
            assert_eq!(first.row, expected_row);
            assert_eq!(first.side, OperandSide::Left);
            assert_eq!(first.wire, expected_wire);
            assert!(first.c1_active && first.c3_active && !first.c2_active);
            assert_eq!(right.occurrence, first.occurrence);
            assert_eq!(right.row, expected_row);
            assert_eq!(right.side, OperandSide::Right);
            assert_eq!(right.wire, expected_wire);
            assert!(!right.c1_active && !right.c2_active && right.c3_active);
        }
        // The HEADER anchor and both Boolean Map sides make an empty or
        // constant-only scan incapable of passing the stop check.
        checked_owners += 1;
    }

    assert_eq!(checked_owners, 2);
    println!(
        "C502_C451_EARLY_CARRY_MAP_HEADER_SOURCE_STOP_PASS owners=844673,844674 map_cells_each=11514 required_header_zero_each=4870 map_terms_each_context=7579 header_anchor_each=1 coefficient_aware_sides=true synthetic=true frame=false native_map_pair=false full_row=false"
    );
    Ok(())
}

#[test]
fn c451_general_map_tier_branches_and_cut_edges_are_explicit_no_frame() {
    use crate::bank53_map::{self,CutDescriptor};
    use crate::legacy_envelope_map::{LowerBranch,LowerSelector,LowerSource,Map};

    const N:u64=1_827_840;
    let cut=CutDescriptor::eligible08();
    let terminals=cut.terminals();
    let lower=LowerSelector{source:LowerSource::HeaderDifficulty{height:841_729},
        branch:LowerBranch::Pivot(54)};
    let maps=[
        Map::new_modern_global_u_selected_lower(terminals[0] as u64,21,55,lower).unwrap(),
        Map::new_modern_global_u_selected_lower(terminals[1] as u64,21,55,lower).unwrap(),
    ];

    for q in 0..=8u64 {
        let s=1024*q+959;
        for map in &maps {assert_eq!(map.tier(s).unwrap(),Some(q.min(8) as usize),"q={q}");}
    }
    for map in &maps {
        assert_eq!(map.tier(1024*407+959).unwrap(),None,"q=407 excluded tier");
        assert_eq!(map.tier(1024*408+959).unwrap(),Some(8),"q=408 resumes capped tier");
        assert_eq!(map.tier(1024*823+959).unwrap(),Some(8),"q=823 upper boundary");
        assert_eq!(map.tier(1024*824+959).unwrap(),None,"q=824 excluded upper boundary");
        assert_eq!(map.tier(N-1).unwrap(),None,"non-anchor terminal neighbor");
    }

    // Materialize only selected owner-local lists. Their sizes are read from
    // map_owner_terms_for_descriptor; no Genesis count is used as a gate.
    let mut non_genesis_count=false;
    for (context,map) in maps.iter().enumerate() {
        for q in [0u64,8,407,408,823,824] {
            let owner=1024*q+959;
            let terms=bank53_map::map_owner_terms_for_descriptor(map,owner,context,cut).unwrap();
            assert!(!terms.is_empty(),"owner={owner} context={context}");
            non_genesis_count|=terms.len()!=7_579;
        }
        for terminal in terminals {
            for owner in [terminal-2,terminal-1,terminal] {
                let terms=bank53_map::map_owner_terms_for_descriptor(map,owner as u64,context,cut).unwrap();
                assert!(terms.iter().all(|term|term.row/bank53_map::ROW_STRIDE==owner),
                    "Map source ROWs remain owner-local at cut edge owner={owner} context={context}");
            }
        }
    }
    assert!(non_genesis_count,"tier/cut samples include dynamic counts beyond Genesis 7,579");
}

// Deliberately tiny, self-consistent structural fixture. Its selected-owner
// identity does not establish native history or physical source authority.
fn c453_diagnostic_paired() -> PairedMapBatch {
    let owner=CAP0_OWNER;let row=owner*ROWS;let wire=owner*WIDTH;
    let mut base=diagnostic_batch(vec![
        gate_term(row+10,wire+99,wire+98,Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero()),
        gate_term(row+11,wire+7,wire+98,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()),
        gate_term(row+12,wire+7,wire+7,Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()),
        gate_term(row+13,wire+99,wire+11,Fr::zero(),Fr::zero(),Fr::one(),Fr::zero()),
    ]);
    base.owner=owner;base.class=OwnerClass::Carry;
    base.source=HeaderSourceBinding::diagnostic_for_test(owner);
    let base=Arc::new(base);
    let maps=[vec![
        gate_term(row+477_074,wire+99,wire+98,Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero()),
        gate_term(row+477_075,wire+111,wire+98,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()),
        gate_term(row+477_076,wire+111,wire+111,Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()),
    ],vec![
        gate_term(row+492_305,wire+99,wire+222,Fr::zero(),Fr::zero(),Fr::one(),Fr::zero()),
    ]];
    PairedMapBatch{source:base.source.clone(),class:base.class,
        base:base.clone(),expected_base:base,maps:maps.clone(),expected_maps:maps,
        map_relations:[Relation::Map(0),Relation::Map(1)],
        layout:Layout::paired_map_general().digest(),expected_layout:Layout::paired_map_general().digest()}
}

#[test]
fn c453_paired_occurrences_count_constants_and_preserve_repeated_sides_no_frame() {
    let paired=c453_diagnostic_paired();let row=CAP0_OWNER*ROWS;let wire=CAP0_OWNER*WIDTH;
    paired.check_source_tuples().unwrap();
    let expected=[
        ActiveOperand{occurrence:1,relation:Relation::Header,row:row+11,side:OperandSide::Left,
            wire:wire+7,c1_active:true,c2_active:false,c3_active:false},
        ActiveOperand{occurrence:2,relation:Relation::Header,row:row+12,side:OperandSide::Left,
            wire:wire+7,c1_active:false,c2_active:false,c3_active:true},
        ActiveOperand{occurrence:2,relation:Relation::Header,row:row+12,side:OperandSide::Right,
            wire:wire+7,c1_active:false,c2_active:false,c3_active:true},
        ActiveOperand{occurrence:3,relation:Relation::Header,row:row+13,side:OperandSide::Right,
            wire:wire+11,c1_active:false,c2_active:true,c3_active:false},
        ActiveOperand{occurrence:5,relation:Relation::Map(0),row:row+477_075,side:OperandSide::Left,
            wire:wire+111,c1_active:true,c2_active:false,c3_active:false},
        ActiveOperand{occurrence:6,relation:Relation::Map(0),row:row+477_076,side:OperandSide::Left,
            wire:wire+111,c1_active:false,c2_active:false,c3_active:true},
        ActiveOperand{occurrence:6,relation:Relation::Map(0),row:row+477_076,side:OperandSide::Right,
            wire:wire+111,c1_active:false,c2_active:false,c3_active:true},
        ActiveOperand{occurrence:7,relation:Relation::Map(1),row:row+492_305,side:OperandSide::Right,
            wire:wire+222,c1_active:false,c2_active:true,c3_active:false},
    ];
    assert_eq!(paired.terms().count(),8);
    assert_eq!(paired.active_operands().collect::<Vec<_>>(),expected);
    assert_eq!(paired.base.active_operands().collect::<Vec<_>>(),expected[..4]);
    // Equal-wire products still carry two distinct operand occurrences.
    assert_eq!(expected[1].wire,expected[2].wire);
    assert_ne!(expected[1].side,expected[2].side);
    assert_eq!(expected[5].wire,expected[6].wire);
    assert_ne!(expected[5].side,expected[6].side);
    let mut reordered=expected;reordered.swap(5,6);
    assert!(matches!(compare_expected_to_stream(expected.into_iter(),reordered.into_iter()),
        Err(CensusError::Mismatch{..})));
    let omitted=expected.into_iter().filter(|operand|!(operand.occurrence==6&&operand.side==OperandSide::Right));
    assert!(compare_expected_to_stream(expected.into_iter(),omitted).is_err());
    let duplicate=expected.into_iter().chain(std::iter::once(expected[7]));
    assert!(matches!(compare_expected_to_stream(expected.into_iter(),duplicate),Err(CensusError::Extra{..})));
}

#[test]
fn c453_c370_adoption_checks_complete_base_and_each_read_occurrence_no_frame() {
    let paired=c453_diagnostic_paired();let base=paired.base.as_ref();
    let reads=base.active_operands().map(|operand|NativeRead::Header{operand,value:false})
        .collect::<Vec<_>>();
    assert_eq!(reads.len(),4);
    paired.checked_adopt_c370_parts(base,&reads,CAP0_OWNER).unwrap();
    assert!(paired.checked_adopt_c370_parts(base,&reads,CAP0_OWNER+1).unwrap_err()
        .contains("complete ordinary batch mismatch"));
    let reject_base=|bad:Batch|{
        assert!(paired.checked_adopt_c370_parts(&bad,&reads,CAP0_OWNER).unwrap_err()
            .contains("complete ordinary batch mismatch"));
    };
    let mut bad=base.clone();bad.owner+=1;reject_base(bad);
    let mut bad=base.clone();bad.class=OwnerClass::Initial;reject_base(bad);
    let mut bad=base.clone();bad.layout[0]^=1;reject_base(bad);
    for field in 0..6 {
        let mut bad=base.clone();bad.source=base.source.mutated_field_for_test(field);reject_base(bad);
    }
    let mut bad=base.clone();bad.expected[0]+=1;reject_base(bad);
    let mut bad=base.clone();bad.relations[0]=Some(Relation::DaaLane(0));reject_base(bad);
    let mut bad=base.clone();bad.terms[1].relation=Relation::DaaLane(0);reject_base(bad);
    let mut bad=base.clone();bad.terms[1].term.row+=1;reject_base(bad);
    let mut bad=base.clone();bad.terms[1].term.gate.left+=1;reject_base(bad);
    let mut bad=base.clone();bad.terms[1].term.gate.c1+=Fr::one();reject_base(bad);
    // Omitting a zero-only term changes no active values, but changes the
    // complete base and all subsequent term ordinals.
    let mut bad=base.clone();bad.terms.remove(0);reject_base(bad);
    let mut bad=base.clone();bad.terms.push(bad.terms[0].clone());reject_base(bad);
    let mut bad=base.clone();bad.terms.swap(0,1);reject_base(bad);

    let reject_reads=|bad:Vec<NativeRead>|{
        assert!(paired.checked_adopt_c370_parts(base,&bad,CAP0_OWNER).is_err());
    };
    let mut bad=reads.clone();bad.pop();reject_reads(bad);
    let mut bad=reads.clone();bad.push(reads[3]);reject_reads(bad);
    // Same-length omission/duplication is not excused by an equal value.
    let mut bad=reads.clone();bad[1]=bad[2];reject_reads(bad);
    let mut bad=reads.clone();bad.swap(1,2);reject_reads(bad);
    for field in 0..8 {
        let mut operand=reads[0].operand();
        match field {
            0=>operand.occurrence+=1,
            1=>operand.relation=Relation::DaaLane(0),
            2=>operand.row+=1,
            3=>operand.side=OperandSide::Right,
            4=>operand.wire+=1,
            5=>operand.c1_active=false,
            6=>operand.c2_active=true,
            _=>operand.c3_active=true,
        }
        let mut bad=reads.clone();bad[0]=NativeRead::Header{operand,value:false};reject_reads(bad);
    }
    // Adoption checks identity and occurrence order; values are qualified by
    // the retained source/physical join in the consuming stage.
    let mut other_values=reads.clone();other_values[0]=NativeRead::Header{
        operand:reads[0].operand(),value:true};
    paired.checked_adopt_c370_parts(base,&other_values,CAP0_OWNER).unwrap();
}

#[test]
fn c453_residuals_include_zero_only_terms_and_reject_value_count_faults_no_frame() {
    let paired=c453_diagnostic_paired();let count=paired.active_operands().count();
    assert_eq!(paired.checked_residuals(std::iter::repeat(false).take(count)).unwrap(),(8,ROWS));
    assert!(paired.checked_residuals(std::iter::repeat(false).take(count-1)).is_err());
    assert!(paired.checked_residuals(std::iter::repeat(false).take(count+1)).is_err());
    let mut values=vec![false;count];values[0]=true;
    assert_eq!(paired.checked_residuals(values.into_iter()).unwrap_err(),
        "coactive Map ROW nonzero residual q=11");

    let mut constant_fault=paired.clone();
    Arc::make_mut(&mut constant_fault.base).terms[0].term.gate.c0=Fr::one();
    assert_eq!(constant_fault.active_operands().count(),count);
    assert_eq!(constant_fault.checked_residuals(std::iter::repeat(false).take(count)).unwrap_err(),
        "coactive Map ROW nonzero residual q=10");

    // Residuals are sums per physical row, rather than a requirement that
    // every individual monomial evaluate to zero.
    let mut cancellation=paired.clone();let base=Arc::make_mut(&mut cancellation.base);
    base.terms[0].term.gate.c0=Fr::one();
    base.terms[1].term.row=base.terms[0].term.row;
    base.terms[1].term.gate.c0=-Fr::one();
    assert_eq!(cancellation.checked_residuals(std::iter::repeat(false).take(count)).unwrap(),(8,ROWS));
}

fn c453_canonical_maps_only(view:&Eligible08MapSourceView<'_>) -> PairedMapBatch {
    let mut paired=c453_diagnostic_paired();
    let base=Arc::make_mut(&mut paired.base);
    base.source=view.binding().clone();base.terms.clear();
    base.expected=[0;RELATIONS];base.relations=[None;RELATIONS];
    paired.source=base.source.clone();paired.expected_base=paired.base.clone();
    for context in 0..2 {
        paired.maps[context]=view.checked_terms(&paired.source,CAP0_OWNER,OwnerClass::Carry,context)
            .unwrap().iter().map(|term|Layout::paired_map_general().place(
                OwnerClass::Carry,Relation::Map(context),CAP0_OWNER,term.clone()).unwrap()).collect();
    }
    paired.expected_maps=paired.maps.clone();paired
}

fn c453_maps_only_registry(paired:&PairedMapBatch) -> RowRegistry {
    RowRegistry{owner:CAP0_OWNER,class:OwnerClass::Carry,layout:paired.layout,
        source:paired.source.clone(),committed:false,rows:vec![0;ROWS],relations:[None;RELATIONS]}
}

#[test]
fn c453_coactive_commit_rejects_work_d_custody_and_value_faults_atomically_no_frame() {
    use crate::packed_owner_assembly::{c453_coactive_fixture_for_test,flip_native_row_bit_for_test};
    use crate::packed_owner_assembly::Eligible08OwnerSink;
    let sink=Eligible08OwnerSink::synthetic_map_source_for_test();
    let view=sink.map_source_view_for_test().unwrap();
    let paired=c453_canonical_maps_only(&view);
    let local=crate::legacy_envelope_map::D_LOCAL;
    let (row,census)=c453_coactive_fixture_for_test(&view).unwrap();
    assert_eq!(census.checked_cell(&paired.source,&row,CAP0_OWNER*WIDTH+local).unwrap(),
        (NativePhysicalAuthor::Tree,false));
    let stage=NativePartialXRowStage{row:&row,batch:paired.base.as_ref().clone(),
        reads:vec![],claims:vec![]};
    paired.checked_adopt_c370_base(&stage).unwrap();
    stage.join_physical_census(&paired.source,&census).unwrap();
    let mut baseline=c453_maps_only_registry(&paired);let before=baseline.clone();
    baseline.check_map_pair(&paired).unwrap();
    // Synthetic source/packed zeros are a custody fixture, not an authentic
    // eleven-relation witness. Its only permitted later failure is residuals.
    match baseline.commit_coactive_map_pair(&paired,&stage,&census,&view) {
        Ok(evidence)=>{
            assert_eq!(evidence.work_d_source_cells,[224;2]);
            assert_eq!(evidence.map_source_cells,[crate::bank53_map::MAP_LIVE;2]);
            assert!(baseline.committed);
        }
        Err(error)=>{
            assert!(error.contains("coactive Map ROW nonzero residual"),"baseline: {error}");
            assert_eq!(baseline,before);
        }
    }
    for fault in 0..5 {
        let (mut row,mut census)=c453_coactive_fixture_for_test(&view).unwrap();
        let expected=match fault {
            0=>{census.c453_set_author_for_test(local,Some(NativePhysicalAuthor::Header));
                "physical author geometry"},
            1=>{census.c453_set_author_for_test(local,None);"missing physical author"},
            2=>{census.c453_flip_tree_source_bit_for_test(local);"Tree source/packed"},
            3=>{census.c453_remove_tree_source_for_test(local);"Tree exclusive source mask"},
            _=>{flip_native_row_bit_for_test(&mut row,local).unwrap();"source/packed bit mismatch"},
        };
        let stage=NativePartialXRowStage{row:&row,batch:paired.base.as_ref().clone(),
            reads:vec![],claims:vec![]};
        let mut registry=c453_maps_only_registry(&paired);let snapshot=registry.clone();
        let error=registry.commit_coactive_map_pair(&paired,&stage,&census,&view).unwrap_err();
        assert!(error.contains(expected),"fault={fault}: {error}");
        assert_eq!(registry,snapshot,"fault={fault} must leave every registry field unchanged");
    }
}

#[test]
fn c453_coactive_commit_rejects_retained_term_mutations_atomically_no_frame() {
    use crate::packed_owner_assembly::c453_coactive_fixture_for_test;
    use crate::packed_owner_assembly::Eligible08OwnerSink;
    let sink=Eligible08OwnerSink::synthetic_map_source_for_test();
    let view=sink.map_source_view_for_test().unwrap();let paired=c453_canonical_maps_only(&view);
    let (row,census)=c453_coactive_fixture_for_test(&view).unwrap();
    let stage=NativePartialXRowStage{row:&row,batch:paired.base.as_ref().clone(),
        reads:vec![],claims:vec![]};
    for fault in 0..4 {
        let mut bad=paired.clone();
        let expected=match fault {
            0=>{
                let index=bad.maps[0].iter().position(|term|term.gate.c0.is_zero())
                    .expect("synthetic zeros include a zero equation");
                bad.maps[0].remove(index);"retained term count"
            }
            1=>{let duplicate=bad.maps[0][0].clone();bad.maps[0].push(duplicate);"retained term count"},
            2=>{
                let next=bad.maps[0].iter().position(|term|*term!=bad.maps[0][0])
                    .expect("canonical Map includes distinct source terms");
                bad.maps[0].swap(0,next);"retained ordered source term"
            },
            _=>{bad.maps[0][0].gate.left^=1;"retained ordered source term"},
        };
        // Keep the structural snapshot consistent so the rejection exercises
        // the retained source consumer rather than the earlier tuple guard.
        bad.expected_maps=bad.maps.clone();
        let mut registry=c453_maps_only_registry(&paired);let snapshot=registry.clone();
        registry.check_map_pair(&bad).unwrap();
        let error=registry.commit_coactive_map_pair(&bad,&stage,&census,&view).unwrap_err();
        assert!(error.contains(expected),"fault={fault}: {error}");
        assert_eq!(registry,snapshot,"fault={fault} must not commit");
    }
}

fn complete_ordered_import_records()->Vec<(usize,
    crate::packed_owner_assembly::Eligible08ScoreImportKind,usize,Fr)> {
    use crate::packed_owner_assembly::Eligible08ScoreImportKind as Kind;
    let mut records=Vec::with_capacity(1_028);
    let previous_bases=[677_501usize,685_693];
    let cap_bases=[CAP0_BASE,CAP1_BASE];
    for context in 0..2 {
        for bit in 0..225 {
            records.push((context,Kind::PreviousR{owner:COMPLETE_OWNER-1},
                (COMPLETE_OWNER-1)*WIDTH+previous_bases[context]+1_318+bit,Fr::zero()));
        }
        for bit in 0..65 {
            records.push((context,Kind::Cap{owner:COMPLETE_OWNER,origin:CAP0_ORIGIN,
                max_owner:FOREIGN_MAX_OWNER},
                COMPLETE_OWNER*WIDTH+cap_bases[context]+740+bit,Fr::zero()));
        }
        for bit in 0..224 {
            records.push((context,Kind::WorkUpper{owner:COMPLETE_OWNER-1,height:CAP0_ORIGIN},
                (COMPLETE_OWNER-1)*WIDTH+987_450+bit,Fr::zero()));
        }
    }
    records
}

#[test]
fn c455_complete_import_census_rejects_reordered_records_no_frame() {
    let records=complete_ordered_import_records();
    assert_eq!(records.len(),1_028);
    let checked=CompleteScoreImportCensus::from_records(records.clone().into_iter())
        .expect("exact ordered 1,028-record projection");
    assert_eq!(checked.record_counts(),[450,130,448]);

    // The same context and kind are insufficient: order binds each retained
    // publication record to its expected block bit and physical wire.
    let mut reordered=records.clone();
    reordered.swap(7,8);
    assert!(CompleteScoreImportCensus::from_records(reordered.into_iter()).is_err());

    // Upper wires recur between contexts, so the context component is part of
    // the identity even when the wire and field value are identical.
    let first_upper=225+65;
    let second_upper=514+225+65;
    let mut context_swapped=records;
    context_swapped.swap(first_upper,second_upper);
    assert!(CompleteScoreImportCensus::from_records(context_swapped.into_iter()).is_err());
}

#[test]
fn c455_complete_layout_moves_only_six_declared_row_intervals_no_frame() {
    assert_eq!(RELATIONS,11,"legacy relation identity remains unchanged");
    assert_ne!(CompleteLayout::digest(),Layout::fixed().digest());
    assert_ne!(CompleteLayout::digest(),Layout::paired_map().digest());
    assert_ne!(CompleteLayout::digest(),Layout::paired_map_general().digest());
    assert_ne!(CompleteLayout::digest(),AnchorLayout::digest());
    for index in 0..6 {
        let (source_start,source_end)=COMPLETE_SOURCE_INTERVALS[index];
        let (destination_start,destination_end)=COMPLETE_DESTINATION_INTERVALS[index];
        for (source_q,destination_q) in [(source_start,destination_start),
            (source_end-1,destination_end-1)] {
            let source=gate_term(COMPLETE_OWNER*ROWS+source_q,WIDTH*OWNERS-1,
                WIDTH*OWNERS-2,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero());
            let placed=CompleteLayout::place(index,source.clone()).unwrap();
            assert_eq!(placed.row,COMPLETE_OWNER*ROWS+destination_q);
            assert_eq!(placed.gate.left,source.gate.left);
            assert_eq!(placed.gate.right,source.gate.right);
        }
        let foreign=gate_term((COMPLETE_OWNER-1)*ROWS+source_start,0,1,
            Fr::zero(),Fr::one(),Fr::zero(),Fr::zero());
        assert!(CompleteLayout::place(index,foreign).is_err());
    }
}

#[test]
fn c455_complete_layout_descriptor_binds_all_v5_identity_fields_no_frame() {
    let owner=COMPLETE_OWNER;
    let class="Carry";
    let predecessor=Layout::paired_map_general().digest();
    let cut=crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
    let mut slots=[0usize;COMPLETE_RELATIONS];
    for (slot,value) in slots.iter_mut().enumerate(){*value=slot;}
    let source=COMPLETE_SOURCE_INTERVALS;
    let destination=COMPLETE_DESTINATION_INTERVALS;
    let descriptor=CompleteLayout::descriptor();
    assert_eq!(CompleteLayout::descriptor_parts(owner,class,predecessor,&cut,
        &slots,&source,&destination),descriptor);
    let distinct=|owner,class,predecessor,cut:&[u8],slots:&[usize;COMPLETE_RELATIONS],
        source:&[(usize,usize);6],destination:&[(usize,usize);6]| {
        CompleteLayout::descriptor_parts(owner,class,predecessor,cut,slots,source,destination)
    };
    assert_ne!(distinct(owner+1,class,predecessor,&cut,&slots,&source,&destination),descriptor);
    assert_ne!(distinct(owner,"M1",predecessor,&cut,&slots,&source,&destination),descriptor);
    assert_ne!(distinct(owner,class,[0x55;32],&cut,&slots,&source,&destination),descriptor);
    let mut changed_cut=cut.clone();changed_cut.push(0);
    assert_ne!(distinct(owner,class,predecessor,&changed_cut,&slots,&source,&destination),descriptor);
    for index in 0..COMPLETE_RELATIONS {
        let mut changed_slots=slots;changed_slots[index]=changed_slots[index].wrapping_add(1);
        assert_ne!(distinct(owner,class,predecessor,&cut,&changed_slots,&source,&destination),
            descriptor,"slot={index}");
    }
    for index in 0..6 {
        for endpoint in 0..2 {
            let mut changed_source=source;
            if endpoint==0 {changed_source[index].0+=1;}else{changed_source[index].1-=1;}
            assert_ne!(distinct(owner,class,predecessor,&cut,&slots,&changed_source,&destination),
                descriptor,"source interval={index} endpoint={endpoint}");
            let mut changed_destination=destination;
            if endpoint==0 {changed_destination[index].0+=1;}else{changed_destination[index].1-=1;}
            assert_ne!(distinct(owner,class,predecessor,&cut,&slots,&source,&changed_destination),
                descriptor,"destination interval={index} endpoint={endpoint}");
        }
    }

    let relations=[
        CompleteRelation::Ordinary(Relation::Header),
        CompleteRelation::Ordinary(Relation::DaaLane(0)),
        CompleteRelation::Ordinary(Relation::DaaLane(1)),
        CompleteRelation::Ordinary(Relation::DaaLane(2)),
        CompleteRelation::Ordinary(Relation::DaaLane(3)),
        CompleteRelation::Ordinary(Relation::Scheduled(Writer::Max{context:0,end:owner+2})),
        CompleteRelation::Ordinary(Relation::Scheduled(Writer::Max{context:1,end:owner+2})),
        CompleteRelation::Ordinary(Relation::Scheduled(Writer::Cap{context:0,origin:owner+1})),
        CompleteRelation::Ordinary(Relation::Scheduled(Writer::Cap{context:1,origin:owner+1})),
        CompleteRelation::Map(0),CompleteRelation::Map(1),
        CompleteRelation::Score(0),CompleteRelation::Score(1),
        CompleteRelation::Slack(0),CompleteRelation::Slack(1),
    ];
    for (slot,relation) in relations.into_iter().enumerate(){
        assert_eq!(relation.slot(owner).unwrap(),slot);
    }
}

#[test]
fn c455_active_operand_iterator_preserves_constant_ordinals_and_repeats_no_frame() {
    let terms=[
        gate_term(COMPLETE_OWNER*ROWS+7,11,12,Fr::from(9u64),Fr::zero(),
            Fr::zero(),Fr::zero()),
        gate_term(COMPLETE_OWNER*ROWS+8,21,22,Fr::zero(),Fr::one(),
            Fr::from(2u64),Fr::from(3u64)),
        gate_term(COMPLETE_OWNER*ROWS+9,31,32,Fr::zero(),Fr::zero(),
            Fr::zero(),Fr::one()),
    ];
    let source=vec![
        (CompleteRelation::Score(0),&terms[0]),
        (CompleteRelation::Score(0),&terms[1]),
        (CompleteRelation::Slack(1),&terms[2]),
    ];
    let active=CompleteActiveOperandIter{terms:source.into_iter().enumerate(),pending_right:None}
        .collect::<Vec<_>>();
    assert_eq!(active.iter().map(|operand|operand.occurrence).collect::<Vec<_>>(),
        [1,1,2,2]);
    assert_eq!(active.iter().map(|operand|operand.side).collect::<Vec<_>>(),
        [OperandSide::Left,OperandSide::Right,OperandSide::Left,OperandSide::Right]);
    assert_eq!(active.iter().map(|operand|operand.relation).collect::<Vec<_>>(),
        [CompleteRelation::Score(0),CompleteRelation::Score(0),
            CompleteRelation::Slack(1),CompleteRelation::Slack(1)]);
    assert_eq!(active.iter().map(|operand|operand.wire).collect::<Vec<_>>(),[21,22,31,32]);
}

fn c455_check_complete_entries(registry:&CompleteRowRegistry,
    entries:&[(CompleteRelation,Term)])
    ->Result<(Vec<u8>,[Option<CompleteRelation>;COMPLETE_RELATIONS]),String> {
    let mut counts=[0usize;COMPLETE_RELATIONS];
    let mut relations=[None;COMPLETE_RELATIONS];
    for (relation,_) in entries {
        let slot=relation.slot(COMPLETE_OWNER)?;
        counts[slot]+=1;relations[slot]=Some(*relation);
    }
    registry.check_entries(COMPLETE_OWNER,OwnerClass::Carry,CompleteLayout::digest(),
        &registry.source,&counts,&relations,
        entries.iter().map(|(relation,term)|(*relation,term)))
}

#[test]
fn c455_complete_registry_engine_checks_collision_placement_and_owner_no_frame() {
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[0x51;32],[0x52;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let scheduled=Scheduled::eligible08();
    let plan=RowPlan::new(&roster,&scheduled).unwrap();
    let registry=plan.registry_with_complete(COMPLETE_OWNER).unwrap();
    let original=registry.clone();
    let zero_term=|row|gate_term(row,COMPLETE_OWNER*WIDTH,COMPLETE_OWNER*WIDTH,
        Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero());

    // Same-relation terms may accumulate at one placed row, even when their
    // gates are equal zero constants.
    let q=COMPLETE_DESTINATION_INTERVALS[2].0;
    let same_relation=[
        (CompleteRelation::Score(0),zero_term(COMPLETE_OWNER*ROWS+q)),
        (CompleteRelation::Score(0),zero_term(COMPLETE_OWNER*ROWS+q)),
    ];
    let (rows,relations)=c455_check_complete_entries(&registry,&same_relation).unwrap();
    assert_eq!(rows[q],12);
    assert_eq!(relations[11],Some(CompleteRelation::Score(0)));
    assert_eq!(registry,original);

    // Equal zero terms from distinct relation identities still collide.
    let q=COMPLETE_DESTINATION_INTERVALS[0].0;
    let same_zero=zero_term(COMPLETE_OWNER*ROWS+q);
    let cross_relation=[(CompleteRelation::Map(0),same_zero.clone()),
        (CompleteRelation::Score(0),same_zero)];
    let error=c455_check_complete_entries(&registry,&cross_relation).unwrap_err();
    assert!(error.contains("cross-relation"),"{error}");
    assert_eq!(registry,original,"cross-relation rejection preserves registry state");

    // Crossing either half-open endpoint of every new Score/Slack destination
    // invalidates that relation's placement, independently of gate values.
    for (relation,interval_index) in [
        (CompleteRelation::Score(0),2),(CompleteRelation::Score(1),3),
        (CompleteRelation::Slack(0),4),(CompleteRelation::Slack(1),5),
    ] {
        let (start,end)=COMPLETE_DESTINATION_INTERVALS[interval_index];
        for q in [start-1,end] {
            let bad=[(relation,zero_term(COMPLETE_OWNER*ROWS+q))];
            let error=c455_check_complete_entries(&registry,&bad).unwrap_err();
            assert!(error.contains("placement/reservation"),
                "relation={relation:?} q={q}: {error}");
            assert_eq!(registry,original,"endpoint rejection preserves registry state");
        }
    }

    let foreign_row=(COMPLETE_OWNER-1)*ROWS+COMPLETE_DESTINATION_INTERVALS[2].0;
    let foreign=[(CompleteRelation::Score(0),zero_term(foreign_row))];
    let error=c455_check_complete_entries(&registry,&foreign).unwrap_err();
    assert!(error.contains("physical ROW owner"),"{error}");
    assert_eq!(registry,original,"foreign ROW rejection preserves registry state");
}

fn c455_empty_paired_for_residual(
    view:&crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'_>,
)->PairedMapBatch {
    let source=view.binding().clone();
    let layout=Layout::paired_map_general().digest();
    let base=Arc::new(Batch{owner:COMPLETE_OWNER,class:OwnerClass::Carry,layout,
        source:source.clone(),terms:Vec::new(),expected:[0;RELATIONS],relations:[None;RELATIONS]});
    PairedMapBatch{base:base.clone(),expected_base:base,maps:[Vec::new(),Vec::new()],
        expected_maps:[Vec::new(),Vec::new()],map_relations:[Relation::Map(0),Relation::Map(1)],
        source,class:OwnerClass::Carry,layout,expected_layout:layout}
}

#[test]
fn c455_complete_residual_slack_and_failed_commit_guards_no_frame() {
    use crate::packed_owner_assembly::{c453_coactive_fixture_for_test,Eligible08OwnerSink};
    let sink=Eligible08OwnerSink::synthetic_complete_row_source_for_test();
    let view=sink.local_source_view_for_test().unwrap();
    let map_view=view.map_view();
    let paired=c453_canonical_maps_only(&map_view);

    // A constant-only v5 term still contributes its ROW residual and must not
    // disappear merely because it creates no active X read.
    let empty_base=c455_empty_paired_for_residual(&view);
    let q=COMPLETE_DESTINATION_INTERVALS[2].0;
    let nonzero=gate_term(COMPLETE_OWNER*ROWS+q,COMPLETE_OWNER*WIDTH,
        COMPLETE_OWNER*WIDTH,Fr::one(),Fr::zero(),Fr::zero(),Fr::zero());
    let empty:&[Term]=&[];
    let score_terms=[std::slice::from_ref(&nonzero),empty];
    let residual_batch=CompleteBatch{base:&empty_base,view:&view,score_terms,
        slack_terms:[Vec::new(),Vec::new()],expected:[0;COMPLETE_RELATIONS],
        relations:[None;COMPLETE_RELATIONS]};
    let error=residual_batch.checked_complete_residuals(std::iter::empty::<bool>()).unwrap_err();
    assert!(error.contains("v5 nonzero ROW residual"),"{error}");

    // Slack is authored as a complete canonical zero relation. Omitting one
    // equation must fail retained source comparison despite its zero value.
    let mut omitted=CompleteBatch::checked_from_retained_map(&paired,&view).unwrap();
    assert_eq!(omitted.slack_terms[0].len(),387);
    omitted.slack_terms[0].pop();
    let error=omitted.check_source_tuples().unwrap_err();
    assert!(error.contains("retained Slack source tuple count"),"{error}");

    // The local-only synthetic view deliberately has no qualified foreign
    // publication cache. Commit must fail at that boundary without changing
    // any registry field; the authentic harness owns successful commit tests.
    let batch=CompleteBatch::checked_from_retained_map(&paired,&view).unwrap();
    let (row,census)=c453_coactive_fixture_for_test(&map_view).unwrap();
    let stage=NativePartialXRowStage{row:&row,batch:paired.base.as_ref().clone(),
        reads:vec![],claims:vec![]};
    let mut registry=CompleteRowRegistry{owner:COMPLETE_OWNER,class:OwnerClass::Carry,
        layout:CompleteLayout::digest(),source:paired.source.clone(),committed:false,
        rows:vec![0;ROWS],relations:[None;COMPLETE_RELATIONS]};
    let before=registry.clone();
    let error=registry.commit_complete_coactive(&batch,&stage,&census,&view).unwrap_err();
    assert!(error.contains("imports lack completed publication qualification"),"{error}");
    assert_eq!(registry,before,"failed complete commit preserves every registry field");
}

const C458_TAIL_START:usize=393216;
const C458_TAIL_END:usize=406406;
const C458_TAIL_SHIFT:usize=114320;
const C458_TAIL_COUNT:usize=13960;
const C458_A4_START:usize=348440;
const C458_A4_END:usize=356632;

struct C458LocalEqTables {row:Vec<Fr>,left:Vec<Fr>,right:Vec<Fr>}

fn c458_eq_table(point:&[Fr])->Vec<Fr> {
    let mut table=vec![Fr::one()];
    for coordinate in point {
        let old_len=table.len();
        table.reserve(old_len);
        let low=Fr::one()-coordinate;
        for index in 0..old_len {
            let value=table[index];
            table[index]=value*low;
            table.push(value*coordinate);
        }
    }
    table
}

impl C458LocalEqTables {
    fn new(r:&[Fr],u:&[Fr],v:&[Fr])->Self {
        assert_eq!(r.len(),19);assert_eq!(u.len(),20);assert_eq!(v.len(),20);
        Self{row:c458_eq_table(r),left:c458_eq_table(u),right:c458_eq_table(v)}
    }
    fn evaluate(&self,terms:&[Term])->[Fr;4] {
        let mut out=[Fr::zero();4];
        for term in terms {
            let weight=self.row[term.row]*self.left[term.gate.left]*self.right[term.gate.right];
            out[0]+=weight*term.gate.c0;out[1]+=weight*term.gate.c1;
            out[2]+=weight*term.gate.c2;out[3]+=weight*term.gate.c3;
        }
        out
    }
}

fn c458_local_point(seed:u64)->(Vec<Fr>,Vec<Fr>,Vec<Fr>) {
    let r=(0..19).map(|i|Fr::from(seed+2+17*i as u64)).collect();
    let u=(0..20).map(|i|Fr::from(seed+31+23*i as u64)).collect();
    let v=(0..20).map(|i|Fr::from(seed+67+29*i as u64)).collect();
    (r,u,v)
}

fn c458_general_high_point()->(Vec<Fr>,Vec<Fr>,Vec<Fr>) {
    let r=(0..21).map(|i|Fr::from(3+11*i as u64)).collect();
    let u=(0..21).map(|i|Fr::from(41+13*i as u64)).collect();
    let v=(0..21).map(|i|Fr::from(89+17*i as u64)).collect();
    (r,u,v)
}

fn c458_owner_bits(owner:usize)->Vec<Fr> {
    (0..21).map(|bit|Fr::from(((owner>>bit)&1) as u64)).collect()
}

fn c458_join_point(local:&[Fr],high:&[Fr])->Vec<Fr> {
    let mut point=Vec::with_capacity(local.len()+high.len());
    point.extend_from_slice(local);point.extend_from_slice(high);point
}

fn c458_owner_extension(r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    assert_eq!((r.len(),u.len(),v.len()),(21,21,21));
    (0..21).fold(Fr::one(),|acc,bit|{
        acc*((Fr::one()-r[bit])*(Fr::one()-u[bit])*(Fr::one()-v[bit])
            +r[bit]*u[bit]*v[bit])
    })
}

fn c458_owner_delta(r:&[Fr],u:&[Fr],v:&[Fr],owner:usize)->Fr {
    (0..21).fold(Fr::one(),|acc,bit|{
        let coordinate=if (owner>>bit)&1==1 {
            r[bit]*u[bit]*v[bit]
        } else {
            (Fr::one()-r[bit])*(Fr::one()-u[bit])*(Fr::one()-v[bit])
        };
        acc*coordinate
    })
}

fn c458_short_a4_owner_mask(r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    [Profile::M2,Profile::M3,Profile::M4,Profile::M5,Profile::M6,Profile::M7]
        .into_iter().map(|profile|{
            c458_owner_delta(r,u,v,profile.child_height() as usize-1)
        }).sum()
}

fn c458_localize_term(mut term:Term,owner:usize)->Term {
    term.row=term.row.checked_sub(owner*ROWS).expect("C458 owner-local ROW");
    term.gate.left=term.gate.left.checked_sub(owner*WIDTH).expect("C458 owner-local left X");
    term.gate.right=term.gate.right.checked_sub(owner*WIDTH).expect("C458 owner-local right X");
    term
}

fn c458_worktree_retired_local_terms(parent:&WorkTreeHistoryPlan,owner:usize)->Vec<Term> {
    let source=&parent.header_boundary().canonical_circuit().terms;
    let mut source_index=0usize;let mut retired=Vec::new();
    let counts=parent.visit_slot_terms(owner as u64,|global|{
        let local=c458_localize_term(global,owner);
        while source_index<source.len() && source[source_index]!=local {
            retired.push(source[source_index].clone());source_index+=1;
        }
        if source_index==source.len() {
            return Err("C458 retained work-tree term is not an ordered canonical subsequence".into());
        }
        source_index+=1;Ok(())
    }).expect("C458 retained source stream for non-A4 owner");
    assert_eq!(counts.omitted_a4,0,"owner 1 does not release mature A4");
    retired.extend_from_slice(&source[source_index..]);
    assert_eq!(retired.len(),counts.omitted_worktree);
    retired
}

fn c458_anchor_retirement(scheduled:&Scheduled,r:&[Fr],u:&[Fr],v:&[Fr],
    tables:&C458LocalEqTables)->Fr {
    const RANGES:[(usize,usize,usize);4]=[
        (356632,999424,673),(357305,1000097,673),
        (357978,1000770,2048),(360026,1002818,2048),
    ];
    let owners=scheduled.anchor_owner_weights(&r[19..],&u[20..],&v[20..])
        .expect("C458 independent scheduled owner weights");
    let mut out=Fr::zero();
    for (index,(row_start,wire_start,count)) in RANGES.into_iter().enumerate() {
        for offset in 0..count {
            out+=owners[index]*tables.row[row_start+offset]
                *tables.left[wire_start+offset]*tables.right[0];
        }
    }
    out
}

fn c458_oracle_tail_delta(source:&[Term],owner:usize,class:OwnerClass,
    tables:&C458LocalEqTables)->([Fr;4],usize) {
    let mut out=[Fr::zero();4];let mut count=0usize;
    let layout=Layout::paired_map_general();
    for term in source {
        let q=term.row.checked_sub(owner*ROWS).expect("C458 source owner") ;
        if !(C458_TAIL_START..C458_TAIL_END).contains(&q) {continue;}
        let placed=layout.place_for_test(class,Relation::Header,owner,term.clone())
            .expect("C458 oracle placement of canonical HEADER tail");
        assert_eq!(placed.gate,term.gate,"HEADER tail placement preserves both X endpoints");
        let source_local=c458_localize_term(term.clone(),owner);
        let placed_local=c458_localize_term(placed,owner);
        assert_eq!(placed_local.row,C458_TAIL_START+C458_TAIL_SHIFT+q-C458_TAIL_START);
        let weight=(tables.row[placed_local.row]-tables.row[source_local.row])
            *tables.left[source_local.gate.left]*tables.right[source_local.gate.right];
        out[0]+=weight*term.gate.c0;out[1]+=weight*term.gate.c1;
        out[2]+=weight*term.gate.c2;out[3]+=weight*term.gate.c3;
        count+=1;
    }
    (out,count)
}

fn c458_tail_delta_literal(source:&[Term],owner:usize,tables:&C458LocalEqTables,
    start:usize,end:usize,shift:isize,right_override:Option<usize>)->[Fr;4] {
    let mut out=[Fr::zero();4];
    for term in source {
        let q=term.row.checked_sub(owner*ROWS).expect("C458 literal source owner");
        if q<start || q>=end {continue;}
        let target=if shift>=0 {q+shift as usize} else {q-(-shift) as usize};
        assert!(target<ROWS,"C458 literal placed row is in the ROW domain");
        let left=term.gate.left.checked_sub(owner*WIDTH).expect("C458 literal left owner");
        let right=right_override.unwrap_or_else(||
            term.gate.right.checked_sub(owner*WIDTH).expect("C458 literal right owner"));
        let weight=(tables.row[target]-tables.row[q])*tables.left[left]*tables.right[right];
        out[0]+=weight*term.gate.c0;out[1]+=weight*term.gate.c1;
        out[2]+=weight*term.gate.c2;out[3]+=weight*term.gate.c3;
    }
    out
}

fn c458_tail_delta_owner_local_right_zero(source:&[Term],owner:usize,
    tables:&C458LocalEqTables)->([Fr;4],usize) {
    let mut out=[Fr::zero();4];let mut count=0usize;
    for term in source {
        let q=term.row.checked_sub(owner*ROWS).expect("C458 owner-local placeholder source");
        if !(C458_TAIL_START..C458_TAIL_END).contains(&q) {continue;}
        let left=term.gate.left.checked_sub(owner*WIDTH).expect("C458 owner-local placeholder left");
        let right=term.gate.right.checked_sub(owner*WIDTH).expect("C458 owner-local placeholder right");
        if right!=0 {continue;}
        let target=q+C458_TAIL_SHIFT;
        let weight=(tables.row[target]-tables.row[q])*tables.left[left]*tables.right[0];
        out[0]+=weight*term.gate.c0;out[1]+=weight*term.gate.c1;
        out[2]+=weight*term.gate.c2;out[3]+=weight*term.gate.c3;
        count+=1;
    }
    (out,count)
}

fn c458_wrong_global_right_zero_mask(r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    let same_row_left=(0..21).fold(Fr::one(),|acc,bit|{
        acc*((Fr::one()-r[bit])*(Fr::one()-u[bit])+r[bit]*u[bit])
    });
    same_row_left*v.iter().fold(Fr::one(),|acc,coordinate|acc*(Fr::one()-coordinate))
}

fn c458_general_layout_descriptor()->Vec<u8> {
    let mut out=b"c451-row19-paired-map-general-v4\0".to_vec();
    out.extend_from_slice(&Layout::fixed().digest());
    let cut=crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
    out.extend_from_slice(&(cut.len() as u64).to_le_bytes());out.extend_from_slice(&cut);
    out.extend_from_slice(&(RELATIONS as u64).to_le_bytes());
    for slot in 0..RELATIONS {out.extend_from_slice(&(slot as u64).to_le_bytes());}
    for word in [0u64,409600,419947,477074,487421,1,442368,452715,492305,502652] {
        out.extend_from_slice(&word.to_le_bytes());
    }
    out.extend_from_slice(b"all-h21-owner-classes-including-padding-map-zero-equations\0");
    out
}

struct C458FactoredReference {
    coefficients:[Fr;4],
    f:[Fr;4],
    retired:Fr,
    delta_local:[Fr;4],
    delta:[Fr;4],
    same_slot:Fr,
    mature_a4:[Fr;4],
    short_a4:[Fr;4],
}

fn c458_factored_global_reference(parent:&WorkTreeHistoryPlan,scheduled:&Scheduled,
    canonical_shape:&crate::sparse::Shape,worktree_retired:&[Term],a4_local:&[Fr;4],
    selected_header:&[Term],selected_owner:usize,selected_class:OwnerClass,
    r:&[Fr],u:&[Fr],v:&[Fr],tables:&C458LocalEqTables)->C458FactoredReference {
    let canonical=crate::sparse::wiring(parent.header_boundary().canonical_circuit(),canonical_shape,
        &r[..19],&u[..20],&v[..20]).expect("C458 canonical local HEADER coefficients");
    let worktree=tables.evaluate(worktree_retired);
    let same_slot=c458_owner_extension(&r[19..],&u[20..],&v[20..]);
    let mut mature_a4=[Fr::zero();4];
    mature_a4[1]=parent.header_boundary().mature_layout(Epoch::Legacy)
        .a4_release_coefficient(r,u,v).expect("C458 mature Legacy A4 mask")
        +parent.header_boundary().mature_layout(Epoch::Eip)
            .a4_release_coefficient(r,u,v).expect("C458 mature EIP A4 mask");
    let short_mask=c458_short_a4_owner_mask(&r[19..],&u[20..],&v[20..]);
    let short_a4=std::array::from_fn(|channel|a4_local[channel]*short_mask);
    let mut f=std::array::from_fn(|channel|
        canonical[channel]*same_slot-worktree[channel]*same_slot-mature_a4[channel]-short_a4[channel]);
    let retired=c458_anchor_retirement(scheduled,r,u,v,tables);
    let (delta_local,tail_count)=c458_oracle_tail_delta(
        selected_header,selected_owner,selected_class,tables);
    assert_eq!(tail_count,C458_TAIL_COUNT,"C458 oracle tail cardinality");
    let delta=std::array::from_fn(|channel|delta_local[channel]*same_slot);
    let mut coefficients=f;
    coefficients[1]-=retired;
    for channel in 0..4 {coefficients[channel]+=delta[channel];}
    C458FactoredReference{coefficients,f,retired,delta_local,delta,same_slot,mature_a4,short_a4}
}

#[test]
fn c458_placed_header_matches_no_frame_owner_and_independent_global_oracles() {
    use ark_ff::Zero;
    use blake2::{Blake2b,Digest,digest::consts::U32};
    use std::time::Instant;

    let plan_started=Instant::now();
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[0x58;32],[0x58;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let eligible=Scheduled::eligible08();let merge=Merge::new(&roster,&eligible).unwrap();
    let plan_elapsed=plan_started.elapsed();
    println!("C458_PUBLIC_PLAN_CONSTRUCTION elapsed_ms={}",plan_elapsed.as_millis());
    let layout=Layout::paired_map_general();
    let descriptor=c458_general_layout_descriptor();
    assert_eq!(layout.descriptor(),descriptor,"C458 exact general slot0 layout descriptor");
    assert_eq!(layout.digest(),<[u8;32]>::from(Blake2b::<U32>::digest(&descriptor)));
    assert_eq!(eligible.descriptor(),crate::bank53_map::CutDescriptor::eligible08(),
        "C458 source cut is exact Eligible08");
    assert_ne!(eligible.descriptor(),crate::bank53_map::CutDescriptor::diagnostic08());

    let (local_r,local_u,local_v)=c458_local_point(19);
    let (high_r,high_u,high_v)=c458_general_high_point();
    let r=c458_join_point(&local_r,&high_r);let u=c458_join_point(&local_u,&high_u);
    let v=c458_join_point(&local_v,&high_v);
    let diagnostic=Scheduled::new();
    let diagnostic_merge=Merge::new(&roster,&diagnostic).unwrap();
    let diagnostic_error=diagnostic_merge.placed_header_coefficients(&r,&u,&v).unwrap_err();
    assert!(diagnostic_error.contains("Eligible08"),
        "C458 evaluator must explicitly reject Diagnostic08: {diagnostic_error}");

    let selected_owner=845_759usize;
    let selected_class=roster.owner_class(selected_owner as u64).unwrap();
    assert_eq!(CompleteRelation::Ordinary(Relation::Header).slot(selected_owner).unwrap(),0,
        "C455 v5 selected ordinary HEADER remains linked to slot0");
    let mut cases=vec![
        (0,OwnerClass::Genesis),(1,OwnerClass::Initial),(2,OwnerClass::Carry),
        (417_791,OwnerClass::FixedV2),(1_024,OwnerClass::Singleton),(2_048,OwnerClass::M1),
        (3_072,OwnerClass::Short(Profile::M2)),(4_096,OwnerClass::Short(Profile::M3)),
        (5_120,OwnerClass::Short(Profile::M4)),(6_144,OwnerClass::Short(Profile::M5)),
        (7_168,OwnerClass::Short(Profile::M6)),(8_192,OwnerClass::Short(Profile::M7)),
        (9_216,OwnerClass::Mature(Epoch::Legacy)),
        (844_672,OwnerClass::Mature(Epoch::Eip)),
        (1_827_840,OwnerClass::Padding),(selected_owner,selected_class),
    ];
    cases.sort_by_key(|(owner,_)|*owner);
    let started=Instant::now();let mut oracle_terms_visited=0usize;
    for seed in [19u64,73u64] {
        let (local_r,local_u,local_v)=c458_local_point(seed);
        let tables=C458LocalEqTables::new(&local_r,&local_u,&local_v);
        for &(owner,expected_class) in &cases {
            let class=roster.owner_class(owner as u64).unwrap();
            assert_eq!(class,expected_class,"C458 representative owner {owner}");
            let mut header=merge.header_terms(owner).expect("real no-frame HEADER oracle terms");
            oracle_terms_visited+=header.terms.len();
            let tail_count=header.terms.iter().filter(|term|{
                let q=term.row-owner*ROWS;(C458_TAIL_START..C458_TAIL_END).contains(&q)
            }).count();
            assert_eq!(tail_count,C458_TAIL_COUNT,"owner={owner} class={class:?}");
            if owner==selected_owner {
                assert_eq!(header.retired,[0,0,2048,2048],"C455 owner845759 scheduled anchors");
                assert_eq!(layout.descriptor(),c458_general_layout_descriptor());
                assert_eq!(eligible.descriptor(),crate::bank53_map::CutDescriptor::eligible08());
            }
            for term in &mut header.terms {
                let placed=layout.place_for_test(class,Relation::Header,owner,term.clone())
                    .expect("C458 oracle places every real HEADER term");
                *term=c458_localize_term(placed,owner);
            }
            let oracle=tables.evaluate(&header.terms);
            let high=c458_owner_bits(owner);
            let r=c458_join_point(&local_r,&high);let u=c458_join_point(&local_u,&high);
            let v=c458_join_point(&local_v,&high);
            let actual=merge.placed_header_coefficients(&r,&u,&v)
                .expect("C458 placed HEADER coefficients at Boolean owner bits");
            assert_eq!(actual,oracle,
                "C458 all-channel local differential owner={owner} class={class:?} seed={seed}");
        }
    }
    println!("C458_LOCAL_ORACLE owners={} deterministic_points=2 real_header_term_visits={} elapsed_ms={}",
        cases.len(),oracle_terms_visited,started.elapsed().as_millis());

    let canonical=parent.header_boundary().canonical_circuit();
    let canonical_shape=crate::sparse::validate(canonical,0).expect("C458 canonical local shape");
    let worktree_retired=c458_worktree_retired_local_terms(&parent,1);
    let (global_r,global_u,global_v)=c458_local_point(113);
    let global_tables=C458LocalEqTables::new(&global_r,&global_u,&global_v);
    let a4_terms:Vec<Term>=canonical.terms.iter().filter(|term|
        (C458_A4_START..C458_A4_END).contains(&term.row)).cloned().collect();
    assert_eq!(a4_terms.len(),8192,"C458 canonical local A4 source rows");
    let a4_local=global_tables.evaluate(&a4_terms);
    let selected_header=merge.header_terms(selected_owner).unwrap();
    assert_eq!(selected_header.terms.iter().filter(|term|{
        let q=term.row-selected_owner*ROWS;(C458_TAIL_START..C458_TAIL_END).contains(&q)
    }).count(),C458_TAIL_COUNT,"C455 selected source tail cardinality");
    let (high_r,high_u,high_v)=c458_general_high_point();
    let r=c458_join_point(&global_r,&high_r);let u=c458_join_point(&global_u,&high_u);
    let v=c458_join_point(&global_v,&high_v);
    let reference=c458_factored_global_reference(&parent,&eligible,&canonical_shape,
        &worktree_retired,&a4_local,&selected_header.terms,selected_owner,selected_class,
        &r,&u,&v,&global_tables);
    let evaluate_started=Instant::now();
    let actual=merge.placed_header_coefficients(&r,&u,&v).unwrap();
    let evaluate_elapsed=evaluate_started.elapsed();
    assert_eq!(actual,reference.coefficients,
        "C458 full four-channel non-Boolean high-owner factored differential");

    let extension=reference.same_slot;
    assert_ne!(extension,Fr::zero());assert_ne!(extension,Fr::one());
    assert!(reference.f.iter().any(|value|!value.is_zero()),"F*S mutant needs nonzero F");
    assert_ne!(reference.retired,Fr::zero(),"R*S mutant needs nonzero scheduled retirement");
    assert_ne!(reference.retired*(extension-Fr::one()),Fr::zero(),
        "R*S mutant has a nonzero high-owner discriminant");
    assert!(reference.f.iter().any(|value|!(*value*(extension-Fr::one())).is_zero()),
        "F*S mutant has a nonzero high-owner discriminant");

    let mut f_times_s=std::array::from_fn(|channel|reference.f[channel]*extension+reference.delta[channel]);
    f_times_s[1]-=reference.retired;
    assert_ne!(f_times_s,reference.coefficients,"isolated incorrect F*S mutant");
    let mut r_times_s=reference.f;
    for channel in 0..4 {r_times_s[channel]+=reference.delta[channel];}
    r_times_s[1]-=reference.retired*extension;
    assert_ne!(r_times_s,reference.coefficients,"isolated incorrect R*S mutant");

    assert!(!reference.delta_local.iter().all(|value|value.is_zero()),"C458 tail correction is nonzero");
    let no_tail=reference.f;
    let mut no_tail_result=no_tail;no_tail_result[1]-=reference.retired;
    assert_ne!(no_tail_result,reference.coefficients,"isolated omitted tail correction");
    let rotated_delta=[reference.delta_local[1],reference.delta_local[2],
        reference.delta_local[3],reference.delta_local[0]];
    let mut wrong_channel=reference.f;
    for channel in 0..4 {wrong_channel[channel]+=rotated_delta[channel]*extension;}
    wrong_channel[1]-=reference.retired;
    assert_ne!(wrong_channel,reference.coefficients,"isolated wrong tail coefficient channel");

    assert!(!reference.mature_a4[1].is_zero(),"mature A4 negative has a nonzero discriminant");
    let mut omitted_mature=reference.coefficients;omitted_mature[1]+=reference.mature_a4[1];
    assert_ne!(omitted_mature,reference.coefficients,"isolated omitted mature A4 release");
    let mut doubled_mature=reference.coefficients;doubled_mature[1]-=reference.mature_a4[1];
    assert_ne!(doubled_mature,reference.coefficients,"isolated doubled mature A4 release");
    assert!(!reference.short_a4.iter().all(|value|value.is_zero()),"short A4 negative has a nonzero discriminant");
    let mut omitted_short=reference.coefficients;
    for channel in 0..4 {omitted_short[channel]+=reference.short_a4[channel];}
    assert_ne!(omitted_short,reference.coefficients,"isolated omitted short A4 release");
    let mut doubled_short=reference.coefficients;
    for channel in 0..4 {doubled_short[channel]-=reference.short_a4[channel];}
    assert_ne!(doubled_short,reference.coefficients,"isolated doubled short A4 release");
    let mut omitted_scheduled=reference.coefficients;omitted_scheduled[1]+=reference.retired;
    assert_ne!(omitted_scheduled,reference.coefficients,"isolated omitted scheduled retirement");
    let mut doubled_scheduled=reference.coefficients;doubled_scheduled[1]-=reference.retired;
    assert_ne!(doubled_scheduled,reference.coefficients,"isolated doubled scheduled retirement");

    let (owner_local_right_zero_delta,owner_local_right_zero_terms)=
        c458_tail_delta_owner_local_right_zero(&selected_header.terms,selected_owner,&global_tables);
    assert!(owner_local_right_zero_terms>0,"C458 tail has authentic owner-local X(o,0) terms");
    assert!(owner_local_right_zero_delta.iter().any(|value|!value.is_zero()),
        "C458 owner-local X(o,0) contribution has a nonzero discriminant");
    let wrong_right_mask=c458_wrong_global_right_zero_mask(&high_r,&high_u,&high_v);
    let correct_right_zero_delta:[Fr;4]=std::array::from_fn(|channel|
        owner_local_right_zero_delta[channel]*extension);
    let wrong_right_delta:[Fr;4]=std::array::from_fn(|channel|
        owner_local_right_zero_delta[channel]*wrong_right_mask);
    assert!(owner_local_right_zero_delta.iter().any(|value|
        !(*value*(extension-wrong_right_mask)).is_zero()),
        "global-zero right mutant has a nonzero high-owner discriminant");
    let other_tail_delta:[Fr;4]=std::array::from_fn(|channel|
        reference.delta[channel]-correct_right_zero_delta[channel]);
    let mut wrong_right=reference.f;
    for channel in 0..4 {wrong_right[channel]+=other_tail_delta[channel]+wrong_right_delta[channel];}
    wrong_right[1]-=reference.retired;
    assert_ne!(wrong_right,reference.coefficients,
        "global-zero right endpoint mutant differs from owner-local X(o,0)");

    let exact_literal=c458_tail_delta_literal(&selected_header.terms,selected_owner,
        &global_tables,C458_TAIL_START,C458_TAIL_END,C458_TAIL_SHIFT as isize,None);
    assert_eq!(exact_literal,reference.delta_local,"literal tail correction matches placement oracle");
    for (name,start,end,boundary) in [
        ("lower-minus",C458_TAIL_START-1,C458_TAIL_END,C458_TAIL_START-1),
        ("lower-plus",C458_TAIL_START+1,C458_TAIL_END,C458_TAIL_START),
        ("upper-minus",C458_TAIL_START,C458_TAIL_END-1,C458_TAIL_END-1),
        ("upper-plus",C458_TAIL_START,C458_TAIL_END+1,C458_TAIL_END),
    ] {
        let at_boundary:Vec<Term>=selected_header.terms.iter().filter(|term|
            term.row-selected_owner*ROWS==boundary).cloned().collect();
        if at_boundary.is_empty() {
            let control=vec![gate_term(selected_owner*ROWS+boundary,
                selected_owner*WIDTH+17,selected_owner*WIDTH,Fr::zero(),Fr::one(),
                Fr::from(2u64),Fr::from(3u64))];
            let exact=c458_tail_delta_literal(&control,selected_owner,&global_tables,
                C458_TAIL_START,C458_TAIL_END,C458_TAIL_SHIFT as isize,None);
            let mutant=c458_tail_delta_literal(&control,selected_owner,&global_tables,
                start,end,C458_TAIL_SHIFT as isize,None);
            assert_ne!(exact,mutant,"C458 {name} synthetic one-term boundary control");
            println!("C458_CUTOFF_CONTROL {name} boundary_q={boundary} synthetic_one_term=true authentic_terms=0");
        } else {
            let mutant=c458_tail_delta_literal(&selected_header.terms,selected_owner,&global_tables,
                start,end,C458_TAIL_SHIFT as isize,None);
            assert_ne!(exact_literal,mutant,"C458 {name} authentic boundary term count={}",
                at_boundary.len());
        }
    }
    for shift in [C458_TAIL_SHIFT as isize-1,C458_TAIL_SHIFT as isize+1] {
        let mutant=c458_tail_delta_literal(&selected_header.terms,selected_owner,&global_tables,
            C458_TAIL_START,C458_TAIL_END,shift,None);
        assert_ne!(exact_literal,mutant,"isolated tail delta mutant shift={shift}");
    }
    println!("C458_GLOBAL_ORACLE canonical_terms={} worktree_retired_terms={} a4_terms={} tail_terms={} elapsed_ms={} oracle_eq_table_bytes={}",
        canonical.terms.len(),worktree_retired.len(),a4_terms.len(),C458_TAIL_COUNT,
        evaluate_elapsed.as_millis(),(global_tables.row.capacity()+global_tables.left.capacity()
            +global_tables.right.capacity())*std::mem::size_of::<Fr>());
}

#[test]
fn c509_pure_geometry_fixture_layout_is_separately_versioned_and_bounded() {
    assert_ne!(C509RegularLayout::digest(),CompleteLayout::digest(),
        "regular owner 845887 must not reuse selected-owner C455 identity");
    assert!(C509RegularLayout::intervals_disjoint(&C509_SOURCE_INTERVALS));
    assert!(C509RegularLayout::intervals_disjoint(&C509_DESTINATION_INTERVALS));

    for (index,(_,end)) in C509_SOURCE_INTERVALS.iter().copied().enumerate() {
        let input=gate_term(C509_OWNER*ROWS+C509_SOURCE_INTERVALS[index].0,
            C509_OWNER*WIDTH+17,C509_OWNER*WIDTH+23,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero());
        let placed=C509RegularLayout::place(index,input.clone()).unwrap();
        assert_eq!(placed.row,C509_OWNER*ROWS+C509_DESTINATION_INTERVALS[index].0);
        assert!(C509RegularLayout::require_destination(index,&placed).is_ok());
        assert_eq!((placed.gate.left,placed.gate.right),
            (input.gate.left,input.gate.right),"ROW relocation keeps exact X wires");
        let mut at_end=input;at_end.row=C509_OWNER*ROWS+end;
        assert!(C509RegularLayout::place(index,at_end).is_err(),
            "source interval end is exclusive for family {index}");
    }
    let mut wrong_destination=gate_term(C509_OWNER*ROWS+C509_DESTINATION_INTERVALS[0].1,
        C509_OWNER*WIDTH,C509_OWNER*WIDTH,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero());
    assert!(C509RegularLayout::require_destination(0,&wrong_destination).is_err());
    wrong_destination.row=C509_OWNER*ROWS+C509_DESTINATION_INTERVALS[0].0;
    assert!(C509RegularLayout::require_destination(0,&wrong_destination).is_ok());
}

#[test]
fn c509_pure_geometry_fixture_checks_order_and_operand_identity_only() {
    // These entries exercise the ordered-tuple and operand geometry kernels;
    // they do not mint a C509RegularRowSourceView or test production custody.
    let binding=HeaderSourceBinding::from_sink_for_test([1;32],[2;28],[3;32],vec![4],C509_OWNER);
    assert!(c509_source_identity(C509_OWNER,&binding,&binding));
    assert!(!c509_source_identity(C509_OWNER-1,&binding,&binding));
    for field in 0..6 {
        let wrong=binding.mutated_field_for_test(field);
        assert!(!c509_source_identity(C509_OWNER,&wrong,&binding),
            "C509 parent/owner binding field {field}");
    }
    let entries=vec![
        C509Entry{relation:C509Relation::Score(0),term:gate_term(C509_OWNER*ROWS+487421,
            C509_OWNER*WIDTH+100,C509_OWNER*WIDTH+101,Fr::zero(),Fr::one(),Fr::one(),Fr::zero())},
        C509Entry{relation:C509Relation::Score(1),term:gate_term(C509_OWNER*ROWS+502652,
            C509_OWNER*WIDTH+102,C509_OWNER*WIDTH+103,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero())},
        C509Entry{relation:C509Relation::Slack(0),term:gate_term(C509_OWNER*ROWS+491918,
            C509_OWNER*WIDTH+104,C509_OWNER*WIDTH+105,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero())},
        C509Entry{relation:C509Relation::Slack(1),term:gate_term(C509_OWNER*ROWS+507149,
            C509_OWNER*WIDTH+106,C509_OWNER*WIDTH+107,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero())},
    ];
    assert!(c509_same_ordered_entries(&entries,&entries));
    for mutant in [entries[1..].to_vec(),
        [entries.clone(),vec![entries[0].clone()]].concat(),
        vec![entries[1].clone(),entries[0].clone(),entries[2].clone(),entries[3].clone()]] {
        assert!(!c509_same_ordered_entries(&entries,&mutant),
            "missing, duplicate, and reordered Score/Slack occurrences reject");
    }

    let operands=c509_active_operands_for_term(0,entries[0].relation,&entries[0].term);
    let left=operands[0].unwrap();let right=operands[1].unwrap();
    assert_eq!((left.side,left.wire,left.c1_active,left.c2_active),
        (OperandSide::Left,C509_OWNER*WIDTH+100,true,false));
    assert_eq!((right.side,right.wire,right.c1_active,right.c2_active),
        (OperandSide::Right,C509_OWNER*WIDTH+101,false,true));
    let mut wrong_wire=entries.clone();wrong_wire[0].term.gate.left+=1;
    assert!(!c509_same_ordered_entries(&entries,&wrong_wire));
    let mut wrong_row=entries.clone();wrong_row[0].term.row+=1;
    assert!(!c509_same_ordered_entries(&entries,&wrong_row));
    let mut wrong_side=entries.clone();
    let gate=&mut wrong_side[0].term.gate;
    std::mem::swap(&mut gate.left,&mut gate.right);
    std::mem::swap(&mut gate.c1,&mut gate.c2);
    assert!(!c509_same_ordered_entries(&entries,&wrong_side));
    let mut wrong_context=entries.clone();wrong_context[0].relation=C509Relation::Score(1);
    assert!(!c509_same_ordered_entries(&entries,&wrong_context));
    let mut row_claims=BTreeMap::new();
    assert!(c509_claim_row_relation(&mut row_claims,C509_OWNER*ROWS+1,11).is_ok());
    assert!(c509_claim_row_relation(&mut row_claims,C509_OWNER*ROWS+1,11).is_ok(),
        "same relation may repeat at a shared ROW");
    assert!(c509_claim_row_relation(&mut row_claims,C509_OWNER*ROWS+1,12).is_err(),
        "different relation at the same ROW is rejected");
    // This structural fixture carries no C492 synthetic cell or physical
    // author claim; all active X operands remain open in C509.
}

#[test]
fn c509_retained_packed_candidate_to_row_typechecks_only() {
    // The function body is typechecked but never invoked with a fabricated
    // source. Runtime admission still needs a genuine retained candidate.
    fn join(candidate:&crate::packed_owner_assembly::NativePartialScoredOwnerPackedCandidate<'_, '_>)
        ->Result<(),String> {
        let view=candidate.c509_regular_row_source()?;
        let batch=C509RegularBatch::checked_from_source(&view,candidate.binding()?)?;
        let _=batch.terms()?.count();
        let _=batch.active_operands()?.count();
        Ok(())
    }
    let _=join;
}

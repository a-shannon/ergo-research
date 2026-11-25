//! No-frame c141 diagnostics. Synthetic parent descriptors carry no native
//! provenance, authenticated X, global writer, PCS, proof or client claim.
use super::*;
use crate::{h21_row_support::{EligibleParentMapSources,MapParameters,ParentMapSources},
    legacy_envelope_map::{LowerBranch,LowerSelector,LowerSource}};
use ark_ff::One;
use std::io::Write;

fn parent()->WorkTreeHistoryPlan {
    WorkTreeHistoryPlan::compile(1_827_840,21,[0x5a;32],[0x31;28]).unwrap()
}
fn parameters(exponent:usize,pivot:usize)->[MapParameters;2] {
    [1_827_840,1_827_775].map(|cut|MapParameters {cut,exponent,
        lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841729},
            branch:LowerBranch::Pivot(pivot)}})
}
fn eligible_parameters(exponent:usize,pivot:usize)->[MapParameters;2] {
    [1_827_840,1_810_842].map(|cut|MapParameters {cut,exponent,
        lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841729},
            branch:LowerBranch::Pivot(pivot)}})
}

#[test]
fn c168_eligible_map_source_preflight_is_cut_parent_and_x_bound() {
    std::thread::Builder::new().stack_size(16*1024*1024)
        .spawn(c168_eligible_map_source_preflight_body).unwrap().join().unwrap();
}
fn c168_eligible_map_source_preflight_body() {
    let parent=parent();
    let eligible=EligibleParentMapSources::new(&parent,eligible_parameters(55,54)).unwrap();
    let owner=841_727usize;
    let x=|context:usize|671_744+context*8_192..677_501+context*8_192;
    let terms=eligible.source_owner_terms(owner,0).unwrap();
    assert!(!terms.is_empty(),"selected lower Map source must be emitted");
    eligible.preflight_owner(&parent,eligible.binding(),owner,0,&terms,x(0)).unwrap();
    let mut changed=terms.clone();changed[0].gate.c0+=ark_bn254::Fr::one();
    assert_eq!(eligible.preflight_owner(&parent,eligible.binding(),owner,0,
        &changed,x(0)).unwrap_err(),"c168 emitted Map source tuples");
    for false_x in [677_501..679_549,999_424..1_000_097,
        x(0).start..x(0).end+1] {
        assert_eq!(eligible.preflight_owner(&parent,eligible.binding(),owner,0,
            &terms,false_x).unwrap_err(),"c168 Map X source domain");
    }
    assert_eq!(eligible.preflight_owner(&parent,eligible.binding(),owner,2,
        &terms,x(0)).unwrap_err(),"c168 Map context");
    // At the last eligible cut owner, the second Map no longer emits the
    // nonterminal guard. The old-cut Map still does: source tuples differ.
    let terminal_owner=1_810_841usize;
    let eligible_cut_terms=eligible.source_owner_terms(terminal_owner,1).unwrap();
    eligible.preflight_owner(&parent,eligible.binding(),terminal_owner,1,
        &eligible_cut_terms,x(1)).unwrap();
    let old_cut_map=crate::legacy_envelope_map::Map::new_modern_global_u_selected_lower(
        1_827_775,21,55,parameters(55,54)[1].lower).unwrap();
    let old_cut_terms=crate::bank53_map::map_owner_terms(&old_cut_map,terminal_owner as u64,1).unwrap();
    assert_ne!(old_cut_terms,eligible_cut_terms,"the cut must alter emitted equations");
    assert_eq!(eligible.preflight_owner(&parent,eligible.binding(),terminal_owner,1,
        &old_cut_terms,x(1)).unwrap_err(),"c168 emitted Map source tuples");
    let mut wrong=eligible_parameters(55,54);wrong[1].cut=1_827_775;
    assert_eq!(EligibleParentMapSources::new(&parent,wrong).err().unwrap(),
        "c168 exact descriptor context cut");
    let mut wrong=eligible_parameters(55,54);wrong.swap(0,1);
    assert_eq!(EligibleParentMapSources::new(&parent,wrong).err().unwrap(),
        "c168 exact descriptor context cut");
    let h20=crate::legacy_envelope_map::Map::new(1_000_000,20,0).unwrap();
    assert_eq!(crate::bank53_map::map_owner_terms_for_descriptor(&h20,0,0,
        crate::h21_scheduled_max_cap::CutDescriptor::eligible08()).unwrap_err(),
        "bank53 descriptor requires H21 Map geometry");
    let mut wrong=eligible.binding().clone();wrong.cut_identity[0]^=1;
    assert_eq!(eligible.preflight_owner(&parent,&wrong,owner,0,&terms,x(0)).unwrap_err(),
        "c168 eligible parent/Map/cut source binding");
    let mut wrong=eligible.binding().clone();wrong.maps[0].e+=1;
    assert_eq!(eligible.preflight_owner(&parent,&wrong,owner,0,&terms,x(0)).unwrap_err(),
        "c168 eligible parent/Map/cut source binding");
    let different=WorkTreeHistoryPlan::compile(1_827_840,21,[0x5b;32],[0x31;28]).unwrap();
    assert_eq!(eligible.preflight_owner(&different,eligible.binding(),owner,0,&terms,x(0)).unwrap_err(),
        "c168 eligible parent/Map/cut source binding");
    let different=WorkTreeHistoryPlan::compile(1_827_840,21,[0x5a;32],[0x32;28]).unwrap();
    assert_eq!(eligible.preflight_owner(&different,eligible.binding(),owner,0,&terms,x(0)).unwrap_err(),
        "c168 eligible parent/Map/cut source binding");
    let alternate=EligibleParentMapSources::new(&parent,eligible_parameters(56,55)).unwrap();
    let alternate_terms=alternate.source_owner_terms(owner,0).unwrap();
    assert_eq!(eligible.preflight_owner(&parent,eligible.binding(),owner,0,
        &alternate_terms,x(0)).unwrap_err(),"c168 emitted Map source tuples");
    assert_eq!(eligible.preflight_owner(&parent,alternate.binding(),owner,0,
        &terms,x(0)).unwrap_err(),"c168 eligible parent/Map/cut source binding");
    let diagnostic=ParentMapSources::new(&parent,parameters(55,54)).unwrap();
    assert_ne!(diagnostic.binding().cut_identity,eligible.binding().cut_identity);
    assert_eq!(eligible.preflight_owner(&parent,diagnostic.binding(),owner,0,
        &terms,x(0)).unwrap_err(),"c168 eligible parent/Map/cut source binding");
    println!("C168_ELIGIBLE_MAP_PREFLIGHT_PASS contexts=2 parent_cut_source=true terminal_equations_differ=true altered_tuple=true score_max_x_claims_rejected=true ledger=false global_x=false proof=false");
}
fn reject(merger:&mut ParentBoundMerger,parent:&WorkTreeHistoryPlan,
    candidate:ParentBoundCandidate,expected:&str) {
    let before=merger.destination.clone();
    let error=merger.publish(parent,candidate).err().expect("isolated rejection");
    assert!(error.contains(expected),"expected {expected}, got {error}");
    assert_eq!(merger.destination,before,"failed publication changed destination");
}

#[test]
fn c141_parent_map_binding_and_exact_context_cuts() {
    let p=parent();
    let sources=ParentMapSources::new(&p,parameters(55,54)).unwrap();
    sources.validate(&p,sources.binding()).unwrap();
    let mut wrong=sources.binding().clone();wrong.root[0]^=1;
    assert!(sources.validate(&p,&wrong).is_err());
    let mut wrong=sources.binding().clone();wrong.total[0]^=1;
    assert!(sources.validate(&p,&wrong).is_err());
    let mut wrong=sources.binding().clone();wrong.headers-=1;
    assert!(sources.validate(&p,&wrong).is_err());
    let mut wrong=sources.binding().clone();wrong.slot_log-=1;
    assert!(sources.validate(&p,&wrong).is_err());
    let mut wrong=sources.binding().clone();wrong.maps.swap(0,1);
    assert!(sources.validate(&p,&wrong).is_err());
    let alternate=ParentMapSources::new(&p,parameters(56,55)).unwrap();
    assert!(sources.validate(&p,alternate.binding()).is_err());
    let alternate=ParentMapSources::new(&p,parameters(55,52)).unwrap();
    assert!(sources.validate(&p,alternate.binding()).is_err());
    // The lower-selector parameter reaches the real emitted source tuples at
    // its selected D owner, rather than existing only in a wrapper label.
    let terms=|s:&ParentMapSources|s.sources().stage_sparse_score_owner(841727).unwrap()
        .terms().iter().map(|t|RowClaim {writer:support_row_writer(t.writer),term:t.term.clone()})
        .collect::<Vec<_>>();
    assert!(!gate_multisets_equal(&row_claim_multiset(&terms(&sources)),
        &row_claim_multiset(&terms(&alternate))));
    let mut wrong=parameters(55,54);wrong[1].cut+=1;
    assert_eq!(ParentMapSources::new(&p,wrong).err().unwrap(),"c141 exact context cut");
    let different=WorkTreeHistoryPlan::compile(1_827_840,21,[0x5b;32],[0x31;28]).unwrap();
    assert!(sources.validate(&different,sources.binding()).is_err());
    println!("C141_BINDING_PASS isolated_negatives=9 maps_symbolic=true source_parent_bound=true native=false");
}

#[test]
fn c141_three_owner_actual_local_publication_and_atomic_late_fault() {
    let started=std::time::Instant::now();
    let p=parent();let mut merger=ParentBoundMerger::new(&p,parameters(55,54)).unwrap();
    let mut published_rows=0;let mut published_terms=0;
    for owner in [844_670,844_672,845_759] {
        let staged=merger.stage(&p,owner).unwrap();
        let mut bad=staged.clone();bad.binding.maps[0].e+=1;
        reject(&mut merger,&p,bad,"complete parent/Map source binding");
        if owner==844_672 {
            // A coherent change to both staged copies still differs from the
            // independently retained immutable ROW source.
            let mut bad=staged.clone();bad.candidate.rows[0].term.gate.c0+=ark_bn254::Fr::one();
            bad.candidate.row_source[0].term.gate.c0+=ark_bn254::Fr::one();
            reject(&mut merger,&p,bad,"immutable source ROW occurrence multiset");
            let mut bad=staged.clone();
            let index=bad.candidate.support_source.iter().position(|t|
                matches!(t.writer,SupportWriter::Relocated(Family::Map(0)))).unwrap();
            bad.candidate.support_source[index].term.gate.c0+=ark_bn254::Fr::one();
            bad.candidate.support[index].term.gate.c0+=ark_bn254::Fr::one();
            reject(&mut merger,&p,bad,"emitted source tuple/reservation multiset");
            let alternate=ParentMapSources::new(&p,parameters(56,55)).unwrap();
            let stale=alternate.sources().stage_sparse_score_owner(owner).unwrap();
            let mut bad=staged.clone();
            bad.candidate.support=stale.terms().to_vec();
            bad.candidate.support_source=stale.terms().to_vec();
            bad.candidate.reservations=stale.reservations().collect();
            bad.candidate.reservation_source=stale.reservations().collect();
            reject(&mut merger,&p,bad,"emitted source tuple/reservation multiset");
            // Duplicate an exact source occurrence in both mutable copies.
            let mut bad=staged.clone();
            bad.candidate.support_source.push(bad.candidate.support_source[index].clone());
            bad.candidate.support.push(bad.candidate.support[index].clone());
            reject(&mut merger,&p,bad,"emitted source tuple/reservation multiset");
            // Force the late X-overlap check, after this owner's ROWs have
            // been staged into the publisher's temporary next destination.
            let obstruction=XDomain {writer:XWriter::Map(0),start:owner*WIDTH+671744,
                end:owner*WIDTH+671745};
            merger.destination.x.push(obstruction);
            reject(&mut merger,&p,staged.clone(),"destination X domain overlap");
            merger.destination.x.pop();
            let row=staged.candidate.rows[0].term.row;
            merger.destination.rows.insert(row,RowWriter::Header);
            reject(&mut merger,&p,staged.clone(),"destination ROW already occupied");
            merger.destination.rows.remove(&row);
        }
        let expected_local=row_claim_multiset(&staged.candidate.row_source);
        assert!(gate_multisets_equal(&expected_local,&row_claim_multiset(&staged.source_rows)));
        let ledger=merger.publish(&p,staged.clone()).unwrap();
        assert!(ledger.rows.iter().all(|(row,_)|row/ROWS==owner));
        assert_eq!(ledger.source_term_count,ledger.terms.len());
        assert!(ledger.terms.len()>ledger.rows.len(),"source multiplicity lost");
        assert_eq!(ledger.x.first().unwrap().start,owner*WIDTH);
        assert_eq!(ledger.x.last().unwrap().end,(owner+1)*WIDTH);
        assert!(ledger.x.windows(2).all(|w|w[0].end==w[1].start));
        published_rows+=ledger.rows.len();published_terms+=ledger.terms.len();
        reject(&mut merger,&p,staged,"destination ROW already occupied");
        println!("C141_OWNER_PASS owner={owner} rows={} terms={} elapsed_s={:.6}",
            ledger.rows.len(),ledger.terms.len(),started.elapsed().as_secs_f64());
        std::io::stdout().flush().unwrap();
    }
    assert_eq!(merger.destination.rows.len(),published_rows);
    assert_eq!(merger.destination.terms.len(),published_terms);
    let mut domains=merger.destination.x.clone();domains.sort_by_key(|d|d.start);
    assert!(domains.windows(2).all(|w|w[0].end<=w[1].start));
    // Local semantic writers cannot share a ROW even when gate values match.
    let mut semantic=BTreeMap::new();insert_row(&mut semantic,17,RowWriter::Header).unwrap();
    assert!(insert_row(&mut semantic,17,RowWriter::Daa(3)).is_err());
    for owner in [10175,3070] {
        assert_eq!(merger.stage(&p,owner).err().unwrap(),"c141 owner outside admitted LOCAL set");
    }
    println!("C141_MULTIOWNER_PASS owners=3 namespace=LOCAL source_multiplicity=true disjoint_x=true atomic_late_fault=true global_writer=false native=false proof=false");
}

#[test]
fn c141_q9_private_source_probe_does_not_expand_admission() {
    let p=parent();let sources=ParentMapSources::new(&p,parameters(55,54)).unwrap();
    // D3070 is a typed read at q9, not a requested owner-writer publication.
    let map=crate::legacy_envelope_map::Map::new_modern_global_u_selected_lower(
        1_827_840,21,55,parameters(55,54)[0].lower).unwrap();
    assert!(map.imports(10175).unwrap().iter().any(|i|
        i.owner==3070&&i.kind==crate::legacy_envelope_map::Kind::Difficulty));
    let mut destination=Destination::default();
    let result=Candidate::stage_from_sources(&p,10175,sources.sources())
        .map_err(|e|format!("stage: {e}"))
        .and_then(|candidate| {let class=candidate.class;
            close_source_candidate(candidate,10175,class).map_err(|e|format!("close: {e}"))})
        .and_then(|ledger|Ledger::publish_closed(ledger,&mut destination).map_err(|e|format!("publish: {e}")));
    match result {
        Ok(ledger)=>{
            assert_eq!(ledger.class,OwnerClass::Carry);
            assert_eq!(map.imports(10175).unwrap().len(),18);
            assert_eq!(destination.rows,ledger.rows);
            assert_eq!(destination.terms,ledger.terms);
            assert_eq!(destination.x,ledger.x);
            assert_eq!(ledger.x.iter().map(|x|x.end-x.start).sum::<usize>(),WIDTH);
            println!("C141_Q9_SOURCE_PROBE source_closed=true published=true rows={} terms={} domains={} imports=18 class=Carry public_admission=false native=false",
                ledger.rows.len(),ledger.terms.len(),ledger.x.len());
        },
        Err(error)=>{
            assert_eq!(destination,Destination::default());
            println!("C141_Q9_SOURCE_PROBE source_closed=false first_error={error:?} public_admission=false native=false");
        },
    }
    let merger=ParentBoundMerger::new(&p,parameters(55,54)).unwrap();
    assert_eq!(merger.stage(&p,10175).err().unwrap(),"c141 owner outside admitted LOCAL set");
    assert!(merger.destination.rows.is_empty());
}

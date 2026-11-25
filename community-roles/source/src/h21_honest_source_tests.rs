//! Pure boundary fixtures do not mint a native source or a closed stream.
use super::*;
use crate::packed_owner_assembly::NativeRegularPhysicalAuthor as Physical;

type ReadFixture = ((usize, ScoreRelationReadAuthor, Fr),
    (usize, ScoreReplayAuthor, bool), (usize, ScoreReplayAuthor, bool));

fn fixture(bit: usize) -> ReadFixture {
    let layout = crate::origin_score::Layout::new();
    let value = bit % 2 != 0;
    let source = 845_887 * WIDTH + 677_501 + layout.r.start + bit;
    let destination = 846_015 * WIDTH + 677_501 + layout.p.start + bit;
    ((source, ScoreRelationReadAuthor::PreviousR {context:0,owner:845_887}, Fr::from(value as u64)),
        (source, c574_author(845_887).unwrap(), value),
        (destination, c574_author(846_015).unwrap(), value))
}

fn check(fixtures: &[ReadFixture]) -> Result<(), String> {
    for (bit, &(read, source, destination)) in fixtures.iter().enumerate() {
        c574_check_read(bit, read, source, destination)?;
    }
    c574_require_census(fixtures.len(), false)
}

#[test]
fn c574_ordered_previous_r_original_fr_and_author_single_faults() {
    c576_physical_import_controls();
    c578_physical_upper_controls();
    let pristine: Vec<_> = (0..225).map(fixture).collect();
    check(&pristine).unwrap();
    for fault in 0..22 {
        let mut rows = pristine.clone();
        let (read, source, destination) = &mut rows[0];
        match fault {
            0 => read.0 += 1,
            1 => read.1 = ScoreRelationReadAuthor::PreviousR {context:1,owner:845_887},
            2 => read.1 = ScoreRelationReadAuthor::PreviousR {context:0,owner:845_759},
            3 => read.2 = Fr::from(2u64),
            4 => read.2 = Fr::one(),
            5 => source.0 += 1, 6 => destination.0 += 1,
            7 => source.1.context = 1, 8 => source.1.origin += 1,
            9 => source.1.previous_owner += 1, 10 => source.1.max_owner += 1,
            11 => source.1.cap_owner += 1,
            12 => destination.1.context = 1, 13 => destination.1.origin += 1,
            14 => destination.1.previous_owner += 1, 15 => destination.1.max_owner += 1,
            16 => destination.1.cap_owner += 1,
            17 => source.2 = true, 18 => destination.2 = true,
            19 => { rows.remove(0); }, // omitted zero-valued occurrence
            20 => { rows[1] = rows[0]; },
            _ => rows.swap(0, 1),
        }
        assert!(check(&rows).is_err(), "fault{fault}");
    }
    let mut extra = pristine.clone(); extra.push(fixture(0));
    assert!(check(&extra).is_err());
    assert!(c574_require_census(224, false).is_err());
    assert!(c574_require_census(225, true).is_err());
    let (mut read, source, destination) = fixture(0);
    read.2 = Fr::from(2u64);
    assert_eq!(c574_check_read(0,read,source,destination).unwrap_err(),
        "C574 non-Boolean retained Fr occurrence");
}

#[test]
fn c574_row_replay_zero_inclusive_authors_and_order() {
    let bytes = vec![0u8;8192];
    let authors = vec![Some(Physical::Scored);8192*8];
    c574_replay_chunk(845_887,0,&bytes,&authors,&bytes,&authors).unwrap();
    let mut bad_bytes = bytes.clone(); bad_bytes[0] = 1;
    assert!(c574_replay_chunk(845_887,0,&bytes,&authors,&bad_bytes,&authors).is_err());
    for wrong in [None, Some(Physical::Header), Some(Physical::Tree), Some(Physical::Daa)] {
        let mut bad = authors.clone(); bad[0] = wrong;
        assert!(c574_replay_chunk(845_887,0,&bytes,&authors,&bytes,&bad).is_err());
    }
    let mut missing = authors.clone(); missing[0] = None;
    assert!(c574_replay_chunk(845_887,0,&bytes,&missing,&bytes,&missing).is_err());
    assert!(c574_replay_chunk(845_887,1,&bytes,&authors,&bytes,&authors).is_err());
    assert!(c574_replay_chunk(845_887,0,&bytes[..8191],&authors,&bytes,&authors).is_err());
    let mut cursor = C574RowCursor::new();
    assert!(cursor.complete().is_err());
    assert!(cursor.accept(846_015,0,8192).is_err());
    assert!(cursor.accept(845_887,8192,8192).is_err());
    for owner in [845_887,846_015] {
        for offset in (0..WIDTH/8).step_by(8192) { cursor.accept(owner,offset,8192).unwrap(); }
    }
    cursor.complete().unwrap();
    assert!(cursor.accept(846_015,0,8192).is_err());
}

#[test]
fn c574_budget_atomicity_and_actual_writer_policy() {
    crate::packed_owner_assembly::c578_factory_controls_for_test().unwrap();
    let work_bound=crate::packed_owner_assembly::c578_work_retained_bound().unwrap();
    let mut work=C578WorkBudget::new(1,896,work_bound);
    work.charge(1,448,work_bound).unwrap();let work_before=work.usage();
    for delta in [(1,0,0),(0,449,0),(0,0,work_bound+1)] {
        assert!(work.charge(delta.0,delta.1,delta.2).is_err());
        assert_eq!(work.usage(),work_before);
    }
    work.charge(0,448,0).unwrap();assert_eq!(work.usage(),[1,896,work_bound]);
    let mut zero_work=C578WorkBudget::new(0,896,work_bound);
    assert!(zero_work.charge(1,0,work_bound).is_err());assert_eq!(zero_work.usage(),[0;3]);
    let mut overflow_work=C578WorkBudget::new(usize::MAX,usize::MAX,work_bound);
    overflow_work.charge(usize::MAX,0,0).unwrap();
    assert!(overflow_work.charge(1,0,0).is_err());assert_eq!(overflow_work.usage(),[usize::MAX,0,0]);
    let mut physical=C576MaxBudget::new(1,896,1024);
    physical.charge(1,448,1024).unwrap();let before=physical.usage();
    for delta in [(1,0,0),(0,449,0),(0,0,1025)] {
        assert!(physical.charge(delta.0,delta.1,delta.2).is_err());assert_eq!(physical.usage(),before);
    }
    physical.charge(0,448,0).unwrap();assert_eq!(physical.usage(),[1,896,1024]);
    let mut budget = C574Budget::new(4,262144,225,usize::MAX);
    budget.charge(4,262144,225,1).unwrap();
    let before = budget.usage();
    for delta in [(1,0,0,0),(0,1,0,0),(0,0,1,0)] {
        assert!(budget.charge(delta.0,delta.1,delta.2,delta.3).is_err());
        assert_eq!(budget.usage(),before);
    }
    let mut zero = C574Budget::new(4,262144,225,0);
    assert!(zero.charge(0,0,0,1).is_err());
    assert_eq!(zero.usage(),[0;4]);
    let mut overflow = C574Budget::new(usize::MAX,usize::MAX,usize::MAX,usize::MAX);
    overflow.charge(usize::MAX,0,0,0).unwrap();
    assert!(overflow.charge(1,0,0,0).is_err());
    crate::packed_owner_assembly::c574_writer_controls_for_test().unwrap();
    super::super::h21_eligible_score::c575_structural_guard_controls();
}

fn c578_physical_upper_controls() {
    use crate::packed_owner_assembly::NativeWorkEndpointAuthor;
    c578_require_upper_census(448,224).unwrap();
    for (occurrences,unique) in [(447,224),(449,224),(448,223),(448,225)] {
        assert_eq!(c578_require_upper_census(occurrences,unique).unwrap_err(),
            "C578 exact448 Upper occurrences/224 coordinates");
    }
    for ordinal in 0..448 {
        let bit=ordinal%224;
        let read=OpenScoredRead {wire:846_014*WIDTH+987_450+bit,
            author:OpenScoredReadAuthor::WorkUpper{owner:846_014,height:846_016},value:Fr::zero()};
        let physical=(NativeWorkEndpointAuthor::Tree,Fr::zero());
        c578_check_upper_import(ordinal,&read,physical).unwrap();
        if [0,223,224,447].contains(&ordinal) {for fault in 0..8 {
            let mut bad=read;let mut actual=physical;
            let expected=match fault {
                0=>{bad.wire+=224;"C578 Upper occurrence/domain/typed author"},
                1=>{bad.author=OpenScoredReadAuthor::WorkUpper{owner:846_013,height:846_016};"C578 Upper occurrence/domain/typed author"},
                2=>{bad.author=OpenScoredReadAuthor::WorkUpper{owner:846_014,height:846_017};"C578 Upper occurrence/domain/typed author"},
                3=>{bad.author=OpenScoredReadAuthor::PreviousR{context:1,owner:846_014};"C578 Upper occurrence/domain/typed author"},
                4=>{bad.value=Fr::from(2u64);"C578 expected Upper Fr is not Boolean"},
                5=>{actual.1=Fr::from(2u64);"C578 original Upper Fr is not Boolean"},
                6=>{actual.1=Fr::one();"C578 physical Upper/Score.sw value mismatch"},
                _=>{bad.wire+=1;"C578 Upper occurrence/domain/typed author"},
            };
            assert_eq!(c578_check_upper_import(ordinal,&bad,actual).unwrap_err(),expected);
            c578_check_upper_import(ordinal,&read,physical).unwrap();
        }}
        if ordinal>0 && ordinal%224!=0 {
            assert!(c578_check_upper_import(ordinal-1,&read,physical).is_err());
        }
    }
    let read=OpenScoredRead {wire:846_014*WIDTH+987_450,
        author:OpenScoredReadAuthor::WorkUpper{owner:846_014,height:846_016},value:Fr::zero()};
    assert_eq!(c578_check_upper_import(448,&read,(NativeWorkEndpointAuthor::Tree,Fr::zero())).unwrap_err(),
        "C578 Upper occurrence extent");
}

// Pure read-edge mechanics only; no stream or physical row can be minted here.
fn c576_physical_import_controls() {
    use crate::h21_scheduled_max_cap::{MaxReplayAuthor,Writer};
    for ordinal in 0..448 {
        let context=ordinal/224;let bit=ordinal%224;
        let read=OpenScoredRead {wire:844_926*WIDTH+[999_424,1_000_097][context]+bit,
            author:OpenScoredReadAuthor::Max{context,end:844_928},value:Fr::zero()};
        let actual=(MaxReplayAuthor::Scheduled(Writer::Max{context,end:844_928}),Fr::zero());
        c576_check_physical_import(ordinal,&read,actual).unwrap();
        if [0,223,224,447].contains(&ordinal) {for fault in 0..9 {
            let mut wrong=read;let mut physical=actual;
            let expected=match fault {
                0=>{wrong.wire+=1;"C576 physical import global order/coordinate/typed author"},
                1=>{wrong.author=OpenScoredReadAuthor::Max{context:1-context,end:844_928};"C576 physical import global order/coordinate/typed author"},
                2=>{wrong.author=OpenScoredReadAuthor::Max{context,end:844_929};"C576 physical import global order/coordinate/typed author"},
                3=>{physical.0=MaxReplayAuthor::NativeWorkD{height:844_928};"C576 physical import global order/coordinate/typed author"},
                4=>{physical.0=MaxReplayAuthor::Scheduled(Writer::Max{context:1-context,end:844_928});"C576 physical import global order/coordinate/typed author"},
                5=>{physical.0=MaxReplayAuthor::Scheduled(Writer::Max{context,end:844_929});"C576 physical import global order/coordinate/typed author"},
                6=>{physical.1=Fr::from(2u8);"C576 original physical import Fr is not Boolean"},
                7=>{wrong.value=Fr::from(2u8);"C576 expected import Fr is not Boolean"},
                _=>{physical.1=Fr::one();"C576 physical/Cap import value mismatch"},
            };
            assert_eq!(c576_check_physical_import(ordinal,&wrong,physical).unwrap_err(),expected);
            c576_check_physical_import(ordinal,&read,actual).unwrap();
        }}
    }
}

#[test]
#[ignore]
fn c574_native_second_regular_previous_r_rows() -> Result<(), String> {
    use crate::packed_owner_assembly::H21EligibleContext;
    use crate::h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxStream, Plan as MaxPlan};
    use crate::work_tree_history_plan::WorkTreeHistoryPlan;
    // Cheap code-owned fixed factory/policy checks precede full-prefix work.
    crate::packed_owner_assembly::c578_factory_controls_for_test()?;
    crate::packed_owner_assembly::c574_writer_controls_for_test()?;
    crate::h21_native_admission_tests::c574_with_pinned_prefix(|prefix| {
        let plan = WorkTreeHistoryPlan::compile(1_827_840,21,prefix.root(),prefix.total_be28())?;
        let context = H21EligibleContext::new(&plan,prefix)?;
        let snapshot = Eligible08NativeSnapshot::new(&plan,prefix)?;
        let mut max = MaxStream::new(&plan,prefix,&snapshot)?;
        for (owner,_) in MaxPlan::eligible08().max_calendar() {
            max.push_native(&context.producer,owner)?;
        }
        // Reuse this exact closed stream; no second 7,683-owner pass.
        // A fresh empty stream supplies only a distinct identity for a refusal.
        // It does not repeat the closed stream's owner replay.
        let other_max = MaxStream::new(&plan, prefix, &snapshot)?;
        crate::packed_owner_assembly::c581_native_coactive_probe(
            &context.producer, &max, &other_max)?;
        let mut score = context.score_endpoint_stream(&max)?;
        score.c575_check_incomplete_source_gate()?;
        while let Some(owner) = score.next_owner() { score.push_native(owner)?; }
        score.terminal_r()?;
        let retained = 4 * (2*(WIDTH/8) + WIDTH*std::mem::size_of::<Option<Physical>>());
        let mut budget = C574Budget::new(4,2*(WIDTH/8),225,retained);
        let max_bound=crate::packed_owner_assembly::c576_max_retained_bound(844_926)?;
        let mut max_budget=C576MaxBudget::new(1,896,max_bound);
        let work_bound=crate::packed_owner_assembly::c578_work_retained_bound()?;
        let mut work_budget=C578WorkBudget::new(1,896,work_bound);
        let mut chunks = 0usize;
        let usage = crate::packed_owner_assembly::c578_with_native_assembly_checks(|| score.c575_with_native_carrier_checks(|| {
            score.c574_second_regular_rows(&mut budget,&mut max_budget,&mut work_budget,|_,_,_,_| {
                chunks = chunks.checked_add(1).ok_or("C574 sink chunk counter overflow")?;
                Ok(())
            })
        }))?;
        if chunks != 32 || usage != [4,2*(WIDTH/8),225,retained] {
            return Err("C574 actual sink work census".into());
        }
        if max_budget.usage()!=[1,896,max_bound] {return Err("C576 native MAX assembly/import/retained counters".into());}
        if work_budget.usage()!=[1,896,work_bound] {return Err("C578 native Work assembly/import/retained counters".into());}
        println!("C574_NATIVE_SECOND_REGULAR_ROWS_PASS donor=845887 destination=846015 context=0 reads=225 rows=2 replay=true global=false proof=false");
        Ok(())
    })
}
